import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical117
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical138
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical162
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical168
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical174
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical177
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical181
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical190
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical197
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical215
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical217
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical220
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical229
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical230
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical231
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical232
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical233

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA2144 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2144 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC2144 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceForm2144 : Integer.Sparse Master := [(Sum.inr 933, 2), (Sum.inr 938, 2), (Sum.inr 1050, 1), (Sum.inr 2334, 4), (Sum.inr 2342, 2), (Sum.inr 2344, 2), (Sum.inr 2432, 2), (Sum.inr 2489, 2), (Sum.inr 2595, 4), (Sum.inr 2598, 2), (Sum.inr 2767, 2), (Sum.inr 3931, 2), (Sum.inr 3934, 1), (Sum.inr 4000, 2)]

theorem sourceEq2144 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2144 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2144 + difference 0 1) (sourceB2144 + difference 1 0) sourceC2144) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3934) := by
    have ha : (tripleCharges (sourceA2144 + difference 0 1) (sourceB2144 + difference 1 0) sourceC2144) = raw29660 := by
      apply Matrix.ext; unfold tripleCharges sourceA2144 sourceB2144 sourceC2144 difference raw29660; decide +kernel
    rw [ha]
    exact (canonical29660 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2144 + difference 0 2) (sourceB2144 + difference 2 0) sourceC2144) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3931) := by
    have ha : (tripleCharges (sourceA2144 + difference 0 2) (sourceB2144 + difference 2 0) sourceC2144) = raw29661 := by
      apply Matrix.ext; unfold tripleCharges sourceA2144 sourceB2144 sourceC2144 difference raw29661; decide +kernel
    rw [ha]
    exact (canonical29661 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2144 + difference 0 3) (sourceB2144 + difference 3 0) sourceC2144) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3931) := by
    have ha : (tripleCharges (sourceA2144 + difference 0 3) (sourceB2144 + difference 3 0) sourceC2144) = raw29662 := by
      apply Matrix.ext; unfold tripleCharges sourceA2144 sourceB2144 sourceC2144 difference raw29662; decide +kernel
    rw [ha]
    exact (canonical29662 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2144 + difference 0 4) (sourceB2144 + difference 4 0) sourceC2144) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4000) := by
    have ha : (tripleCharges (sourceA2144 + difference 0 4) (sourceB2144 + difference 4 0) sourceC2144) = raw2802 := by
      apply Matrix.ext; unfold tripleCharges sourceA2144 sourceB2144 sourceC2144 difference raw2802; decide +kernel
    rw [ha]
    exact (canonical2802 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2144 + difference 0 5) (sourceB2144 + difference 5 0) sourceC2144) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4000) := by
    have ha : (tripleCharges (sourceA2144 + difference 0 5) (sourceB2144 + difference 5 0) sourceC2144) = raw29663 := by
      apply Matrix.ext; unfold tripleCharges sourceA2144 sourceB2144 sourceC2144 difference raw29663; decide +kernel
    rw [ha]
    exact (canonical29663 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2144 + difference 1 0) (sourceB2144 + difference 0 1) sourceC2144) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1050) := by
    have ha : (tripleCharges (sourceA2144 + difference 1 0) (sourceB2144 + difference 0 1) sourceC2144) = raw21515 := by
      apply Matrix.ext; unfold tripleCharges sourceA2144 sourceB2144 sourceC2144 difference raw21515; decide +kernel
    rw [ha]
    exact (canonical21515 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2144 + difference 1 2) (sourceB2144 + difference 2 1) sourceC2144) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2489) := by
    have ha : (tripleCharges (sourceA2144 + difference 1 2) (sourceB2144 + difference 2 1) sourceC2144) = raw23240 := by
      apply Matrix.ext; unfold tripleCharges sourceA2144 sourceB2144 sourceC2144 difference raw23240; decide +kernel
    rw [ha]
    exact (canonical23240 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2144 + difference 1 3) (sourceB2144 + difference 3 1) sourceC2144) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2489) := by
    have ha : (tripleCharges (sourceA2144 + difference 1 3) (sourceB2144 + difference 3 1) sourceC2144) = raw23241 := by
      apply Matrix.ext; unfold tripleCharges sourceA2144 sourceB2144 sourceC2144 difference raw23241; decide +kernel
    rw [ha]
    exact (canonical23241 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2144 + difference 1 4) (sourceB2144 + difference 4 1) sourceC2144) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2767) := by
    have ha : (tripleCharges (sourceA2144 + difference 1 4) (sourceB2144 + difference 4 1) sourceC2144) = raw2801 := by
      apply Matrix.ext; unfold tripleCharges sourceA2144 sourceB2144 sourceC2144 difference raw2801; decide +kernel
    rw [ha]
    exact (canonical2801 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2144 + difference 1 5) (sourceB2144 + difference 5 1) sourceC2144) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2767) := by
    have ha : (tripleCharges (sourceA2144 + difference 1 5) (sourceB2144 + difference 5 1) sourceC2144) = raw23242 := by
      apply Matrix.ext; unfold tripleCharges sourceA2144 sourceB2144 sourceC2144 difference raw23242; decide +kernel
    rw [ha]
    exact (canonical23242 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2144 + difference 2 0) (sourceB2144 + difference 0 2) sourceC2144) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 933) := by
    have ha : (tripleCharges (sourceA2144 + difference 2 0) (sourceB2144 + difference 0 2) sourceC2144) = raw23248 := by
      apply Matrix.ext; unfold tripleCharges sourceA2144 sourceB2144 sourceC2144 difference raw23248; decide +kernel
    rw [ha]
    exact (canonical23248 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2144 + difference 2 1) (sourceB2144 + difference 1 2) sourceC2144) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2342) := by
    have ha : (tripleCharges (sourceA2144 + difference 2 1) (sourceB2144 + difference 1 2) sourceC2144) = raw29664 := by
      apply Matrix.ext; unfold tripleCharges sourceA2144 sourceB2144 sourceC2144 difference raw29664; decide +kernel
    rw [ha]
    exact (canonical29664 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2144 + difference 2 3) (sourceB2144 + difference 3 2) sourceC2144) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2432) := by
    have ha : (tripleCharges (sourceA2144 + difference 2 3) (sourceB2144 + difference 3 2) sourceC2144) = raw29665 := by
      apply Matrix.ext; unfold tripleCharges sourceA2144 sourceB2144 sourceC2144 difference raw29665; decide +kernel
    rw [ha]
    exact (canonical29665 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2144 + difference 2 4) (sourceB2144 + difference 4 2) sourceC2144) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2595) := by
    have ha : (tripleCharges (sourceA2144 + difference 2 4) (sourceB2144 + difference 4 2) sourceC2144) = raw27601 := by
      apply Matrix.ext; unfold tripleCharges sourceA2144 sourceB2144 sourceC2144 difference raw27601; decide +kernel
    rw [ha]
    exact (canonical27601 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2144 + difference 2 5) (sourceB2144 + difference 5 2) sourceC2144) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2595) := by
    have ha : (tripleCharges (sourceA2144 + difference 2 5) (sourceB2144 + difference 5 2) sourceC2144) = raw29666 := by
      apply Matrix.ext; unfold tripleCharges sourceA2144 sourceB2144 sourceC2144 difference raw29666; decide +kernel
    rw [ha]
    exact (canonical29666 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2144 + difference 3 0) (sourceB2144 + difference 0 3) sourceC2144) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 933) := by
    have ha : (tripleCharges (sourceA2144 + difference 3 0) (sourceB2144 + difference 0 3) sourceC2144) = raw23252 := by
      apply Matrix.ext; unfold tripleCharges sourceA2144 sourceB2144 sourceC2144 difference raw23252; decide +kernel
    rw [ha]
    exact (canonical23252 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2144 + difference 3 1) (sourceB2144 + difference 1 3) sourceC2144) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2342) := by
    have ha : (tripleCharges (sourceA2144 + difference 3 1) (sourceB2144 + difference 1 3) sourceC2144) = raw29667 := by
      apply Matrix.ext; unfold tripleCharges sourceA2144 sourceB2144 sourceC2144 difference raw29667; decide +kernel
    rw [ha]
    exact (canonical29667 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2144 + difference 3 2) (sourceB2144 + difference 2 3) sourceC2144) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2432) := by
    have ha : (tripleCharges (sourceA2144 + difference 3 2) (sourceB2144 + difference 2 3) sourceC2144) = raw29668 := by
      apply Matrix.ext; unfold tripleCharges sourceA2144 sourceB2144 sourceC2144 difference raw29668; decide +kernel
    rw [ha]
    exact (canonical29668 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2144 + difference 3 4) (sourceB2144 + difference 4 3) sourceC2144) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2595) := by
    have ha : (tripleCharges (sourceA2144 + difference 3 4) (sourceB2144 + difference 4 3) sourceC2144) = raw25256 := by
      apply Matrix.ext; unfold tripleCharges sourceA2144 sourceB2144 sourceC2144 difference raw25256; decide +kernel
    rw [ha]
    exact (canonical25256 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2144 + difference 3 5) (sourceB2144 + difference 5 3) sourceC2144) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2595) := by
    have ha : (tripleCharges (sourceA2144 + difference 3 5) (sourceB2144 + difference 5 3) sourceC2144) = raw29669 := by
      apply Matrix.ext; unfold tripleCharges sourceA2144 sourceB2144 sourceC2144 difference raw29669; decide +kernel
    rw [ha]
    exact (canonical29669 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2144 + difference 4 0) (sourceB2144 + difference 0 4) sourceC2144) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 938) := by
    have ha : (tripleCharges (sourceA2144 + difference 4 0) (sourceB2144 + difference 0 4) sourceC2144) = raw23256 := by
      apply Matrix.ext; unfold tripleCharges sourceA2144 sourceB2144 sourceC2144 difference raw23256; decide +kernel
    rw [ha]
    exact (canonical23256 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2144 + difference 4 1) (sourceB2144 + difference 1 4) sourceC2144) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2344) := by
    have ha : (tripleCharges (sourceA2144 + difference 4 1) (sourceB2144 + difference 1 4) sourceC2144) = raw29670 := by
      apply Matrix.ext; unfold tripleCharges sourceA2144 sourceB2144 sourceC2144 difference raw29670; decide +kernel
    rw [ha]
    exact (canonical29670 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2144 + difference 4 2) (sourceB2144 + difference 2 4) sourceC2144) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2334) := by
    have ha : (tripleCharges (sourceA2144 + difference 4 2) (sourceB2144 + difference 2 4) sourceC2144) = raw29671 := by
      apply Matrix.ext; unfold tripleCharges sourceA2144 sourceB2144 sourceC2144 difference raw29671; decide +kernel
    rw [ha]
    exact (canonical29671 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2144 + difference 4 3) (sourceB2144 + difference 3 4) sourceC2144) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2334) := by
    have ha : (tripleCharges (sourceA2144 + difference 4 3) (sourceB2144 + difference 3 4) sourceC2144) = raw29672 := by
      apply Matrix.ext; unfold tripleCharges sourceA2144 sourceB2144 sourceC2144 difference raw29672; decide +kernel
    rw [ha]
    exact (canonical29672 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2144 + difference 4 5) (sourceB2144 + difference 5 4) sourceC2144) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2598) := by
    have ha : (tripleCharges (sourceA2144 + difference 4 5) (sourceB2144 + difference 5 4) sourceC2144) = raw29673 := by
      apply Matrix.ext; unfold tripleCharges sourceA2144 sourceB2144 sourceC2144 difference raw29673; decide +kernel
    rw [ha]
    exact (canonical29673 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2144 + difference 5 0) (sourceB2144 + difference 0 5) sourceC2144) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 938) := by
    have ha : (tripleCharges (sourceA2144 + difference 5 0) (sourceB2144 + difference 0 5) sourceC2144) = raw21512 := by
      apply Matrix.ext; unfold tripleCharges sourceA2144 sourceB2144 sourceC2144 difference raw21512; decide +kernel
    rw [ha]
    exact (canonical21512 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2144 + difference 5 1) (sourceB2144 + difference 1 5) sourceC2144) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2344) := by
    have ha : (tripleCharges (sourceA2144 + difference 5 1) (sourceB2144 + difference 1 5) sourceC2144) = raw27604 := by
      apply Matrix.ext; unfold tripleCharges sourceA2144 sourceB2144 sourceC2144 difference raw27604; decide +kernel
    rw [ha]
    exact (canonical27604 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2144 + difference 5 2) (sourceB2144 + difference 2 5) sourceC2144) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2334) := by
    have ha : (tripleCharges (sourceA2144 + difference 5 2) (sourceB2144 + difference 2 5) sourceC2144) = raw27605 := by
      apply Matrix.ext; unfold tripleCharges sourceA2144 sourceB2144 sourceC2144 difference raw27605; decide +kernel
    rw [ha]
    exact (canonical27605 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2144 + difference 5 3) (sourceB2144 + difference 3 5) sourceC2144) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2334) := by
    have ha : (tripleCharges (sourceA2144 + difference 5 3) (sourceB2144 + difference 3 5) sourceC2144) = raw27606 := by
      apply Matrix.ext; unfold tripleCharges sourceA2144 sourceB2144 sourceC2144 difference raw27606; decide +kernel
    rw [ha]
    exact (canonical27606 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2144 + difference 5 4) (sourceB2144 + difference 4 5) sourceC2144) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2598) := by
    have ha : (tripleCharges (sourceA2144 + difference 5 4) (sourceB2144 + difference 4 5) sourceC2144) = raw4958 := by
      apply Matrix.ext; unfold tripleCharges sourceA2144 sourceB2144 sourceC2144 difference raw4958; decide +kernel
    rw [ha]
    exact (canonical4958 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2144 sourceB2144 sourceC2144
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2144, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2145 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceB2145 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC2145 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceForm2145 : Integer.Sparse Master := [(Sum.inr 4811, 2), (Sum.inr 4846, 2), (Sum.inr 4875, 1), (Sum.inr 5081, 4), (Sum.inr 5111, 4), (Sum.inr 5130, 2), (Sum.inr 5141, 4), (Sum.inr 5152, 4), (Sum.inr 5176, 2), (Sum.inr 5177, 1), (Sum.inr 5189, 2), (Sum.inr 5207, 2)]

theorem sourceEq2145 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2145 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2145 + difference 0 1) (sourceB2145 + difference 1 0) sourceC2145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5177) := by
    have ha : (tripleCharges (sourceA2145 + difference 0 1) (sourceB2145 + difference 1 0) sourceC2145) = raw29674 := by
      apply Matrix.ext; unfold tripleCharges sourceA2145 sourceB2145 sourceC2145 difference raw29674; decide +kernel
    rw [ha]
    exact (canonical29674 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2145 + difference 0 2) (sourceB2145 + difference 2 0) sourceC2145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5081) := by
    have ha : (tripleCharges (sourceA2145 + difference 0 2) (sourceB2145 + difference 2 0) sourceC2145) = raw29675 := by
      apply Matrix.ext; unfold tripleCharges sourceA2145 sourceB2145 sourceC2145 difference raw29675; decide +kernel
    rw [ha]
    exact (canonical29675 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2145 + difference 0 3) (sourceB2145 + difference 3 0) sourceC2145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5081) := by
    have ha : (tripleCharges (sourceA2145 + difference 0 3) (sourceB2145 + difference 3 0) sourceC2145) = raw29676 := by
      apply Matrix.ext; unfold tripleCharges sourceA2145 sourceB2145 sourceC2145 difference raw29676; decide +kernel
    rw [ha]
    exact (canonical29676 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2145 + difference 0 4) (sourceB2145 + difference 4 0) sourceC2145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5111) := by
    have ha : (tripleCharges (sourceA2145 + difference 0 4) (sourceB2145 + difference 4 0) sourceC2145) = raw29566 := by
      apply Matrix.ext; unfold tripleCharges sourceA2145 sourceB2145 sourceC2145 difference raw29566; decide +kernel
    rw [ha]
    exact (canonical29566 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2145 + difference 0 5) (sourceB2145 + difference 5 0) sourceC2145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5111) := by
    have ha : (tripleCharges (sourceA2145 + difference 0 5) (sourceB2145 + difference 5 0) sourceC2145) = raw29677 := by
      apply Matrix.ext; unfold tripleCharges sourceA2145 sourceB2145 sourceC2145 difference raw29677; decide +kernel
    rw [ha]
    exact (canonical29677 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2145 + difference 1 0) (sourceB2145 + difference 0 1) sourceC2145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4875) := by
    have ha : (tripleCharges (sourceA2145 + difference 1 0) (sourceB2145 + difference 0 1) sourceC2145) = raw29678 := by
      apply Matrix.ext; unfold tripleCharges sourceA2145 sourceB2145 sourceC2145 difference raw29678; decide +kernel
    rw [ha]
    exact (canonical29678 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2145 + difference 1 2) (sourceB2145 + difference 2 1) sourceC2145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5189) := by
    have ha : (tripleCharges (sourceA2145 + difference 1 2) (sourceB2145 + difference 2 1) sourceC2145) = raw29679 := by
      apply Matrix.ext; unfold tripleCharges sourceA2145 sourceB2145 sourceC2145 difference raw29679; decide +kernel
    rw [ha]
    exact (canonical29679 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2145 + difference 1 3) (sourceB2145 + difference 3 1) sourceC2145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5189) := by
    have ha : (tripleCharges (sourceA2145 + difference 1 3) (sourceB2145 + difference 3 1) sourceC2145) = raw29680 := by
      apply Matrix.ext; unfold tripleCharges sourceA2145 sourceB2145 sourceC2145 difference raw29680; decide +kernel
    rw [ha]
    exact (canonical29680 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2145 + difference 1 4) (sourceB2145 + difference 4 1) sourceC2145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5207) := by
    have ha : (tripleCharges (sourceA2145 + difference 1 4) (sourceB2145 + difference 4 1) sourceC2145) = raw29571 := by
      apply Matrix.ext; unfold tripleCharges sourceA2145 sourceB2145 sourceC2145 difference raw29571; decide +kernel
    rw [ha]
    exact (canonical29571 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2145 + difference 1 5) (sourceB2145 + difference 5 1) sourceC2145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5207) := by
    have ha : (tripleCharges (sourceA2145 + difference 1 5) (sourceB2145 + difference 5 1) sourceC2145) = raw29681 := by
      apply Matrix.ext; unfold tripleCharges sourceA2145 sourceB2145 sourceC2145 difference raw29681; decide +kernel
    rw [ha]
    exact (canonical29681 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2145 + difference 2 0) (sourceB2145 + difference 0 2) sourceC2145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4811) := by
    have ha : (tripleCharges (sourceA2145 + difference 2 0) (sourceB2145 + difference 0 2) sourceC2145) = raw29682 := by
      apply Matrix.ext; unfold tripleCharges sourceA2145 sourceB2145 sourceC2145 difference raw29682; decide +kernel
    rw [ha]
    exact (canonical29682 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2145 + difference 2 1) (sourceB2145 + difference 1 2) sourceC2145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5081) := by
    have ha : (tripleCharges (sourceA2145 + difference 2 1) (sourceB2145 + difference 1 2) sourceC2145) = raw29683 := by
      apply Matrix.ext; unfold tripleCharges sourceA2145 sourceB2145 sourceC2145 difference raw29683; decide +kernel
    rw [ha]
    exact (canonical29683 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2145 + difference 2 3) (sourceB2145 + difference 3 2) sourceC2145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5130) := by
    have ha : (tripleCharges (sourceA2145 + difference 2 3) (sourceB2145 + difference 3 2) sourceC2145) = raw29684 := by
      apply Matrix.ext; unfold tripleCharges sourceA2145 sourceB2145 sourceC2145 difference raw29684; decide +kernel
    rw [ha]
    exact (canonical29684 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2145 + difference 2 4) (sourceB2145 + difference 4 2) sourceC2145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5152) := by
    have ha : (tripleCharges (sourceA2145 + difference 2 4) (sourceB2145 + difference 4 2) sourceC2145) = raw29576 := by
      apply Matrix.ext; unfold tripleCharges sourceA2145 sourceB2145 sourceC2145 difference raw29576; decide +kernel
    rw [ha]
    exact (canonical29576 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2145 + difference 2 5) (sourceB2145 + difference 5 2) sourceC2145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5152) := by
    have ha : (tripleCharges (sourceA2145 + difference 2 5) (sourceB2145 + difference 5 2) sourceC2145) = raw29685 := by
      apply Matrix.ext; unfold tripleCharges sourceA2145 sourceB2145 sourceC2145 difference raw29685; decide +kernel
    rw [ha]
    exact (canonical29685 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2145 + difference 3 0) (sourceB2145 + difference 0 3) sourceC2145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4811) := by
    have ha : (tripleCharges (sourceA2145 + difference 3 0) (sourceB2145 + difference 0 3) sourceC2145) = raw29686 := by
      apply Matrix.ext; unfold tripleCharges sourceA2145 sourceB2145 sourceC2145 difference raw29686; decide +kernel
    rw [ha]
    exact (canonical29686 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2145 + difference 3 1) (sourceB2145 + difference 1 3) sourceC2145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5081) := by
    have ha : (tripleCharges (sourceA2145 + difference 3 1) (sourceB2145 + difference 1 3) sourceC2145) = raw29687 := by
      apply Matrix.ext; unfold tripleCharges sourceA2145 sourceB2145 sourceC2145 difference raw29687; decide +kernel
    rw [ha]
    exact (canonical29687 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2145 + difference 3 2) (sourceB2145 + difference 2 3) sourceC2145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5130) := by
    have ha : (tripleCharges (sourceA2145 + difference 3 2) (sourceB2145 + difference 2 3) sourceC2145) = raw29688 := by
      apply Matrix.ext; unfold tripleCharges sourceA2145 sourceB2145 sourceC2145 difference raw29688; decide +kernel
    rw [ha]
    exact (canonical29688 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2145 + difference 3 4) (sourceB2145 + difference 4 3) sourceC2145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5152) := by
    have ha : (tripleCharges (sourceA2145 + difference 3 4) (sourceB2145 + difference 4 3) sourceC2145) = raw29581 := by
      apply Matrix.ext; unfold tripleCharges sourceA2145 sourceB2145 sourceC2145 difference raw29581; decide +kernel
    rw [ha]
    exact (canonical29581 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2145 + difference 3 5) (sourceB2145 + difference 5 3) sourceC2145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5152) := by
    have ha : (tripleCharges (sourceA2145 + difference 3 5) (sourceB2145 + difference 5 3) sourceC2145) = raw29689 := by
      apply Matrix.ext; unfold tripleCharges sourceA2145 sourceB2145 sourceC2145 difference raw29689; decide +kernel
    rw [ha]
    exact (canonical29689 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2145 + difference 4 0) (sourceB2145 + difference 0 4) sourceC2145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4846) := by
    have ha : (tripleCharges (sourceA2145 + difference 4 0) (sourceB2145 + difference 0 4) sourceC2145) = raw29690 := by
      apply Matrix.ext; unfold tripleCharges sourceA2145 sourceB2145 sourceC2145 difference raw29690; decide +kernel
    rw [ha]
    exact (canonical29690 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2145 + difference 4 1) (sourceB2145 + difference 1 4) sourceC2145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5111) := by
    have ha : (tripleCharges (sourceA2145 + difference 4 1) (sourceB2145 + difference 1 4) sourceC2145) = raw29691 := by
      apply Matrix.ext; unfold tripleCharges sourceA2145 sourceB2145 sourceC2145 difference raw29691; decide +kernel
    rw [ha]
    exact (canonical29691 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2145 + difference 4 2) (sourceB2145 + difference 2 4) sourceC2145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA2145 + difference 4 2) (sourceB2145 + difference 2 4) sourceC2145) = raw29692 := by
      apply Matrix.ext; unfold tripleCharges sourceA2145 sourceB2145 sourceC2145 difference raw29692; decide +kernel
    rw [ha]
    exact (canonical29692 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2145 + difference 4 3) (sourceB2145 + difference 3 4) sourceC2145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA2145 + difference 4 3) (sourceB2145 + difference 3 4) sourceC2145) = raw29693 := by
      apply Matrix.ext; unfold tripleCharges sourceA2145 sourceB2145 sourceC2145 difference raw29693; decide +kernel
    rw [ha]
    exact (canonical29693 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2145 + difference 4 5) (sourceB2145 + difference 5 4) sourceC2145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5176) := by
    have ha : (tripleCharges (sourceA2145 + difference 4 5) (sourceB2145 + difference 5 4) sourceC2145) = raw29694 := by
      apply Matrix.ext; unfold tripleCharges sourceA2145 sourceB2145 sourceC2145 difference raw29694; decide +kernel
    rw [ha]
    exact (canonical29694 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2145 + difference 5 0) (sourceB2145 + difference 0 5) sourceC2145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4846) := by
    have ha : (tripleCharges (sourceA2145 + difference 5 0) (sourceB2145 + difference 0 5) sourceC2145) = raw29582 := by
      apply Matrix.ext; unfold tripleCharges sourceA2145 sourceB2145 sourceC2145 difference raw29582; decide +kernel
    rw [ha]
    exact (canonical29582 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2145 + difference 5 1) (sourceB2145 + difference 1 5) sourceC2145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5111) := by
    have ha : (tripleCharges (sourceA2145 + difference 5 1) (sourceB2145 + difference 1 5) sourceC2145) = raw29583 := by
      apply Matrix.ext; unfold tripleCharges sourceA2145 sourceB2145 sourceC2145 difference raw29583; decide +kernel
    rw [ha]
    exact (canonical29583 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2145 + difference 5 2) (sourceB2145 + difference 2 5) sourceC2145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA2145 + difference 5 2) (sourceB2145 + difference 2 5) sourceC2145) = raw29584 := by
      apply Matrix.ext; unfold tripleCharges sourceA2145 sourceB2145 sourceC2145 difference raw29584; decide +kernel
    rw [ha]
    exact (canonical29584 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2145 + difference 5 3) (sourceB2145 + difference 3 5) sourceC2145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA2145 + difference 5 3) (sourceB2145 + difference 3 5) sourceC2145) = raw29585 := by
      apply Matrix.ext; unfold tripleCharges sourceA2145 sourceB2145 sourceC2145 difference raw29585; decide +kernel
    rw [ha]
    exact (canonical29585 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2145 + difference 5 4) (sourceB2145 + difference 4 5) sourceC2145) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5176) := by
    have ha : (tripleCharges (sourceA2145 + difference 5 4) (sourceB2145 + difference 4 5) sourceC2145) = raw29695 := by
      apply Matrix.ext; unfold tripleCharges sourceA2145 sourceB2145 sourceC2145 difference raw29695; decide +kernel
    rw [ha]
    exact (canonical29695 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2145 sourceB2145 sourceC2145
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2145, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2146 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceB2146 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC2146 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceForm2146 : Integer.Sparse Master := [(Sum.inr 3482, 2), (Sum.inr 3485, 2), (Sum.inr 3616, 2), (Sum.inr 4082, -1)]

theorem sourceEq2146 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2146 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2146 + difference 0 0) (sourceB2146 + difference 0 0) sourceC2146) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3616) := by
    have ha : (tripleCharges (sourceA2146 + difference 0 0) (sourceB2146 + difference 0 0) sourceC2146) = raw29497 := by
      apply Matrix.ext; unfold tripleCharges sourceA2146 sourceB2146 sourceC2146 difference raw29497; decide +kernel
    rw [ha]
    exact (canonical29497 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2146 + difference 0 1) (sourceB2146 + difference 1 0) sourceC2146) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3616) := by
    have ha : (tripleCharges (sourceA2146 + difference 0 1) (sourceB2146 + difference 1 0) sourceC2146) = raw29696 := by
      apply Matrix.ext; unfold tripleCharges sourceA2146 sourceB2146 sourceC2146 difference raw29696; decide +kernel
    rw [ha]
    exact (canonical29696 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2146 + difference 0 2) (sourceB2146 + difference 2 0) sourceC2146) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3482) := by
    have ha : (tripleCharges (sourceA2146 + difference 0 2) (sourceB2146 + difference 2 0) sourceC2146) = raw29491 := by
      apply Matrix.ext; unfold tripleCharges sourceA2146 sourceB2146 sourceC2146 difference raw29491; decide +kernel
    rw [ha]
    exact (canonical29491 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2146 + difference 0 3) (sourceB2146 + difference 3 0) sourceC2146) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3482) := by
    have ha : (tripleCharges (sourceA2146 + difference 0 3) (sourceB2146 + difference 3 0) sourceC2146) = raw29697 := by
      apply Matrix.ext; unfold tripleCharges sourceA2146 sourceB2146 sourceC2146 difference raw29697; decide +kernel
    rw [ha]
    exact (canonical29697 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2146 + difference 0 4) (sourceB2146 + difference 4 0) sourceC2146) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3485) := by
    have ha : (tripleCharges (sourceA2146 + difference 0 4) (sourceB2146 + difference 4 0) sourceC2146) = raw29698 := by
      apply Matrix.ext; unfold tripleCharges sourceA2146 sourceB2146 sourceC2146 difference raw29698; decide +kernel
    rw [ha]
    exact (canonical29698 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2146 + difference 0 5) (sourceB2146 + difference 5 0) sourceC2146) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3485) := by
    have ha : (tripleCharges (sourceA2146 + difference 0 5) (sourceB2146 + difference 5 0) sourceC2146) = raw29699 := by
      apply Matrix.ext; unfold tripleCharges sourceA2146 sourceB2146 sourceC2146 difference raw29699; decide +kernel
    rw [ha]
    exact (canonical29699 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2146 + sourceB2146) sourceC2146) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2146 + sourceB2146) sourceC2146) = raw29319 := by
      apply Matrix.ext; unfold doubleCharges sourceA2146 sourceB2146 sourceC2146 raw29319; decide +kernel
    rw [ha]
    exact (canonical29319 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2146 sourceB2146 sourceC2146
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2146, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2147 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2147 : Charge := ![1, 1, 0, 1, -3, 0]
def sourceC2147 : Charge := ![2, 0, 0, -1, 1, -2]
def sourceForm2147 : Integer.Sparse Master := [(Sum.inr 1171, 1), (Sum.inr 2362, 1), (Sum.inr 2529, 1), (Sum.inr 2575, 1), (Sum.inr 2590, 1), (Sum.inr 2600, 1), (Sum.inr 4092, -1)]

theorem sourceEq2147 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2147 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2147 + difference 3 0) (sourceB2147 + difference 0 3) sourceC2147) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1171) := by
    have ha : (tripleCharges (sourceA2147 + difference 3 0) (sourceB2147 + difference 0 3) sourceC2147) = raw29700 := by
      apply Matrix.ext; unfold tripleCharges sourceA2147 sourceB2147 sourceC2147 difference raw29700; decide +kernel
    rw [ha]
    exact (canonical29700 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2147 + difference 3 1) (sourceB2147 + difference 1 3) sourceC2147) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2362) := by
    have ha : (tripleCharges (sourceA2147 + difference 3 1) (sourceB2147 + difference 1 3) sourceC2147) = raw29701 := by
      apply Matrix.ext; unfold tripleCharges sourceA2147 sourceB2147 sourceC2147 difference raw29701; decide +kernel
    rw [ha]
    exact (canonical29701 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2147 + difference 3 2) (sourceB2147 + difference 2 3) sourceC2147) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2529) := by
    have ha : (tripleCharges (sourceA2147 + difference 3 2) (sourceB2147 + difference 2 3) sourceC2147) = raw29702 := by
      apply Matrix.ext; unfold tripleCharges sourceA2147 sourceB2147 sourceC2147 difference raw29702; decide +kernel
    rw [ha]
    exact (canonical29702 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2147 + difference 3 3) (sourceB2147 + difference 3 3) sourceC2147) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2575) := by
    have ha : (tripleCharges (sourceA2147 + difference 3 3) (sourceB2147 + difference 3 3) sourceC2147) = raw29703 := by
      apply Matrix.ext; unfold tripleCharges sourceA2147 sourceB2147 sourceC2147 difference raw29703; decide +kernel
    rw [ha]
    exact (canonical29703 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2147 + difference 3 4) (sourceB2147 + difference 4 3) sourceC2147) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2590) := by
    have ha : (tripleCharges (sourceA2147 + difference 3 4) (sourceB2147 + difference 4 3) sourceC2147) = raw27816 := by
      apply Matrix.ext; unfold tripleCharges sourceA2147 sourceB2147 sourceC2147 difference raw27816; decide +kernel
    rw [ha]
    exact (canonical27816 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2147 + difference 3 5) (sourceB2147 + difference 5 3) sourceC2147) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2600) := by
    have ha : (tripleCharges (sourceA2147 + difference 3 5) (sourceB2147 + difference 5 3) sourceC2147) = raw29704 := by
      apply Matrix.ext; unfold tripleCharges sourceA2147 sourceB2147 sourceC2147 difference raw29704; decide +kernel
    rw [ha]
    exact (canonical29704 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2147 + sourceB2147) sourceC2147) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2147 + sourceB2147) sourceC2147) = raw24400 := by
      apply Matrix.ext; unfold doubleCharges sourceA2147 sourceB2147 sourceC2147 raw24400; decide +kernel
    rw [ha]
    exact (canonical24400 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2147 sourceB2147 sourceC2147
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2147, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2148 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2148 : Charge := ![2, 0, 0, -1, 1, -2]
def sourceC2148 : Charge := ![1, 1, 0, 1, -3, 0]
def sourceForm2148 : Integer.Sparse Master := [(Sum.inr 1812, 1), (Sum.inr 2892, 1), (Sum.inr 2899, 1), (Sum.inr 2930, 2), (Sum.inr 3394, 1), (Sum.inr 4083, -1)]

theorem sourceEq2148 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2148 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2148 + difference 0 3) (sourceB2148 + difference 3 0) sourceC2148) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3394) := by
    have ha : (tripleCharges (sourceA2148 + difference 0 3) (sourceB2148 + difference 3 0) sourceC2148) = raw29705 := by
      apply Matrix.ext; unfold tripleCharges sourceA2148 sourceB2148 sourceC2148 difference raw29705; decide +kernel
    rw [ha]
    exact (canonical29705 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2148 + difference 1 3) (sourceB2148 + difference 3 1) sourceC2148) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2930) := by
    have ha : (tripleCharges (sourceA2148 + difference 1 3) (sourceB2148 + difference 3 1) sourceC2148) = raw29706 := by
      apply Matrix.ext; unfold tripleCharges sourceA2148 sourceB2148 sourceC2148 difference raw29706; decide +kernel
    rw [ha]
    exact (canonical29706 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2148 + difference 2 3) (sourceB2148 + difference 3 2) sourceC2148) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2892) := by
    have ha : (tripleCharges (sourceA2148 + difference 2 3) (sourceB2148 + difference 3 2) sourceC2148) = raw29707 := by
      apply Matrix.ext; unfold tripleCharges sourceA2148 sourceB2148 sourceC2148 difference raw29707; decide +kernel
    rw [ha]
    exact (canonical29707 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2148 + difference 3 3) (sourceB2148 + difference 3 3) sourceC2148) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2930) := by
    have ha : (tripleCharges (sourceA2148 + difference 3 3) (sourceB2148 + difference 3 3) sourceC2148) = raw29708 := by
      apply Matrix.ext; unfold tripleCharges sourceA2148 sourceB2148 sourceC2148 difference raw29708; decide +kernel
    rw [ha]
    exact (canonical29708 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2148 + difference 4 3) (sourceB2148 + difference 3 4) sourceC2148) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1812) := by
    have ha : (tripleCharges (sourceA2148 + difference 4 3) (sourceB2148 + difference 3 4) sourceC2148) = raw29709 := by
      apply Matrix.ext; unfold tripleCharges sourceA2148 sourceB2148 sourceC2148 difference raw29709; decide +kernel
    rw [ha]
    exact (canonical29709 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2148 + difference 5 3) (sourceB2148 + difference 3 5) sourceC2148) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2899) := by
    have ha : (tripleCharges (sourceA2148 + difference 5 3) (sourceB2148 + difference 3 5) sourceC2148) = raw29710 := by
      apply Matrix.ext; unfold tripleCharges sourceA2148 sourceB2148 sourceC2148 difference raw29710; decide +kernel
    rw [ha]
    exact (canonical29710 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2148 + sourceB2148) sourceC2148) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA2148 + sourceB2148) sourceC2148) = raw29711 := by
      apply Matrix.ext; unfold doubleCharges sourceA2148 sourceB2148 sourceC2148 raw29711; decide +kernel
    rw [ha]
    exact (canonical29711 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2148 sourceB2148 sourceC2148
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2148, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2149 : Charge := ![1, 1, 0, 1, -3, 0]
def sourceB2149 : Charge := ![2, 0, 0, -1, 1, -2]
def sourceC2149 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceForm2149 : Integer.Sparse Master := [(Sum.inr 2396, 1), (Sum.inr 2399, 1), (Sum.inr 2401, 1), (Sum.inr 2405, 1), (Sum.inr 2681, 1), (Sum.inr 3612, 1), (Sum.inr 4082, -1)]

theorem sourceEq2149 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2149 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2149 + difference 0 5) (sourceB2149 + difference 5 0) sourceC2149) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2399) := by
    have ha : (tripleCharges (sourceA2149 + difference 0 5) (sourceB2149 + difference 5 0) sourceC2149) = raw29712 := by
      apply Matrix.ext; unfold tripleCharges sourceA2149 sourceB2149 sourceC2149 difference raw29712; decide +kernel
    rw [ha]
    exact (canonical29712 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2149 + difference 1 5) (sourceB2149 + difference 5 1) sourceC2149) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2401) := by
    have ha : (tripleCharges (sourceA2149 + difference 1 5) (sourceB2149 + difference 5 1) sourceC2149) = raw29353 := by
      apply Matrix.ext; unfold tripleCharges sourceA2149 sourceB2149 sourceC2149 difference raw29353; decide +kernel
    rw [ha]
    exact (canonical29353 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2149 + difference 2 5) (sourceB2149 + difference 5 2) sourceC2149) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2396) := by
    have ha : (tripleCharges (sourceA2149 + difference 2 5) (sourceB2149 + difference 5 2) sourceC2149) = raw29330 := by
      apply Matrix.ext; unfold tripleCharges sourceA2149 sourceB2149 sourceC2149 difference raw29330; decide +kernel
    rw [ha]
    exact (canonical29330 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2149 + difference 3 5) (sourceB2149 + difference 5 3) sourceC2149) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2405) := by
    have ha : (tripleCharges (sourceA2149 + difference 3 5) (sourceB2149 + difference 5 3) sourceC2149) = raw29713 := by
      apply Matrix.ext; unfold tripleCharges sourceA2149 sourceB2149 sourceC2149 difference raw29713; decide +kernel
    rw [ha]
    exact (canonical29713 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2149 + difference 4 5) (sourceB2149 + difference 5 4) sourceC2149) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3612) := by
    have ha : (tripleCharges (sourceA2149 + difference 4 5) (sourceB2149 + difference 5 4) sourceC2149) = raw29313 := by
      apply Matrix.ext; unfold tripleCharges sourceA2149 sourceB2149 sourceC2149 difference raw29313; decide +kernel
    rw [ha]
    exact (canonical29313 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2149 + difference 5 5) (sourceB2149 + difference 5 5) sourceC2149) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2681) := by
    have ha : (tripleCharges (sourceA2149 + difference 5 5) (sourceB2149 + difference 5 5) sourceC2149) = raw29714 := by
      apply Matrix.ext; unfold tripleCharges sourceA2149 sourceB2149 sourceC2149 difference raw29714; decide +kernel
    rw [ha]
    exact (canonical29714 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2149 + sourceB2149) sourceC2149) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2149 + sourceB2149) sourceC2149) = raw29319 := by
      apply Matrix.ext; unfold doubleCharges sourceA2149 sourceB2149 sourceC2149 raw29319; decide +kernel
    rw [ha]
    exact (canonical29319 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2149 sourceB2149 sourceC2149
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2149, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2150 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2150 : Charge := ![1, 1, 0, 1, -2, -1]
def sourceC2150 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceForm2150 : Integer.Sparse Master := [(Sum.inr 4524, 1), (Sum.inr 4525, 1), (Sum.inr 4526, 1), (Sum.inr 4549, 1), (Sum.inr 4612, 1), (Sum.inr 4633, 1), (Sum.inr 4638, 1), (Sum.inr 4650, 1), (Sum.inr 4807, 1), (Sum.inr 4904, 1), (Sum.inr 4908, 1), (Sum.inr 4919, 1), (Sum.inr 4961, 1), (Sum.inr 4977, 1), (Sum.inr 5078, 1), (Sum.inr 5117, 1), (Sum.inr 5119, 1), (Sum.inr 5148, 1), (Sum.inr 5149, 1), (Sum.inr 5152, 1), (Sum.inr 5169, 1), (Sum.inr 5172, 1), (Sum.inr 5207, 1), (Sum.inr 5293, 1), (Sum.inr 5294, 1), (Sum.inr 5354, 1), (Sum.inr 5355, 1), (Sum.inr 5370, 1), (Sum.inr 5434, 1), (Sum.inr 5435, 1)]

theorem sourceEq2150 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2150 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2150 + difference 0 1) (sourceB2150 + difference 1 0) sourceC2150) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5355) := by
    have ha : (tripleCharges (sourceA2150 + difference 0 1) (sourceB2150 + difference 1 0) sourceC2150) = raw15031 := by
      apply Matrix.ext; unfold tripleCharges sourceA2150 sourceB2150 sourceC2150 difference raw15031; decide +kernel
    rw [ha]
    exact (canonical15031 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2150 + difference 0 2) (sourceB2150 + difference 2 0) sourceC2150) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5354) := by
    have ha : (tripleCharges (sourceA2150 + difference 0 2) (sourceB2150 + difference 2 0) sourceC2150) = raw15032 := by
      apply Matrix.ext; unfold tripleCharges sourceA2150 sourceB2150 sourceC2150 difference raw15032; decide +kernel
    rw [ha]
    exact (canonical15032 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2150 + difference 0 3) (sourceB2150 + difference 3 0) sourceC2150) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5370) := by
    have ha : (tripleCharges (sourceA2150 + difference 0 3) (sourceB2150 + difference 3 0) sourceC2150) = raw15033 := by
      apply Matrix.ext; unfold tripleCharges sourceA2150 sourceB2150 sourceC2150 difference raw15033; decide +kernel
    rw [ha]
    exact (canonical15033 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2150 + difference 0 4) (sourceB2150 + difference 4 0) sourceC2150) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA2150 + difference 0 4) (sourceB2150 + difference 4 0) sourceC2150) = raw7806 := by
      apply Matrix.ext; unfold tripleCharges sourceA2150 sourceB2150 sourceC2150 difference raw7806; decide +kernel
    rw [ha]
    exact (canonical7806 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2150 + difference 0 5) (sourceB2150 + difference 5 0) sourceC2150) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA2150 + difference 0 5) (sourceB2150 + difference 5 0) sourceC2150) = raw15034 := by
      apply Matrix.ext; unfold tripleCharges sourceA2150 sourceB2150 sourceC2150 difference raw15034; decide +kernel
    rw [ha]
    exact (canonical15034 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2150 + difference 1 0) (sourceB2150 + difference 0 1) sourceC2150) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA2150 + difference 1 0) (sourceB2150 + difference 0 1) sourceC2150) = raw7826 := by
      apply Matrix.ext; unfold tripleCharges sourceA2150 sourceB2150 sourceC2150 difference raw7826; decide +kernel
    rw [ha]
    exact (canonical7826 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2150 + difference 1 2) (sourceB2150 + difference 2 1) sourceC2150) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5152) := by
    have ha : (tripleCharges (sourceA2150 + difference 1 2) (sourceB2150 + difference 2 1) sourceC2150) = raw7828 := by
      apply Matrix.ext; unfold tripleCharges sourceA2150 sourceB2150 sourceC2150 difference raw7828; decide +kernel
    rw [ha]
    exact (canonical7828 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2150 + difference 1 3) (sourceB2150 + difference 3 1) sourceC2150) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5207) := by
    have ha : (tripleCharges (sourceA2150 + difference 1 3) (sourceB2150 + difference 3 1) sourceC2150) = raw7829 := by
      apply Matrix.ext; unfold tripleCharges sourceA2150 sourceB2150 sourceC2150 difference raw7829; decide +kernel
    rw [ha]
    exact (canonical7829 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2150 + difference 1 4) (sourceB2150 + difference 4 1) sourceC2150) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA2150 + difference 1 4) (sourceB2150 + difference 4 1) sourceC2150) = raw15022 := by
      apply Matrix.ext; unfold tripleCharges sourceA2150 sourceB2150 sourceC2150 difference raw15022; decide +kernel
    rw [ha]
    exact (canonical15022 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2150 + difference 1 5) (sourceB2150 + difference 5 1) sourceC2150) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA2150 + difference 1 5) (sourceB2150 + difference 5 1) sourceC2150) = raw7830 := by
      apply Matrix.ext; unfold tripleCharges sourceA2150 sourceB2150 sourceC2150 difference raw7830; decide +kernel
    rw [ha]
    exact (canonical7830 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2150 + difference 2 0) (sourceB2150 + difference 0 2) sourceC2150) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4524) := by
    have ha : (tripleCharges (sourceA2150 + difference 2 0) (sourceB2150 + difference 0 2) sourceC2150) = raw22742 := by
      apply Matrix.ext; unfold tripleCharges sourceA2150 sourceB2150 sourceC2150 difference raw22742; decide +kernel
    rw [ha]
    exact (canonical22742 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2150 + difference 2 1) (sourceB2150 + difference 1 2) sourceC2150) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4961) := by
    have ha : (tripleCharges (sourceA2150 + difference 2 1) (sourceB2150 + difference 1 2) sourceC2150) = raw29715 := by
      apply Matrix.ext; unfold tripleCharges sourceA2150 sourceB2150 sourceC2150 difference raw29715; decide +kernel
    rw [ha]
    exact (canonical29715 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2150 + difference 2 3) (sourceB2150 + difference 3 2) sourceC2150) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5119) := by
    have ha : (tripleCharges (sourceA2150 + difference 2 3) (sourceB2150 + difference 3 2) sourceC2150) = raw29716 := by
      apply Matrix.ext; unfold tripleCharges sourceA2150 sourceB2150 sourceC2150 difference raw29716; decide +kernel
    rw [ha]
    exact (canonical29716 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2150 + difference 2 4) (sourceB2150 + difference 4 2) sourceC2150) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5148) := by
    have ha : (tripleCharges (sourceA2150 + difference 2 4) (sourceB2150 + difference 4 2) sourceC2150) = raw7817 := by
      apply Matrix.ext; unfold tripleCharges sourceA2150 sourceB2150 sourceC2150 difference raw7817; decide +kernel
    rw [ha]
    exact (canonical7817 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2150 + difference 2 5) (sourceB2150 + difference 5 2) sourceC2150) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5149) := by
    have ha : (tripleCharges (sourceA2150 + difference 2 5) (sourceB2150 + difference 5 2) sourceC2150) = raw29717 := by
      apply Matrix.ext; unfold tripleCharges sourceA2150 sourceB2150 sourceC2150 difference raw29717; decide +kernel
    rw [ha]
    exact (canonical29717 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2150 + difference 3 0) (sourceB2150 + difference 0 3) sourceC2150) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4549) := by
    have ha : (tripleCharges (sourceA2150 + difference 3 0) (sourceB2150 + difference 0 3) sourceC2150) = raw22746 := by
      apply Matrix.ext; unfold tripleCharges sourceA2150 sourceB2150 sourceC2150 difference raw22746; decide +kernel
    rw [ha]
    exact (canonical22746 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2150 + difference 3 1) (sourceB2150 + difference 1 3) sourceC2150) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4977) := by
    have ha : (tripleCharges (sourceA2150 + difference 3 1) (sourceB2150 + difference 1 3) sourceC2150) = raw29718 := by
      apply Matrix.ext; unfold tripleCharges sourceA2150 sourceB2150 sourceC2150 difference raw29718; decide +kernel
    rw [ha]
    exact (canonical29718 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2150 + difference 3 2) (sourceB2150 + difference 2 3) sourceC2150) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5117) := by
    have ha : (tripleCharges (sourceA2150 + difference 3 2) (sourceB2150 + difference 2 3) sourceC2150) = raw29719 := by
      apply Matrix.ext; unfold tripleCharges sourceA2150 sourceB2150 sourceC2150 difference raw29719; decide +kernel
    rw [ha]
    exact (canonical29719 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2150 + difference 3 4) (sourceB2150 + difference 4 3) sourceC2150) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA2150 + difference 3 4) (sourceB2150 + difference 4 3) sourceC2150) = raw7822 := by
      apply Matrix.ext; unfold tripleCharges sourceA2150 sourceB2150 sourceC2150 difference raw7822; decide +kernel
    rw [ha]
    exact (canonical7822 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2150 + difference 3 5) (sourceB2150 + difference 5 3) sourceC2150) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5172) := by
    have ha : (tripleCharges (sourceA2150 + difference 3 5) (sourceB2150 + difference 5 3) sourceC2150) = raw29720 := by
      apply Matrix.ext; unfold tripleCharges sourceA2150 sourceB2150 sourceC2150 difference raw29720; decide +kernel
    rw [ha]
    exact (canonical29720 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2150 + difference 4 0) (sourceB2150 + difference 0 4) sourceC2150) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4525) := by
    have ha : (tripleCharges (sourceA2150 + difference 4 0) (sourceB2150 + difference 0 4) sourceC2150) = raw22750 := by
      apply Matrix.ext; unfold tripleCharges sourceA2150 sourceB2150 sourceC2150 difference raw22750; decide +kernel
    rw [ha]
    exact (canonical22750 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2150 + difference 4 1) (sourceB2150 + difference 1 4) sourceC2150) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4638) := by
    have ha : (tripleCharges (sourceA2150 + difference 4 1) (sourceB2150 + difference 1 4) sourceC2150) = raw29721 := by
      apply Matrix.ext; unfold tripleCharges sourceA2150 sourceB2150 sourceC2150 difference raw29721; decide +kernel
    rw [ha]
    exact (canonical29721 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2150 + difference 4 2) (sourceB2150 + difference 2 4) sourceC2150) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4633) := by
    have ha : (tripleCharges (sourceA2150 + difference 4 2) (sourceB2150 + difference 2 4) sourceC2150) = raw29722 := by
      apply Matrix.ext; unfold tripleCharges sourceA2150 sourceB2150 sourceC2150 difference raw29722; decide +kernel
    rw [ha]
    exact (canonical29722 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2150 + difference 4 3) (sourceB2150 + difference 3 4) sourceC2150) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4650) := by
    have ha : (tripleCharges (sourceA2150 + difference 4 3) (sourceB2150 + difference 3 4) sourceC2150) = raw29723 := by
      apply Matrix.ext; unfold tripleCharges sourceA2150 sourceB2150 sourceC2150 difference raw29723; decide +kernel
    rw [ha]
    exact (canonical29723 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2150 + difference 4 5) (sourceB2150 + difference 5 4) sourceC2150) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA2150 + difference 4 5) (sourceB2150 + difference 5 4) sourceC2150) = raw29724 := by
      apply Matrix.ext; unfold tripleCharges sourceA2150 sourceB2150 sourceC2150 difference raw29724; decide +kernel
    rw [ha]
    exact (canonical29724 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2150 + difference 5 0) (sourceB2150 + difference 0 5) sourceC2150) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4526) := by
    have ha : (tripleCharges (sourceA2150 + difference 5 0) (sourceB2150 + difference 0 5) sourceC2150) = raw20762 := by
      apply Matrix.ext; unfold tripleCharges sourceA2150 sourceB2150 sourceC2150 difference raw20762; decide +kernel
    rw [ha]
    exact (canonical20762 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2150 + difference 5 1) (sourceB2150 + difference 1 5) sourceC2150) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4908) := by
    have ha : (tripleCharges (sourceA2150 + difference 5 1) (sourceB2150 + difference 1 5) sourceC2150) = raw27842 := by
      apply Matrix.ext; unfold tripleCharges sourceA2150 sourceB2150 sourceC2150 difference raw27842; decide +kernel
    rw [ha]
    exact (canonical27842 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2150 + difference 5 2) (sourceB2150 + difference 2 5) sourceC2150) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4904) := by
    have ha : (tripleCharges (sourceA2150 + difference 5 2) (sourceB2150 + difference 2 5) sourceC2150) = raw27843 := by
      apply Matrix.ext; unfold tripleCharges sourceA2150 sourceB2150 sourceC2150 difference raw27843; decide +kernel
    rw [ha]
    exact (canonical27843 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2150 + difference 5 3) (sourceB2150 + difference 3 5) sourceC2150) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4919) := by
    have ha : (tripleCharges (sourceA2150 + difference 5 3) (sourceB2150 + difference 3 5) sourceC2150) = raw27844 := by
      apply Matrix.ext; unfold tripleCharges sourceA2150 sourceB2150 sourceC2150 difference raw27844; decide +kernel
    rw [ha]
    exact (canonical27844 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2150 + difference 5 4) (sourceB2150 + difference 4 5) sourceC2150) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5078) := by
    have ha : (tripleCharges (sourceA2150 + difference 5 4) (sourceB2150 + difference 4 5) sourceC2150) = raw7832 := by
      apply Matrix.ext; unfold tripleCharges sourceA2150 sourceB2150 sourceC2150 difference raw7832; decide +kernel
    rw [ha]
    exact (canonical7832 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2150 sourceB2150 sourceC2150
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2150, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2151 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2151 : Charge := ![1, 1, 0, 1, -2, -1]
def sourceC2151 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceForm2151 : Integer.Sparse Master := [(Sum.inr 1108, 1), (Sum.inr 1109, 1), (Sum.inr 1110, 1), (Sum.inr 1134, 1), (Sum.inr 1246, 1), (Sum.inr 1762, 1), (Sum.inr 1767, 1), (Sum.inr 1778, 1), (Sum.inr 2025, 1), (Sum.inr 2297, 1), (Sum.inr 2301, 1), (Sum.inr 2310, 1), (Sum.inr 2485, 1), (Sum.inr 2796, 1), (Sum.inr 2813, 1), (Sum.inr 2845, 1), (Sum.inr 2889, 1), (Sum.inr 2893, 1), (Sum.inr 2924, 1), (Sum.inr 2927, 1), (Sum.inr 2931, 1), (Sum.inr 2959, 1), (Sum.inr 2960, 1), (Sum.inr 3101, 1), (Sum.inr 3102, 1), (Sum.inr 3692, 1), (Sum.inr 3693, 1), (Sum.inr 3706, 1), (Sum.inr 3853, 1), (Sum.inr 3982, 1)]

theorem sourceEq2151 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2151 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2151 + difference 0 1) (sourceB2151 + difference 1 0) sourceC2151) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3693) := by
    have ha : (tripleCharges (sourceA2151 + difference 0 1) (sourceB2151 + difference 1 0) sourceC2151) = raw15053 := by
      apply Matrix.ext; unfold tripleCharges sourceA2151 sourceB2151 sourceC2151 difference raw15053; decide +kernel
    rw [ha]
    exact (canonical15053 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2151 + difference 0 2) (sourceB2151 + difference 2 0) sourceC2151) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3692) := by
    have ha : (tripleCharges (sourceA2151 + difference 0 2) (sourceB2151 + difference 2 0) sourceC2151) = raw15054 := by
      apply Matrix.ext; unfold tripleCharges sourceA2151 sourceB2151 sourceC2151 difference raw15054; decide +kernel
    rw [ha]
    exact (canonical15054 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2151 + difference 0 3) (sourceB2151 + difference 3 0) sourceC2151) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3706) := by
    have ha : (tripleCharges (sourceA2151 + difference 0 3) (sourceB2151 + difference 3 0) sourceC2151) = raw15055 := by
      apply Matrix.ext; unfold tripleCharges sourceA2151 sourceB2151 sourceC2151 difference raw15055; decide +kernel
    rw [ha]
    exact (canonical15055 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2151 + difference 0 4) (sourceB2151 + difference 4 0) sourceC2151) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3982) := by
    have ha : (tripleCharges (sourceA2151 + difference 0 4) (sourceB2151 + difference 4 0) sourceC2151) = raw7836 := by
      apply Matrix.ext; unfold tripleCharges sourceA2151 sourceB2151 sourceC2151 difference raw7836; decide +kernel
    rw [ha]
    exact (canonical7836 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2151 + difference 0 5) (sourceB2151 + difference 5 0) sourceC2151) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3853) := by
    have ha : (tripleCharges (sourceA2151 + difference 0 5) (sourceB2151 + difference 5 0) sourceC2151) = raw15056 := by
      apply Matrix.ext; unfold tripleCharges sourceA2151 sourceB2151 sourceC2151 difference raw15056; decide +kernel
    rw [ha]
    exact (canonical15056 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2151 + difference 1 0) (sourceB2151 + difference 0 1) sourceC2151) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1246) := by
    have ha : (tripleCharges (sourceA2151 + difference 1 0) (sourceB2151 + difference 0 1) sourceC2151) = raw7856 := by
      apply Matrix.ext; unfold tripleCharges sourceA2151 sourceB2151 sourceC2151 difference raw7856; decide +kernel
    rw [ha]
    exact (canonical7856 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2151 + difference 1 2) (sourceB2151 + difference 2 1) sourceC2151) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2931) := by
    have ha : (tripleCharges (sourceA2151 + difference 1 2) (sourceB2151 + difference 2 1) sourceC2151) = raw7858 := by
      apply Matrix.ext; unfold tripleCharges sourceA2151 sourceB2151 sourceC2151 difference raw7858; decide +kernel
    rw [ha]
    exact (canonical7858 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2151 + difference 1 3) (sourceB2151 + difference 3 1) sourceC2151) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2889) := by
    have ha : (tripleCharges (sourceA2151 + difference 1 3) (sourceB2151 + difference 3 1) sourceC2151) = raw7859 := by
      apply Matrix.ext; unfold tripleCharges sourceA2151 sourceB2151 sourceC2151 difference raw7859; decide +kernel
    rw [ha]
    exact (canonical7859 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2151 + difference 1 4) (sourceB2151 + difference 4 1) sourceC2151) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3102) := by
    have ha : (tripleCharges (sourceA2151 + difference 1 4) (sourceB2151 + difference 4 1) sourceC2151) = raw15044 := by
      apply Matrix.ext; unfold tripleCharges sourceA2151 sourceB2151 sourceC2151 difference raw15044; decide +kernel
    rw [ha]
    exact (canonical15044 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2151 + difference 1 5) (sourceB2151 + difference 5 1) sourceC2151) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3101) := by
    have ha : (tripleCharges (sourceA2151 + difference 1 5) (sourceB2151 + difference 5 1) sourceC2151) = raw7860 := by
      apply Matrix.ext; unfold tripleCharges sourceA2151 sourceB2151 sourceC2151 difference raw7860; decide +kernel
    rw [ha]
    exact (canonical7860 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2151 + difference 2 0) (sourceB2151 + difference 0 2) sourceC2151) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1108) := by
    have ha : (tripleCharges (sourceA2151 + difference 2 0) (sourceB2151 + difference 0 2) sourceC2151) = raw22759 := by
      apply Matrix.ext; unfold tripleCharges sourceA2151 sourceB2151 sourceC2151 difference raw22759; decide +kernel
    rw [ha]
    exact (canonical22759 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2151 + difference 2 1) (sourceB2151 + difference 1 2) sourceC2151) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2796) := by
    have ha : (tripleCharges (sourceA2151 + difference 2 1) (sourceB2151 + difference 1 2) sourceC2151) = raw29725 := by
      apply Matrix.ext; unfold tripleCharges sourceA2151 sourceB2151 sourceC2151 difference raw29725; decide +kernel
    rw [ha]
    exact (canonical29725 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2151 + difference 2 3) (sourceB2151 + difference 3 2) sourceC2151) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2845) := by
    have ha : (tripleCharges (sourceA2151 + difference 2 3) (sourceB2151 + difference 3 2) sourceC2151) = raw29726 := by
      apply Matrix.ext; unfold tripleCharges sourceA2151 sourceB2151 sourceC2151 difference raw29726; decide +kernel
    rw [ha]
    exact (canonical29726 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2151 + difference 2 4) (sourceB2151 + difference 4 2) sourceC2151) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2927) := by
    have ha : (tripleCharges (sourceA2151 + difference 2 4) (sourceB2151 + difference 4 2) sourceC2151) = raw7847 := by
      apply Matrix.ext; unfold tripleCharges sourceA2151 sourceB2151 sourceC2151 difference raw7847; decide +kernel
    rw [ha]
    exact (canonical7847 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2151 + difference 2 5) (sourceB2151 + difference 5 2) sourceC2151) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2924) := by
    have ha : (tripleCharges (sourceA2151 + difference 2 5) (sourceB2151 + difference 5 2) sourceC2151) = raw29727 := by
      apply Matrix.ext; unfold tripleCharges sourceA2151 sourceB2151 sourceC2151 difference raw29727; decide +kernel
    rw [ha]
    exact (canonical29727 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2151 + difference 3 0) (sourceB2151 + difference 0 3) sourceC2151) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1134) := by
    have ha : (tripleCharges (sourceA2151 + difference 3 0) (sourceB2151 + difference 0 3) sourceC2151) = raw22763 := by
      apply Matrix.ext; unfold tripleCharges sourceA2151 sourceB2151 sourceC2151 difference raw22763; decide +kernel
    rw [ha]
    exact (canonical22763 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2151 + difference 3 1) (sourceB2151 + difference 1 3) sourceC2151) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2813) := by
    have ha : (tripleCharges (sourceA2151 + difference 3 1) (sourceB2151 + difference 1 3) sourceC2151) = raw29728 := by
      apply Matrix.ext; unfold tripleCharges sourceA2151 sourceB2151 sourceC2151 difference raw29728; decide +kernel
    rw [ha]
    exact (canonical29728 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2151 + difference 3 2) (sourceB2151 + difference 2 3) sourceC2151) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2893) := by
    have ha : (tripleCharges (sourceA2151 + difference 3 2) (sourceB2151 + difference 2 3) sourceC2151) = raw29729 := by
      apply Matrix.ext; unfold tripleCharges sourceA2151 sourceB2151 sourceC2151 difference raw29729; decide +kernel
    rw [ha]
    exact (canonical29729 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2151 + difference 3 4) (sourceB2151 + difference 4 3) sourceC2151) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2960) := by
    have ha : (tripleCharges (sourceA2151 + difference 3 4) (sourceB2151 + difference 4 3) sourceC2151) = raw7852 := by
      apply Matrix.ext; unfold tripleCharges sourceA2151 sourceB2151 sourceC2151 difference raw7852; decide +kernel
    rw [ha]
    exact (canonical7852 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2151 + difference 3 5) (sourceB2151 + difference 5 3) sourceC2151) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2959) := by
    have ha : (tripleCharges (sourceA2151 + difference 3 5) (sourceB2151 + difference 5 3) sourceC2151) = raw29730 := by
      apply Matrix.ext; unfold tripleCharges sourceA2151 sourceB2151 sourceC2151 difference raw29730; decide +kernel
    rw [ha]
    exact (canonical29730 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2151 + difference 4 0) (sourceB2151 + difference 0 4) sourceC2151) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1109) := by
    have ha : (tripleCharges (sourceA2151 + difference 4 0) (sourceB2151 + difference 0 4) sourceC2151) = raw22767 := by
      apply Matrix.ext; unfold tripleCharges sourceA2151 sourceB2151 sourceC2151 difference raw22767; decide +kernel
    rw [ha]
    exact (canonical22767 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2151 + difference 4 1) (sourceB2151 + difference 1 4) sourceC2151) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1767) := by
    have ha : (tripleCharges (sourceA2151 + difference 4 1) (sourceB2151 + difference 1 4) sourceC2151) = raw29731 := by
      apply Matrix.ext; unfold tripleCharges sourceA2151 sourceB2151 sourceC2151 difference raw29731; decide +kernel
    rw [ha]
    exact (canonical29731 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2151 + difference 4 2) (sourceB2151 + difference 2 4) sourceC2151) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1762) := by
    have ha : (tripleCharges (sourceA2151 + difference 4 2) (sourceB2151 + difference 2 4) sourceC2151) = raw29732 := by
      apply Matrix.ext; unfold tripleCharges sourceA2151 sourceB2151 sourceC2151 difference raw29732; decide +kernel
    rw [ha]
    exact (canonical29732 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2151 + difference 4 3) (sourceB2151 + difference 3 4) sourceC2151) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1778) := by
    have ha : (tripleCharges (sourceA2151 + difference 4 3) (sourceB2151 + difference 3 4) sourceC2151) = raw29733 := by
      apply Matrix.ext; unfold tripleCharges sourceA2151 sourceB2151 sourceC2151 difference raw29733; decide +kernel
    rw [ha]
    exact (canonical29733 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2151 + difference 4 5) (sourceB2151 + difference 5 4) sourceC2151) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2025) := by
    have ha : (tripleCharges (sourceA2151 + difference 4 5) (sourceB2151 + difference 5 4) sourceC2151) = raw29734 := by
      apply Matrix.ext; unfold tripleCharges sourceA2151 sourceB2151 sourceC2151 difference raw29734; decide +kernel
    rw [ha]
    exact (canonical29734 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2151 + difference 5 0) (sourceB2151 + difference 0 5) sourceC2151) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1110) := by
    have ha : (tripleCharges (sourceA2151 + difference 5 0) (sourceB2151 + difference 0 5) sourceC2151) = raw20783 := by
      apply Matrix.ext; unfold tripleCharges sourceA2151 sourceB2151 sourceC2151 difference raw20783; decide +kernel
    rw [ha]
    exact (canonical20783 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2151 + difference 5 1) (sourceB2151 + difference 1 5) sourceC2151) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2301) := by
    have ha : (tripleCharges (sourceA2151 + difference 5 1) (sourceB2151 + difference 1 5) sourceC2151) = raw27855 := by
      apply Matrix.ext; unfold tripleCharges sourceA2151 sourceB2151 sourceC2151 difference raw27855; decide +kernel
    rw [ha]
    exact (canonical27855 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2151 + difference 5 2) (sourceB2151 + difference 2 5) sourceC2151) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2297) := by
    have ha : (tripleCharges (sourceA2151 + difference 5 2) (sourceB2151 + difference 2 5) sourceC2151) = raw27856 := by
      apply Matrix.ext; unfold tripleCharges sourceA2151 sourceB2151 sourceC2151 difference raw27856; decide +kernel
    rw [ha]
    exact (canonical27856 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2151 + difference 5 3) (sourceB2151 + difference 3 5) sourceC2151) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2310) := by
    have ha : (tripleCharges (sourceA2151 + difference 5 3) (sourceB2151 + difference 3 5) sourceC2151) = raw27857 := by
      apply Matrix.ext; unfold tripleCharges sourceA2151 sourceB2151 sourceC2151 difference raw27857; decide +kernel
    rw [ha]
    exact (canonical27857 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2151 + difference 5 4) (sourceB2151 + difference 4 5) sourceC2151) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2485) := by
    have ha : (tripleCharges (sourceA2151 + difference 5 4) (sourceB2151 + difference 4 5) sourceC2151) = raw7862 := by
      apply Matrix.ext; unfold tripleCharges sourceA2151 sourceB2151 sourceC2151 difference raw7862; decide +kernel
    rw [ha]
    exact (canonical7862 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2151 sourceB2151 sourceC2151
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2151, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2152 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2152 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC2152 : Charge := ![1, 1, 0, 1, -2, -1]
def sourceForm2152 : Integer.Sparse Master := [(Sum.inr 4332, 1), (Sum.inr 4334, 1), (Sum.inr 4335, 1), (Sum.inr 4357, 1), (Sum.inr 4444, 1), (Sum.inr 4930, 1), (Sum.inr 4933, 1), (Sum.inr 4934, 1), (Sum.inr 4935, 1), (Sum.inr 4948, 1), (Sum.inr 4951, 1), (Sum.inr 4954, 1), (Sum.inr 4970, 1), (Sum.inr 5040, 1), (Sum.inr 5067, 1), (Sum.inr 5078, 1), (Sum.inr 5117, 1), (Sum.inr 5145, 1), (Sum.inr 5147, 1), (Sum.inr 5149, 1), (Sum.inr 5152, 1), (Sum.inr 5164, 1), (Sum.inr 5170, 1), (Sum.inr 5282, 1), (Sum.inr 5284, 1), (Sum.inr 5352, 1), (Sum.inr 5356, 1), (Sum.inr 5369, 1), (Sum.inr 5410, 1), (Sum.inr 5473, 1)]

theorem sourceEq2152 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2152 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2152 + difference 0 1) (sourceB2152 + difference 1 0) sourceC2152) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5356) := by
    have ha : (tripleCharges (sourceA2152 + difference 0 1) (sourceB2152 + difference 1 0) sourceC2152) = raw17724 := by
      apply Matrix.ext; unfold tripleCharges sourceA2152 sourceB2152 sourceC2152 difference raw17724; decide +kernel
    rw [ha]
    exact (canonical17724 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2152 + difference 0 2) (sourceB2152 + difference 2 0) sourceC2152) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5352) := by
    have ha : (tripleCharges (sourceA2152 + difference 0 2) (sourceB2152 + difference 2 0) sourceC2152) = raw17725 := by
      apply Matrix.ext; unfold tripleCharges sourceA2152 sourceB2152 sourceC2152 difference raw17725; decide +kernel
    rw [ha]
    exact (canonical17725 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2152 + difference 0 3) (sourceB2152 + difference 3 0) sourceC2152) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5369) := by
    have ha : (tripleCharges (sourceA2152 + difference 0 3) (sourceB2152 + difference 3 0) sourceC2152) = raw17726 := by
      apply Matrix.ext; unfold tripleCharges sourceA2152 sourceB2152 sourceC2152 difference raw17726; decide +kernel
    rw [ha]
    exact (canonical17726 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2152 + difference 0 4) (sourceB2152 + difference 4 0) sourceC2152) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA2152 + difference 0 4) (sourceB2152 + difference 4 0) sourceC2152) = raw29735 := by
      apply Matrix.ext; unfold tripleCharges sourceA2152 sourceB2152 sourceC2152 difference raw29735; decide +kernel
    rw [ha]
    exact (canonical29735 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2152 + difference 0 5) (sourceB2152 + difference 5 0) sourceC2152) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5410) := by
    have ha : (tripleCharges (sourceA2152 + difference 0 5) (sourceB2152 + difference 5 0) sourceC2152) = raw17727 := by
      apply Matrix.ext; unfold tripleCharges sourceA2152 sourceB2152 sourceC2152 difference raw17727; decide +kernel
    rw [ha]
    exact (canonical17727 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2152 + difference 1 0) (sourceB2152 + difference 0 1) sourceC2152) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4444) := by
    have ha : (tripleCharges (sourceA2152 + difference 1 0) (sourceB2152 + difference 0 1) sourceC2152) = raw29736 := by
      apply Matrix.ext; unfold tripleCharges sourceA2152 sourceB2152 sourceC2152 difference raw29736; decide +kernel
    rw [ha]
    exact (canonical29736 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2152 + difference 1 2) (sourceB2152 + difference 2 1) sourceC2152) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5067) := by
    have ha : (tripleCharges (sourceA2152 + difference 1 2) (sourceB2152 + difference 2 1) sourceC2152) = raw29737 := by
      apply Matrix.ext; unfold tripleCharges sourceA2152 sourceB2152 sourceC2152 difference raw29737; decide +kernel
    rw [ha]
    exact (canonical29737 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2152 + difference 1 3) (sourceB2152 + difference 3 1) sourceC2152) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5152) := by
    have ha : (tripleCharges (sourceA2152 + difference 1 3) (sourceB2152 + difference 3 1) sourceC2152) = raw29738 := by
      apply Matrix.ext; unfold tripleCharges sourceA2152 sourceB2152 sourceC2152 difference raw29738; decide +kernel
    rw [ha]
    exact (canonical29738 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2152 + difference 1 4) (sourceB2152 + difference 4 1) sourceC2152) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5282) := by
    have ha : (tripleCharges (sourceA2152 + difference 1 4) (sourceB2152 + difference 4 1) sourceC2152) = raw17708 := by
      apply Matrix.ext; unfold tripleCharges sourceA2152 sourceB2152 sourceC2152 difference raw17708; decide +kernel
    rw [ha]
    exact (canonical17708 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2152 + difference 1 5) (sourceB2152 + difference 5 1) sourceC2152) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA2152 + difference 1 5) (sourceB2152 + difference 5 1) sourceC2152) = raw29739 := by
      apply Matrix.ext; unfold tripleCharges sourceA2152 sourceB2152 sourceC2152 difference raw29739; decide +kernel
    rw [ha]
    exact (canonical29739 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2152 + difference 2 0) (sourceB2152 + difference 0 2) sourceC2152) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4332) := by
    have ha : (tripleCharges (sourceA2152 + difference 2 0) (sourceB2152 + difference 0 2) sourceC2152) = raw29740 := by
      apply Matrix.ext; unfold tripleCharges sourceA2152 sourceB2152 sourceC2152 difference raw29740; decide +kernel
    rw [ha]
    exact (canonical29740 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2152 + difference 2 1) (sourceB2152 + difference 1 2) sourceC2152) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4933) := by
    have ha : (tripleCharges (sourceA2152 + difference 2 1) (sourceB2152 + difference 1 2) sourceC2152) = raw29741 := by
      apply Matrix.ext; unfold tripleCharges sourceA2152 sourceB2152 sourceC2152 difference raw29741; decide +kernel
    rw [ha]
    exact (canonical29741 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2152 + difference 2 3) (sourceB2152 + difference 3 2) sourceC2152) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5117) := by
    have ha : (tripleCharges (sourceA2152 + difference 2 3) (sourceB2152 + difference 3 2) sourceC2152) = raw29742 := by
      apply Matrix.ext; unfold tripleCharges sourceA2152 sourceB2152 sourceC2152 difference raw29742; decide +kernel
    rw [ha]
    exact (canonical29742 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2152 + difference 2 4) (sourceB2152 + difference 4 2) sourceC2152) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5145) := by
    have ha : (tripleCharges (sourceA2152 + difference 2 4) (sourceB2152 + difference 4 2) sourceC2152) = raw17713 := by
      apply Matrix.ext; unfold tripleCharges sourceA2152 sourceB2152 sourceC2152 difference raw17713; decide +kernel
    rw [ha]
    exact (canonical17713 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2152 + difference 2 5) (sourceB2152 + difference 5 2) sourceC2152) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5149) := by
    have ha : (tripleCharges (sourceA2152 + difference 2 5) (sourceB2152 + difference 5 2) sourceC2152) = raw29743 := by
      apply Matrix.ext; unfold tripleCharges sourceA2152 sourceB2152 sourceC2152 difference raw29743; decide +kernel
    rw [ha]
    exact (canonical29743 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2152 + difference 3 0) (sourceB2152 + difference 0 3) sourceC2152) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4357) := by
    have ha : (tripleCharges (sourceA2152 + difference 3 0) (sourceB2152 + difference 0 3) sourceC2152) = raw29744 := by
      apply Matrix.ext; unfold tripleCharges sourceA2152 sourceB2152 sourceC2152 difference raw29744; decide +kernel
    rw [ha]
    exact (canonical29744 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2152 + difference 3 1) (sourceB2152 + difference 1 3) sourceC2152) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4951) := by
    have ha : (tripleCharges (sourceA2152 + difference 3 1) (sourceB2152 + difference 1 3) sourceC2152) = raw29745 := by
      apply Matrix.ext; unfold tripleCharges sourceA2152 sourceB2152 sourceC2152 difference raw29745; decide +kernel
    rw [ha]
    exact (canonical29745 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2152 + difference 3 2) (sourceB2152 + difference 2 3) sourceC2152) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5040) := by
    have ha : (tripleCharges (sourceA2152 + difference 3 2) (sourceB2152 + difference 2 3) sourceC2152) = raw29746 := by
      apply Matrix.ext; unfold tripleCharges sourceA2152 sourceB2152 sourceC2152 difference raw29746; decide +kernel
    rw [ha]
    exact (canonical29746 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2152 + difference 3 4) (sourceB2152 + difference 4 3) sourceC2152) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5164) := by
    have ha : (tripleCharges (sourceA2152 + difference 3 4) (sourceB2152 + difference 4 3) sourceC2152) = raw17718 := by
      apply Matrix.ext; unfold tripleCharges sourceA2152 sourceB2152 sourceC2152 difference raw17718; decide +kernel
    rw [ha]
    exact (canonical17718 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2152 + difference 3 5) (sourceB2152 + difference 5 3) sourceC2152) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5170) := by
    have ha : (tripleCharges (sourceA2152 + difference 3 5) (sourceB2152 + difference 5 3) sourceC2152) = raw29747 := by
      apply Matrix.ext; unfold tripleCharges sourceA2152 sourceB2152 sourceC2152 difference raw29747; decide +kernel
    rw [ha]
    exact (canonical29747 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2152 + difference 4 0) (sourceB2152 + difference 0 4) sourceC2152) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4335) := by
    have ha : (tripleCharges (sourceA2152 + difference 4 0) (sourceB2152 + difference 0 4) sourceC2152) = raw29748 := by
      apply Matrix.ext; unfold tripleCharges sourceA2152 sourceB2152 sourceC2152 difference raw29748; decide +kernel
    rw [ha]
    exact (canonical29748 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2152 + difference 4 1) (sourceB2152 + difference 1 4) sourceC2152) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4935) := by
    have ha : (tripleCharges (sourceA2152 + difference 4 1) (sourceB2152 + difference 1 4) sourceC2152) = raw29749 := by
      apply Matrix.ext; unfold tripleCharges sourceA2152 sourceB2152 sourceC2152 difference raw29749; decide +kernel
    rw [ha]
    exact (canonical29749 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2152 + difference 4 2) (sourceB2152 + difference 2 4) sourceC2152) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4930) := by
    have ha : (tripleCharges (sourceA2152 + difference 4 2) (sourceB2152 + difference 2 4) sourceC2152) = raw29750 := by
      apply Matrix.ext; unfold tripleCharges sourceA2152 sourceB2152 sourceC2152 difference raw29750; decide +kernel
    rw [ha]
    exact (canonical29750 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2152 + difference 4 3) (sourceB2152 + difference 3 4) sourceC2152) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4948) := by
    have ha : (tripleCharges (sourceA2152 + difference 4 3) (sourceB2152 + difference 3 4) sourceC2152) = raw29751 := by
      apply Matrix.ext; unfold tripleCharges sourceA2152 sourceB2152 sourceC2152 difference raw29751; decide +kernel
    rw [ha]
    exact (canonical29751 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2152 + difference 4 5) (sourceB2152 + difference 5 4) sourceC2152) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5078) := by
    have ha : (tripleCharges (sourceA2152 + difference 4 5) (sourceB2152 + difference 5 4) sourceC2152) = raw29752 := by
      apply Matrix.ext; unfold tripleCharges sourceA2152 sourceB2152 sourceC2152 difference raw29752; decide +kernel
    rw [ha]
    exact (canonical29752 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2152 + difference 5 0) (sourceB2152 + difference 0 5) sourceC2152) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4334) := by
    have ha : (tripleCharges (sourceA2152 + difference 5 0) (sourceB2152 + difference 0 5) sourceC2152) = raw29753 := by
      apply Matrix.ext; unfold tripleCharges sourceA2152 sourceB2152 sourceC2152 difference raw29753; decide +kernel
    rw [ha]
    exact (canonical29753 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2152 + difference 5 1) (sourceB2152 + difference 1 5) sourceC2152) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4934) := by
    have ha : (tripleCharges (sourceA2152 + difference 5 1) (sourceB2152 + difference 1 5) sourceC2152) = raw29754 := by
      apply Matrix.ext; unfold tripleCharges sourceA2152 sourceB2152 sourceC2152 difference raw29754; decide +kernel
    rw [ha]
    exact (canonical29754 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2152 + difference 5 2) (sourceB2152 + difference 2 5) sourceC2152) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4954) := by
    have ha : (tripleCharges (sourceA2152 + difference 5 2) (sourceB2152 + difference 2 5) sourceC2152) = raw29755 := by
      apply Matrix.ext; unfold tripleCharges sourceA2152 sourceB2152 sourceC2152 difference raw29755; decide +kernel
    rw [ha]
    exact (canonical29755 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2152 + difference 5 3) (sourceB2152 + difference 3 5) sourceC2152) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4970) := by
    have ha : (tripleCharges (sourceA2152 + difference 5 3) (sourceB2152 + difference 3 5) sourceC2152) = raw29756 := by
      apply Matrix.ext; unfold tripleCharges sourceA2152 sourceB2152 sourceC2152 difference raw29756; decide +kernel
    rw [ha]
    exact (canonical29756 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2152 + difference 5 4) (sourceB2152 + difference 4 5) sourceC2152) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5147) := by
    have ha : (tripleCharges (sourceA2152 + difference 5 4) (sourceB2152 + difference 4 5) sourceC2152) = raw17728 := by
      apply Matrix.ext; unfold tripleCharges sourceA2152 sourceB2152 sourceC2152 difference raw17728; decide +kernel
    rw [ha]
    exact (canonical17728 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2152 sourceB2152 sourceC2152
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2152, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2153 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2153 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC2153 : Charge := ![1, 1, 0, 1, -2, -1]
def sourceForm2153 : Integer.Sparse Master := [(Sum.inr 910, 1), (Sum.inr 912, 1), (Sum.inr 913, 1), (Sum.inr 935, 1), (Sum.inr 1026, 1), (Sum.inr 2324, 1), (Sum.inr 2325, 1), (Sum.inr 2326, 1), (Sum.inr 2343, 1), (Sum.inr 2347, 1), (Sum.inr 2357, 1), (Sum.inr 2422, 1), (Sum.inr 2433, 1), (Sum.inr 2473, 1), (Sum.inr 2530, 1), (Sum.inr 2531, 1), (Sum.inr 2567, 1), (Sum.inr 2569, 1), (Sum.inr 2570, 1), (Sum.inr 2572, 1), (Sum.inr 2576, 1), (Sum.inr 2591, 1), (Sum.inr 2596, 1), (Sum.inr 2751, 1), (Sum.inr 2753, 1), (Sum.inr 3926, 1), (Sum.inr 3936, 1), (Sum.inr 3940, 1), (Sum.inr 3995, 1), (Sum.inr 3996, 1)]

theorem sourceEq2153 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2153 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2153 + difference 0 1) (sourceB2153 + difference 1 0) sourceC2153) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3926) := by
    have ha : (tripleCharges (sourceA2153 + difference 0 1) (sourceB2153 + difference 1 0) sourceC2153) = raw29757 := by
      apply Matrix.ext; unfold tripleCharges sourceA2153 sourceB2153 sourceC2153 difference raw29757; decide +kernel
    rw [ha]
    exact (canonical29757 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2153 + difference 0 2) (sourceB2153 + difference 2 0) sourceC2153) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3936) := by
    have ha : (tripleCharges (sourceA2153 + difference 0 2) (sourceB2153 + difference 2 0) sourceC2153) = raw29758 := by
      apply Matrix.ext; unfold tripleCharges sourceA2153 sourceB2153 sourceC2153 difference raw29758; decide +kernel
    rw [ha]
    exact (canonical29758 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2153 + difference 0 3) (sourceB2153 + difference 3 0) sourceC2153) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3940) := by
    have ha : (tripleCharges (sourceA2153 + difference 0 3) (sourceB2153 + difference 3 0) sourceC2153) = raw29759 := by
      apply Matrix.ext; unfold tripleCharges sourceA2153 sourceB2153 sourceC2153 difference raw29759; decide +kernel
    rw [ha]
    exact (canonical29759 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2153 + difference 0 4) (sourceB2153 + difference 4 0) sourceC2153) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3995) := by
    have ha : (tripleCharges (sourceA2153 + difference 0 4) (sourceB2153 + difference 4 0) sourceC2153) = raw29760 := by
      apply Matrix.ext; unfold tripleCharges sourceA2153 sourceB2153 sourceC2153 difference raw29760; decide +kernel
    rw [ha]
    exact (canonical29760 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2153 + difference 0 5) (sourceB2153 + difference 5 0) sourceC2153) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3996) := by
    have ha : (tripleCharges (sourceA2153 + difference 0 5) (sourceB2153 + difference 5 0) sourceC2153) = raw29761 := by
      apply Matrix.ext; unfold tripleCharges sourceA2153 sourceB2153 sourceC2153 difference raw29761; decide +kernel
    rw [ha]
    exact (canonical29761 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2153 + difference 1 0) (sourceB2153 + difference 0 1) sourceC2153) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1026) := by
    have ha : (tripleCharges (sourceA2153 + difference 1 0) (sourceB2153 + difference 0 1) sourceC2153) = raw29762 := by
      apply Matrix.ext; unfold tripleCharges sourceA2153 sourceB2153 sourceC2153 difference raw29762; decide +kernel
    rw [ha]
    exact (canonical29762 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2153 + difference 1 2) (sourceB2153 + difference 2 1) sourceC2153) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2473) := by
    have ha : (tripleCharges (sourceA2153 + difference 1 2) (sourceB2153 + difference 2 1) sourceC2153) = raw29763 := by
      apply Matrix.ext; unfold tripleCharges sourceA2153 sourceB2153 sourceC2153 difference raw29763; decide +kernel
    rw [ha]
    exact (canonical29763 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2153 + difference 1 3) (sourceB2153 + difference 3 1) sourceC2153) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2576) := by
    have ha : (tripleCharges (sourceA2153 + difference 1 3) (sourceB2153 + difference 3 1) sourceC2153) = raw29764 := by
      apply Matrix.ext; unfold tripleCharges sourceA2153 sourceB2153 sourceC2153 difference raw29764; decide +kernel
    rw [ha]
    exact (canonical29764 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2153 + difference 1 4) (sourceB2153 + difference 4 1) sourceC2153) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2751) := by
    have ha : (tripleCharges (sourceA2153 + difference 1 4) (sourceB2153 + difference 4 1) sourceC2153) = raw29765 := by
      apply Matrix.ext; unfold tripleCharges sourceA2153 sourceB2153 sourceC2153 difference raw29765; decide +kernel
    rw [ha]
    exact (canonical29765 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2153 + difference 1 5) (sourceB2153 + difference 5 1) sourceC2153) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2753) := by
    have ha : (tripleCharges (sourceA2153 + difference 1 5) (sourceB2153 + difference 5 1) sourceC2153) = raw29766 := by
      apply Matrix.ext; unfold tripleCharges sourceA2153 sourceB2153 sourceC2153 difference raw29766; decide +kernel
    rw [ha]
    exact (canonical29766 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2153 + difference 2 0) (sourceB2153 + difference 0 2) sourceC2153) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 910) := by
    have ha : (tripleCharges (sourceA2153 + difference 2 0) (sourceB2153 + difference 0 2) sourceC2153) = raw29767 := by
      apply Matrix.ext; unfold tripleCharges sourceA2153 sourceB2153 sourceC2153 difference raw29767; decide +kernel
    rw [ha]
    exact (canonical29767 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2153 + difference 2 1) (sourceB2153 + difference 1 2) sourceC2153) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2324) := by
    have ha : (tripleCharges (sourceA2153 + difference 2 1) (sourceB2153 + difference 1 2) sourceC2153) = raw29768 := by
      apply Matrix.ext; unfold tripleCharges sourceA2153 sourceB2153 sourceC2153 difference raw29768; decide +kernel
    rw [ha]
    exact (canonical29768 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2153 + difference 2 3) (sourceB2153 + difference 3 2) sourceC2153) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2530) := by
    have ha : (tripleCharges (sourceA2153 + difference 2 3) (sourceB2153 + difference 3 2) sourceC2153) = raw29769 := by
      apply Matrix.ext; unfold tripleCharges sourceA2153 sourceB2153 sourceC2153 difference raw29769; decide +kernel
    rw [ha]
    exact (canonical29769 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2153 + difference 2 4) (sourceB2153 + difference 4 2) sourceC2153) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2567) := by
    have ha : (tripleCharges (sourceA2153 + difference 2 4) (sourceB2153 + difference 4 2) sourceC2153) = raw29770 := by
      apply Matrix.ext; unfold tripleCharges sourceA2153 sourceB2153 sourceC2153 difference raw29770; decide +kernel
    rw [ha]
    exact (canonical29770 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2153 + difference 2 5) (sourceB2153 + difference 5 2) sourceC2153) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2570) := by
    have ha : (tripleCharges (sourceA2153 + difference 2 5) (sourceB2153 + difference 5 2) sourceC2153) = raw29771 := by
      apply Matrix.ext; unfold tripleCharges sourceA2153 sourceB2153 sourceC2153 difference raw29771; decide +kernel
    rw [ha]
    exact (canonical29771 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2153 + difference 3 0) (sourceB2153 + difference 0 3) sourceC2153) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 935) := by
    have ha : (tripleCharges (sourceA2153 + difference 3 0) (sourceB2153 + difference 0 3) sourceC2153) = raw29772 := by
      apply Matrix.ext; unfold tripleCharges sourceA2153 sourceB2153 sourceC2153 difference raw29772; decide +kernel
    rw [ha]
    exact (canonical29772 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2153 + difference 3 1) (sourceB2153 + difference 1 3) sourceC2153) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2343) := by
    have ha : (tripleCharges (sourceA2153 + difference 3 1) (sourceB2153 + difference 1 3) sourceC2153) = raw29773 := by
      apply Matrix.ext; unfold tripleCharges sourceA2153 sourceB2153 sourceC2153 difference raw29773; decide +kernel
    rw [ha]
    exact (canonical29773 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2153 + difference 3 2) (sourceB2153 + difference 2 3) sourceC2153) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2433) := by
    have ha : (tripleCharges (sourceA2153 + difference 3 2) (sourceB2153 + difference 2 3) sourceC2153) = raw29774 := by
      apply Matrix.ext; unfold tripleCharges sourceA2153 sourceB2153 sourceC2153 difference raw29774; decide +kernel
    rw [ha]
    exact (canonical29774 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2153 + difference 3 4) (sourceB2153 + difference 4 3) sourceC2153) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2591) := by
    have ha : (tripleCharges (sourceA2153 + difference 3 4) (sourceB2153 + difference 4 3) sourceC2153) = raw29775 := by
      apply Matrix.ext; unfold tripleCharges sourceA2153 sourceB2153 sourceC2153 difference raw29775; decide +kernel
    rw [ha]
    exact (canonical29775 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2153 + difference 3 5) (sourceB2153 + difference 5 3) sourceC2153) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2596) := by
    have ha : (tripleCharges (sourceA2153 + difference 3 5) (sourceB2153 + difference 5 3) sourceC2153) = raw29776 := by
      apply Matrix.ext; unfold tripleCharges sourceA2153 sourceB2153 sourceC2153 difference raw29776; decide +kernel
    rw [ha]
    exact (canonical29776 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2153 + difference 4 0) (sourceB2153 + difference 0 4) sourceC2153) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 913) := by
    have ha : (tripleCharges (sourceA2153 + difference 4 0) (sourceB2153 + difference 0 4) sourceC2153) = raw29777 := by
      apply Matrix.ext; unfold tripleCharges sourceA2153 sourceB2153 sourceC2153 difference raw29777; decide +kernel
    rw [ha]
    exact (canonical29777 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2153 + difference 4 1) (sourceB2153 + difference 1 4) sourceC2153) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2326) := by
    have ha : (tripleCharges (sourceA2153 + difference 4 1) (sourceB2153 + difference 1 4) sourceC2153) = raw29778 := by
      apply Matrix.ext; unfold tripleCharges sourceA2153 sourceB2153 sourceC2153 difference raw29778; decide +kernel
    rw [ha]
    exact (canonical29778 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2153 + difference 4 2) (sourceB2153 + difference 2 4) sourceC2153) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2422) := by
    have ha : (tripleCharges (sourceA2153 + difference 4 2) (sourceB2153 + difference 2 4) sourceC2153) = raw29779 := by
      apply Matrix.ext; unfold tripleCharges sourceA2153 sourceB2153 sourceC2153 difference raw29779; decide +kernel
    rw [ha]
    exact (canonical29779 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2153 + difference 4 3) (sourceB2153 + difference 3 4) sourceC2153) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2531) := by
    have ha : (tripleCharges (sourceA2153 + difference 4 3) (sourceB2153 + difference 3 4) sourceC2153) = raw29780 := by
      apply Matrix.ext; unfold tripleCharges sourceA2153 sourceB2153 sourceC2153 difference raw29780; decide +kernel
    rw [ha]
    exact (canonical29780 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2153 + difference 4 5) (sourceB2153 + difference 5 4) sourceC2153) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2572) := by
    have ha : (tripleCharges (sourceA2153 + difference 4 5) (sourceB2153 + difference 5 4) sourceC2153) = raw29781 := by
      apply Matrix.ext; unfold tripleCharges sourceA2153 sourceB2153 sourceC2153 difference raw29781; decide +kernel
    rw [ha]
    exact (canonical29781 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2153 + difference 5 0) (sourceB2153 + difference 0 5) sourceC2153) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 912) := by
    have ha : (tripleCharges (sourceA2153 + difference 5 0) (sourceB2153 + difference 0 5) sourceC2153) = raw29782 := by
      apply Matrix.ext; unfold tripleCharges sourceA2153 sourceB2153 sourceC2153 difference raw29782; decide +kernel
    rw [ha]
    exact (canonical29782 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2153 + difference 5 1) (sourceB2153 + difference 1 5) sourceC2153) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2325) := by
    have ha : (tripleCharges (sourceA2153 + difference 5 1) (sourceB2153 + difference 1 5) sourceC2153) = raw29783 := by
      apply Matrix.ext; unfold tripleCharges sourceA2153 sourceB2153 sourceC2153 difference raw29783; decide +kernel
    rw [ha]
    exact (canonical29783 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2153 + difference 5 2) (sourceB2153 + difference 2 5) sourceC2153) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2347) := by
    have ha : (tripleCharges (sourceA2153 + difference 5 2) (sourceB2153 + difference 2 5) sourceC2153) = raw29784 := by
      apply Matrix.ext; unfold tripleCharges sourceA2153 sourceB2153 sourceC2153 difference raw29784; decide +kernel
    rw [ha]
    exact (canonical29784 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2153 + difference 5 3) (sourceB2153 + difference 3 5) sourceC2153) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2357) := by
    have ha : (tripleCharges (sourceA2153 + difference 5 3) (sourceB2153 + difference 3 5) sourceC2153) = raw29785 := by
      apply Matrix.ext; unfold tripleCharges sourceA2153 sourceB2153 sourceC2153 difference raw29785; decide +kernel
    rw [ha]
    exact (canonical29785 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2153 + difference 5 4) (sourceB2153 + difference 4 5) sourceC2153) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2569) := by
    have ha : (tripleCharges (sourceA2153 + difference 5 4) (sourceB2153 + difference 4 5) sourceC2153) = raw29786 := by
      apply Matrix.ext; unfold tripleCharges sourceA2153 sourceB2153 sourceC2153 difference raw29786; decide +kernel
    rw [ha]
    exact (canonical29786 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2153 sourceB2153 sourceC2153
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2153, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2154 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2154 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC2154 : Charge := ![1, 1, 0, 1, -2, -1]
def sourceForm2154 : Integer.Sparse Master := [(Sum.inr 1678, 1), (Sum.inr 1679, 1), (Sum.inr 1682, 1), (Sum.inr 1689, 1), (Sum.inr 1736, 1), (Sum.inr 3408, 1), (Sum.inr 3414, 1), (Sum.inr 3415, 1), (Sum.inr 3418, 1), (Sum.inr 3419, 1), (Sum.inr 3420, 1), (Sum.inr 3452, 1), (Sum.inr 3454, 1), (Sum.inr 3476, 1), (Sum.inr 3481, 1), (Sum.inr 3530, 1), (Sum.inr 3562, 1), (Sum.inr 3565, 1), (Sum.inr 3580, 1), (Sum.inr 3588, 1), (Sum.inr 3599, 1), (Sum.inr 3605, 1), (Sum.inr 3606, 1), (Sum.inr 3612, 1), (Sum.inr 3625, 1), (Sum.inr 3764, 1), (Sum.inr 3773, 1), (Sum.inr 3774, 1), (Sum.inr 3816, 1), (Sum.inr 3961, 1)]

theorem sourceEq2154 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2154 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2154 + difference 0 1) (sourceB2154 + difference 1 0) sourceC2154) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3773) := by
    have ha : (tripleCharges (sourceA2154 + difference 0 1) (sourceB2154 + difference 1 0) sourceC2154) = raw17754 := by
      apply Matrix.ext; unfold tripleCharges sourceA2154 sourceB2154 sourceC2154 difference raw17754; decide +kernel
    rw [ha]
    exact (canonical17754 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2154 + difference 0 2) (sourceB2154 + difference 2 0) sourceC2154) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3764) := by
    have ha : (tripleCharges (sourceA2154 + difference 0 2) (sourceB2154 + difference 2 0) sourceC2154) = raw17755 := by
      apply Matrix.ext; unfold tripleCharges sourceA2154 sourceB2154 sourceC2154 difference raw17755; decide +kernel
    rw [ha]
    exact (canonical17755 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2154 + difference 0 3) (sourceB2154 + difference 3 0) sourceC2154) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3774) := by
    have ha : (tripleCharges (sourceA2154 + difference 0 3) (sourceB2154 + difference 3 0) sourceC2154) = raw17756 := by
      apply Matrix.ext; unfold tripleCharges sourceA2154 sourceB2154 sourceC2154 difference raw17756; decide +kernel
    rw [ha]
    exact (canonical17756 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2154 + difference 0 4) (sourceB2154 + difference 4 0) sourceC2154) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3961) := by
    have ha : (tripleCharges (sourceA2154 + difference 0 4) (sourceB2154 + difference 4 0) sourceC2154) = raw29787 := by
      apply Matrix.ext; unfold tripleCharges sourceA2154 sourceB2154 sourceC2154 difference raw29787; decide +kernel
    rw [ha]
    exact (canonical29787 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2154 + difference 0 5) (sourceB2154 + difference 5 0) sourceC2154) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3816) := by
    have ha : (tripleCharges (sourceA2154 + difference 0 5) (sourceB2154 + difference 5 0) sourceC2154) = raw17757 := by
      apply Matrix.ext; unfold tripleCharges sourceA2154 sourceB2154 sourceC2154 difference raw17757; decide +kernel
    rw [ha]
    exact (canonical17757 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2154 + difference 1 0) (sourceB2154 + difference 0 1) sourceC2154) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1736) := by
    have ha : (tripleCharges (sourceA2154 + difference 1 0) (sourceB2154 + difference 0 1) sourceC2154) = raw29788 := by
      apply Matrix.ext; unfold tripleCharges sourceA2154 sourceB2154 sourceC2154 difference raw29788; decide +kernel
    rw [ha]
    exact (canonical29788 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2154 + difference 1 2) (sourceB2154 + difference 2 1) sourceC2154) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3476) := by
    have ha : (tripleCharges (sourceA2154 + difference 1 2) (sourceB2154 + difference 2 1) sourceC2154) = raw29789 := by
      apply Matrix.ext; unfold tripleCharges sourceA2154 sourceB2154 sourceC2154 difference raw29789; decide +kernel
    rw [ha]
    exact (canonical29789 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2154 + difference 1 3) (sourceB2154 + difference 3 1) sourceC2154) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3612) := by
    have ha : (tripleCharges (sourceA2154 + difference 1 3) (sourceB2154 + difference 3 1) sourceC2154) = raw29790 := by
      apply Matrix.ext; unfold tripleCharges sourceA2154 sourceB2154 sourceC2154 difference raw29790; decide +kernel
    rw [ha]
    exact (canonical29790 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2154 + difference 1 4) (sourceB2154 + difference 4 1) sourceC2154) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3580) := by
    have ha : (tripleCharges (sourceA2154 + difference 1 4) (sourceB2154 + difference 4 1) sourceC2154) = raw17738 := by
      apply Matrix.ext; unfold tripleCharges sourceA2154 sourceB2154 sourceC2154 difference raw17738; decide +kernel
    rw [ha]
    exact (canonical17738 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2154 + difference 1 5) (sourceB2154 + difference 5 1) sourceC2154) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3625) := by
    have ha : (tripleCharges (sourceA2154 + difference 1 5) (sourceB2154 + difference 5 1) sourceC2154) = raw29791 := by
      apply Matrix.ext; unfold tripleCharges sourceA2154 sourceB2154 sourceC2154 difference raw29791; decide +kernel
    rw [ha]
    exact (canonical29791 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2154 + difference 2 0) (sourceB2154 + difference 0 2) sourceC2154) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1678) := by
    have ha : (tripleCharges (sourceA2154 + difference 2 0) (sourceB2154 + difference 0 2) sourceC2154) = raw29792 := by
      apply Matrix.ext; unfold tripleCharges sourceA2154 sourceB2154 sourceC2154 difference raw29792; decide +kernel
    rw [ha]
    exact (canonical29792 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2154 + difference 2 1) (sourceB2154 + difference 1 2) sourceC2154) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3414) := by
    have ha : (tripleCharges (sourceA2154 + difference 2 1) (sourceB2154 + difference 1 2) sourceC2154) = raw29793 := by
      apply Matrix.ext; unfold tripleCharges sourceA2154 sourceB2154 sourceC2154 difference raw29793; decide +kernel
    rw [ha]
    exact (canonical29793 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2154 + difference 2 3) (sourceB2154 + difference 3 2) sourceC2154) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3599) := by
    have ha : (tripleCharges (sourceA2154 + difference 2 3) (sourceB2154 + difference 3 2) sourceC2154) = raw29794 := by
      apply Matrix.ext; unfold tripleCharges sourceA2154 sourceB2154 sourceC2154 difference raw29794; decide +kernel
    rw [ha]
    exact (canonical29794 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2154 + difference 2 4) (sourceB2154 + difference 4 2) sourceC2154) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3562) := by
    have ha : (tripleCharges (sourceA2154 + difference 2 4) (sourceB2154 + difference 4 2) sourceC2154) = raw17743 := by
      apply Matrix.ext; unfold tripleCharges sourceA2154 sourceB2154 sourceC2154 difference raw17743; decide +kernel
    rw [ha]
    exact (canonical17743 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2154 + difference 2 5) (sourceB2154 + difference 5 2) sourceC2154) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3605) := by
    have ha : (tripleCharges (sourceA2154 + difference 2 5) (sourceB2154 + difference 5 2) sourceC2154) = raw29795 := by
      apply Matrix.ext; unfold tripleCharges sourceA2154 sourceB2154 sourceC2154 difference raw29795; decide +kernel
    rw [ha]
    exact (canonical29795 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2154 + difference 3 0) (sourceB2154 + difference 0 3) sourceC2154) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1682) := by
    have ha : (tripleCharges (sourceA2154 + difference 3 0) (sourceB2154 + difference 0 3) sourceC2154) = raw29796 := by
      apply Matrix.ext; unfold tripleCharges sourceA2154 sourceB2154 sourceC2154 difference raw29796; decide +kernel
    rw [ha]
    exact (canonical29796 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2154 + difference 3 1) (sourceB2154 + difference 1 3) sourceC2154) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3418) := by
    have ha : (tripleCharges (sourceA2154 + difference 3 1) (sourceB2154 + difference 1 3) sourceC2154) = raw29797 := by
      apply Matrix.ext; unfold tripleCharges sourceA2154 sourceB2154 sourceC2154 difference raw29797; decide +kernel
    rw [ha]
    exact (canonical29797 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2154 + difference 3 2) (sourceB2154 + difference 2 3) sourceC2154) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3454) := by
    have ha : (tripleCharges (sourceA2154 + difference 3 2) (sourceB2154 + difference 2 3) sourceC2154) = raw29798 := by
      apply Matrix.ext; unfold tripleCharges sourceA2154 sourceB2154 sourceC2154 difference raw29798; decide +kernel
    rw [ha]
    exact (canonical29798 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2154 + difference 3 4) (sourceB2154 + difference 4 3) sourceC2154) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3565) := by
    have ha : (tripleCharges (sourceA2154 + difference 3 4) (sourceB2154 + difference 4 3) sourceC2154) = raw17748 := by
      apply Matrix.ext; unfold tripleCharges sourceA2154 sourceB2154 sourceC2154 difference raw17748; decide +kernel
    rw [ha]
    exact (canonical17748 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2154 + difference 3 5) (sourceB2154 + difference 5 3) sourceC2154) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3606) := by
    have ha : (tripleCharges (sourceA2154 + difference 3 5) (sourceB2154 + difference 5 3) sourceC2154) = raw29799 := by
      apply Matrix.ext; unfold tripleCharges sourceA2154 sourceB2154 sourceC2154 difference raw29799; decide +kernel
    rw [ha]
    exact (canonical29799 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2154 + difference 4 0) (sourceB2154 + difference 0 4) sourceC2154) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1689) := by
    have ha : (tripleCharges (sourceA2154 + difference 4 0) (sourceB2154 + difference 0 4) sourceC2154) = raw29800 := by
      apply Matrix.ext; unfold tripleCharges sourceA2154 sourceB2154 sourceC2154 difference raw29800; decide +kernel
    rw [ha]
    exact (canonical29800 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2154 + difference 4 1) (sourceB2154 + difference 1 4) sourceC2154) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3419) := by
    have ha : (tripleCharges (sourceA2154 + difference 4 1) (sourceB2154 + difference 1 4) sourceC2154) = raw29801 := by
      apply Matrix.ext; unfold tripleCharges sourceA2154 sourceB2154 sourceC2154 difference raw29801; decide +kernel
    rw [ha]
    exact (canonical29801 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2154 + difference 4 2) (sourceB2154 + difference 2 4) sourceC2154) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3408) := by
    have ha : (tripleCharges (sourceA2154 + difference 4 2) (sourceB2154 + difference 2 4) sourceC2154) = raw29802 := by
      apply Matrix.ext; unfold tripleCharges sourceA2154 sourceB2154 sourceC2154 difference raw29802; decide +kernel
    rw [ha]
    exact (canonical29802 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2154 + difference 4 3) (sourceB2154 + difference 3 4) sourceC2154) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3420) := by
    have ha : (tripleCharges (sourceA2154 + difference 4 3) (sourceB2154 + difference 3 4) sourceC2154) = raw29803 := by
      apply Matrix.ext; unfold tripleCharges sourceA2154 sourceB2154 sourceC2154 difference raw29803; decide +kernel
    rw [ha]
    exact (canonical29803 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2154 + difference 4 5) (sourceB2154 + difference 5 4) sourceC2154) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3481) := by
    have ha : (tripleCharges (sourceA2154 + difference 4 5) (sourceB2154 + difference 5 4) sourceC2154) = raw29804 := by
      apply Matrix.ext; unfold tripleCharges sourceA2154 sourceB2154 sourceC2154 difference raw29804; decide +kernel
    rw [ha]
    exact (canonical29804 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2154 + difference 5 0) (sourceB2154 + difference 0 5) sourceC2154) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1679) := by
    have ha : (tripleCharges (sourceA2154 + difference 5 0) (sourceB2154 + difference 0 5) sourceC2154) = raw29805 := by
      apply Matrix.ext; unfold tripleCharges sourceA2154 sourceB2154 sourceC2154 difference raw29805; decide +kernel
    rw [ha]
    exact (canonical29805 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2154 + difference 5 1) (sourceB2154 + difference 1 5) sourceC2154) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3415) := by
    have ha : (tripleCharges (sourceA2154 + difference 5 1) (sourceB2154 + difference 1 5) sourceC2154) = raw29806 := by
      apply Matrix.ext; unfold tripleCharges sourceA2154 sourceB2154 sourceC2154 difference raw29806; decide +kernel
    rw [ha]
    exact (canonical29806 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2154 + difference 5 2) (sourceB2154 + difference 2 5) sourceC2154) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3452) := by
    have ha : (tripleCharges (sourceA2154 + difference 5 2) (sourceB2154 + difference 2 5) sourceC2154) = raw29807 := by
      apply Matrix.ext; unfold tripleCharges sourceA2154 sourceB2154 sourceC2154 difference raw29807; decide +kernel
    rw [ha]
    exact (canonical29807 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2154 + difference 5 3) (sourceB2154 + difference 3 5) sourceC2154) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3588) := by
    have ha : (tripleCharges (sourceA2154 + difference 5 3) (sourceB2154 + difference 3 5) sourceC2154) = raw29808 := by
      apply Matrix.ext; unfold tripleCharges sourceA2154 sourceB2154 sourceC2154 difference raw29808; decide +kernel
    rw [ha]
    exact (canonical29808 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2154 + difference 5 4) (sourceB2154 + difference 4 5) sourceC2154) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3530) := by
    have ha : (tripleCharges (sourceA2154 + difference 5 4) (sourceB2154 + difference 4 5) sourceC2154) = raw17758 := by
      apply Matrix.ext; unfold tripleCharges sourceA2154 sourceB2154 sourceC2154 difference raw17758; decide +kernel
    rw [ha]
    exact (canonical17758 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2154 sourceB2154 sourceC2154
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2154, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2155 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2155 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC2155 : Charge := ![1, 1, 0, 1, -2, -1]
def sourceForm2155 : Integer.Sparse Master := [(Sum.inr 2326, 1), (Sum.inr 2802, 1), (Sum.inr 2822, 1), (Sum.inr 2827, 1), (Sum.inr 2931, 1), (Sum.inr 3694, 1), (Sum.inr 4091, -1)]

theorem sourceEq2155 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2155 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2155 + difference 0 1) (sourceB2155 + difference 1 0) sourceC2155) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3694) := by
    have ha : (tripleCharges (sourceA2155 + difference 0 1) (sourceB2155 + difference 1 0) sourceC2155) = raw29809 := by
      apply Matrix.ext; unfold tripleCharges sourceA2155 sourceB2155 sourceC2155 difference raw29809; decide +kernel
    rw [ha]
    exact (canonical29809 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2155 + difference 1 1) (sourceB2155 + difference 1 1) sourceC2155) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2931) := by
    have ha : (tripleCharges (sourceA2155 + difference 1 1) (sourceB2155 + difference 1 1) sourceC2155) = raw27827 := by
      apply Matrix.ext; unfold tripleCharges sourceA2155 sourceB2155 sourceC2155 difference raw27827; decide +kernel
    rw [ha]
    exact (canonical27827 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2155 + difference 2 1) (sourceB2155 + difference 1 2) sourceC2155) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2822) := by
    have ha : (tripleCharges (sourceA2155 + difference 2 1) (sourceB2155 + difference 1 2) sourceC2155) = raw29810 := by
      apply Matrix.ext; unfold tripleCharges sourceA2155 sourceB2155 sourceC2155 difference raw29810; decide +kernel
    rw [ha]
    exact (canonical29810 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2155 + difference 3 1) (sourceB2155 + difference 1 3) sourceC2155) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2827) := by
    have ha : (tripleCharges (sourceA2155 + difference 3 1) (sourceB2155 + difference 1 3) sourceC2155) = raw29811 := by
      apply Matrix.ext; unfold tripleCharges sourceA2155 sourceB2155 sourceC2155 difference raw29811; decide +kernel
    rw [ha]
    exact (canonical29811 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2155 + difference 4 1) (sourceB2155 + difference 1 4) sourceC2155) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2326) := by
    have ha : (tripleCharges (sourceA2155 + difference 4 1) (sourceB2155 + difference 1 4) sourceC2155) = raw29812 := by
      apply Matrix.ext; unfold tripleCharges sourceA2155 sourceB2155 sourceC2155 difference raw29812; decide +kernel
    rw [ha]
    exact (canonical29812 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2155 + difference 5 1) (sourceB2155 + difference 1 5) sourceC2155) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2802) := by
    have ha : (tripleCharges (sourceA2155 + difference 5 1) (sourceB2155 + difference 1 5) sourceC2155) = raw27825 := by
      apply Matrix.ext; unfold tripleCharges sourceA2155 sourceB2155 sourceC2155 difference raw27825; decide +kernel
    rw [ha]
    exact (canonical27825 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2155 + sourceB2155) sourceC2155) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA2155 + sourceB2155) sourceC2155) = raw27823 := by
      apply Matrix.ext; unfold doubleCharges sourceA2155 sourceB2155 sourceC2155 raw27823; decide +kernel
    rw [ha]
    exact (canonical27823 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2155 sourceB2155 sourceC2155
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2155, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2156 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2156 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC2156 : Charge := ![1, 1, 0, 1, -2, -1]
def sourceForm2156 : Integer.Sparse Master := [(Sum.inr 1328, 1), (Sum.inr 2822, 1), (Sum.inr 2893, 1), (Sum.inr 2924, 1), (Sum.inr 2925, 1), (Sum.inr 2931, 1), (Sum.inr 4091, -1)]

theorem sourceEq2156 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2156 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2156 + difference 2 0) (sourceB2156 + difference 0 2) sourceC2156) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1328) := by
    have ha : (tripleCharges (sourceA2156 + difference 2 0) (sourceB2156 + difference 0 2) sourceC2156) = raw29813 := by
      apply Matrix.ext; unfold tripleCharges sourceA2156 sourceB2156 sourceC2156 difference raw29813; decide +kernel
    rw [ha]
    exact (canonical29813 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2156 + difference 2 1) (sourceB2156 + difference 1 2) sourceC2156) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2822) := by
    have ha : (tripleCharges (sourceA2156 + difference 2 1) (sourceB2156 + difference 1 2) sourceC2156) = raw29810 := by
      apply Matrix.ext; unfold tripleCharges sourceA2156 sourceB2156 sourceC2156 difference raw29810; decide +kernel
    rw [ha]
    exact (canonical29810 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2156 + difference 2 2) (sourceB2156 + difference 2 2) sourceC2156) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2931) := by
    have ha : (tripleCharges (sourceA2156 + difference 2 2) (sourceB2156 + difference 2 2) sourceC2156) = raw27827 := by
      apply Matrix.ext; unfold tripleCharges sourceA2156 sourceB2156 sourceC2156 difference raw27827; decide +kernel
    rw [ha]
    exact (canonical27827 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2156 + difference 2 3) (sourceB2156 + difference 3 2) sourceC2156) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2893) := by
    have ha : (tripleCharges (sourceA2156 + difference 2 3) (sourceB2156 + difference 3 2) sourceC2156) = raw29814 := by
      apply Matrix.ext; unfold tripleCharges sourceA2156 sourceB2156 sourceC2156 difference raw29814; decide +kernel
    rw [ha]
    exact (canonical29814 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2156 + difference 2 4) (sourceB2156 + difference 4 2) sourceC2156) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2925) := by
    have ha : (tripleCharges (sourceA2156 + difference 2 4) (sourceB2156 + difference 4 2) sourceC2156) = raw29815 := by
      apply Matrix.ext; unfold tripleCharges sourceA2156 sourceB2156 sourceC2156 difference raw29815; decide +kernel
    rw [ha]
    exact (canonical29815 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2156 + difference 2 5) (sourceB2156 + difference 5 2) sourceC2156) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2924) := by
    have ha : (tripleCharges (sourceA2156 + difference 2 5) (sourceB2156 + difference 5 2) sourceC2156) = raw29816 := by
      apply Matrix.ext; unfold tripleCharges sourceA2156 sourceB2156 sourceC2156 difference raw29816; decide +kernel
    rw [ha]
    exact (canonical29816 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2156 + sourceB2156) sourceC2156) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA2156 + sourceB2156) sourceC2156) = raw27823 := by
      apply Matrix.ext; unfold doubleCharges sourceA2156 sourceB2156 sourceC2156 raw27823; decide +kernel
    rw [ha]
    exact (canonical27823 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2156 sourceB2156 sourceC2156
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2156, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2157 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2157 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC2157 : Charge := ![1, 1, 0, 1, -2, -1]
def sourceForm2157 : Integer.Sparse Master := [(Sum.inr 1338, 1), (Sum.inr 2827, 1), (Sum.inr 2900, 1), (Sum.inr 2931, 1), (Sum.inr 2954, 1), (Sum.inr 2955, 1), (Sum.inr 4091, -1)]

theorem sourceEq2157 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2157 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2157 + difference 3 0) (sourceB2157 + difference 0 3) sourceC2157) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1338) := by
    have ha : (tripleCharges (sourceA2157 + difference 3 0) (sourceB2157 + difference 0 3) sourceC2157) = raw29817 := by
      apply Matrix.ext; unfold tripleCharges sourceA2157 sourceB2157 sourceC2157 difference raw29817; decide +kernel
    rw [ha]
    exact (canonical29817 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2157 + difference 3 1) (sourceB2157 + difference 1 3) sourceC2157) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2827) := by
    have ha : (tripleCharges (sourceA2157 + difference 3 1) (sourceB2157 + difference 1 3) sourceC2157) = raw29811 := by
      apply Matrix.ext; unfold tripleCharges sourceA2157 sourceB2157 sourceC2157 difference raw29811; decide +kernel
    rw [ha]
    exact (canonical29811 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2157 + difference 3 2) (sourceB2157 + difference 2 3) sourceC2157) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2900) := by
    have ha : (tripleCharges (sourceA2157 + difference 3 2) (sourceB2157 + difference 2 3) sourceC2157) = raw29818 := by
      apply Matrix.ext; unfold tripleCharges sourceA2157 sourceB2157 sourceC2157 difference raw29818; decide +kernel
    rw [ha]
    exact (canonical29818 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2157 + difference 3 3) (sourceB2157 + difference 3 3) sourceC2157) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2931) := by
    have ha : (tripleCharges (sourceA2157 + difference 3 3) (sourceB2157 + difference 3 3) sourceC2157) = raw27827 := by
      apply Matrix.ext; unfold tripleCharges sourceA2157 sourceB2157 sourceC2157 difference raw27827; decide +kernel
    rw [ha]
    exact (canonical27827 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2157 + difference 3 4) (sourceB2157 + difference 4 3) sourceC2157) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2955) := by
    have ha : (tripleCharges (sourceA2157 + difference 3 4) (sourceB2157 + difference 4 3) sourceC2157) = raw29819 := by
      apply Matrix.ext; unfold tripleCharges sourceA2157 sourceB2157 sourceC2157 difference raw29819; decide +kernel
    rw [ha]
    exact (canonical29819 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2157 + difference 3 5) (sourceB2157 + difference 5 3) sourceC2157) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2954) := by
    have ha : (tripleCharges (sourceA2157 + difference 3 5) (sourceB2157 + difference 5 3) sourceC2157) = raw29820 := by
      apply Matrix.ext; unfold tripleCharges sourceA2157 sourceB2157 sourceC2157 difference raw29820; decide +kernel
    rw [ha]
    exact (canonical29820 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2157 + sourceB2157) sourceC2157) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA2157 + sourceB2157) sourceC2157) = raw27823 := by
      apply Matrix.ext; unfold doubleCharges sourceA2157 sourceB2157 sourceC2157 raw27823; decide +kernel
    rw [ha]
    exact (canonical27823 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2157 sourceB2157 sourceC2157
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2157, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2158 : Charge := ![1, 1, 0, 1, -2, -1]
def sourceB2158 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC2158 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceForm2158 : Integer.Sparse Master := [(Sum.inr 4795, 1), (Sum.inr 4810, 1), (Sum.inr 4811, 1), (Sum.inr 4821, 1), (Sum.inr 4856, 1), (Sum.inr 5011, 1), (Sum.inr 5014, 1), (Sum.inr 5016, 1), (Sum.inr 5019, 1), (Sum.inr 5050, 1), (Sum.inr 5063, 1), (Sum.inr 5067, 1), (Sum.inr 5080, 1), (Sum.inr 5081, 1), (Sum.inr 5090, 1), (Sum.inr 5111, 1), (Sum.inr 5129, 1), (Sum.inr 5130, 1), (Sum.inr 5131, 1), (Sum.inr 5141, 1), (Sum.inr 5142, 1), (Sum.inr 5151, 1), (Sum.inr 5152, 2), (Sum.inr 5156, 1), (Sum.inr 5176, 1), (Sum.inr 5177, 1), (Sum.inr 5182, 1), (Sum.inr 5193, 1), (Sum.inr 5207, 1)]

theorem sourceEq2158 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2158 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2158 + difference 0 1) (sourceB2158 + difference 1 0) sourceC2158) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA2158 + difference 0 1) (sourceB2158 + difference 1 0) sourceC2158) = raw29821 := by
      apply Matrix.ext; unfold tripleCharges sourceA2158 sourceB2158 sourceC2158 difference raw29821; decide +kernel
    rw [ha]
    exact (canonical29821 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2158 + difference 0 2) (sourceB2158 + difference 2 0) sourceC2158) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5050) := by
    have ha : (tripleCharges (sourceA2158 + difference 0 2) (sourceB2158 + difference 2 0) sourceC2158) = raw29822 := by
      apply Matrix.ext; unfold tripleCharges sourceA2158 sourceB2158 sourceC2158 difference raw29822; decide +kernel
    rw [ha]
    exact (canonical29822 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2158 + difference 0 3) (sourceB2158 + difference 3 0) sourceC2158) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5111) := by
    have ha : (tripleCharges (sourceA2158 + difference 0 3) (sourceB2158 + difference 3 0) sourceC2158) = raw29566 := by
      apply Matrix.ext; unfold tripleCharges sourceA2158 sourceB2158 sourceC2158 difference raw29566; decide +kernel
    rw [ha]
    exact (canonical29566 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2158 + difference 0 4) (sourceB2158 + difference 4 0) sourceC2158) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5014) := by
    have ha : (tripleCharges (sourceA2158 + difference 0 4) (sourceB2158 + difference 4 0) sourceC2158) = raw29823 := by
      apply Matrix.ext; unfold tripleCharges sourceA2158 sourceB2158 sourceC2158 difference raw29823; decide +kernel
    rw [ha]
    exact (canonical29823 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2158 + difference 0 5) (sourceB2158 + difference 5 0) sourceC2158) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5063) := by
    have ha : (tripleCharges (sourceA2158 + difference 0 5) (sourceB2158 + difference 5 0) sourceC2158) = raw29824 := by
      apply Matrix.ext; unfold tripleCharges sourceA2158 sourceB2158 sourceC2158 difference raw29824; decide +kernel
    rw [ha]
    exact (canonical29824 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2158 + difference 1 0) (sourceB2158 + difference 0 1) sourceC2158) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4856) := by
    have ha : (tripleCharges (sourceA2158 + difference 1 0) (sourceB2158 + difference 0 1) sourceC2158) = raw29825 := by
      apply Matrix.ext; unfold tripleCharges sourceA2158 sourceB2158 sourceC2158 difference raw29825; decide +kernel
    rw [ha]
    exact (canonical29825 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2158 + difference 1 2) (sourceB2158 + difference 2 1) sourceC2158) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5182) := by
    have ha : (tripleCharges (sourceA2158 + difference 1 2) (sourceB2158 + difference 2 1) sourceC2158) = raw29826 := by
      apply Matrix.ext; unfold tripleCharges sourceA2158 sourceB2158 sourceC2158 difference raw29826; decide +kernel
    rw [ha]
    exact (canonical29826 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2158 + difference 1 3) (sourceB2158 + difference 3 1) sourceC2158) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5207) := by
    have ha : (tripleCharges (sourceA2158 + difference 1 3) (sourceB2158 + difference 3 1) sourceC2158) = raw29571 := by
      apply Matrix.ext; unfold tripleCharges sourceA2158 sourceB2158 sourceC2158 difference raw29571; decide +kernel
    rw [ha]
    exact (canonical29571 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2158 + difference 1 4) (sourceB2158 + difference 4 1) sourceC2158) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5016) := by
    have ha : (tripleCharges (sourceA2158 + difference 1 4) (sourceB2158 + difference 4 1) sourceC2158) = raw29827 := by
      apply Matrix.ext; unfold tripleCharges sourceA2158 sourceB2158 sourceC2158 difference raw29827; decide +kernel
    rw [ha]
    exact (canonical29827 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2158 + difference 1 5) (sourceB2158 + difference 5 1) sourceC2158) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5193) := by
    have ha : (tripleCharges (sourceA2158 + difference 1 5) (sourceB2158 + difference 5 1) sourceC2158) = raw29828 := by
      apply Matrix.ext; unfold tripleCharges sourceA2158 sourceB2158 sourceC2158 difference raw29828; decide +kernel
    rw [ha]
    exact (canonical29828 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2158 + difference 2 0) (sourceB2158 + difference 0 2) sourceC2158) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4795) := by
    have ha : (tripleCharges (sourceA2158 + difference 2 0) (sourceB2158 + difference 0 2) sourceC2158) = raw29829 := by
      apply Matrix.ext; unfold tripleCharges sourceA2158 sourceB2158 sourceC2158 difference raw29829; decide +kernel
    rw [ha]
    exact (canonical29829 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2158 + difference 2 1) (sourceB2158 + difference 1 2) sourceC2158) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5067) := by
    have ha : (tripleCharges (sourceA2158 + difference 2 1) (sourceB2158 + difference 1 2) sourceC2158) = raw29830 := by
      apply Matrix.ext; unfold tripleCharges sourceA2158 sourceB2158 sourceC2158 difference raw29830; decide +kernel
    rw [ha]
    exact (canonical29830 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2158 + difference 2 3) (sourceB2158 + difference 3 2) sourceC2158) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5152) := by
    have ha : (tripleCharges (sourceA2158 + difference 2 3) (sourceB2158 + difference 3 2) sourceC2158) = raw29576 := by
      apply Matrix.ext; unfold tripleCharges sourceA2158 sourceB2158 sourceC2158 difference raw29576; decide +kernel
    rw [ha]
    exact (canonical29576 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2158 + difference 2 4) (sourceB2158 + difference 4 2) sourceC2158) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5011) := by
    have ha : (tripleCharges (sourceA2158 + difference 2 4) (sourceB2158 + difference 4 2) sourceC2158) = raw29831 := by
      apply Matrix.ext; unfold tripleCharges sourceA2158 sourceB2158 sourceC2158 difference raw29831; decide +kernel
    rw [ha]
    exact (canonical29831 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2158 + difference 2 5) (sourceB2158 + difference 5 2) sourceC2158) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5142) := by
    have ha : (tripleCharges (sourceA2158 + difference 2 5) (sourceB2158 + difference 5 2) sourceC2158) = raw29832 := by
      apply Matrix.ext; unfold tripleCharges sourceA2158 sourceB2158 sourceC2158 difference raw29832; decide +kernel
    rw [ha]
    exact (canonical29832 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2158 + difference 3 0) (sourceB2158 + difference 0 3) sourceC2158) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4821) := by
    have ha : (tripleCharges (sourceA2158 + difference 3 0) (sourceB2158 + difference 0 3) sourceC2158) = raw29833 := by
      apply Matrix.ext; unfold tripleCharges sourceA2158 sourceB2158 sourceC2158 difference raw29833; decide +kernel
    rw [ha]
    exact (canonical29833 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2158 + difference 3 1) (sourceB2158 + difference 1 3) sourceC2158) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5090) := by
    have ha : (tripleCharges (sourceA2158 + difference 3 1) (sourceB2158 + difference 1 3) sourceC2158) = raw29834 := by
      apply Matrix.ext; unfold tripleCharges sourceA2158 sourceB2158 sourceC2158 difference raw29834; decide +kernel
    rw [ha]
    exact (canonical29834 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2158 + difference 3 2) (sourceB2158 + difference 2 3) sourceC2158) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5131) := by
    have ha : (tripleCharges (sourceA2158 + difference 3 2) (sourceB2158 + difference 2 3) sourceC2158) = raw29835 := by
      apply Matrix.ext; unfold tripleCharges sourceA2158 sourceB2158 sourceC2158 difference raw29835; decide +kernel
    rw [ha]
    exact (canonical29835 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2158 + difference 3 4) (sourceB2158 + difference 4 3) sourceC2158) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5019) := by
    have ha : (tripleCharges (sourceA2158 + difference 3 4) (sourceB2158 + difference 4 3) sourceC2158) = raw29836 := by
      apply Matrix.ext; unfold tripleCharges sourceA2158 sourceB2158 sourceC2158 difference raw29836; decide +kernel
    rw [ha]
    exact (canonical29836 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2158 + difference 3 5) (sourceB2158 + difference 5 3) sourceC2158) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5156) := by
    have ha : (tripleCharges (sourceA2158 + difference 3 5) (sourceB2158 + difference 5 3) sourceC2158) = raw29837 := by
      apply Matrix.ext; unfold tripleCharges sourceA2158 sourceB2158 sourceC2158 difference raw29837; decide +kernel
    rw [ha]
    exact (canonical29837 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2158 + difference 4 0) (sourceB2158 + difference 0 4) sourceC2158) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4811) := by
    have ha : (tripleCharges (sourceA2158 + difference 4 0) (sourceB2158 + difference 0 4) sourceC2158) = raw29686 := by
      apply Matrix.ext; unfold tripleCharges sourceA2158 sourceB2158 sourceC2158 difference raw29686; decide +kernel
    rw [ha]
    exact (canonical29686 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2158 + difference 4 1) (sourceB2158 + difference 1 4) sourceC2158) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5081) := by
    have ha : (tripleCharges (sourceA2158 + difference 4 1) (sourceB2158 + difference 1 4) sourceC2158) = raw29687 := by
      apply Matrix.ext; unfold tripleCharges sourceA2158 sourceB2158 sourceC2158 difference raw29687; decide +kernel
    rw [ha]
    exact (canonical29687 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2158 + difference 4 2) (sourceB2158 + difference 2 4) sourceC2158) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5130) := by
    have ha : (tripleCharges (sourceA2158 + difference 4 2) (sourceB2158 + difference 2 4) sourceC2158) = raw29688 := by
      apply Matrix.ext; unfold tripleCharges sourceA2158 sourceB2158 sourceC2158 difference raw29688; decide +kernel
    rw [ha]
    exact (canonical29688 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2158 + difference 4 3) (sourceB2158 + difference 3 4) sourceC2158) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5177) := by
    have ha : (tripleCharges (sourceA2158 + difference 4 3) (sourceB2158 + difference 3 4) sourceC2158) = raw29586 := by
      apply Matrix.ext; unfold tripleCharges sourceA2158 sourceB2158 sourceC2158 difference raw29586; decide +kernel
    rw [ha]
    exact (canonical29586 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2158 + difference 4 5) (sourceB2158 + difference 5 4) sourceC2158) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5152) := by
    have ha : (tripleCharges (sourceA2158 + difference 4 5) (sourceB2158 + difference 5 4) sourceC2158) = raw29689 := by
      apply Matrix.ext; unfold tripleCharges sourceA2158 sourceB2158 sourceC2158 difference raw29689; decide +kernel
    rw [ha]
    exact (canonical29689 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2158 + difference 5 0) (sourceB2158 + difference 0 5) sourceC2158) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4810) := by
    have ha : (tripleCharges (sourceA2158 + difference 5 0) (sourceB2158 + difference 0 5) sourceC2158) = raw29577 := by
      apply Matrix.ext; unfold tripleCharges sourceA2158 sourceB2158 sourceC2158 difference raw29577; decide +kernel
    rw [ha]
    exact (canonical29577 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2158 + difference 5 1) (sourceB2158 + difference 1 5) sourceC2158) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5080) := by
    have ha : (tripleCharges (sourceA2158 + difference 5 1) (sourceB2158 + difference 1 5) sourceC2158) = raw29578 := by
      apply Matrix.ext; unfold tripleCharges sourceA2158 sourceB2158 sourceC2158 difference raw29578; decide +kernel
    rw [ha]
    exact (canonical29578 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2158 + difference 5 2) (sourceB2158 + difference 2 5) sourceC2158) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5129) := by
    have ha : (tripleCharges (sourceA2158 + difference 5 2) (sourceB2158 + difference 2 5) sourceC2158) = raw29579 := by
      apply Matrix.ext; unfold tripleCharges sourceA2158 sourceB2158 sourceC2158 difference raw29579; decide +kernel
    rw [ha]
    exact (canonical29579 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2158 + difference 5 3) (sourceB2158 + difference 3 5) sourceC2158) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5176) := by
    have ha : (tripleCharges (sourceA2158 + difference 5 3) (sourceB2158 + difference 3 5) sourceC2158) = raw29695 := by
      apply Matrix.ext; unfold tripleCharges sourceA2158 sourceB2158 sourceC2158 difference raw29695; decide +kernel
    rw [ha]
    exact (canonical29695 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2158 + difference 5 4) (sourceB2158 + difference 4 5) sourceC2158) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5151) := by
    have ha : (tripleCharges (sourceA2158 + difference 5 4) (sourceB2158 + difference 4 5) sourceC2158) = raw29580 := by
      apply Matrix.ext; unfold tripleCharges sourceA2158 sourceB2158 sourceC2158 difference raw29580; decide +kernel
    rw [ha]
    exact (canonical29580 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2158 sourceB2158 sourceC2158
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2158, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2159 : Charge := ![1, 1, 0, 1, -2, -1]
def sourceB2159 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC2159 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceForm2159 : Integer.Sparse Master := [(Sum.inr 2452, 1), (Sum.inr 2467, 1), (Sum.inr 2468, 1), (Sum.inr 2523, 1), (Sum.inr 2561, 1), (Sum.inr 2850, 1), (Sum.inr 2855, 1), (Sum.inr 2856, 1), (Sum.inr 2889, 1), (Sum.inr 2905, 1), (Sum.inr 2910, 1), (Sum.inr 2911, 1), (Sum.inr 2912, 1), (Sum.inr 2913, 1), (Sum.inr 2916, 1), (Sum.inr 2917, 1), (Sum.inr 2930, 1), (Sum.inr 2931, 2), (Sum.inr 2968, 1), (Sum.inr 2969, 1), (Sum.inr 2979, 1), (Sum.inr 2981, 1), (Sum.inr 2990, 1), (Sum.inr 2991, 1), (Sum.inr 3174, 1), (Sum.inr 3198, 1), (Sum.inr 3199, 1), (Sum.inr 3206, 1), (Sum.inr 3207, 1)]

theorem sourceEq2159 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2159 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2159 + difference 0 1) (sourceB2159 + difference 1 0) sourceC2159) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2561) := by
    have ha : (tripleCharges (sourceA2159 + difference 0 1) (sourceB2159 + difference 1 0) sourceC2159) = raw29838 := by
      apply Matrix.ext; unfold tripleCharges sourceA2159 sourceB2159 sourceC2159 difference raw29838; decide +kernel
    rw [ha]
    exact (canonical29838 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2159 + difference 0 2) (sourceB2159 + difference 2 0) sourceC2159) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2452) := by
    have ha : (tripleCharges (sourceA2159 + difference 0 2) (sourceB2159 + difference 2 0) sourceC2159) = raw29839 := by
      apply Matrix.ext; unfold tripleCharges sourceA2159 sourceB2159 sourceC2159 difference raw29839; decide +kernel
    rw [ha]
    exact (canonical29839 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2159 + difference 0 3) (sourceB2159 + difference 3 0) sourceC2159) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2523) := by
    have ha : (tripleCharges (sourceA2159 + difference 0 3) (sourceB2159 + difference 3 0) sourceC2159) = raw29596 := by
      apply Matrix.ext; unfold tripleCharges sourceA2159 sourceB2159 sourceC2159 difference raw29596; decide +kernel
    rw [ha]
    exact (canonical29596 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2159 + difference 0 4) (sourceB2159 + difference 4 0) sourceC2159) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2467) := by
    have ha : (tripleCharges (sourceA2159 + difference 0 4) (sourceB2159 + difference 4 0) sourceC2159) = raw29840 := by
      apply Matrix.ext; unfold tripleCharges sourceA2159 sourceB2159 sourceC2159 difference raw29840; decide +kernel
    rw [ha]
    exact (canonical29840 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2159 + difference 0 5) (sourceB2159 + difference 5 0) sourceC2159) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2468) := by
    have ha : (tripleCharges (sourceA2159 + difference 0 5) (sourceB2159 + difference 5 0) sourceC2159) = raw29841 := by
      apply Matrix.ext; unfold tripleCharges sourceA2159 sourceB2159 sourceC2159 difference raw29841; decide +kernel
    rw [ha]
    exact (canonical29841 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2159 + difference 1 0) (sourceB2159 + difference 0 1) sourceC2159) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3174) := by
    have ha : (tripleCharges (sourceA2159 + difference 1 0) (sourceB2159 + difference 0 1) sourceC2159) = raw29842 := by
      apply Matrix.ext; unfold tripleCharges sourceA2159 sourceB2159 sourceC2159 difference raw29842; decide +kernel
    rw [ha]
    exact (canonical29842 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2159 + difference 1 2) (sourceB2159 + difference 2 1) sourceC2159) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2850) := by
    have ha : (tripleCharges (sourceA2159 + difference 1 2) (sourceB2159 + difference 2 1) sourceC2159) = raw29843 := by
      apply Matrix.ext; unfold tripleCharges sourceA2159 sourceB2159 sourceC2159 difference raw29843; decide +kernel
    rw [ha]
    exact (canonical29843 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2159 + difference 1 3) (sourceB2159 + difference 3 1) sourceC2159) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2889) := by
    have ha : (tripleCharges (sourceA2159 + difference 1 3) (sourceB2159 + difference 3 1) sourceC2159) = raw29601 := by
      apply Matrix.ext; unfold tripleCharges sourceA2159 sourceB2159 sourceC2159 difference raw29601; decide +kernel
    rw [ha]
    exact (canonical29601 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2159 + difference 1 4) (sourceB2159 + difference 4 1) sourceC2159) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2855) := by
    have ha : (tripleCharges (sourceA2159 + difference 1 4) (sourceB2159 + difference 4 1) sourceC2159) = raw29844 := by
      apply Matrix.ext; unfold tripleCharges sourceA2159 sourceB2159 sourceC2159 difference raw29844; decide +kernel
    rw [ha]
    exact (canonical29844 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2159 + difference 1 5) (sourceB2159 + difference 5 1) sourceC2159) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2856) := by
    have ha : (tripleCharges (sourceA2159 + difference 1 5) (sourceB2159 + difference 5 1) sourceC2159) = raw29845 := by
      apply Matrix.ext; unfold tripleCharges sourceA2159 sourceB2159 sourceC2159 difference raw29845; decide +kernel
    rw [ha]
    exact (canonical29845 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2159 + difference 2 0) (sourceB2159 + difference 0 2) sourceC2159) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3199) := by
    have ha : (tripleCharges (sourceA2159 + difference 2 0) (sourceB2159 + difference 0 2) sourceC2159) = raw29846 := by
      apply Matrix.ext; unfold tripleCharges sourceA2159 sourceB2159 sourceC2159 difference raw29846; decide +kernel
    rw [ha]
    exact (canonical29846 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2159 + difference 2 1) (sourceB2159 + difference 1 2) sourceC2159) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2981) := by
    have ha : (tripleCharges (sourceA2159 + difference 2 1) (sourceB2159 + difference 1 2) sourceC2159) = raw29847 := by
      apply Matrix.ext; unfold tripleCharges sourceA2159 sourceB2159 sourceC2159 difference raw29847; decide +kernel
    rw [ha]
    exact (canonical29847 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2159 + difference 2 3) (sourceB2159 + difference 3 2) sourceC2159) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2931) := by
    have ha : (tripleCharges (sourceA2159 + difference 2 3) (sourceB2159 + difference 3 2) sourceC2159) = raw29606 := by
      apply Matrix.ext; unfold tripleCharges sourceA2159 sourceB2159 sourceC2159 difference raw29606; decide +kernel
    rw [ha]
    exact (canonical29606 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2159 + difference 2 4) (sourceB2159 + difference 4 2) sourceC2159) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2912) := by
    have ha : (tripleCharges (sourceA2159 + difference 2 4) (sourceB2159 + difference 4 2) sourceC2159) = raw29848 := by
      apply Matrix.ext; unfold tripleCharges sourceA2159 sourceB2159 sourceC2159 difference raw29848; decide +kernel
    rw [ha]
    exact (canonical29848 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2159 + difference 2 5) (sourceB2159 + difference 5 2) sourceC2159) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2913) := by
    have ha : (tripleCharges (sourceA2159 + difference 2 5) (sourceB2159 + difference 5 2) sourceC2159) = raw29849 := by
      apply Matrix.ext; unfold tripleCharges sourceA2159 sourceB2159 sourceC2159 difference raw29849; decide +kernel
    rw [ha]
    exact (canonical29849 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2159 + difference 3 0) (sourceB2159 + difference 0 3) sourceC2159) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3198) := by
    have ha : (tripleCharges (sourceA2159 + difference 3 0) (sourceB2159 + difference 0 3) sourceC2159) = raw29850 := by
      apply Matrix.ext; unfold tripleCharges sourceA2159 sourceB2159 sourceC2159 difference raw29850; decide +kernel
    rw [ha]
    exact (canonical29850 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2159 + difference 3 1) (sourceB2159 + difference 1 3) sourceC2159) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2979) := by
    have ha : (tripleCharges (sourceA2159 + difference 3 1) (sourceB2159 + difference 1 3) sourceC2159) = raw29851 := by
      apply Matrix.ext; unfold tripleCharges sourceA2159 sourceB2159 sourceC2159 difference raw29851; decide +kernel
    rw [ha]
    exact (canonical29851 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2159 + difference 3 2) (sourceB2159 + difference 2 3) sourceC2159) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2905) := by
    have ha : (tripleCharges (sourceA2159 + difference 3 2) (sourceB2159 + difference 2 3) sourceC2159) = raw29852 := by
      apply Matrix.ext; unfold tripleCharges sourceA2159 sourceB2159 sourceC2159 difference raw29852; decide +kernel
    rw [ha]
    exact (canonical29852 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2159 + difference 3 4) (sourceB2159 + difference 4 3) sourceC2159) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2910) := by
    have ha : (tripleCharges (sourceA2159 + difference 3 4) (sourceB2159 + difference 4 3) sourceC2159) = raw29853 := by
      apply Matrix.ext; unfold tripleCharges sourceA2159 sourceB2159 sourceC2159 difference raw29853; decide +kernel
    rw [ha]
    exact (canonical29853 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2159 + difference 3 5) (sourceB2159 + difference 5 3) sourceC2159) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2911) := by
    have ha : (tripleCharges (sourceA2159 + difference 3 5) (sourceB2159 + difference 5 3) sourceC2159) = raw29854 := by
      apply Matrix.ext; unfold tripleCharges sourceA2159 sourceB2159 sourceC2159 difference raw29854; decide +kernel
    rw [ha]
    exact (canonical29854 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2159 + difference 4 0) (sourceB2159 + difference 0 4) sourceC2159) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3207) := by
    have ha : (tripleCharges (sourceA2159 + difference 4 0) (sourceB2159 + difference 0 4) sourceC2159) = raw29855 := by
      apply Matrix.ext; unfold tripleCharges sourceA2159 sourceB2159 sourceC2159 difference raw29855; decide +kernel
    rw [ha]
    exact (canonical29855 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2159 + difference 4 1) (sourceB2159 + difference 1 4) sourceC2159) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2991) := by
    have ha : (tripleCharges (sourceA2159 + difference 4 1) (sourceB2159 + difference 1 4) sourceC2159) = raw29856 := by
      apply Matrix.ext; unfold tripleCharges sourceA2159 sourceB2159 sourceC2159 difference raw29856; decide +kernel
    rw [ha]
    exact (canonical29856 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2159 + difference 4 2) (sourceB2159 + difference 2 4) sourceC2159) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2917) := by
    have ha : (tripleCharges (sourceA2159 + difference 4 2) (sourceB2159 + difference 2 4) sourceC2159) = raw29857 := by
      apply Matrix.ext; unfold tripleCharges sourceA2159 sourceB2159 sourceC2159 difference raw29857; decide +kernel
    rw [ha]
    exact (canonical29857 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2159 + difference 4 3) (sourceB2159 + difference 3 4) sourceC2159) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2969) := by
    have ha : (tripleCharges (sourceA2159 + difference 4 3) (sourceB2159 + difference 3 4) sourceC2159) = raw29616 := by
      apply Matrix.ext; unfold tripleCharges sourceA2159 sourceB2159 sourceC2159 difference raw29616; decide +kernel
    rw [ha]
    exact (canonical29616 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2159 + difference 4 5) (sourceB2159 + difference 5 4) sourceC2159) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2931) := by
    have ha : (tripleCharges (sourceA2159 + difference 4 5) (sourceB2159 + difference 5 4) sourceC2159) = raw29858 := by
      apply Matrix.ext; unfold tripleCharges sourceA2159 sourceB2159 sourceC2159 difference raw29858; decide +kernel
    rw [ha]
    exact (canonical29858 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2159 + difference 5 0) (sourceB2159 + difference 0 5) sourceC2159) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3206) := by
    have ha : (tripleCharges (sourceA2159 + difference 5 0) (sourceB2159 + difference 0 5) sourceC2159) = raw29607 := by
      apply Matrix.ext; unfold tripleCharges sourceA2159 sourceB2159 sourceC2159 difference raw29607; decide +kernel
    rw [ha]
    exact (canonical29607 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2159 + difference 5 1) (sourceB2159 + difference 1 5) sourceC2159) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2990) := by
    have ha : (tripleCharges (sourceA2159 + difference 5 1) (sourceB2159 + difference 1 5) sourceC2159) = raw29608 := by
      apply Matrix.ext; unfold tripleCharges sourceA2159 sourceB2159 sourceC2159 difference raw29608; decide +kernel
    rw [ha]
    exact (canonical29608 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2159 + difference 5 2) (sourceB2159 + difference 2 5) sourceC2159) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2916) := by
    have ha : (tripleCharges (sourceA2159 + difference 5 2) (sourceB2159 + difference 2 5) sourceC2159) = raw29609 := by
      apply Matrix.ext; unfold tripleCharges sourceA2159 sourceB2159 sourceC2159 difference raw29609; decide +kernel
    rw [ha]
    exact (canonical29609 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2159 + difference 5 3) (sourceB2159 + difference 3 5) sourceC2159) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2968) := by
    have ha : (tripleCharges (sourceA2159 + difference 5 3) (sourceB2159 + difference 3 5) sourceC2159) = raw29859 := by
      apply Matrix.ext; unfold tripleCharges sourceA2159 sourceB2159 sourceC2159 difference raw29859; decide +kernel
    rw [ha]
    exact (canonical29859 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2159 + difference 5 4) (sourceB2159 + difference 4 5) sourceC2159) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2930) := by
    have ha : (tripleCharges (sourceA2159 + difference 5 4) (sourceB2159 + difference 4 5) sourceC2159) = raw29610 := by
      apply Matrix.ext; unfold tripleCharges sourceA2159 sourceB2159 sourceC2159 difference raw29610; decide +kernel
    rw [ha]
    exact (canonical29610 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2159 sourceB2159 sourceC2159
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2159, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2160 : Charge := ![1, 1, 0, 1, -2, -1]
def sourceB2160 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceC2160 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceForm2160 : Integer.Sparse Master := [(Sum.inr 2399, 1), (Sum.inr 3433, 1), (Sum.inr 3439, 1), (Sum.inr 3485, 1), (Sum.inr 3522, 1), (Sum.inr 3612, 1), (Sum.inr 4082, -1)]

theorem sourceEq2160 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2160 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2160 + difference 0 0) (sourceB2160 + difference 0 0) sourceC2160) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3612) := by
    have ha : (tripleCharges (sourceA2160 + difference 0 0) (sourceB2160 + difference 0 0) sourceC2160) = raw29313 := by
      apply Matrix.ext; unfold tripleCharges sourceA2160 sourceB2160 sourceC2160 difference raw29313; decide +kernel
    rw [ha]
    exact (canonical29313 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2160 + difference 0 1) (sourceB2160 + difference 1 0) sourceC2160) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3522) := by
    have ha : (tripleCharges (sourceA2160 + difference 0 1) (sourceB2160 + difference 1 0) sourceC2160) = raw29391 := by
      apply Matrix.ext; unfold tripleCharges sourceA2160 sourceB2160 sourceC2160 difference raw29391; decide +kernel
    rw [ha]
    exact (canonical29391 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2160 + difference 0 2) (sourceB2160 + difference 2 0) sourceC2160) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3433) := by
    have ha : (tripleCharges (sourceA2160 + difference 0 2) (sourceB2160 + difference 2 0) sourceC2160) = raw29476 := by
      apply Matrix.ext; unfold tripleCharges sourceA2160 sourceB2160 sourceC2160 difference raw29476; decide +kernel
    rw [ha]
    exact (canonical29476 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2160 + difference 0 3) (sourceB2160 + difference 3 0) sourceC2160) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3485) := by
    have ha : (tripleCharges (sourceA2160 + difference 0 3) (sourceB2160 + difference 3 0) sourceC2160) = raw29698 := by
      apply Matrix.ext; unfold tripleCharges sourceA2160 sourceB2160 sourceC2160 difference raw29698; decide +kernel
    rw [ha]
    exact (canonical29698 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2160 + difference 0 4) (sourceB2160 + difference 4 0) sourceC2160) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2399) := by
    have ha : (tripleCharges (sourceA2160 + difference 0 4) (sourceB2160 + difference 4 0) sourceC2160) = raw29712 := by
      apply Matrix.ext; unfold tripleCharges sourceA2160 sourceB2160 sourceC2160 difference raw29712; decide +kernel
    rw [ha]
    exact (canonical29712 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2160 + difference 0 5) (sourceB2160 + difference 5 0) sourceC2160) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3439) := by
    have ha : (tripleCharges (sourceA2160 + difference 0 5) (sourceB2160 + difference 5 0) sourceC2160) = raw29860 := by
      apply Matrix.ext; unfold tripleCharges sourceA2160 sourceB2160 sourceC2160 difference raw29860; decide +kernel
    rw [ha]
    exact (canonical29860 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2160 + sourceB2160) sourceC2160) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2160 + sourceB2160) sourceC2160) = raw29319 := by
      apply Matrix.ext; unfold doubleCharges sourceA2160 sourceB2160 sourceC2160 raw29319; decide +kernel
    rw [ha]
    exact (canonical29319 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2160 sourceB2160 sourceC2160
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2160, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2161 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2161 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC2161 : Charge := ![1, 1, 0, 2, -3, -1]
def sourceForm2161 : Integer.Sparse Master := [(Sum.inr 2910, 1), (Sum.inr 3346, 1), (Sum.inr 3349, 1), (Sum.inr 3357, 1), (Sum.inr 3479, 1), (Sum.inr 3570, 1), (Sum.inr 4080, -1)]

theorem sourceEq2161 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2161 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2161 + difference 0 0) (sourceB2161 + difference 0 0) sourceC2161) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2910) := by
    have ha : (tripleCharges (sourceA2161 + difference 0 0) (sourceB2161 + difference 0 0) sourceC2161) = raw29861 := by
      apply Matrix.ext; unfold tripleCharges sourceA2161 sourceB2161 sourceC2161 difference raw29861; decide +kernel
    rw [ha]
    exact (canonical29861 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2161 + difference 0 1) (sourceB2161 + difference 1 0) sourceC2161) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3349) := by
    have ha : (tripleCharges (sourceA2161 + difference 0 1) (sourceB2161 + difference 1 0) sourceC2161) = raw29862 := by
      apply Matrix.ext; unfold tripleCharges sourceA2161 sourceB2161 sourceC2161 difference raw29862; decide +kernel
    rw [ha]
    exact (canonical29862 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2161 + difference 0 2) (sourceB2161 + difference 2 0) sourceC2161) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3346) := by
    have ha : (tripleCharges (sourceA2161 + difference 0 2) (sourceB2161 + difference 2 0) sourceC2161) = raw29863 := by
      apply Matrix.ext; unfold tripleCharges sourceA2161 sourceB2161 sourceC2161 difference raw29863; decide +kernel
    rw [ha]
    exact (canonical29863 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2161 + difference 0 3) (sourceB2161 + difference 3 0) sourceC2161) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3357) := by
    have ha : (tripleCharges (sourceA2161 + difference 0 3) (sourceB2161 + difference 3 0) sourceC2161) = raw29864 := by
      apply Matrix.ext; unfold tripleCharges sourceA2161 sourceB2161 sourceC2161 difference raw29864; decide +kernel
    rw [ha]
    exact (canonical29864 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2161 + difference 0 4) (sourceB2161 + difference 4 0) sourceC2161) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3570) := by
    have ha : (tripleCharges (sourceA2161 + difference 0 4) (sourceB2161 + difference 4 0) sourceC2161) = raw29865 := by
      apply Matrix.ext; unfold tripleCharges sourceA2161 sourceB2161 sourceC2161 difference raw29865; decide +kernel
    rw [ha]
    exact (canonical29865 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2161 + difference 0 5) (sourceB2161 + difference 5 0) sourceC2161) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3479) := by
    have ha : (tripleCharges (sourceA2161 + difference 0 5) (sourceB2161 + difference 5 0) sourceC2161) = raw29866 := by
      apply Matrix.ext; unfold tripleCharges sourceA2161 sourceB2161 sourceC2161 difference raw29866; decide +kernel
    rw [ha]
    exact (canonical29866 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2161 + sourceB2161) sourceC2161) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA2161 + sourceB2161) sourceC2161) = raw29867 := by
      apply Matrix.ext; unfold doubleCharges sourceA2161 sourceB2161 sourceC2161 raw29867; decide +kernel
    rw [ha]
    exact (canonical29867 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2161 sourceB2161 sourceC2161
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2161, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2162 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2162 : Charge := ![2, 0, 0, -2, 0, 0]
def sourceC2162 : Charge := ![1, 1, 0, 2, -2, -2]
def sourceForm2162 : Integer.Sparse Master := [(Sum.inr 2310, 2), (Sum.inr 2844, 1), (Sum.inr 2856, 1), (Sum.inr 2911, 1), (Sum.inr 3665, 1), (Sum.inr 4088, -1)]

theorem sourceEq2162 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2162 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2162 + difference 0 3) (sourceB2162 + difference 3 0) sourceC2162) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3665) := by
    have ha : (tripleCharges (sourceA2162 + difference 0 3) (sourceB2162 + difference 3 0) sourceC2162) = raw29868 := by
      apply Matrix.ext; unfold tripleCharges sourceA2162 sourceB2162 sourceC2162 difference raw29868; decide +kernel
    rw [ha]
    exact (canonical29868 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2162 + difference 1 3) (sourceB2162 + difference 3 1) sourceC2162) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2856) := by
    have ha : (tripleCharges (sourceA2162 + difference 1 3) (sourceB2162 + difference 3 1) sourceC2162) = raw29869 := by
      apply Matrix.ext; unfold tripleCharges sourceA2162 sourceB2162 sourceC2162 difference raw29869; decide +kernel
    rw [ha]
    exact (canonical29869 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2162 + difference 2 3) (sourceB2162 + difference 3 2) sourceC2162) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2844) := by
    have ha : (tripleCharges (sourceA2162 + difference 2 3) (sourceB2162 + difference 3 2) sourceC2162) = raw29870 := by
      apply Matrix.ext; unfold tripleCharges sourceA2162 sourceB2162 sourceC2162 difference raw29870; decide +kernel
    rw [ha]
    exact (canonical29870 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2162 + difference 3 3) (sourceB2162 + difference 3 3) sourceC2162) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2911) := by
    have ha : (tripleCharges (sourceA2162 + difference 3 3) (sourceB2162 + difference 3 3) sourceC2162) = raw28178 := by
      apply Matrix.ext; unfold tripleCharges sourceA2162 sourceB2162 sourceC2162 difference raw28178; decide +kernel
    rw [ha]
    exact (canonical28178 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2162 + difference 4 3) (sourceB2162 + difference 3 4) sourceC2162) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2310) := by
    have ha : (tripleCharges (sourceA2162 + difference 4 3) (sourceB2162 + difference 3 4) sourceC2162) = raw29871 := by
      apply Matrix.ext; unfold tripleCharges sourceA2162 sourceB2162 sourceC2162 difference raw29871; decide +kernel
    rw [ha]
    exact (canonical29871 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2162 + difference 5 3) (sourceB2162 + difference 3 5) sourceC2162) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2310) := by
    have ha : (tripleCharges (sourceA2162 + difference 5 3) (sourceB2162 + difference 3 5) sourceC2162) = raw29872 := by
      apply Matrix.ext; unfold tripleCharges sourceA2162 sourceB2162 sourceC2162 difference raw29872; decide +kernel
    rw [ha]
    exact (canonical29872 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2162 + sourceB2162) sourceC2162) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA2162 + sourceB2162) sourceC2162) = raw28174 := by
      apply Matrix.ext; unfold doubleCharges sourceA2162 sourceB2162 sourceC2162 raw28174; decide +kernel
    rw [ha]
    exact (canonical28174 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2162 sourceB2162 sourceC2162
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2162, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2163 : Charge := ![1, 1, 0, 2, -2, -2]
def sourceB2163 : Charge := ![2, 0, 0, -2, 0, 0]
def sourceC2163 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceForm2163 : Integer.Sparse Master := [(Sum.inr 2311, 2), (Sum.inr 3362, 1), (Sum.inr 3372, 1), (Sum.inr 3439, 1), (Sum.inr 3611, 1), (Sum.inr 4082, -1)]

theorem sourceEq2163 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2163 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2163 + difference 0 0) (sourceB2163 + difference 0 0) sourceC2163) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3611) := by
    have ha : (tripleCharges (sourceA2163 + difference 0 0) (sourceB2163 + difference 0 0) sourceC2163) = raw29873 := by
      apply Matrix.ext; unfold tripleCharges sourceA2163 sourceB2163 sourceC2163 difference raw29873; decide +kernel
    rw [ha]
    exact (canonical29873 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2163 + difference 0 1) (sourceB2163 + difference 1 0) sourceC2163) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3372) := by
    have ha : (tripleCharges (sourceA2163 + difference 0 1) (sourceB2163 + difference 1 0) sourceC2163) = raw29393 := by
      apply Matrix.ext; unfold tripleCharges sourceA2163 sourceB2163 sourceC2163 difference raw29393; decide +kernel
    rw [ha]
    exact (canonical29393 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2163 + difference 0 2) (sourceB2163 + difference 2 0) sourceC2163) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3362) := by
    have ha : (tripleCharges (sourceA2163 + difference 0 2) (sourceB2163 + difference 2 0) sourceC2163) = raw29874 := by
      apply Matrix.ext; unfold tripleCharges sourceA2163 sourceB2163 sourceC2163 difference raw29874; decide +kernel
    rw [ha]
    exact (canonical29874 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2163 + difference 0 3) (sourceB2163 + difference 3 0) sourceC2163) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3439) := by
    have ha : (tripleCharges (sourceA2163 + difference 0 3) (sourceB2163 + difference 3 0) sourceC2163) = raw29860 := by
      apply Matrix.ext; unfold tripleCharges sourceA2163 sourceB2163 sourceC2163 difference raw29860; decide +kernel
    rw [ha]
    exact (canonical29860 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2163 + difference 0 4) (sourceB2163 + difference 4 0) sourceC2163) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2311) := by
    have ha : (tripleCharges (sourceA2163 + difference 0 4) (sourceB2163 + difference 4 0) sourceC2163) = raw29875 := by
      apply Matrix.ext; unfold tripleCharges sourceA2163 sourceB2163 sourceC2163 difference raw29875; decide +kernel
    rw [ha]
    exact (canonical29875 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2163 + difference 0 5) (sourceB2163 + difference 5 0) sourceC2163) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2311) := by
    have ha : (tripleCharges (sourceA2163 + difference 0 5) (sourceB2163 + difference 5 0) sourceC2163) = raw29876 := by
      apply Matrix.ext; unfold tripleCharges sourceA2163 sourceB2163 sourceC2163 difference raw29876; decide +kernel
    rw [ha]
    exact (canonical29876 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2163 + sourceB2163) sourceC2163) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2163 + sourceB2163) sourceC2163) = raw29319 := by
      apply Matrix.ext; unfold doubleCharges sourceA2163 sourceB2163 sourceC2163 raw29319; decide +kernel
    rw [ha]
    exact (canonical29319 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2163 sourceB2163 sourceC2163
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2163, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2164 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2164 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC2164 : Charge := ![1, 1, 1, 1, -3, -1]
def sourceForm2164 : Integer.Sparse Master := [(Sum.inr 2912, 1), (Sum.inr 3338, 1), (Sum.inr 3341, 2), (Sum.inr 3460, 1), (Sum.inr 3569, 1), (Sum.inr 4079, -1)]

theorem sourceEq2164 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2164 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2164 + difference 0 0) (sourceB2164 + difference 0 0) sourceC2164) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2912) := by
    have ha : (tripleCharges (sourceA2164 + difference 0 0) (sourceB2164 + difference 0 0) sourceC2164) = raw29877 := by
      apply Matrix.ext; unfold tripleCharges sourceA2164 sourceB2164 sourceC2164 difference raw29877; decide +kernel
    rw [ha]
    exact (canonical29877 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2164 + difference 0 1) (sourceB2164 + difference 1 0) sourceC2164) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3338) := by
    have ha : (tripleCharges (sourceA2164 + difference 0 1) (sourceB2164 + difference 1 0) sourceC2164) = raw29878 := by
      apply Matrix.ext; unfold tripleCharges sourceA2164 sourceB2164 sourceC2164 difference raw29878; decide +kernel
    rw [ha]
    exact (canonical29878 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2164 + difference 0 2) (sourceB2164 + difference 2 0) sourceC2164) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3341) := by
    have ha : (tripleCharges (sourceA2164 + difference 0 2) (sourceB2164 + difference 2 0) sourceC2164) = raw29879 := by
      apply Matrix.ext; unfold tripleCharges sourceA2164 sourceB2164 sourceC2164 difference raw29879; decide +kernel
    rw [ha]
    exact (canonical29879 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2164 + difference 0 3) (sourceB2164 + difference 3 0) sourceC2164) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3341) := by
    have ha : (tripleCharges (sourceA2164 + difference 0 3) (sourceB2164 + difference 3 0) sourceC2164) = raw29880 := by
      apply Matrix.ext; unfold tripleCharges sourceA2164 sourceB2164 sourceC2164 difference raw29880; decide +kernel
    rw [ha]
    exact (canonical29880 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2164 + difference 0 4) (sourceB2164 + difference 4 0) sourceC2164) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3569) := by
    have ha : (tripleCharges (sourceA2164 + difference 0 4) (sourceB2164 + difference 4 0) sourceC2164) = raw29881 := by
      apply Matrix.ext; unfold tripleCharges sourceA2164 sourceB2164 sourceC2164 difference raw29881; decide +kernel
    rw [ha]
    exact (canonical29881 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2164 + difference 0 5) (sourceB2164 + difference 5 0) sourceC2164) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3460) := by
    have ha : (tripleCharges (sourceA2164 + difference 0 5) (sourceB2164 + difference 5 0) sourceC2164) = raw29882 := by
      apply Matrix.ext; unfold tripleCharges sourceA2164 sourceB2164 sourceC2164 difference raw29882; decide +kernel
    rw [ha]
    exact (canonical29882 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2164 + sourceB2164) sourceC2164) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4079) := by
    have ha : (doubleCharges (sourceA2164 + sourceB2164) sourceC2164) = raw29883 := by
      apply Matrix.ext; unfold doubleCharges sourceA2164 sourceB2164 sourceC2164 raw29883; decide +kernel
    rw [ha]
    exact (canonical29883 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2164 sourceB2164 sourceC2164
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2164, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2165 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2165 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC2165 : Charge := ![1, 1, 1, 1, -2, -2]
def sourceForm2165 : Integer.Sparse Master := [(Sum.inr 2913, 1), (Sum.inr 3647, 1), (Sum.inr 3652, 2), (Sum.inr 3758, 2), (Sum.inr 4087, -1)]

theorem sourceEq2165 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2165 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2165 + difference 0 0) (sourceB2165 + difference 0 0) sourceC2165) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2913) := by
    have ha : (tripleCharges (sourceA2165 + difference 0 0) (sourceB2165 + difference 0 0) sourceC2165) = raw22386 := by
      apply Matrix.ext; unfold tripleCharges sourceA2165 sourceB2165 sourceC2165 difference raw22386; decide +kernel
    rw [ha]
    exact (canonical22386 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2165 + difference 0 1) (sourceB2165 + difference 1 0) sourceC2165) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3647) := by
    have ha : (tripleCharges (sourceA2165 + difference 0 1) (sourceB2165 + difference 1 0) sourceC2165) = raw29884 := by
      apply Matrix.ext; unfold tripleCharges sourceA2165 sourceB2165 sourceC2165 difference raw29884; decide +kernel
    rw [ha]
    exact (canonical29884 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2165 + difference 0 2) (sourceB2165 + difference 2 0) sourceC2165) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3652) := by
    have ha : (tripleCharges (sourceA2165 + difference 0 2) (sourceB2165 + difference 2 0) sourceC2165) = raw29885 := by
      apply Matrix.ext; unfold tripleCharges sourceA2165 sourceB2165 sourceC2165 difference raw29885; decide +kernel
    rw [ha]
    exact (canonical29885 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2165 + difference 0 3) (sourceB2165 + difference 3 0) sourceC2165) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3652) := by
    have ha : (tripleCharges (sourceA2165 + difference 0 3) (sourceB2165 + difference 3 0) sourceC2165) = raw29886 := by
      apply Matrix.ext; unfold tripleCharges sourceA2165 sourceB2165 sourceC2165 difference raw29886; decide +kernel
    rw [ha]
    exact (canonical29886 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2165 + difference 0 4) (sourceB2165 + difference 4 0) sourceC2165) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3758) := by
    have ha : (tripleCharges (sourceA2165 + difference 0 4) (sourceB2165 + difference 4 0) sourceC2165) = raw28195 := by
      apply Matrix.ext; unfold tripleCharges sourceA2165 sourceB2165 sourceC2165 difference raw28195; decide +kernel
    rw [ha]
    exact (canonical28195 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2165 + difference 0 5) (sourceB2165 + difference 5 0) sourceC2165) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3758) := by
    have ha : (tripleCharges (sourceA2165 + difference 0 5) (sourceB2165 + difference 5 0) sourceC2165) = raw29887 := by
      apply Matrix.ext; unfold tripleCharges sourceA2165 sourceB2165 sourceC2165 difference raw29887; decide +kernel
    rw [ha]
    exact (canonical29887 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2165 + sourceB2165) sourceC2165) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4087) := by
    have ha : (doubleCharges (sourceA2165 + sourceB2165) sourceC2165) = raw22391 := by
      apply Matrix.ext; unfold doubleCharges sourceA2165 sourceB2165 sourceC2165 raw22391; decide +kernel
    rw [ha]
    exact (canonical22391 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2165 sourceB2165 sourceC2165
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2165, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2166 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2166 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC2166 : Charge := ![1, 1, 1, 1, -2, -2]
def sourceForm2166 : Integer.Sparse Master := [(Sum.inr 2297, 2), (Sum.inr 2891, 1), (Sum.inr 2913, 2), (Sum.inr 3652, 1), (Sum.inr 4087, -1)]

theorem sourceEq2166 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2166 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2166 + difference 0 2) (sourceB2166 + difference 2 0) sourceC2166) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3652) := by
    have ha : (tripleCharges (sourceA2166 + difference 0 2) (sourceB2166 + difference 2 0) sourceC2166) = raw29885 := by
      apply Matrix.ext; unfold tripleCharges sourceA2166 sourceB2166 sourceC2166 difference raw29885; decide +kernel
    rw [ha]
    exact (canonical29885 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2166 + difference 1 2) (sourceB2166 + difference 2 1) sourceC2166) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2913) := by
    have ha : (tripleCharges (sourceA2166 + difference 1 2) (sourceB2166 + difference 2 1) sourceC2166) = raw22387 := by
      apply Matrix.ext; unfold tripleCharges sourceA2166 sourceB2166 sourceC2166 difference raw22387; decide +kernel
    rw [ha]
    exact (canonical22387 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2166 + difference 2 2) (sourceB2166 + difference 2 2) sourceC2166) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2913) := by
    have ha : (tripleCharges (sourceA2166 + difference 2 2) (sourceB2166 + difference 2 2) sourceC2166) = raw22386 := by
      apply Matrix.ext; unfold tripleCharges sourceA2166 sourceB2166 sourceC2166 difference raw22386; decide +kernel
    rw [ha]
    exact (canonical22386 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2166 + difference 3 2) (sourceB2166 + difference 2 3) sourceC2166) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2891) := by
    have ha : (tripleCharges (sourceA2166 + difference 3 2) (sourceB2166 + difference 2 3) sourceC2166) = raw29888 := by
      apply Matrix.ext; unfold tripleCharges sourceA2166 sourceB2166 sourceC2166 difference raw29888; decide +kernel
    rw [ha]
    exact (canonical29888 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2166 + difference 4 2) (sourceB2166 + difference 2 4) sourceC2166) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2297) := by
    have ha : (tripleCharges (sourceA2166 + difference 4 2) (sourceB2166 + difference 2 4) sourceC2166) = raw29889 := by
      apply Matrix.ext; unfold tripleCharges sourceA2166 sourceB2166 sourceC2166 difference raw29889; decide +kernel
    rw [ha]
    exact (canonical29889 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2166 + difference 5 2) (sourceB2166 + difference 2 5) sourceC2166) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2297) := by
    have ha : (tripleCharges (sourceA2166 + difference 5 2) (sourceB2166 + difference 2 5) sourceC2166) = raw29890 := by
      apply Matrix.ext; unfold tripleCharges sourceA2166 sourceB2166 sourceC2166 difference raw29890; decide +kernel
    rw [ha]
    exact (canonical29890 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2166 + sourceB2166) sourceC2166) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4087) := by
    have ha : (doubleCharges (sourceA2166 + sourceB2166) sourceC2166) = raw22391 := by
      apply Matrix.ext; unfold doubleCharges sourceA2166 sourceB2166 sourceC2166 raw22391; decide +kernel
    rw [ha]
    exact (canonical22391 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2166 sourceB2166 sourceC2166
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2166, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2167 : Charge := ![1, 1, 1, 1, -2, -2]
def sourceB2167 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC2167 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceForm2167 : Integer.Sparse Master := [(Sum.inr 2302, 2), (Sum.inr 3439, 2), (Sum.inr 3487, 1), (Sum.inr 3610, 1), (Sum.inr 4082, -1)]

theorem sourceEq2167 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2167 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2167 + difference 0 0) (sourceB2167 + difference 0 0) sourceC2167) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3610) := by
    have ha : (tripleCharges (sourceA2167 + difference 0 0) (sourceB2167 + difference 0 0) sourceC2167) = raw29331 := by
      apply Matrix.ext; unfold tripleCharges sourceA2167 sourceB2167 sourceC2167 difference raw29331; decide +kernel
    rw [ha]
    exact (canonical29331 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2167 + difference 0 1) (sourceB2167 + difference 1 0) sourceC2167) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3487) := by
    have ha : (tripleCharges (sourceA2167 + difference 0 1) (sourceB2167 + difference 1 0) sourceC2167) = raw29415 := by
      apply Matrix.ext; unfold tripleCharges sourceA2167 sourceB2167 sourceC2167 difference raw29415; decide +kernel
    rw [ha]
    exact (canonical29415 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2167 + difference 0 2) (sourceB2167 + difference 2 0) sourceC2167) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3439) := by
    have ha : (tripleCharges (sourceA2167 + difference 0 2) (sourceB2167 + difference 2 0) sourceC2167) = raw29860 := by
      apply Matrix.ext; unfold tripleCharges sourceA2167 sourceB2167 sourceC2167 difference raw29860; decide +kernel
    rw [ha]
    exact (canonical29860 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2167 + difference 0 3) (sourceB2167 + difference 3 0) sourceC2167) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3439) := by
    have ha : (tripleCharges (sourceA2167 + difference 0 3) (sourceB2167 + difference 3 0) sourceC2167) = raw29891 := by
      apply Matrix.ext; unfold tripleCharges sourceA2167 sourceB2167 sourceC2167 difference raw29891; decide +kernel
    rw [ha]
    exact (canonical29891 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2167 + difference 0 4) (sourceB2167 + difference 4 0) sourceC2167) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2302) := by
    have ha : (tripleCharges (sourceA2167 + difference 0 4) (sourceB2167 + difference 4 0) sourceC2167) = raw29892 := by
      apply Matrix.ext; unfold tripleCharges sourceA2167 sourceB2167 sourceC2167 difference raw29892; decide +kernel
    rw [ha]
    exact (canonical29892 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2167 + difference 0 5) (sourceB2167 + difference 5 0) sourceC2167) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2302) := by
    have ha : (tripleCharges (sourceA2167 + difference 0 5) (sourceB2167 + difference 5 0) sourceC2167) = raw29893 := by
      apply Matrix.ext; unfold tripleCharges sourceA2167 sourceB2167 sourceC2167 difference raw29893; decide +kernel
    rw [ha]
    exact (canonical29893 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2167 + sourceB2167) sourceC2167) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2167 + sourceB2167) sourceC2167) = raw29319 := by
      apply Matrix.ext; unfold doubleCharges sourceA2167 sourceB2167 sourceC2167 raw29319; decide +kernel
    rw [ha]
    exact (canonical29319 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2167 sourceB2167 sourceC2167
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2167, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2168 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2168 : Charge := ![1, 2, -1, 0, -2, 0]
def sourceC2168 : Charge := ![2, -1, 1, 0, 0, -2]
def sourceForm2168 : Integer.Sparse Master := [(Sum.inr 2355, 1), (Sum.inr 2438, 1), (Sum.inr 2443, 1), (Sum.inr 2488, 1), (Sum.inr 2620, 1), (Sum.inr 3732, 1), (Sum.inr 4092, -1)]

theorem sourceEq2168 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2168 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2168 + difference 0 2) (sourceB2168 + difference 2 0) sourceC2168) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3732) := by
    have ha : (tripleCharges (sourceA2168 + difference 0 2) (sourceB2168 + difference 2 0) sourceC2168) = raw29894 := by
      apply Matrix.ext; unfold tripleCharges sourceA2168 sourceB2168 sourceC2168 difference raw29894; decide +kernel
    rw [ha]
    exact (canonical29894 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2168 + difference 1 2) (sourceB2168 + difference 2 1) sourceC2168) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2488) := by
    have ha : (tripleCharges (sourceA2168 + difference 1 2) (sourceB2168 + difference 2 1) sourceC2168) = raw29895 := by
      apply Matrix.ext; unfold tripleCharges sourceA2168 sourceB2168 sourceC2168 difference raw29895; decide +kernel
    rw [ha]
    exact (canonical29895 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2168 + difference 2 2) (sourceB2168 + difference 2 2) sourceC2168) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2620) := by
    have ha : (tripleCharges (sourceA2168 + difference 2 2) (sourceB2168 + difference 2 2) sourceC2168) = raw29896 := by
      apply Matrix.ext; unfold tripleCharges sourceA2168 sourceB2168 sourceC2168 difference raw29896; decide +kernel
    rw [ha]
    exact (canonical29896 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2168 + difference 3 2) (sourceB2168 + difference 2 3) sourceC2168) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2438) := by
    have ha : (tripleCharges (sourceA2168 + difference 3 2) (sourceB2168 + difference 2 3) sourceC2168) = raw29897 := by
      apply Matrix.ext; unfold tripleCharges sourceA2168 sourceB2168 sourceC2168 difference raw29897; decide +kernel
    rw [ha]
    exact (canonical29897 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2168 + difference 4 2) (sourceB2168 + difference 2 4) sourceC2168) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2443) := by
    have ha : (tripleCharges (sourceA2168 + difference 4 2) (sourceB2168 + difference 2 4) sourceC2168) = raw29898 := by
      apply Matrix.ext; unfold tripleCharges sourceA2168 sourceB2168 sourceC2168 difference raw29898; decide +kernel
    rw [ha]
    exact (canonical29898 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2168 + difference 5 2) (sourceB2168 + difference 2 5) sourceC2168) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2355) := by
    have ha : (tripleCharges (sourceA2168 + difference 5 2) (sourceB2168 + difference 2 5) sourceC2168) = raw29899 := by
      apply Matrix.ext; unfold tripleCharges sourceA2168 sourceB2168 sourceC2168 difference raw29899; decide +kernel
    rw [ha]
    exact (canonical29899 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2168 + sourceB2168) sourceC2168) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2168 + sourceB2168) sourceC2168) = raw29900 := by
      apply Matrix.ext; unfold doubleCharges sourceA2168 sourceB2168 sourceC2168 raw29900; decide +kernel
    rw [ha]
    exact (canonical29900 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2168 sourceB2168 sourceC2168
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2168, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2169 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2169 : Charge := ![2, -1, 1, 0, 0, -2]
def sourceC2169 : Charge := ![1, 2, -1, 0, -2, 0]
def sourceForm2169 : Integer.Sparse Master := [(Sum.inr 2352, 1), (Sum.inr 2798, 1), (Sum.inr 2803, 1), (Sum.inr 2817, 1), (Sum.inr 2867, 1), (Sum.inr 3693, 1), (Sum.inr 4092, -1)]

theorem sourceEq2169 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2169 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2169 + difference 0 1) (sourceB2169 + difference 1 0) sourceC2169) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3693) := by
    have ha : (tripleCharges (sourceA2169 + difference 0 1) (sourceB2169 + difference 1 0) sourceC2169) = raw29901 := by
      apply Matrix.ext; unfold tripleCharges sourceA2169 sourceB2169 sourceC2169 difference raw29901; decide +kernel
    rw [ha]
    exact (canonical29901 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2169 + difference 1 1) (sourceB2169 + difference 1 1) sourceC2169) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2867) := by
    have ha : (tripleCharges (sourceA2169 + difference 1 1) (sourceB2169 + difference 1 1) sourceC2169) = raw29902 := by
      apply Matrix.ext; unfold tripleCharges sourceA2169 sourceB2169 sourceC2169 difference raw29902; decide +kernel
    rw [ha]
    exact (canonical29902 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2169 + difference 2 1) (sourceB2169 + difference 1 2) sourceC2169) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2817) := by
    have ha : (tripleCharges (sourceA2169 + difference 2 1) (sourceB2169 + difference 1 2) sourceC2169) = raw29903 := by
      apply Matrix.ext; unfold tripleCharges sourceA2169 sourceB2169 sourceC2169 difference raw29903; decide +kernel
    rw [ha]
    exact (canonical29903 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2169 + difference 3 1) (sourceB2169 + difference 1 3) sourceC2169) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2798) := by
    have ha : (tripleCharges (sourceA2169 + difference 3 1) (sourceB2169 + difference 1 3) sourceC2169) = raw29904 := by
      apply Matrix.ext; unfold tripleCharges sourceA2169 sourceB2169 sourceC2169 difference raw29904; decide +kernel
    rw [ha]
    exact (canonical29904 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2169 + difference 4 1) (sourceB2169 + difference 1 4) sourceC2169) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2352) := by
    have ha : (tripleCharges (sourceA2169 + difference 4 1) (sourceB2169 + difference 1 4) sourceC2169) = raw29905 := by
      apply Matrix.ext; unfold tripleCharges sourceA2169 sourceB2169 sourceC2169 difference raw29905; decide +kernel
    rw [ha]
    exact (canonical29905 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2169 + difference 5 1) (sourceB2169 + difference 1 5) sourceC2169) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2803) := by
    have ha : (tripleCharges (sourceA2169 + difference 5 1) (sourceB2169 + difference 1 5) sourceC2169) = raw29906 := by
      apply Matrix.ext; unfold tripleCharges sourceA2169 sourceB2169 sourceC2169 difference raw29906; decide +kernel
    rw [ha]
    exact (canonical29906 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2169 + sourceB2169) sourceC2169) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2169 + sourceB2169) sourceC2169) = raw29907 := by
      apply Matrix.ext; unfold doubleCharges sourceA2169 sourceB2169 sourceC2169 raw29907; decide +kernel
    rw [ha]
    exact (canonical29907 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2169 sourceB2169 sourceC2169
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2169, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2170 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2170 : Charge := ![2, -1, 1, 0, 0, -2]
def sourceC2170 : Charge := ![1, 2, -1, 0, -2, 0]
def sourceForm2170 : Integer.Sparse Master := [(Sum.inr 1321, 1), (Sum.inr 2817, 1), (Sum.inr 2848, 1), (Sum.inr 2867, 1), (Sum.inr 2881, 1), (Sum.inr 2885, 1), (Sum.inr 4092, -1)]

theorem sourceEq2170 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2170 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2170 + difference 2 0) (sourceB2170 + difference 0 2) sourceC2170) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1321) := by
    have ha : (tripleCharges (sourceA2170 + difference 2 0) (sourceB2170 + difference 0 2) sourceC2170) = raw29908 := by
      apply Matrix.ext; unfold tripleCharges sourceA2170 sourceB2170 sourceC2170 difference raw29908; decide +kernel
    rw [ha]
    exact (canonical29908 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2170 + difference 2 1) (sourceB2170 + difference 1 2) sourceC2170) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2817) := by
    have ha : (tripleCharges (sourceA2170 + difference 2 1) (sourceB2170 + difference 1 2) sourceC2170) = raw29903 := by
      apply Matrix.ext; unfold tripleCharges sourceA2170 sourceB2170 sourceC2170 difference raw29903; decide +kernel
    rw [ha]
    exact (canonical29903 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2170 + difference 2 2) (sourceB2170 + difference 2 2) sourceC2170) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2867) := by
    have ha : (tripleCharges (sourceA2170 + difference 2 2) (sourceB2170 + difference 2 2) sourceC2170) = raw29902 := by
      apply Matrix.ext; unfold tripleCharges sourceA2170 sourceB2170 sourceC2170 difference raw29902; decide +kernel
    rw [ha]
    exact (canonical29902 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2170 + difference 2 3) (sourceB2170 + difference 3 2) sourceC2170) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2848) := by
    have ha : (tripleCharges (sourceA2170 + difference 2 3) (sourceB2170 + difference 3 2) sourceC2170) = raw29909 := by
      apply Matrix.ext; unfold tripleCharges sourceA2170 sourceB2170 sourceC2170 difference raw29909; decide +kernel
    rw [ha]
    exact (canonical29909 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2170 + difference 2 4) (sourceB2170 + difference 4 2) sourceC2170) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2885) := by
    have ha : (tripleCharges (sourceA2170 + difference 2 4) (sourceB2170 + difference 4 2) sourceC2170) = raw29910 := by
      apply Matrix.ext; unfold tripleCharges sourceA2170 sourceB2170 sourceC2170 difference raw29910; decide +kernel
    rw [ha]
    exact (canonical29910 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2170 + difference 2 5) (sourceB2170 + difference 5 2) sourceC2170) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2881) := by
    have ha : (tripleCharges (sourceA2170 + difference 2 5) (sourceB2170 + difference 5 2) sourceC2170) = raw29911 := by
      apply Matrix.ext; unfold tripleCharges sourceA2170 sourceB2170 sourceC2170 difference raw29911; decide +kernel
    rw [ha]
    exact (canonical29911 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2170 + sourceB2170) sourceC2170) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2170 + sourceB2170) sourceC2170) = raw29907 := by
      apply Matrix.ext; unfold doubleCharges sourceA2170 sourceB2170 sourceC2170 raw29907; decide +kernel
    rw [ha]
    exact (canonical29907 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2170 sourceB2170 sourceC2170
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2170, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2171 : Charge := ![1, 2, -1, 0, -2, 0]
def sourceB2171 : Charge := ![2, -1, 1, 0, 0, -2]
def sourceC2171 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceForm2171 : Integer.Sparse Master := [(Sum.inr 2538, 1), (Sum.inr 3345, 1), (Sum.inr 3348, 1), (Sum.inr 3354, 1), (Sum.inr 3478, 1), (Sum.inr 3538, 1), (Sum.inr 4082, -1)]

theorem sourceEq2171 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2171 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2171 + difference 0 0) (sourceB2171 + difference 0 0) sourceC2171) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3538) := by
    have ha : (tripleCharges (sourceA2171 + difference 0 0) (sourceB2171 + difference 0 0) sourceC2171) = raw29451 := by
      apply Matrix.ext; unfold tripleCharges sourceA2171 sourceB2171 sourceC2171 difference raw29451; decide +kernel
    rw [ha]
    exact (canonical29451 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2171 + difference 0 1) (sourceB2171 + difference 1 0) sourceC2171) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3478) := by
    have ha : (tripleCharges (sourceA2171 + difference 0 1) (sourceB2171 + difference 1 0) sourceC2171) = raw29450 := by
      apply Matrix.ext; unfold tripleCharges sourceA2171 sourceB2171 sourceC2171 difference raw29450; decide +kernel
    rw [ha]
    exact (canonical29450 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2171 + difference 0 2) (sourceB2171 + difference 2 0) sourceC2171) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3348) := by
    have ha : (tripleCharges (sourceA2171 + difference 0 2) (sourceB2171 + difference 2 0) sourceC2171) = raw29912 := by
      apply Matrix.ext; unfold tripleCharges sourceA2171 sourceB2171 sourceC2171 difference raw29912; decide +kernel
    rw [ha]
    exact (canonical29912 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2171 + difference 0 3) (sourceB2171 + difference 3 0) sourceC2171) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3345) := by
    have ha : (tripleCharges (sourceA2171 + difference 0 3) (sourceB2171 + difference 3 0) sourceC2171) = raw29913 := by
      apply Matrix.ext; unfold tripleCharges sourceA2171 sourceB2171 sourceC2171 difference raw29913; decide +kernel
    rw [ha]
    exact (canonical29913 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2171 + difference 0 4) (sourceB2171 + difference 4 0) sourceC2171) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2538) := by
    have ha : (tripleCharges (sourceA2171 + difference 0 4) (sourceB2171 + difference 4 0) sourceC2171) = raw29914 := by
      apply Matrix.ext; unfold tripleCharges sourceA2171 sourceB2171 sourceC2171 difference raw29914; decide +kernel
    rw [ha]
    exact (canonical29914 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2171 + difference 0 5) (sourceB2171 + difference 5 0) sourceC2171) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3354) := by
    have ha : (tripleCharges (sourceA2171 + difference 0 5) (sourceB2171 + difference 5 0) sourceC2171) = raw29915 := by
      apply Matrix.ext; unfold tripleCharges sourceA2171 sourceB2171 sourceC2171 difference raw29915; decide +kernel
    rw [ha]
    exact (canonical29915 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2171 + sourceB2171) sourceC2171) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2171 + sourceB2171) sourceC2171) = raw29319 := by
      apply Matrix.ext; unfold doubleCharges sourceA2171 sourceB2171 sourceC2171 raw29319; decide +kernel
    rw [ha]
    exact (canonical29319 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2171 sourceB2171 sourceC2171
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2171, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2172 : Charge := ![1, 2, -1, 0, -2, 0]
def sourceB2172 : Charge := ![2, -1, 1, 0, 0, -2]
def sourceC2172 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceForm2172 : Integer.Sparse Master := [(Sum.inr 2048, 1), (Sum.inr 3386, 1), (Sum.inr 3491, 1), (Sum.inr 3522, 1), (Sum.inr 3538, 1), (Sum.inr 3542, 1), (Sum.inr 4082, -1)]

theorem sourceEq2172 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2172 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2172 + difference 4 0) (sourceB2172 + difference 0 4) sourceC2172) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2048) := by
    have ha : (tripleCharges (sourceA2172 + difference 4 0) (sourceB2172 + difference 0 4) sourceC2172) = raw29916 := by
      apply Matrix.ext; unfold tripleCharges sourceA2172 sourceB2172 sourceC2172 difference raw29916; decide +kernel
    rw [ha]
    exact (canonical29916 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2172 + difference 4 1) (sourceB2172 + difference 1 4) sourceC2172) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3522) := by
    have ha : (tripleCharges (sourceA2172 + difference 4 1) (sourceB2172 + difference 1 4) sourceC2172) = raw29454 := by
      apply Matrix.ext; unfold tripleCharges sourceA2172 sourceB2172 sourceC2172 difference raw29454; decide +kernel
    rw [ha]
    exact (canonical29454 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2172 + difference 4 2) (sourceB2172 + difference 2 4) sourceC2172) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3386) := by
    have ha : (tripleCharges (sourceA2172 + difference 4 2) (sourceB2172 + difference 2 4) sourceC2172) = raw29917 := by
      apply Matrix.ext; unfold tripleCharges sourceA2172 sourceB2172 sourceC2172 difference raw29917; decide +kernel
    rw [ha]
    exact (canonical29917 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2172 + difference 4 3) (sourceB2172 + difference 3 4) sourceC2172) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3491) := by
    have ha : (tripleCharges (sourceA2172 + difference 4 3) (sourceB2172 + difference 3 4) sourceC2172) = raw29918 := by
      apply Matrix.ext; unfold tripleCharges sourceA2172 sourceB2172 sourceC2172 difference raw29918; decide +kernel
    rw [ha]
    exact (canonical29918 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2172 + difference 4 4) (sourceB2172 + difference 4 4) sourceC2172) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3538) := by
    have ha : (tripleCharges (sourceA2172 + difference 4 4) (sourceB2172 + difference 4 4) sourceC2172) = raw29451 := by
      apply Matrix.ext; unfold tripleCharges sourceA2172 sourceB2172 sourceC2172 difference raw29451; decide +kernel
    rw [ha]
    exact (canonical29451 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2172 + difference 4 5) (sourceB2172 + difference 5 4) sourceC2172) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3542) := by
    have ha : (tripleCharges (sourceA2172 + difference 4 5) (sourceB2172 + difference 5 4) sourceC2172) = raw29496 := by
      apply Matrix.ext; unfold tripleCharges sourceA2172 sourceB2172 sourceC2172 difference raw29496; decide +kernel
    rw [ha]
    exact (canonical29496 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2172 + sourceB2172) sourceC2172) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2172 + sourceB2172) sourceC2172) = raw29319 := by
      apply Matrix.ext; unfold doubleCharges sourceA2172 sourceB2172 sourceC2172 raw29319; decide +kernel
    rw [ha]
    exact (canonical29319 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2172 sourceB2172 sourceC2172
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2172, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2173 : Charge := ![1, 2, -1, 0, -2, 0]
def sourceB2173 : Charge := ![2, -1, 1, 0, 0, -2]
def sourceC2173 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceForm2173 : Integer.Sparse Master := [(Sum.inr 2838, 1), (Sum.inr 3354, 1), (Sum.inr 3536, 1), (Sum.inr 3538, 1), (Sum.inr 3542, 1), (Sum.inr 3631, 1), (Sum.inr 4082, -1)]

theorem sourceEq2173 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2173 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2173 + difference 0 5) (sourceB2173 + difference 5 0) sourceC2173) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3354) := by
    have ha : (tripleCharges (sourceA2173 + difference 0 5) (sourceB2173 + difference 5 0) sourceC2173) = raw29915 := by
      apply Matrix.ext; unfold tripleCharges sourceA2173 sourceB2173 sourceC2173 difference raw29915; decide +kernel
    rw [ha]
    exact (canonical29915 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2173 + difference 1 5) (sourceB2173 + difference 5 1) sourceC2173) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2838) := by
    have ha : (tripleCharges (sourceA2173 + difference 1 5) (sourceB2173 + difference 5 1) sourceC2173) = raw29919 := by
      apply Matrix.ext; unfold tripleCharges sourceA2173 sourceB2173 sourceC2173 difference raw29919; decide +kernel
    rw [ha]
    exact (canonical29919 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2173 + difference 2 5) (sourceB2173 + difference 5 2) sourceC2173) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3631) := by
    have ha : (tripleCharges (sourceA2173 + difference 2 5) (sourceB2173 + difference 5 2) sourceC2173) = raw29352 := by
      apply Matrix.ext; unfold tripleCharges sourceA2173 sourceB2173 sourceC2173 difference raw29352; decide +kernel
    rw [ha]
    exact (canonical29352 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2173 + difference 3 5) (sourceB2173 + difference 5 3) sourceC2173) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3536) := by
    have ha : (tripleCharges (sourceA2173 + difference 3 5) (sourceB2173 + difference 5 3) sourceC2173) = raw29351 := by
      apply Matrix.ext; unfold tripleCharges sourceA2173 sourceB2173 sourceC2173 difference raw29351; decide +kernel
    rw [ha]
    exact (canonical29351 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2173 + difference 4 5) (sourceB2173 + difference 5 4) sourceC2173) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3542) := by
    have ha : (tripleCharges (sourceA2173 + difference 4 5) (sourceB2173 + difference 5 4) sourceC2173) = raw29496 := by
      apply Matrix.ext; unfold tripleCharges sourceA2173 sourceB2173 sourceC2173 difference raw29496; decide +kernel
    rw [ha]
    exact (canonical29496 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2173 + difference 5 5) (sourceB2173 + difference 5 5) sourceC2173) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3538) := by
    have ha : (tripleCharges (sourceA2173 + difference 5 5) (sourceB2173 + difference 5 5) sourceC2173) = raw29451 := by
      apply Matrix.ext; unfold tripleCharges sourceA2173 sourceB2173 sourceC2173 difference raw29451; decide +kernel
    rw [ha]
    exact (canonical29451 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2173 + sourceB2173) sourceC2173) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2173 + sourceB2173) sourceC2173) = raw29319 := by
      apply Matrix.ext; unfold doubleCharges sourceA2173 sourceB2173 sourceC2173 raw29319; decide +kernel
    rw [ha]
    exact (canonical29319 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2173 sourceB2173 sourceC2173
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2173, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2174 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2174 : Charge := ![1, 2, -1, 0, -1, -1]
def sourceC2174 : Charge := ![2, -1, 1, 0, -1, -1]
def sourceForm2174 : Integer.Sparse Master := [(Sum.inr 2439, 1), (Sum.inr 2442, 2), (Sum.inr 2489, 1), (Sum.inr 2621, 1), (Sum.inr 3790, 1), (Sum.inr 4091, -1)]

theorem sourceEq2174 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2174 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2174 + difference 0 2) (sourceB2174 + difference 2 0) sourceC2174) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3790) := by
    have ha : (tripleCharges (sourceA2174 + difference 0 2) (sourceB2174 + difference 2 0) sourceC2174) = raw29920 := by
      apply Matrix.ext; unfold tripleCharges sourceA2174 sourceB2174 sourceC2174 difference raw29920; decide +kernel
    rw [ha]
    exact (canonical29920 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2174 + difference 1 2) (sourceB2174 + difference 2 1) sourceC2174) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2489) := by
    have ha : (tripleCharges (sourceA2174 + difference 1 2) (sourceB2174 + difference 2 1) sourceC2174) = raw29921 := by
      apply Matrix.ext; unfold tripleCharges sourceA2174 sourceB2174 sourceC2174 difference raw29921; decide +kernel
    rw [ha]
    exact (canonical29921 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2174 + difference 2 2) (sourceB2174 + difference 2 2) sourceC2174) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2621) := by
    have ha : (tripleCharges (sourceA2174 + difference 2 2) (sourceB2174 + difference 2 2) sourceC2174) = raw29922 := by
      apply Matrix.ext; unfold tripleCharges sourceA2174 sourceB2174 sourceC2174 difference raw29922; decide +kernel
    rw [ha]
    exact (canonical29922 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2174 + difference 3 2) (sourceB2174 + difference 2 3) sourceC2174) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2439) := by
    have ha : (tripleCharges (sourceA2174 + difference 3 2) (sourceB2174 + difference 2 3) sourceC2174) = raw29923 := by
      apply Matrix.ext; unfold tripleCharges sourceA2174 sourceB2174 sourceC2174 difference raw29923; decide +kernel
    rw [ha]
    exact (canonical29923 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2174 + difference 4 2) (sourceB2174 + difference 2 4) sourceC2174) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2442) := by
    have ha : (tripleCharges (sourceA2174 + difference 4 2) (sourceB2174 + difference 2 4) sourceC2174) = raw29924 := by
      apply Matrix.ext; unfold tripleCharges sourceA2174 sourceB2174 sourceC2174 difference raw29924; decide +kernel
    rw [ha]
    exact (canonical29924 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2174 + difference 5 2) (sourceB2174 + difference 2 5) sourceC2174) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2442) := by
    have ha : (tripleCharges (sourceA2174 + difference 5 2) (sourceB2174 + difference 2 5) sourceC2174) = raw29925 := by
      apply Matrix.ext; unfold tripleCharges sourceA2174 sourceB2174 sourceC2174 difference raw29925; decide +kernel
    rw [ha]
    exact (canonical29925 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2174 + sourceB2174) sourceC2174) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA2174 + sourceB2174) sourceC2174) = raw29926 := by
      apply Matrix.ext; unfold doubleCharges sourceA2174 sourceB2174 sourceC2174 raw29926; decide +kernel
    rw [ha]
    exact (canonical29926 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2174 sourceB2174 sourceC2174
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2174, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2175 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2175 : Charge := ![2, -1, 1, 0, -1, -1]
def sourceC2175 : Charge := ![1, 2, -1, 0, -1, -1]
def sourceForm2175 : Integer.Sparse Master := [(Sum.inr 2799, 1), (Sum.inr 2802, 2), (Sum.inr 2818, 1), (Sum.inr 2868, 1), (Sum.inr 3694, 1), (Sum.inr 4091, -1)]

theorem sourceEq2175 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2175 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2175 + difference 0 1) (sourceB2175 + difference 1 0) sourceC2175) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3694) := by
    have ha : (tripleCharges (sourceA2175 + difference 0 1) (sourceB2175 + difference 1 0) sourceC2175) = raw29927 := by
      apply Matrix.ext; unfold tripleCharges sourceA2175 sourceB2175 sourceC2175 difference raw29927; decide +kernel
    rw [ha]
    exact (canonical29927 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2175 + difference 1 1) (sourceB2175 + difference 1 1) sourceC2175) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2868) := by
    have ha : (tripleCharges (sourceA2175 + difference 1 1) (sourceB2175 + difference 1 1) sourceC2175) = raw29928 := by
      apply Matrix.ext; unfold tripleCharges sourceA2175 sourceB2175 sourceC2175 difference raw29928; decide +kernel
    rw [ha]
    exact (canonical29928 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2175 + difference 2 1) (sourceB2175 + difference 1 2) sourceC2175) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2818) := by
    have ha : (tripleCharges (sourceA2175 + difference 2 1) (sourceB2175 + difference 1 2) sourceC2175) = raw29929 := by
      apply Matrix.ext; unfold tripleCharges sourceA2175 sourceB2175 sourceC2175 difference raw29929; decide +kernel
    rw [ha]
    exact (canonical29929 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2175 + difference 3 1) (sourceB2175 + difference 1 3) sourceC2175) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2799) := by
    have ha : (tripleCharges (sourceA2175 + difference 3 1) (sourceB2175 + difference 1 3) sourceC2175) = raw29930 := by
      apply Matrix.ext; unfold tripleCharges sourceA2175 sourceB2175 sourceC2175 difference raw29930; decide +kernel
    rw [ha]
    exact (canonical29930 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2175 + difference 4 1) (sourceB2175 + difference 1 4) sourceC2175) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2802) := by
    have ha : (tripleCharges (sourceA2175 + difference 4 1) (sourceB2175 + difference 1 4) sourceC2175) = raw29931 := by
      apply Matrix.ext; unfold tripleCharges sourceA2175 sourceB2175 sourceC2175 difference raw29931; decide +kernel
    rw [ha]
    exact (canonical29931 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2175 + difference 5 1) (sourceB2175 + difference 1 5) sourceC2175) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2802) := by
    have ha : (tripleCharges (sourceA2175 + difference 5 1) (sourceB2175 + difference 1 5) sourceC2175) = raw29932 := by
      apply Matrix.ext; unfold tripleCharges sourceA2175 sourceB2175 sourceC2175 difference raw29932; decide +kernel
    rw [ha]
    exact (canonical29932 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2175 + sourceB2175) sourceC2175) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA2175 + sourceB2175) sourceC2175) = raw29933 := by
      apply Matrix.ext; unfold doubleCharges sourceA2175 sourceB2175 sourceC2175 raw29933; decide +kernel
    rw [ha]
    exact (canonical29933 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2175 sourceB2175 sourceC2175
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2175, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
