import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical111
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical167
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical168
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical181
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical195
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical197
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical206
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical208
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical209
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical210
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical211
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical212

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA1856 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1856 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC1856 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceForm1856 : Integer.Sparse Master := [(Sum.inr 4149, 1), (Sum.inr 4150, 3), (Sum.inr 4169, 1), (Sum.inr 4544, 3), (Sum.inr 4550, 1), (Sum.inr 4589, 3), (Sum.inr 4590, 6), (Sum.inr 4599, 3), (Sum.inr 4606, 3), (Sum.inr 4618, 1), (Sum.inr 5100, 1), (Sum.inr 5257, 3), (Sum.inr 5273, 1)]

theorem sourceEq1856 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1856 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1856 + difference 0 1) (sourceB1856 + difference 1 0) sourceC1856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5100) := by
    have ha : (tripleCharges (sourceA1856 + difference 0 1) (sourceB1856 + difference 1 0) sourceC1856) = raw26708 := by
      apply Matrix.ext; unfold tripleCharges sourceA1856 sourceB1856 sourceC1856 difference raw26708; decide +kernel
    rw [ha]
    exact (canonical26708 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1856 + difference 0 2) (sourceB1856 + difference 2 0) sourceC1856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA1856 + difference 0 2) (sourceB1856 + difference 2 0) sourceC1856) = raw7310 := by
      apply Matrix.ext; unfold tripleCharges sourceA1856 sourceB1856 sourceC1856 difference raw7310; decide +kernel
    rw [ha]
    exact (canonical7310 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1856 + difference 0 3) (sourceB1856 + difference 3 0) sourceC1856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA1856 + difference 0 3) (sourceB1856 + difference 3 0) sourceC1856) = raw7305 := by
      apply Matrix.ext; unfold tripleCharges sourceA1856 sourceB1856 sourceC1856 difference raw7305; decide +kernel
    rw [ha]
    exact (canonical7305 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1856 + difference 0 4) (sourceB1856 + difference 4 0) sourceC1856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA1856 + difference 0 4) (sourceB1856 + difference 4 0) sourceC1856) = raw26709 := by
      apply Matrix.ext; unfold tripleCharges sourceA1856 sourceB1856 sourceC1856 difference raw26709; decide +kernel
    rw [ha]
    exact (canonical26709 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1856 + difference 0 5) (sourceB1856 + difference 5 0) sourceC1856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5273) := by
    have ha : (tripleCharges (sourceA1856 + difference 0 5) (sourceB1856 + difference 5 0) sourceC1856) = raw26710 := by
      apply Matrix.ext; unfold tripleCharges sourceA1856 sourceB1856 sourceC1856 difference raw26710; decide +kernel
    rw [ha]
    exact (canonical26710 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1856 + difference 1 0) (sourceB1856 + difference 0 1) sourceC1856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4169) := by
    have ha : (tripleCharges (sourceA1856 + difference 1 0) (sourceB1856 + difference 0 1) sourceC1856) = raw26711 := by
      apply Matrix.ext; unfold tripleCharges sourceA1856 sourceB1856 sourceC1856 difference raw26711; decide +kernel
    rw [ha]
    exact (canonical26711 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1856 + difference 1 2) (sourceB1856 + difference 2 1) sourceC1856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4599) := by
    have ha : (tripleCharges (sourceA1856 + difference 1 2) (sourceB1856 + difference 2 1) sourceC1856) = raw26712 := by
      apply Matrix.ext; unfold tripleCharges sourceA1856 sourceB1856 sourceC1856 difference raw26712; decide +kernel
    rw [ha]
    exact (canonical26712 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1856 + difference 1 3) (sourceB1856 + difference 3 1) sourceC1856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4599) := by
    have ha : (tripleCharges (sourceA1856 + difference 1 3) (sourceB1856 + difference 3 1) sourceC1856) = raw26713 := by
      apply Matrix.ext; unfold tripleCharges sourceA1856 sourceB1856 sourceC1856 difference raw26713; decide +kernel
    rw [ha]
    exact (canonical26713 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1856 + difference 1 4) (sourceB1856 + difference 4 1) sourceC1856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4599) := by
    have ha : (tripleCharges (sourceA1856 + difference 1 4) (sourceB1856 + difference 4 1) sourceC1856) = raw26714 := by
      apply Matrix.ext; unfold tripleCharges sourceA1856 sourceB1856 sourceC1856 difference raw26714; decide +kernel
    rw [ha]
    exact (canonical26714 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1856 + difference 1 5) (sourceB1856 + difference 5 1) sourceC1856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4618) := by
    have ha : (tripleCharges (sourceA1856 + difference 1 5) (sourceB1856 + difference 5 1) sourceC1856) = raw26715 := by
      apply Matrix.ext; unfold tripleCharges sourceA1856 sourceB1856 sourceC1856 difference raw26715; decide +kernel
    rw [ha]
    exact (canonical26715 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1856 + difference 2 0) (sourceB1856 + difference 0 2) sourceC1856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4150) := by
    have ha : (tripleCharges (sourceA1856 + difference 2 0) (sourceB1856 + difference 0 2) sourceC1856) = raw26716 := by
      apply Matrix.ext; unfold tripleCharges sourceA1856 sourceB1856 sourceC1856 difference raw26716; decide +kernel
    rw [ha]
    exact (canonical26716 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1856 + difference 2 1) (sourceB1856 + difference 1 2) sourceC1856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4544) := by
    have ha : (tripleCharges (sourceA1856 + difference 2 1) (sourceB1856 + difference 1 2) sourceC1856) = raw26717 := by
      apply Matrix.ext; unfold tripleCharges sourceA1856 sourceB1856 sourceC1856 difference raw26717; decide +kernel
    rw [ha]
    exact (canonical26717 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1856 + difference 2 3) (sourceB1856 + difference 3 2) sourceC1856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4590) := by
    have ha : (tripleCharges (sourceA1856 + difference 2 3) (sourceB1856 + difference 3 2) sourceC1856) = raw26718 := by
      apply Matrix.ext; unfold tripleCharges sourceA1856 sourceB1856 sourceC1856 difference raw26718; decide +kernel
    rw [ha]
    exact (canonical26718 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1856 + difference 2 4) (sourceB1856 + difference 4 2) sourceC1856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4590) := by
    have ha : (tripleCharges (sourceA1856 + difference 2 4) (sourceB1856 + difference 4 2) sourceC1856) = raw26719 := by
      apply Matrix.ext; unfold tripleCharges sourceA1856 sourceB1856 sourceC1856 difference raw26719; decide +kernel
    rw [ha]
    exact (canonical26719 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1856 + difference 2 5) (sourceB1856 + difference 5 2) sourceC1856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4606) := by
    have ha : (tripleCharges (sourceA1856 + difference 2 5) (sourceB1856 + difference 5 2) sourceC1856) = raw26720 := by
      apply Matrix.ext; unfold tripleCharges sourceA1856 sourceB1856 sourceC1856 difference raw26720; decide +kernel
    rw [ha]
    exact (canonical26720 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1856 + difference 3 0) (sourceB1856 + difference 0 3) sourceC1856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4150) := by
    have ha : (tripleCharges (sourceA1856 + difference 3 0) (sourceB1856 + difference 0 3) sourceC1856) = raw26721 := by
      apply Matrix.ext; unfold tripleCharges sourceA1856 sourceB1856 sourceC1856 difference raw26721; decide +kernel
    rw [ha]
    exact (canonical26721 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1856 + difference 3 1) (sourceB1856 + difference 1 3) sourceC1856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4544) := by
    have ha : (tripleCharges (sourceA1856 + difference 3 1) (sourceB1856 + difference 1 3) sourceC1856) = raw26722 := by
      apply Matrix.ext; unfold tripleCharges sourceA1856 sourceB1856 sourceC1856 difference raw26722; decide +kernel
    rw [ha]
    exact (canonical26722 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1856 + difference 3 2) (sourceB1856 + difference 2 3) sourceC1856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4590) := by
    have ha : (tripleCharges (sourceA1856 + difference 3 2) (sourceB1856 + difference 2 3) sourceC1856) = raw26723 := by
      apply Matrix.ext; unfold tripleCharges sourceA1856 sourceB1856 sourceC1856 difference raw26723; decide +kernel
    rw [ha]
    exact (canonical26723 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1856 + difference 3 4) (sourceB1856 + difference 4 3) sourceC1856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4590) := by
    have ha : (tripleCharges (sourceA1856 + difference 3 4) (sourceB1856 + difference 4 3) sourceC1856) = raw26724 := by
      apply Matrix.ext; unfold tripleCharges sourceA1856 sourceB1856 sourceC1856 difference raw26724; decide +kernel
    rw [ha]
    exact (canonical26724 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1856 + difference 3 5) (sourceB1856 + difference 5 3) sourceC1856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4606) := by
    have ha : (tripleCharges (sourceA1856 + difference 3 5) (sourceB1856 + difference 5 3) sourceC1856) = raw26725 := by
      apply Matrix.ext; unfold tripleCharges sourceA1856 sourceB1856 sourceC1856 difference raw26725; decide +kernel
    rw [ha]
    exact (canonical26725 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1856 + difference 4 0) (sourceB1856 + difference 0 4) sourceC1856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4150) := by
    have ha : (tripleCharges (sourceA1856 + difference 4 0) (sourceB1856 + difference 0 4) sourceC1856) = raw26726 := by
      apply Matrix.ext; unfold tripleCharges sourceA1856 sourceB1856 sourceC1856 difference raw26726; decide +kernel
    rw [ha]
    exact (canonical26726 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1856 + difference 4 1) (sourceB1856 + difference 1 4) sourceC1856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4544) := by
    have ha : (tripleCharges (sourceA1856 + difference 4 1) (sourceB1856 + difference 1 4) sourceC1856) = raw26727 := by
      apply Matrix.ext; unfold tripleCharges sourceA1856 sourceB1856 sourceC1856 difference raw26727; decide +kernel
    rw [ha]
    exact (canonical26727 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1856 + difference 4 2) (sourceB1856 + difference 2 4) sourceC1856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4590) := by
    have ha : (tripleCharges (sourceA1856 + difference 4 2) (sourceB1856 + difference 2 4) sourceC1856) = raw26728 := by
      apply Matrix.ext; unfold tripleCharges sourceA1856 sourceB1856 sourceC1856 difference raw26728; decide +kernel
    rw [ha]
    exact (canonical26728 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1856 + difference 4 3) (sourceB1856 + difference 3 4) sourceC1856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4590) := by
    have ha : (tripleCharges (sourceA1856 + difference 4 3) (sourceB1856 + difference 3 4) sourceC1856) = raw26729 := by
      apply Matrix.ext; unfold tripleCharges sourceA1856 sourceB1856 sourceC1856 difference raw26729; decide +kernel
    rw [ha]
    exact (canonical26729 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1856 + difference 4 5) (sourceB1856 + difference 5 4) sourceC1856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4606) := by
    have ha : (tripleCharges (sourceA1856 + difference 4 5) (sourceB1856 + difference 5 4) sourceC1856) = raw26730 := by
      apply Matrix.ext; unfold tripleCharges sourceA1856 sourceB1856 sourceC1856 difference raw26730; decide +kernel
    rw [ha]
    exact (canonical26730 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1856 + difference 5 0) (sourceB1856 + difference 0 5) sourceC1856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4149) := by
    have ha : (tripleCharges (sourceA1856 + difference 5 0) (sourceB1856 + difference 0 5) sourceC1856) = raw26731 := by
      apply Matrix.ext; unfold tripleCharges sourceA1856 sourceB1856 sourceC1856 difference raw26731; decide +kernel
    rw [ha]
    exact (canonical26731 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1856 + difference 5 1) (sourceB1856 + difference 1 5) sourceC1856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4550) := by
    have ha : (tripleCharges (sourceA1856 + difference 5 1) (sourceB1856 + difference 1 5) sourceC1856) = raw26732 := by
      apply Matrix.ext; unfold tripleCharges sourceA1856 sourceB1856 sourceC1856 difference raw26732; decide +kernel
    rw [ha]
    exact (canonical26732 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1856 + difference 5 2) (sourceB1856 + difference 2 5) sourceC1856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4589) := by
    have ha : (tripleCharges (sourceA1856 + difference 5 2) (sourceB1856 + difference 2 5) sourceC1856) = raw7306 := by
      apply Matrix.ext; unfold tripleCharges sourceA1856 sourceB1856 sourceC1856 difference raw7306; decide +kernel
    rw [ha]
    exact (canonical7306 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1856 + difference 5 3) (sourceB1856 + difference 3 5) sourceC1856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4589) := by
    have ha : (tripleCharges (sourceA1856 + difference 5 3) (sourceB1856 + difference 3 5) sourceC1856) = raw7301 := by
      apply Matrix.ext; unfold tripleCharges sourceA1856 sourceB1856 sourceC1856 difference raw7301; decide +kernel
    rw [ha]
    exact (canonical7301 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1856 + difference 5 4) (sourceB1856 + difference 4 5) sourceC1856) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4589) := by
    have ha : (tripleCharges (sourceA1856 + difference 5 4) (sourceB1856 + difference 4 5) sourceC1856) = raw26733 := by
      apply Matrix.ext; unfold tripleCharges sourceA1856 sourceB1856 sourceC1856 difference raw26733; decide +kernel
    rw [ha]
    exact (canonical26733 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1856 sourceB1856 sourceC1856
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1856, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1857 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1857 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC1857 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceForm1857 : Integer.Sparse Master := [(Sum.inr 577, 1), (Sum.inr 578, 3), (Sum.inr 597, 1), (Sum.inr 1161, 1), (Sum.inr 1162, 3), (Sum.inr 1212, 3), (Sum.inr 1213, 6), (Sum.inr 1233, 3), (Sum.inr 1266, 3), (Sum.inr 1298, 1), (Sum.inr 2999, 1), (Sum.inr 3087, 3), (Sum.inr 3111, 1)]

theorem sourceEq1857 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1857 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1857 + difference 0 1) (sourceB1857 + difference 1 0) sourceC1857) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2999) := by
    have ha : (tripleCharges (sourceA1857 + difference 0 1) (sourceB1857 + difference 1 0) sourceC1857) = raw26734 := by
      apply Matrix.ext; unfold tripleCharges sourceA1857 sourceB1857 sourceC1857 difference raw26734; decide +kernel
    rw [ha]
    exact (canonical26734 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1857 + difference 0 2) (sourceB1857 + difference 2 0) sourceC1857) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3087) := by
    have ha : (tripleCharges (sourceA1857 + difference 0 2) (sourceB1857 + difference 2 0) sourceC1857) = raw7340 := by
      apply Matrix.ext; unfold tripleCharges sourceA1857 sourceB1857 sourceC1857 difference raw7340; decide +kernel
    rw [ha]
    exact (canonical7340 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1857 + difference 0 3) (sourceB1857 + difference 3 0) sourceC1857) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3087) := by
    have ha : (tripleCharges (sourceA1857 + difference 0 3) (sourceB1857 + difference 3 0) sourceC1857) = raw7335 := by
      apply Matrix.ext; unfold tripleCharges sourceA1857 sourceB1857 sourceC1857 difference raw7335; decide +kernel
    rw [ha]
    exact (canonical7335 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1857 + difference 0 4) (sourceB1857 + difference 4 0) sourceC1857) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3087) := by
    have ha : (tripleCharges (sourceA1857 + difference 0 4) (sourceB1857 + difference 4 0) sourceC1857) = raw26735 := by
      apply Matrix.ext; unfold tripleCharges sourceA1857 sourceB1857 sourceC1857 difference raw26735; decide +kernel
    rw [ha]
    exact (canonical26735 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1857 + difference 0 5) (sourceB1857 + difference 5 0) sourceC1857) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3111) := by
    have ha : (tripleCharges (sourceA1857 + difference 0 5) (sourceB1857 + difference 5 0) sourceC1857) = raw26736 := by
      apply Matrix.ext; unfold tripleCharges sourceA1857 sourceB1857 sourceC1857 difference raw26736; decide +kernel
    rw [ha]
    exact (canonical26736 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1857 + difference 1 0) (sourceB1857 + difference 0 1) sourceC1857) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 597) := by
    have ha : (tripleCharges (sourceA1857 + difference 1 0) (sourceB1857 + difference 0 1) sourceC1857) = raw26737 := by
      apply Matrix.ext; unfold tripleCharges sourceA1857 sourceB1857 sourceC1857 difference raw26737; decide +kernel
    rw [ha]
    exact (canonical26737 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1857 + difference 1 2) (sourceB1857 + difference 2 1) sourceC1857) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1233) := by
    have ha : (tripleCharges (sourceA1857 + difference 1 2) (sourceB1857 + difference 2 1) sourceC1857) = raw26738 := by
      apply Matrix.ext; unfold tripleCharges sourceA1857 sourceB1857 sourceC1857 difference raw26738; decide +kernel
    rw [ha]
    exact (canonical26738 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1857 + difference 1 3) (sourceB1857 + difference 3 1) sourceC1857) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1233) := by
    have ha : (tripleCharges (sourceA1857 + difference 1 3) (sourceB1857 + difference 3 1) sourceC1857) = raw26739 := by
      apply Matrix.ext; unfold tripleCharges sourceA1857 sourceB1857 sourceC1857 difference raw26739; decide +kernel
    rw [ha]
    exact (canonical26739 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1857 + difference 1 4) (sourceB1857 + difference 4 1) sourceC1857) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1233) := by
    have ha : (tripleCharges (sourceA1857 + difference 1 4) (sourceB1857 + difference 4 1) sourceC1857) = raw26740 := by
      apply Matrix.ext; unfold tripleCharges sourceA1857 sourceB1857 sourceC1857 difference raw26740; decide +kernel
    rw [ha]
    exact (canonical26740 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1857 + difference 1 5) (sourceB1857 + difference 5 1) sourceC1857) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1298) := by
    have ha : (tripleCharges (sourceA1857 + difference 1 5) (sourceB1857 + difference 5 1) sourceC1857) = raw26741 := by
      apply Matrix.ext; unfold tripleCharges sourceA1857 sourceB1857 sourceC1857 difference raw26741; decide +kernel
    rw [ha]
    exact (canonical26741 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1857 + difference 2 0) (sourceB1857 + difference 0 2) sourceC1857) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 578) := by
    have ha : (tripleCharges (sourceA1857 + difference 2 0) (sourceB1857 + difference 0 2) sourceC1857) = raw26742 := by
      apply Matrix.ext; unfold tripleCharges sourceA1857 sourceB1857 sourceC1857 difference raw26742; decide +kernel
    rw [ha]
    exact (canonical26742 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1857 + difference 2 1) (sourceB1857 + difference 1 2) sourceC1857) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1162) := by
    have ha : (tripleCharges (sourceA1857 + difference 2 1) (sourceB1857 + difference 1 2) sourceC1857) = raw26743 := by
      apply Matrix.ext; unfold tripleCharges sourceA1857 sourceB1857 sourceC1857 difference raw26743; decide +kernel
    rw [ha]
    exact (canonical26743 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1857 + difference 2 3) (sourceB1857 + difference 3 2) sourceC1857) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1213) := by
    have ha : (tripleCharges (sourceA1857 + difference 2 3) (sourceB1857 + difference 3 2) sourceC1857) = raw26744 := by
      apply Matrix.ext; unfold tripleCharges sourceA1857 sourceB1857 sourceC1857 difference raw26744; decide +kernel
    rw [ha]
    exact (canonical26744 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1857 + difference 2 4) (sourceB1857 + difference 4 2) sourceC1857) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1213) := by
    have ha : (tripleCharges (sourceA1857 + difference 2 4) (sourceB1857 + difference 4 2) sourceC1857) = raw26745 := by
      apply Matrix.ext; unfold tripleCharges sourceA1857 sourceB1857 sourceC1857 difference raw26745; decide +kernel
    rw [ha]
    exact (canonical26745 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1857 + difference 2 5) (sourceB1857 + difference 5 2) sourceC1857) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1266) := by
    have ha : (tripleCharges (sourceA1857 + difference 2 5) (sourceB1857 + difference 5 2) sourceC1857) = raw26746 := by
      apply Matrix.ext; unfold tripleCharges sourceA1857 sourceB1857 sourceC1857 difference raw26746; decide +kernel
    rw [ha]
    exact (canonical26746 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1857 + difference 3 0) (sourceB1857 + difference 0 3) sourceC1857) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 578) := by
    have ha : (tripleCharges (sourceA1857 + difference 3 0) (sourceB1857 + difference 0 3) sourceC1857) = raw26747 := by
      apply Matrix.ext; unfold tripleCharges sourceA1857 sourceB1857 sourceC1857 difference raw26747; decide +kernel
    rw [ha]
    exact (canonical26747 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1857 + difference 3 1) (sourceB1857 + difference 1 3) sourceC1857) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1162) := by
    have ha : (tripleCharges (sourceA1857 + difference 3 1) (sourceB1857 + difference 1 3) sourceC1857) = raw26748 := by
      apply Matrix.ext; unfold tripleCharges sourceA1857 sourceB1857 sourceC1857 difference raw26748; decide +kernel
    rw [ha]
    exact (canonical26748 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1857 + difference 3 2) (sourceB1857 + difference 2 3) sourceC1857) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1213) := by
    have ha : (tripleCharges (sourceA1857 + difference 3 2) (sourceB1857 + difference 2 3) sourceC1857) = raw26749 := by
      apply Matrix.ext; unfold tripleCharges sourceA1857 sourceB1857 sourceC1857 difference raw26749; decide +kernel
    rw [ha]
    exact (canonical26749 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1857 + difference 3 4) (sourceB1857 + difference 4 3) sourceC1857) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1213) := by
    have ha : (tripleCharges (sourceA1857 + difference 3 4) (sourceB1857 + difference 4 3) sourceC1857) = raw26750 := by
      apply Matrix.ext; unfold tripleCharges sourceA1857 sourceB1857 sourceC1857 difference raw26750; decide +kernel
    rw [ha]
    exact (canonical26750 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1857 + difference 3 5) (sourceB1857 + difference 5 3) sourceC1857) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1266) := by
    have ha : (tripleCharges (sourceA1857 + difference 3 5) (sourceB1857 + difference 5 3) sourceC1857) = raw26751 := by
      apply Matrix.ext; unfold tripleCharges sourceA1857 sourceB1857 sourceC1857 difference raw26751; decide +kernel
    rw [ha]
    exact (canonical26751 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1857 + difference 4 0) (sourceB1857 + difference 0 4) sourceC1857) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 578) := by
    have ha : (tripleCharges (sourceA1857 + difference 4 0) (sourceB1857 + difference 0 4) sourceC1857) = raw26752 := by
      apply Matrix.ext; unfold tripleCharges sourceA1857 sourceB1857 sourceC1857 difference raw26752; decide +kernel
    rw [ha]
    exact (canonical26752 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1857 + difference 4 1) (sourceB1857 + difference 1 4) sourceC1857) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1162) := by
    have ha : (tripleCharges (sourceA1857 + difference 4 1) (sourceB1857 + difference 1 4) sourceC1857) = raw26753 := by
      apply Matrix.ext; unfold tripleCharges sourceA1857 sourceB1857 sourceC1857 difference raw26753; decide +kernel
    rw [ha]
    exact (canonical26753 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1857 + difference 4 2) (sourceB1857 + difference 2 4) sourceC1857) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1213) := by
    have ha : (tripleCharges (sourceA1857 + difference 4 2) (sourceB1857 + difference 2 4) sourceC1857) = raw26754 := by
      apply Matrix.ext; unfold tripleCharges sourceA1857 sourceB1857 sourceC1857 difference raw26754; decide +kernel
    rw [ha]
    exact (canonical26754 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1857 + difference 4 3) (sourceB1857 + difference 3 4) sourceC1857) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1213) := by
    have ha : (tripleCharges (sourceA1857 + difference 4 3) (sourceB1857 + difference 3 4) sourceC1857) = raw26755 := by
      apply Matrix.ext; unfold tripleCharges sourceA1857 sourceB1857 sourceC1857 difference raw26755; decide +kernel
    rw [ha]
    exact (canonical26755 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1857 + difference 4 5) (sourceB1857 + difference 5 4) sourceC1857) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1266) := by
    have ha : (tripleCharges (sourceA1857 + difference 4 5) (sourceB1857 + difference 5 4) sourceC1857) = raw26756 := by
      apply Matrix.ext; unfold tripleCharges sourceA1857 sourceB1857 sourceC1857 difference raw26756; decide +kernel
    rw [ha]
    exact (canonical26756 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1857 + difference 5 0) (sourceB1857 + difference 0 5) sourceC1857) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 577) := by
    have ha : (tripleCharges (sourceA1857 + difference 5 0) (sourceB1857 + difference 0 5) sourceC1857) = raw26757 := by
      apply Matrix.ext; unfold tripleCharges sourceA1857 sourceB1857 sourceC1857 difference raw26757; decide +kernel
    rw [ha]
    exact (canonical26757 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1857 + difference 5 1) (sourceB1857 + difference 1 5) sourceC1857) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1161) := by
    have ha : (tripleCharges (sourceA1857 + difference 5 1) (sourceB1857 + difference 1 5) sourceC1857) = raw26758 := by
      apply Matrix.ext; unfold tripleCharges sourceA1857 sourceB1857 sourceC1857 difference raw26758; decide +kernel
    rw [ha]
    exact (canonical26758 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1857 + difference 5 2) (sourceB1857 + difference 2 5) sourceC1857) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1212) := by
    have ha : (tripleCharges (sourceA1857 + difference 5 2) (sourceB1857 + difference 2 5) sourceC1857) = raw7336 := by
      apply Matrix.ext; unfold tripleCharges sourceA1857 sourceB1857 sourceC1857 difference raw7336; decide +kernel
    rw [ha]
    exact (canonical7336 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1857 + difference 5 3) (sourceB1857 + difference 3 5) sourceC1857) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1212) := by
    have ha : (tripleCharges (sourceA1857 + difference 5 3) (sourceB1857 + difference 3 5) sourceC1857) = raw7331 := by
      apply Matrix.ext; unfold tripleCharges sourceA1857 sourceB1857 sourceC1857 difference raw7331; decide +kernel
    rw [ha]
    exact (canonical7331 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1857 + difference 5 4) (sourceB1857 + difference 4 5) sourceC1857) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1212) := by
    have ha : (tripleCharges (sourceA1857 + difference 5 4) (sourceB1857 + difference 4 5) sourceC1857) = raw26759 := by
      apply Matrix.ext; unfold tripleCharges sourceA1857 sourceB1857 sourceC1857 difference raw26759; decide +kernel
    rw [ha]
    exact (canonical26759 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1857 sourceB1857 sourceC1857
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1857, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1858 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1858 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC1858 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceForm1858 : Integer.Sparse Master := [(Sum.inr 1501, 1), (Sum.inr 1502, 1), (Sum.inr 1504, 3), (Sum.inr 3263, 3), (Sum.inr 3269, 1), (Sum.inr 3288, 3), (Sum.inr 3289, 3), (Sum.inr 3290, 6), (Sum.inr 3299, 3), (Sum.inr 3304, 1), (Sum.inr 3469, 1), (Sum.inr 3532, 3), (Sum.inr 3546, 1)]

theorem sourceEq1858 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1858 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1858 + difference 0 1) (sourceB1858 + difference 1 0) sourceC1858) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3469) := by
    have ha : (tripleCharges (sourceA1858 + difference 0 1) (sourceB1858 + difference 1 0) sourceC1858) = raw26760 := by
      apply Matrix.ext; unfold tripleCharges sourceA1858 sourceB1858 sourceC1858 difference raw26760; decide +kernel
    rw [ha]
    exact (canonical26760 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1858 + difference 0 2) (sourceB1858 + difference 2 0) sourceC1858) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3532) := by
    have ha : (tripleCharges (sourceA1858 + difference 0 2) (sourceB1858 + difference 2 0) sourceC1858) = raw7370 := by
      apply Matrix.ext; unfold tripleCharges sourceA1858 sourceB1858 sourceC1858 difference raw7370; decide +kernel
    rw [ha]
    exact (canonical7370 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1858 + difference 0 3) (sourceB1858 + difference 3 0) sourceC1858) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3532) := by
    have ha : (tripleCharges (sourceA1858 + difference 0 3) (sourceB1858 + difference 3 0) sourceC1858) = raw7365 := by
      apply Matrix.ext; unfold tripleCharges sourceA1858 sourceB1858 sourceC1858 difference raw7365; decide +kernel
    rw [ha]
    exact (canonical7365 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1858 + difference 0 4) (sourceB1858 + difference 4 0) sourceC1858) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3532) := by
    have ha : (tripleCharges (sourceA1858 + difference 0 4) (sourceB1858 + difference 4 0) sourceC1858) = raw26761 := by
      apply Matrix.ext; unfold tripleCharges sourceA1858 sourceB1858 sourceC1858 difference raw26761; decide +kernel
    rw [ha]
    exact (canonical26761 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1858 + difference 0 5) (sourceB1858 + difference 5 0) sourceC1858) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3546) := by
    have ha : (tripleCharges (sourceA1858 + difference 0 5) (sourceB1858 + difference 5 0) sourceC1858) = raw26762 := by
      apply Matrix.ext; unfold tripleCharges sourceA1858 sourceB1858 sourceC1858 difference raw26762; decide +kernel
    rw [ha]
    exact (canonical26762 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1858 + difference 1 0) (sourceB1858 + difference 0 1) sourceC1858) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1502) := by
    have ha : (tripleCharges (sourceA1858 + difference 1 0) (sourceB1858 + difference 0 1) sourceC1858) = raw26763 := by
      apply Matrix.ext; unfold tripleCharges sourceA1858 sourceB1858 sourceC1858 difference raw26763; decide +kernel
    rw [ha]
    exact (canonical26763 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1858 + difference 1 2) (sourceB1858 + difference 2 1) sourceC1858) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3289) := by
    have ha : (tripleCharges (sourceA1858 + difference 1 2) (sourceB1858 + difference 2 1) sourceC1858) = raw26764 := by
      apply Matrix.ext; unfold tripleCharges sourceA1858 sourceB1858 sourceC1858 difference raw26764; decide +kernel
    rw [ha]
    exact (canonical26764 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1858 + difference 1 3) (sourceB1858 + difference 3 1) sourceC1858) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3289) := by
    have ha : (tripleCharges (sourceA1858 + difference 1 3) (sourceB1858 + difference 3 1) sourceC1858) = raw26765 := by
      apply Matrix.ext; unfold tripleCharges sourceA1858 sourceB1858 sourceC1858 difference raw26765; decide +kernel
    rw [ha]
    exact (canonical26765 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1858 + difference 1 4) (sourceB1858 + difference 4 1) sourceC1858) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3289) := by
    have ha : (tripleCharges (sourceA1858 + difference 1 4) (sourceB1858 + difference 4 1) sourceC1858) = raw26766 := by
      apply Matrix.ext; unfold tripleCharges sourceA1858 sourceB1858 sourceC1858 difference raw26766; decide +kernel
    rw [ha]
    exact (canonical26766 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1858 + difference 1 5) (sourceB1858 + difference 5 1) sourceC1858) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3304) := by
    have ha : (tripleCharges (sourceA1858 + difference 1 5) (sourceB1858 + difference 5 1) sourceC1858) = raw26767 := by
      apply Matrix.ext; unfold tripleCharges sourceA1858 sourceB1858 sourceC1858 difference raw26767; decide +kernel
    rw [ha]
    exact (canonical26767 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1858 + difference 2 0) (sourceB1858 + difference 0 2) sourceC1858) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1504) := by
    have ha : (tripleCharges (sourceA1858 + difference 2 0) (sourceB1858 + difference 0 2) sourceC1858) = raw26768 := by
      apply Matrix.ext; unfold tripleCharges sourceA1858 sourceB1858 sourceC1858 difference raw26768; decide +kernel
    rw [ha]
    exact (canonical26768 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1858 + difference 2 1) (sourceB1858 + difference 1 2) sourceC1858) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3263) := by
    have ha : (tripleCharges (sourceA1858 + difference 2 1) (sourceB1858 + difference 1 2) sourceC1858) = raw26769 := by
      apply Matrix.ext; unfold tripleCharges sourceA1858 sourceB1858 sourceC1858 difference raw26769; decide +kernel
    rw [ha]
    exact (canonical26769 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1858 + difference 2 3) (sourceB1858 + difference 3 2) sourceC1858) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3290) := by
    have ha : (tripleCharges (sourceA1858 + difference 2 3) (sourceB1858 + difference 3 2) sourceC1858) = raw26770 := by
      apply Matrix.ext; unfold tripleCharges sourceA1858 sourceB1858 sourceC1858 difference raw26770; decide +kernel
    rw [ha]
    exact (canonical26770 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1858 + difference 2 4) (sourceB1858 + difference 4 2) sourceC1858) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3290) := by
    have ha : (tripleCharges (sourceA1858 + difference 2 4) (sourceB1858 + difference 4 2) sourceC1858) = raw26771 := by
      apply Matrix.ext; unfold tripleCharges sourceA1858 sourceB1858 sourceC1858 difference raw26771; decide +kernel
    rw [ha]
    exact (canonical26771 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1858 + difference 2 5) (sourceB1858 + difference 5 2) sourceC1858) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3299) := by
    have ha : (tripleCharges (sourceA1858 + difference 2 5) (sourceB1858 + difference 5 2) sourceC1858) = raw26772 := by
      apply Matrix.ext; unfold tripleCharges sourceA1858 sourceB1858 sourceC1858 difference raw26772; decide +kernel
    rw [ha]
    exact (canonical26772 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1858 + difference 3 0) (sourceB1858 + difference 0 3) sourceC1858) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1504) := by
    have ha : (tripleCharges (sourceA1858 + difference 3 0) (sourceB1858 + difference 0 3) sourceC1858) = raw26773 := by
      apply Matrix.ext; unfold tripleCharges sourceA1858 sourceB1858 sourceC1858 difference raw26773; decide +kernel
    rw [ha]
    exact (canonical26773 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1858 + difference 3 1) (sourceB1858 + difference 1 3) sourceC1858) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3263) := by
    have ha : (tripleCharges (sourceA1858 + difference 3 1) (sourceB1858 + difference 1 3) sourceC1858) = raw26774 := by
      apply Matrix.ext; unfold tripleCharges sourceA1858 sourceB1858 sourceC1858 difference raw26774; decide +kernel
    rw [ha]
    exact (canonical26774 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1858 + difference 3 2) (sourceB1858 + difference 2 3) sourceC1858) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3290) := by
    have ha : (tripleCharges (sourceA1858 + difference 3 2) (sourceB1858 + difference 2 3) sourceC1858) = raw26775 := by
      apply Matrix.ext; unfold tripleCharges sourceA1858 sourceB1858 sourceC1858 difference raw26775; decide +kernel
    rw [ha]
    exact (canonical26775 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1858 + difference 3 4) (sourceB1858 + difference 4 3) sourceC1858) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3290) := by
    have ha : (tripleCharges (sourceA1858 + difference 3 4) (sourceB1858 + difference 4 3) sourceC1858) = raw26776 := by
      apply Matrix.ext; unfold tripleCharges sourceA1858 sourceB1858 sourceC1858 difference raw26776; decide +kernel
    rw [ha]
    exact (canonical26776 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1858 + difference 3 5) (sourceB1858 + difference 5 3) sourceC1858) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3299) := by
    have ha : (tripleCharges (sourceA1858 + difference 3 5) (sourceB1858 + difference 5 3) sourceC1858) = raw26777 := by
      apply Matrix.ext; unfold tripleCharges sourceA1858 sourceB1858 sourceC1858 difference raw26777; decide +kernel
    rw [ha]
    exact (canonical26777 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1858 + difference 4 0) (sourceB1858 + difference 0 4) sourceC1858) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1504) := by
    have ha : (tripleCharges (sourceA1858 + difference 4 0) (sourceB1858 + difference 0 4) sourceC1858) = raw26778 := by
      apply Matrix.ext; unfold tripleCharges sourceA1858 sourceB1858 sourceC1858 difference raw26778; decide +kernel
    rw [ha]
    exact (canonical26778 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1858 + difference 4 1) (sourceB1858 + difference 1 4) sourceC1858) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3263) := by
    have ha : (tripleCharges (sourceA1858 + difference 4 1) (sourceB1858 + difference 1 4) sourceC1858) = raw26779 := by
      apply Matrix.ext; unfold tripleCharges sourceA1858 sourceB1858 sourceC1858 difference raw26779; decide +kernel
    rw [ha]
    exact (canonical26779 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1858 + difference 4 2) (sourceB1858 + difference 2 4) sourceC1858) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3290) := by
    have ha : (tripleCharges (sourceA1858 + difference 4 2) (sourceB1858 + difference 2 4) sourceC1858) = raw26780 := by
      apply Matrix.ext; unfold tripleCharges sourceA1858 sourceB1858 sourceC1858 difference raw26780; decide +kernel
    rw [ha]
    exact (canonical26780 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1858 + difference 4 3) (sourceB1858 + difference 3 4) sourceC1858) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3290) := by
    have ha : (tripleCharges (sourceA1858 + difference 4 3) (sourceB1858 + difference 3 4) sourceC1858) = raw26781 := by
      apply Matrix.ext; unfold tripleCharges sourceA1858 sourceB1858 sourceC1858 difference raw26781; decide +kernel
    rw [ha]
    exact (canonical26781 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1858 + difference 4 5) (sourceB1858 + difference 5 4) sourceC1858) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3299) := by
    have ha : (tripleCharges (sourceA1858 + difference 4 5) (sourceB1858 + difference 5 4) sourceC1858) = raw26782 := by
      apply Matrix.ext; unfold tripleCharges sourceA1858 sourceB1858 sourceC1858 difference raw26782; decide +kernel
    rw [ha]
    exact (canonical26782 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1858 + difference 5 0) (sourceB1858 + difference 0 5) sourceC1858) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1501) := by
    have ha : (tripleCharges (sourceA1858 + difference 5 0) (sourceB1858 + difference 0 5) sourceC1858) = raw26783 := by
      apply Matrix.ext; unfold tripleCharges sourceA1858 sourceB1858 sourceC1858 difference raw26783; decide +kernel
    rw [ha]
    exact (canonical26783 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1858 + difference 5 1) (sourceB1858 + difference 1 5) sourceC1858) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3269) := by
    have ha : (tripleCharges (sourceA1858 + difference 5 1) (sourceB1858 + difference 1 5) sourceC1858) = raw26784 := by
      apply Matrix.ext; unfold tripleCharges sourceA1858 sourceB1858 sourceC1858 difference raw26784; decide +kernel
    rw [ha]
    exact (canonical26784 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1858 + difference 5 2) (sourceB1858 + difference 2 5) sourceC1858) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3288) := by
    have ha : (tripleCharges (sourceA1858 + difference 5 2) (sourceB1858 + difference 2 5) sourceC1858) = raw7366 := by
      apply Matrix.ext; unfold tripleCharges sourceA1858 sourceB1858 sourceC1858 difference raw7366; decide +kernel
    rw [ha]
    exact (canonical7366 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1858 + difference 5 3) (sourceB1858 + difference 3 5) sourceC1858) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3288) := by
    have ha : (tripleCharges (sourceA1858 + difference 5 3) (sourceB1858 + difference 3 5) sourceC1858) = raw7361 := by
      apply Matrix.ext; unfold tripleCharges sourceA1858 sourceB1858 sourceC1858 difference raw7361; decide +kernel
    rw [ha]
    exact (canonical7361 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1858 + difference 5 4) (sourceB1858 + difference 4 5) sourceC1858) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3288) := by
    have ha : (tripleCharges (sourceA1858 + difference 5 4) (sourceB1858 + difference 4 5) sourceC1858) = raw26785 := by
      apply Matrix.ext; unfold tripleCharges sourceA1858 sourceB1858 sourceC1858 difference raw26785; decide +kernel
    rw [ha]
    exact (canonical26785 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1858 sourceB1858 sourceC1858
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1858, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1859 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1859 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC1859 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceForm1859 : Integer.Sparse Master := [(Sum.inr 625, 3), (Sum.inr 629, 1), (Sum.inr 637, 1), (Sum.inr 1235, 1), (Sum.inr 4091, -1)]

theorem sourceEq1859 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1859 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1859 + difference 0 0) (sourceB1859 + difference 0 0) sourceC1859) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1235) := by
    have ha : (tripleCharges (sourceA1859 + difference 0 0) (sourceB1859 + difference 0 0) sourceC1859) = raw26786 := by
      apply Matrix.ext; unfold tripleCharges sourceA1859 sourceB1859 sourceC1859 difference raw26786; decide +kernel
    rw [ha]
    exact (canonical26786 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1859 + difference 1 0) (sourceB1859 + difference 0 1) sourceC1859) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 637) := by
    have ha : (tripleCharges (sourceA1859 + difference 1 0) (sourceB1859 + difference 0 1) sourceC1859) = raw26787 := by
      apply Matrix.ext; unfold tripleCharges sourceA1859 sourceB1859 sourceC1859 difference raw26787; decide +kernel
    rw [ha]
    exact (canonical26787 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1859 + difference 2 0) (sourceB1859 + difference 0 2) sourceC1859) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 625) := by
    have ha : (tripleCharges (sourceA1859 + difference 2 0) (sourceB1859 + difference 0 2) sourceC1859) = raw26788 := by
      apply Matrix.ext; unfold tripleCharges sourceA1859 sourceB1859 sourceC1859 difference raw26788; decide +kernel
    rw [ha]
    exact (canonical26788 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1859 + difference 3 0) (sourceB1859 + difference 0 3) sourceC1859) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 625) := by
    have ha : (tripleCharges (sourceA1859 + difference 3 0) (sourceB1859 + difference 0 3) sourceC1859) = raw26789 := by
      apply Matrix.ext; unfold tripleCharges sourceA1859 sourceB1859 sourceC1859 difference raw26789; decide +kernel
    rw [ha]
    exact (canonical26789 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1859 + difference 4 0) (sourceB1859 + difference 0 4) sourceC1859) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 625) := by
    have ha : (tripleCharges (sourceA1859 + difference 4 0) (sourceB1859 + difference 0 4) sourceC1859) = raw26790 := by
      apply Matrix.ext; unfold tripleCharges sourceA1859 sourceB1859 sourceC1859 difference raw26790; decide +kernel
    rw [ha]
    exact (canonical26790 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1859 + difference 5 0) (sourceB1859 + difference 0 5) sourceC1859) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 629) := by
    have ha : (tripleCharges (sourceA1859 + difference 5 0) (sourceB1859 + difference 0 5) sourceC1859) = raw26791 := by
      apply Matrix.ext; unfold tripleCharges sourceA1859 sourceB1859 sourceC1859 difference raw26791; decide +kernel
    rw [ha]
    exact (canonical26791 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1859 + sourceB1859) sourceC1859) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1859 + sourceB1859) sourceC1859) = raw7387 := by
      apply Matrix.ext; unfold doubleCharges sourceA1859 sourceB1859 sourceC1859 raw7387; decide +kernel
    rw [ha]
    exact (canonical7387 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1859 sourceB1859 sourceC1859
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1859, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1860 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1860 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceC1860 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceForm1860 : Integer.Sparse Master := [(Sum.inr 4139, 3), (Sum.inr 4143, 1), (Sum.inr 4171, 1), (Sum.inr 4513, 3), (Sum.inr 4516, 1), (Sum.inr 4581, 3), (Sum.inr 4601, 1), (Sum.inr 4602, 6), (Sum.inr 4606, 3), (Sum.inr 4622, 3), (Sum.inr 5202, 1), (Sum.inr 5283, 1), (Sum.inr 5292, 3)]

theorem sourceEq1860 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1860 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1860 + difference 0 1) (sourceB1860 + difference 1 0) sourceC1860) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5202) := by
    have ha : (tripleCharges (sourceA1860 + difference 0 1) (sourceB1860 + difference 1 0) sourceC1860) = raw26792 := by
      apply Matrix.ext; unfold tripleCharges sourceA1860 sourceB1860 sourceC1860 difference raw26792; decide +kernel
    rw [ha]
    exact (canonical26792 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1860 + difference 0 2) (sourceB1860 + difference 2 0) sourceC1860) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA1860 + difference 0 2) (sourceB1860 + difference 2 0) sourceC1860) = raw26793 := by
      apply Matrix.ext; unfold tripleCharges sourceA1860 sourceB1860 sourceC1860 difference raw26793; decide +kernel
    rw [ha]
    exact (canonical26793 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1860 + difference 0 3) (sourceB1860 + difference 3 0) sourceC1860) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA1860 + difference 0 3) (sourceB1860 + difference 3 0) sourceC1860) = raw26794 := by
      apply Matrix.ext; unfold tripleCharges sourceA1860 sourceB1860 sourceC1860 difference raw26794; decide +kernel
    rw [ha]
    exact (canonical26794 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1860 + difference 0 4) (sourceB1860 + difference 4 0) sourceC1860) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA1860 + difference 0 4) (sourceB1860 + difference 4 0) sourceC1860) = raw26795 := by
      apply Matrix.ext; unfold tripleCharges sourceA1860 sourceB1860 sourceC1860 difference raw26795; decide +kernel
    rw [ha]
    exact (canonical26795 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1860 + difference 0 5) (sourceB1860 + difference 5 0) sourceC1860) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5283) := by
    have ha : (tripleCharges (sourceA1860 + difference 0 5) (sourceB1860 + difference 5 0) sourceC1860) = raw26796 := by
      apply Matrix.ext; unfold tripleCharges sourceA1860 sourceB1860 sourceC1860 difference raw26796; decide +kernel
    rw [ha]
    exact (canonical26796 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1860 + difference 1 0) (sourceB1860 + difference 0 1) sourceC1860) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4171) := by
    have ha : (tripleCharges (sourceA1860 + difference 1 0) (sourceB1860 + difference 0 1) sourceC1860) = raw26797 := by
      apply Matrix.ext; unfold tripleCharges sourceA1860 sourceB1860 sourceC1860 difference raw26797; decide +kernel
    rw [ha]
    exact (canonical26797 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1860 + difference 1 2) (sourceB1860 + difference 2 1) sourceC1860) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4622) := by
    have ha : (tripleCharges (sourceA1860 + difference 1 2) (sourceB1860 + difference 2 1) sourceC1860) = raw26798 := by
      apply Matrix.ext; unfold tripleCharges sourceA1860 sourceB1860 sourceC1860 difference raw26798; decide +kernel
    rw [ha]
    exact (canonical26798 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1860 + difference 1 3) (sourceB1860 + difference 3 1) sourceC1860) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4622) := by
    have ha : (tripleCharges (sourceA1860 + difference 1 3) (sourceB1860 + difference 3 1) sourceC1860) = raw26799 := by
      apply Matrix.ext; unfold tripleCharges sourceA1860 sourceB1860 sourceC1860 difference raw26799; decide +kernel
    rw [ha]
    exact (canonical26799 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1860 + difference 1 4) (sourceB1860 + difference 4 1) sourceC1860) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4622) := by
    have ha : (tripleCharges (sourceA1860 + difference 1 4) (sourceB1860 + difference 4 1) sourceC1860) = raw26800 := by
      apply Matrix.ext; unfold tripleCharges sourceA1860 sourceB1860 sourceC1860 difference raw26800; decide +kernel
    rw [ha]
    exact (canonical26800 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1860 + difference 1 5) (sourceB1860 + difference 5 1) sourceC1860) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4601) := by
    have ha : (tripleCharges (sourceA1860 + difference 1 5) (sourceB1860 + difference 5 1) sourceC1860) = raw26801 := by
      apply Matrix.ext; unfold tripleCharges sourceA1860 sourceB1860 sourceC1860 difference raw26801; decide +kernel
    rw [ha]
    exact (canonical26801 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1860 + difference 2 0) (sourceB1860 + difference 0 2) sourceC1860) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4139) := by
    have ha : (tripleCharges (sourceA1860 + difference 2 0) (sourceB1860 + difference 0 2) sourceC1860) = raw26802 := by
      apply Matrix.ext; unfold tripleCharges sourceA1860 sourceB1860 sourceC1860 difference raw26802; decide +kernel
    rw [ha]
    exact (canonical26802 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1860 + difference 2 1) (sourceB1860 + difference 1 2) sourceC1860) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4513) := by
    have ha : (tripleCharges (sourceA1860 + difference 2 1) (sourceB1860 + difference 1 2) sourceC1860) = raw26803 := by
      apply Matrix.ext; unfold tripleCharges sourceA1860 sourceB1860 sourceC1860 difference raw26803; decide +kernel
    rw [ha]
    exact (canonical26803 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1860 + difference 2 3) (sourceB1860 + difference 3 2) sourceC1860) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1860 + difference 2 3) (sourceB1860 + difference 3 2) sourceC1860) = raw26804 := by
      apply Matrix.ext; unfold tripleCharges sourceA1860 sourceB1860 sourceC1860 difference raw26804; decide +kernel
    rw [ha]
    exact (canonical26804 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1860 + difference 2 4) (sourceB1860 + difference 4 2) sourceC1860) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1860 + difference 2 4) (sourceB1860 + difference 4 2) sourceC1860) = raw26805 := by
      apply Matrix.ext; unfold tripleCharges sourceA1860 sourceB1860 sourceC1860 difference raw26805; decide +kernel
    rw [ha]
    exact (canonical26805 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1860 + difference 2 5) (sourceB1860 + difference 5 2) sourceC1860) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4581) := by
    have ha : (tripleCharges (sourceA1860 + difference 2 5) (sourceB1860 + difference 5 2) sourceC1860) = raw26806 := by
      apply Matrix.ext; unfold tripleCharges sourceA1860 sourceB1860 sourceC1860 difference raw26806; decide +kernel
    rw [ha]
    exact (canonical26806 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1860 + difference 3 0) (sourceB1860 + difference 0 3) sourceC1860) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4139) := by
    have ha : (tripleCharges (sourceA1860 + difference 3 0) (sourceB1860 + difference 0 3) sourceC1860) = raw26807 := by
      apply Matrix.ext; unfold tripleCharges sourceA1860 sourceB1860 sourceC1860 difference raw26807; decide +kernel
    rw [ha]
    exact (canonical26807 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1860 + difference 3 1) (sourceB1860 + difference 1 3) sourceC1860) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4513) := by
    have ha : (tripleCharges (sourceA1860 + difference 3 1) (sourceB1860 + difference 1 3) sourceC1860) = raw26808 := by
      apply Matrix.ext; unfold tripleCharges sourceA1860 sourceB1860 sourceC1860 difference raw26808; decide +kernel
    rw [ha]
    exact (canonical26808 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1860 + difference 3 2) (sourceB1860 + difference 2 3) sourceC1860) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1860 + difference 3 2) (sourceB1860 + difference 2 3) sourceC1860) = raw26809 := by
      apply Matrix.ext; unfold tripleCharges sourceA1860 sourceB1860 sourceC1860 difference raw26809; decide +kernel
    rw [ha]
    exact (canonical26809 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1860 + difference 3 4) (sourceB1860 + difference 4 3) sourceC1860) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1860 + difference 3 4) (sourceB1860 + difference 4 3) sourceC1860) = raw26810 := by
      apply Matrix.ext; unfold tripleCharges sourceA1860 sourceB1860 sourceC1860 difference raw26810; decide +kernel
    rw [ha]
    exact (canonical26810 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1860 + difference 3 5) (sourceB1860 + difference 5 3) sourceC1860) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4581) := by
    have ha : (tripleCharges (sourceA1860 + difference 3 5) (sourceB1860 + difference 5 3) sourceC1860) = raw26811 := by
      apply Matrix.ext; unfold tripleCharges sourceA1860 sourceB1860 sourceC1860 difference raw26811; decide +kernel
    rw [ha]
    exact (canonical26811 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1860 + difference 4 0) (sourceB1860 + difference 0 4) sourceC1860) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4139) := by
    have ha : (tripleCharges (sourceA1860 + difference 4 0) (sourceB1860 + difference 0 4) sourceC1860) = raw26812 := by
      apply Matrix.ext; unfold tripleCharges sourceA1860 sourceB1860 sourceC1860 difference raw26812; decide +kernel
    rw [ha]
    exact (canonical26812 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1860 + difference 4 1) (sourceB1860 + difference 1 4) sourceC1860) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4513) := by
    have ha : (tripleCharges (sourceA1860 + difference 4 1) (sourceB1860 + difference 1 4) sourceC1860) = raw26813 := by
      apply Matrix.ext; unfold tripleCharges sourceA1860 sourceB1860 sourceC1860 difference raw26813; decide +kernel
    rw [ha]
    exact (canonical26813 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1860 + difference 4 2) (sourceB1860 + difference 2 4) sourceC1860) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1860 + difference 4 2) (sourceB1860 + difference 2 4) sourceC1860) = raw26814 := by
      apply Matrix.ext; unfold tripleCharges sourceA1860 sourceB1860 sourceC1860 difference raw26814; decide +kernel
    rw [ha]
    exact (canonical26814 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1860 + difference 4 3) (sourceB1860 + difference 3 4) sourceC1860) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1860 + difference 4 3) (sourceB1860 + difference 3 4) sourceC1860) = raw26815 := by
      apply Matrix.ext; unfold tripleCharges sourceA1860 sourceB1860 sourceC1860 difference raw26815; decide +kernel
    rw [ha]
    exact (canonical26815 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1860 + difference 4 5) (sourceB1860 + difference 5 4) sourceC1860) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4581) := by
    have ha : (tripleCharges (sourceA1860 + difference 4 5) (sourceB1860 + difference 5 4) sourceC1860) = raw26816 := by
      apply Matrix.ext; unfold tripleCharges sourceA1860 sourceB1860 sourceC1860 difference raw26816; decide +kernel
    rw [ha]
    exact (canonical26816 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1860 + difference 5 0) (sourceB1860 + difference 0 5) sourceC1860) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4143) := by
    have ha : (tripleCharges (sourceA1860 + difference 5 0) (sourceB1860 + difference 0 5) sourceC1860) = raw26817 := by
      apply Matrix.ext; unfold tripleCharges sourceA1860 sourceB1860 sourceC1860 difference raw26817; decide +kernel
    rw [ha]
    exact (canonical26817 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1860 + difference 5 1) (sourceB1860 + difference 1 5) sourceC1860) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4516) := by
    have ha : (tripleCharges (sourceA1860 + difference 5 1) (sourceB1860 + difference 1 5) sourceC1860) = raw26818 := by
      apply Matrix.ext; unfold tripleCharges sourceA1860 sourceB1860 sourceC1860 difference raw26818; decide +kernel
    rw [ha]
    exact (canonical26818 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1860 + difference 5 2) (sourceB1860 + difference 2 5) sourceC1860) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4606) := by
    have ha : (tripleCharges (sourceA1860 + difference 5 2) (sourceB1860 + difference 2 5) sourceC1860) = raw26819 := by
      apply Matrix.ext; unfold tripleCharges sourceA1860 sourceB1860 sourceC1860 difference raw26819; decide +kernel
    rw [ha]
    exact (canonical26819 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1860 + difference 5 3) (sourceB1860 + difference 3 5) sourceC1860) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4606) := by
    have ha : (tripleCharges (sourceA1860 + difference 5 3) (sourceB1860 + difference 3 5) sourceC1860) = raw26820 := by
      apply Matrix.ext; unfold tripleCharges sourceA1860 sourceB1860 sourceC1860 difference raw26820; decide +kernel
    rw [ha]
    exact (canonical26820 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1860 + difference 5 4) (sourceB1860 + difference 4 5) sourceC1860) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4606) := by
    have ha : (tripleCharges (sourceA1860 + difference 5 4) (sourceB1860 + difference 4 5) sourceC1860) = raw26821 := by
      apply Matrix.ext; unfold tripleCharges sourceA1860 sourceB1860 sourceC1860 difference raw26821; decide +kernel
    rw [ha]
    exact (canonical26821 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1860 sourceB1860 sourceC1860
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1860, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1861 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1861 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceC1861 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceForm1861 : Integer.Sparse Master := [(Sum.inr 567, 3), (Sum.inr 571, 1), (Sum.inr 599, 1), (Sum.inr 1097, 3), (Sum.inr 1100, 1), (Sum.inr 1200, 3), (Sum.inr 1235, 1), (Sum.inr 1236, 6), (Sum.inr 1240, 3), (Sum.inr 1299, 3), (Sum.inr 2880, 1), (Sum.inr 3076, 1), (Sum.inr 3100, 3)]

theorem sourceEq1861 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1861 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1861 + difference 0 1) (sourceB1861 + difference 1 0) sourceC1861) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2880) := by
    have ha : (tripleCharges (sourceA1861 + difference 0 1) (sourceB1861 + difference 1 0) sourceC1861) = raw26822 := by
      apply Matrix.ext; unfold tripleCharges sourceA1861 sourceB1861 sourceC1861 difference raw26822; decide +kernel
    rw [ha]
    exact (canonical26822 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1861 + difference 0 2) (sourceB1861 + difference 2 0) sourceC1861) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3100) := by
    have ha : (tripleCharges (sourceA1861 + difference 0 2) (sourceB1861 + difference 2 0) sourceC1861) = raw26823 := by
      apply Matrix.ext; unfold tripleCharges sourceA1861 sourceB1861 sourceC1861 difference raw26823; decide +kernel
    rw [ha]
    exact (canonical26823 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1861 + difference 0 3) (sourceB1861 + difference 3 0) sourceC1861) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3100) := by
    have ha : (tripleCharges (sourceA1861 + difference 0 3) (sourceB1861 + difference 3 0) sourceC1861) = raw26824 := by
      apply Matrix.ext; unfold tripleCharges sourceA1861 sourceB1861 sourceC1861 difference raw26824; decide +kernel
    rw [ha]
    exact (canonical26824 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1861 + difference 0 4) (sourceB1861 + difference 4 0) sourceC1861) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3100) := by
    have ha : (tripleCharges (sourceA1861 + difference 0 4) (sourceB1861 + difference 4 0) sourceC1861) = raw26825 := by
      apply Matrix.ext; unfold tripleCharges sourceA1861 sourceB1861 sourceC1861 difference raw26825; decide +kernel
    rw [ha]
    exact (canonical26825 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1861 + difference 0 5) (sourceB1861 + difference 5 0) sourceC1861) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3076) := by
    have ha : (tripleCharges (sourceA1861 + difference 0 5) (sourceB1861 + difference 5 0) sourceC1861) = raw26826 := by
      apply Matrix.ext; unfold tripleCharges sourceA1861 sourceB1861 sourceC1861 difference raw26826; decide +kernel
    rw [ha]
    exact (canonical26826 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1861 + difference 1 0) (sourceB1861 + difference 0 1) sourceC1861) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 599) := by
    have ha : (tripleCharges (sourceA1861 + difference 1 0) (sourceB1861 + difference 0 1) sourceC1861) = raw26827 := by
      apply Matrix.ext; unfold tripleCharges sourceA1861 sourceB1861 sourceC1861 difference raw26827; decide +kernel
    rw [ha]
    exact (canonical26827 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1861 + difference 1 2) (sourceB1861 + difference 2 1) sourceC1861) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1299) := by
    have ha : (tripleCharges (sourceA1861 + difference 1 2) (sourceB1861 + difference 2 1) sourceC1861) = raw26828 := by
      apply Matrix.ext; unfold tripleCharges sourceA1861 sourceB1861 sourceC1861 difference raw26828; decide +kernel
    rw [ha]
    exact (canonical26828 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1861 + difference 1 3) (sourceB1861 + difference 3 1) sourceC1861) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1299) := by
    have ha : (tripleCharges (sourceA1861 + difference 1 3) (sourceB1861 + difference 3 1) sourceC1861) = raw26829 := by
      apply Matrix.ext; unfold tripleCharges sourceA1861 sourceB1861 sourceC1861 difference raw26829; decide +kernel
    rw [ha]
    exact (canonical26829 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1861 + difference 1 4) (sourceB1861 + difference 4 1) sourceC1861) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1299) := by
    have ha : (tripleCharges (sourceA1861 + difference 1 4) (sourceB1861 + difference 4 1) sourceC1861) = raw26830 := by
      apply Matrix.ext; unfold tripleCharges sourceA1861 sourceB1861 sourceC1861 difference raw26830; decide +kernel
    rw [ha]
    exact (canonical26830 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1861 + difference 1 5) (sourceB1861 + difference 5 1) sourceC1861) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1235) := by
    have ha : (tripleCharges (sourceA1861 + difference 1 5) (sourceB1861 + difference 5 1) sourceC1861) = raw26831 := by
      apply Matrix.ext; unfold tripleCharges sourceA1861 sourceB1861 sourceC1861 difference raw26831; decide +kernel
    rw [ha]
    exact (canonical26831 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1861 + difference 2 0) (sourceB1861 + difference 0 2) sourceC1861) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 567) := by
    have ha : (tripleCharges (sourceA1861 + difference 2 0) (sourceB1861 + difference 0 2) sourceC1861) = raw26832 := by
      apply Matrix.ext; unfold tripleCharges sourceA1861 sourceB1861 sourceC1861 difference raw26832; decide +kernel
    rw [ha]
    exact (canonical26832 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1861 + difference 2 1) (sourceB1861 + difference 1 2) sourceC1861) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1097) := by
    have ha : (tripleCharges (sourceA1861 + difference 2 1) (sourceB1861 + difference 1 2) sourceC1861) = raw26833 := by
      apply Matrix.ext; unfold tripleCharges sourceA1861 sourceB1861 sourceC1861 difference raw26833; decide +kernel
    rw [ha]
    exact (canonical26833 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1861 + difference 2 3) (sourceB1861 + difference 3 2) sourceC1861) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1236) := by
    have ha : (tripleCharges (sourceA1861 + difference 2 3) (sourceB1861 + difference 3 2) sourceC1861) = raw26834 := by
      apply Matrix.ext; unfold tripleCharges sourceA1861 sourceB1861 sourceC1861 difference raw26834; decide +kernel
    rw [ha]
    exact (canonical26834 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1861 + difference 2 4) (sourceB1861 + difference 4 2) sourceC1861) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1236) := by
    have ha : (tripleCharges (sourceA1861 + difference 2 4) (sourceB1861 + difference 4 2) sourceC1861) = raw26835 := by
      apply Matrix.ext; unfold tripleCharges sourceA1861 sourceB1861 sourceC1861 difference raw26835; decide +kernel
    rw [ha]
    exact (canonical26835 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1861 + difference 2 5) (sourceB1861 + difference 5 2) sourceC1861) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1200) := by
    have ha : (tripleCharges (sourceA1861 + difference 2 5) (sourceB1861 + difference 5 2) sourceC1861) = raw26836 := by
      apply Matrix.ext; unfold tripleCharges sourceA1861 sourceB1861 sourceC1861 difference raw26836; decide +kernel
    rw [ha]
    exact (canonical26836 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1861 + difference 3 0) (sourceB1861 + difference 0 3) sourceC1861) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 567) := by
    have ha : (tripleCharges (sourceA1861 + difference 3 0) (sourceB1861 + difference 0 3) sourceC1861) = raw26837 := by
      apply Matrix.ext; unfold tripleCharges sourceA1861 sourceB1861 sourceC1861 difference raw26837; decide +kernel
    rw [ha]
    exact (canonical26837 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1861 + difference 3 1) (sourceB1861 + difference 1 3) sourceC1861) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1097) := by
    have ha : (tripleCharges (sourceA1861 + difference 3 1) (sourceB1861 + difference 1 3) sourceC1861) = raw26838 := by
      apply Matrix.ext; unfold tripleCharges sourceA1861 sourceB1861 sourceC1861 difference raw26838; decide +kernel
    rw [ha]
    exact (canonical26838 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1861 + difference 3 2) (sourceB1861 + difference 2 3) sourceC1861) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1236) := by
    have ha : (tripleCharges (sourceA1861 + difference 3 2) (sourceB1861 + difference 2 3) sourceC1861) = raw26839 := by
      apply Matrix.ext; unfold tripleCharges sourceA1861 sourceB1861 sourceC1861 difference raw26839; decide +kernel
    rw [ha]
    exact (canonical26839 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1861 + difference 3 4) (sourceB1861 + difference 4 3) sourceC1861) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1236) := by
    have ha : (tripleCharges (sourceA1861 + difference 3 4) (sourceB1861 + difference 4 3) sourceC1861) = raw26840 := by
      apply Matrix.ext; unfold tripleCharges sourceA1861 sourceB1861 sourceC1861 difference raw26840; decide +kernel
    rw [ha]
    exact (canonical26840 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1861 + difference 3 5) (sourceB1861 + difference 5 3) sourceC1861) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1200) := by
    have ha : (tripleCharges (sourceA1861 + difference 3 5) (sourceB1861 + difference 5 3) sourceC1861) = raw26841 := by
      apply Matrix.ext; unfold tripleCharges sourceA1861 sourceB1861 sourceC1861 difference raw26841; decide +kernel
    rw [ha]
    exact (canonical26841 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1861 + difference 4 0) (sourceB1861 + difference 0 4) sourceC1861) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 567) := by
    have ha : (tripleCharges (sourceA1861 + difference 4 0) (sourceB1861 + difference 0 4) sourceC1861) = raw26842 := by
      apply Matrix.ext; unfold tripleCharges sourceA1861 sourceB1861 sourceC1861 difference raw26842; decide +kernel
    rw [ha]
    exact (canonical26842 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1861 + difference 4 1) (sourceB1861 + difference 1 4) sourceC1861) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1097) := by
    have ha : (tripleCharges (sourceA1861 + difference 4 1) (sourceB1861 + difference 1 4) sourceC1861) = raw26843 := by
      apply Matrix.ext; unfold tripleCharges sourceA1861 sourceB1861 sourceC1861 difference raw26843; decide +kernel
    rw [ha]
    exact (canonical26843 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1861 + difference 4 2) (sourceB1861 + difference 2 4) sourceC1861) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1236) := by
    have ha : (tripleCharges (sourceA1861 + difference 4 2) (sourceB1861 + difference 2 4) sourceC1861) = raw26844 := by
      apply Matrix.ext; unfold tripleCharges sourceA1861 sourceB1861 sourceC1861 difference raw26844; decide +kernel
    rw [ha]
    exact (canonical26844 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1861 + difference 4 3) (sourceB1861 + difference 3 4) sourceC1861) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1236) := by
    have ha : (tripleCharges (sourceA1861 + difference 4 3) (sourceB1861 + difference 3 4) sourceC1861) = raw26845 := by
      apply Matrix.ext; unfold tripleCharges sourceA1861 sourceB1861 sourceC1861 difference raw26845; decide +kernel
    rw [ha]
    exact (canonical26845 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1861 + difference 4 5) (sourceB1861 + difference 5 4) sourceC1861) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1200) := by
    have ha : (tripleCharges (sourceA1861 + difference 4 5) (sourceB1861 + difference 5 4) sourceC1861) = raw26846 := by
      apply Matrix.ext; unfold tripleCharges sourceA1861 sourceB1861 sourceC1861 difference raw26846; decide +kernel
    rw [ha]
    exact (canonical26846 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1861 + difference 5 0) (sourceB1861 + difference 0 5) sourceC1861) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 571) := by
    have ha : (tripleCharges (sourceA1861 + difference 5 0) (sourceB1861 + difference 0 5) sourceC1861) = raw26847 := by
      apply Matrix.ext; unfold tripleCharges sourceA1861 sourceB1861 sourceC1861 difference raw26847; decide +kernel
    rw [ha]
    exact (canonical26847 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1861 + difference 5 1) (sourceB1861 + difference 1 5) sourceC1861) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1100) := by
    have ha : (tripleCharges (sourceA1861 + difference 5 1) (sourceB1861 + difference 1 5) sourceC1861) = raw26848 := by
      apply Matrix.ext; unfold tripleCharges sourceA1861 sourceB1861 sourceC1861 difference raw26848; decide +kernel
    rw [ha]
    exact (canonical26848 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1861 + difference 5 2) (sourceB1861 + difference 2 5) sourceC1861) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1240) := by
    have ha : (tripleCharges (sourceA1861 + difference 5 2) (sourceB1861 + difference 2 5) sourceC1861) = raw26849 := by
      apply Matrix.ext; unfold tripleCharges sourceA1861 sourceB1861 sourceC1861 difference raw26849; decide +kernel
    rw [ha]
    exact (canonical26849 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1861 + difference 5 3) (sourceB1861 + difference 3 5) sourceC1861) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1240) := by
    have ha : (tripleCharges (sourceA1861 + difference 5 3) (sourceB1861 + difference 3 5) sourceC1861) = raw26850 := by
      apply Matrix.ext; unfold tripleCharges sourceA1861 sourceB1861 sourceC1861 difference raw26850; decide +kernel
    rw [ha]
    exact (canonical26850 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1861 + difference 5 4) (sourceB1861 + difference 4 5) sourceC1861) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1240) := by
    have ha : (tripleCharges (sourceA1861 + difference 5 4) (sourceB1861 + difference 4 5) sourceC1861) = raw26851 := by
      apply Matrix.ext; unfold tripleCharges sourceA1861 sourceB1861 sourceC1861 difference raw26851; decide +kernel
    rw [ha]
    exact (canonical26851 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1861 sourceB1861 sourceC1861
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1861, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1862 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceB1862 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceC1862 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceForm1862 : Integer.Sparse Master := [(Sum.inr 4417, 3), (Sum.inr 4422, 1), (Sum.inr 4455, 1), (Sum.inr 4456, 3), (Sum.inr 4473, 1), (Sum.inr 4497, 1), (Sum.inr 4566, 3), (Sum.inr 4569, 1), (Sum.inr 4595, 3), (Sum.inr 4599, 6), (Sum.inr 4601, 3), (Sum.inr 4618, 1), (Sum.inr 4622, 3)]

theorem sourceEq1862 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1862 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1862 + difference 0 1) (sourceB1862 + difference 1 0) sourceC1862) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4473) := by
    have ha : (tripleCharges (sourceA1862 + difference 0 1) (sourceB1862 + difference 1 0) sourceC1862) = raw26852 := by
      apply Matrix.ext; unfold tripleCharges sourceA1862 sourceB1862 sourceC1862 difference raw26852; decide +kernel
    rw [ha]
    exact (canonical26852 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1862 + difference 0 2) (sourceB1862 + difference 2 0) sourceC1862) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4456) := by
    have ha : (tripleCharges (sourceA1862 + difference 0 2) (sourceB1862 + difference 2 0) sourceC1862) = raw26853 := by
      apply Matrix.ext; unfold tripleCharges sourceA1862 sourceB1862 sourceC1862 difference raw26853; decide +kernel
    rw [ha]
    exact (canonical26853 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1862 + difference 0 3) (sourceB1862 + difference 3 0) sourceC1862) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4456) := by
    have ha : (tripleCharges (sourceA1862 + difference 0 3) (sourceB1862 + difference 3 0) sourceC1862) = raw26854 := by
      apply Matrix.ext; unfold tripleCharges sourceA1862 sourceB1862 sourceC1862 difference raw26854; decide +kernel
    rw [ha]
    exact (canonical26854 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1862 + difference 0 4) (sourceB1862 + difference 4 0) sourceC1862) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4456) := by
    have ha : (tripleCharges (sourceA1862 + difference 0 4) (sourceB1862 + difference 4 0) sourceC1862) = raw26855 := by
      apply Matrix.ext; unfold tripleCharges sourceA1862 sourceB1862 sourceC1862 difference raw26855; decide +kernel
    rw [ha]
    exact (canonical26855 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1862 + difference 0 5) (sourceB1862 + difference 5 0) sourceC1862) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4455) := by
    have ha : (tripleCharges (sourceA1862 + difference 0 5) (sourceB1862 + difference 5 0) sourceC1862) = raw26856 := by
      apply Matrix.ext; unfold tripleCharges sourceA1862 sourceB1862 sourceC1862 difference raw26856; decide +kernel
    rw [ha]
    exact (canonical26856 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1862 + difference 1 0) (sourceB1862 + difference 0 1) sourceC1862) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4497) := by
    have ha : (tripleCharges (sourceA1862 + difference 1 0) (sourceB1862 + difference 0 1) sourceC1862) = raw26857 := by
      apply Matrix.ext; unfold tripleCharges sourceA1862 sourceB1862 sourceC1862 difference raw26857; decide +kernel
    rw [ha]
    exact (canonical26857 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1862 + difference 1 2) (sourceB1862 + difference 2 1) sourceC1862) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4622) := by
    have ha : (tripleCharges (sourceA1862 + difference 1 2) (sourceB1862 + difference 2 1) sourceC1862) = raw26694 := by
      apply Matrix.ext; unfold tripleCharges sourceA1862 sourceB1862 sourceC1862 difference raw26694; decide +kernel
    rw [ha]
    exact (canonical26694 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1862 + difference 1 3) (sourceB1862 + difference 3 1) sourceC1862) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4622) := by
    have ha : (tripleCharges (sourceA1862 + difference 1 3) (sourceB1862 + difference 3 1) sourceC1862) = raw26690 := by
      apply Matrix.ext; unfold tripleCharges sourceA1862 sourceB1862 sourceC1862 difference raw26690; decide +kernel
    rw [ha]
    exact (canonical26690 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1862 + difference 1 4) (sourceB1862 + difference 4 1) sourceC1862) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4622) := by
    have ha : (tripleCharges (sourceA1862 + difference 1 4) (sourceB1862 + difference 4 1) sourceC1862) = raw26858 := by
      apply Matrix.ext; unfold tripleCharges sourceA1862 sourceB1862 sourceC1862 difference raw26858; decide +kernel
    rw [ha]
    exact (canonical26858 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1862 + difference 1 5) (sourceB1862 + difference 5 1) sourceC1862) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4618) := by
    have ha : (tripleCharges (sourceA1862 + difference 1 5) (sourceB1862 + difference 5 1) sourceC1862) = raw26859 := by
      apply Matrix.ext; unfold tripleCharges sourceA1862 sourceB1862 sourceC1862 difference raw26859; decide +kernel
    rw [ha]
    exact (canonical26859 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1862 + difference 2 0) (sourceB1862 + difference 0 2) sourceC1862) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4417) := by
    have ha : (tripleCharges (sourceA1862 + difference 2 0) (sourceB1862 + difference 0 2) sourceC1862) = raw26860 := by
      apply Matrix.ext; unfold tripleCharges sourceA1862 sourceB1862 sourceC1862 difference raw26860; decide +kernel
    rw [ha]
    exact (canonical26860 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1862 + difference 2 1) (sourceB1862 + difference 1 2) sourceC1862) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4566) := by
    have ha : (tripleCharges (sourceA1862 + difference 2 1) (sourceB1862 + difference 1 2) sourceC1862) = raw26861 := by
      apply Matrix.ext; unfold tripleCharges sourceA1862 sourceB1862 sourceC1862 difference raw26861; decide +kernel
    rw [ha]
    exact (canonical26861 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1862 + difference 2 3) (sourceB1862 + difference 3 2) sourceC1862) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4599) := by
    have ha : (tripleCharges (sourceA1862 + difference 2 3) (sourceB1862 + difference 3 2) sourceC1862) = raw26862 := by
      apply Matrix.ext; unfold tripleCharges sourceA1862 sourceB1862 sourceC1862 difference raw26862; decide +kernel
    rw [ha]
    exact (canonical26862 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1862 + difference 2 4) (sourceB1862 + difference 4 2) sourceC1862) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4599) := by
    have ha : (tripleCharges (sourceA1862 + difference 2 4) (sourceB1862 + difference 4 2) sourceC1862) = raw26863 := by
      apply Matrix.ext; unfold tripleCharges sourceA1862 sourceB1862 sourceC1862 difference raw26863; decide +kernel
    rw [ha]
    exact (canonical26863 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1862 + difference 2 5) (sourceB1862 + difference 5 2) sourceC1862) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4595) := by
    have ha : (tripleCharges (sourceA1862 + difference 2 5) (sourceB1862 + difference 5 2) sourceC1862) = raw26864 := by
      apply Matrix.ext; unfold tripleCharges sourceA1862 sourceB1862 sourceC1862 difference raw26864; decide +kernel
    rw [ha]
    exact (canonical26864 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1862 + difference 3 0) (sourceB1862 + difference 0 3) sourceC1862) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4417) := by
    have ha : (tripleCharges (sourceA1862 + difference 3 0) (sourceB1862 + difference 0 3) sourceC1862) = raw26865 := by
      apply Matrix.ext; unfold tripleCharges sourceA1862 sourceB1862 sourceC1862 difference raw26865; decide +kernel
    rw [ha]
    exact (canonical26865 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1862 + difference 3 1) (sourceB1862 + difference 1 3) sourceC1862) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4566) := by
    have ha : (tripleCharges (sourceA1862 + difference 3 1) (sourceB1862 + difference 1 3) sourceC1862) = raw26866 := by
      apply Matrix.ext; unfold tripleCharges sourceA1862 sourceB1862 sourceC1862 difference raw26866; decide +kernel
    rw [ha]
    exact (canonical26866 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1862 + difference 3 2) (sourceB1862 + difference 2 3) sourceC1862) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4599) := by
    have ha : (tripleCharges (sourceA1862 + difference 3 2) (sourceB1862 + difference 2 3) sourceC1862) = raw26867 := by
      apply Matrix.ext; unfold tripleCharges sourceA1862 sourceB1862 sourceC1862 difference raw26867; decide +kernel
    rw [ha]
    exact (canonical26867 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1862 + difference 3 4) (sourceB1862 + difference 4 3) sourceC1862) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4599) := by
    have ha : (tripleCharges (sourceA1862 + difference 3 4) (sourceB1862 + difference 4 3) sourceC1862) = raw26868 := by
      apply Matrix.ext; unfold tripleCharges sourceA1862 sourceB1862 sourceC1862 difference raw26868; decide +kernel
    rw [ha]
    exact (canonical26868 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1862 + difference 3 5) (sourceB1862 + difference 5 3) sourceC1862) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4595) := by
    have ha : (tripleCharges (sourceA1862 + difference 3 5) (sourceB1862 + difference 5 3) sourceC1862) = raw26869 := by
      apply Matrix.ext; unfold tripleCharges sourceA1862 sourceB1862 sourceC1862 difference raw26869; decide +kernel
    rw [ha]
    exact (canonical26869 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1862 + difference 4 0) (sourceB1862 + difference 0 4) sourceC1862) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4417) := by
    have ha : (tripleCharges (sourceA1862 + difference 4 0) (sourceB1862 + difference 0 4) sourceC1862) = raw26870 := by
      apply Matrix.ext; unfold tripleCharges sourceA1862 sourceB1862 sourceC1862 difference raw26870; decide +kernel
    rw [ha]
    exact (canonical26870 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1862 + difference 4 1) (sourceB1862 + difference 1 4) sourceC1862) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4566) := by
    have ha : (tripleCharges (sourceA1862 + difference 4 1) (sourceB1862 + difference 1 4) sourceC1862) = raw26871 := by
      apply Matrix.ext; unfold tripleCharges sourceA1862 sourceB1862 sourceC1862 difference raw26871; decide +kernel
    rw [ha]
    exact (canonical26871 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1862 + difference 4 2) (sourceB1862 + difference 2 4) sourceC1862) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4599) := by
    have ha : (tripleCharges (sourceA1862 + difference 4 2) (sourceB1862 + difference 2 4) sourceC1862) = raw26872 := by
      apply Matrix.ext; unfold tripleCharges sourceA1862 sourceB1862 sourceC1862 difference raw26872; decide +kernel
    rw [ha]
    exact (canonical26872 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1862 + difference 4 3) (sourceB1862 + difference 3 4) sourceC1862) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4599) := by
    have ha : (tripleCharges (sourceA1862 + difference 4 3) (sourceB1862 + difference 3 4) sourceC1862) = raw26873 := by
      apply Matrix.ext; unfold tripleCharges sourceA1862 sourceB1862 sourceC1862 difference raw26873; decide +kernel
    rw [ha]
    exact (canonical26873 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1862 + difference 4 5) (sourceB1862 + difference 5 4) sourceC1862) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4595) := by
    have ha : (tripleCharges (sourceA1862 + difference 4 5) (sourceB1862 + difference 5 4) sourceC1862) = raw26874 := by
      apply Matrix.ext; unfold tripleCharges sourceA1862 sourceB1862 sourceC1862 difference raw26874; decide +kernel
    rw [ha]
    exact (canonical26874 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1862 + difference 5 0) (sourceB1862 + difference 0 5) sourceC1862) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4422) := by
    have ha : (tripleCharges (sourceA1862 + difference 5 0) (sourceB1862 + difference 0 5) sourceC1862) = raw26875 := by
      apply Matrix.ext; unfold tripleCharges sourceA1862 sourceB1862 sourceC1862 difference raw26875; decide +kernel
    rw [ha]
    exact (canonical26875 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1862 + difference 5 1) (sourceB1862 + difference 1 5) sourceC1862) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4569) := by
    have ha : (tripleCharges (sourceA1862 + difference 5 1) (sourceB1862 + difference 1 5) sourceC1862) = raw26876 := by
      apply Matrix.ext; unfold tripleCharges sourceA1862 sourceB1862 sourceC1862 difference raw26876; decide +kernel
    rw [ha]
    exact (canonical26876 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1862 + difference 5 2) (sourceB1862 + difference 2 5) sourceC1862) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4601) := by
    have ha : (tripleCharges (sourceA1862 + difference 5 2) (sourceB1862 + difference 2 5) sourceC1862) = raw26692 := by
      apply Matrix.ext; unfold tripleCharges sourceA1862 sourceB1862 sourceC1862 difference raw26692; decide +kernel
    rw [ha]
    exact (canonical26692 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1862 + difference 5 3) (sourceB1862 + difference 3 5) sourceC1862) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4601) := by
    have ha : (tripleCharges (sourceA1862 + difference 5 3) (sourceB1862 + difference 3 5) sourceC1862) = raw26688 := by
      apply Matrix.ext; unfold tripleCharges sourceA1862 sourceB1862 sourceC1862 difference raw26688; decide +kernel
    rw [ha]
    exact (canonical26688 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1862 + difference 5 4) (sourceB1862 + difference 4 5) sourceC1862) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4601) := by
    have ha : (tripleCharges (sourceA1862 + difference 5 4) (sourceB1862 + difference 4 5) sourceC1862) = raw26877 := by
      apply Matrix.ext; unfold tripleCharges sourceA1862 sourceB1862 sourceC1862 difference raw26877; decide +kernel
    rw [ha]
    exact (canonical26877 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1862 sourceB1862 sourceC1862
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1862, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1863 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1863 : Charge := ![2, -2, 1, 0, 0, -1]
def sourceC1863 : Charge := ![2, 2, -2, -1, -1, 0]
def sourceForm1863 : Integer.Sparse Master := [(Sum.inr 1183, 1), (Sum.inr 2398, 1), (Sum.inr 2669, 2), (Sum.inr 2676, 1), (Sum.inr 2684, 1), (Sum.inr 4088, -1)]

theorem sourceEq1863 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1863 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1863 + difference 0 0) (sourceB1863 + difference 0 0) sourceC1863) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1183) := by
    have ha : (tripleCharges (sourceA1863 + difference 0 0) (sourceB1863 + difference 0 0) sourceC1863) = raw26878 := by
      apply Matrix.ext; unfold tripleCharges sourceA1863 sourceB1863 sourceC1863 difference raw26878; decide +kernel
    rw [ha]
    exact (canonical26878 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1863 + difference 0 1) (sourceB1863 + difference 1 0) sourceC1863) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2398) := by
    have ha : (tripleCharges (sourceA1863 + difference 0 1) (sourceB1863 + difference 1 0) sourceC1863) = raw26879 := by
      apply Matrix.ext; unfold tripleCharges sourceA1863 sourceB1863 sourceC1863 difference raw26879; decide +kernel
    rw [ha]
    exact (canonical26879 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1863 + difference 0 2) (sourceB1863 + difference 2 0) sourceC1863) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2676) := by
    have ha : (tripleCharges (sourceA1863 + difference 0 2) (sourceB1863 + difference 2 0) sourceC1863) = raw26880 := by
      apply Matrix.ext; unfold tripleCharges sourceA1863 sourceB1863 sourceC1863 difference raw26880; decide +kernel
    rw [ha]
    exact (canonical26880 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1863 + difference 0 3) (sourceB1863 + difference 3 0) sourceC1863) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2669) := by
    have ha : (tripleCharges (sourceA1863 + difference 0 3) (sourceB1863 + difference 3 0) sourceC1863) = raw26881 := by
      apply Matrix.ext; unfold tripleCharges sourceA1863 sourceB1863 sourceC1863 difference raw26881; decide +kernel
    rw [ha]
    exact (canonical26881 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1863 + difference 0 4) (sourceB1863 + difference 4 0) sourceC1863) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2669) := by
    have ha : (tripleCharges (sourceA1863 + difference 0 4) (sourceB1863 + difference 4 0) sourceC1863) = raw26882 := by
      apply Matrix.ext; unfold tripleCharges sourceA1863 sourceB1863 sourceC1863 difference raw26882; decide +kernel
    rw [ha]
    exact (canonical26882 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1863 + difference 0 5) (sourceB1863 + difference 5 0) sourceC1863) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2684) := by
    have ha : (tripleCharges (sourceA1863 + difference 0 5) (sourceB1863 + difference 5 0) sourceC1863) = raw26883 := by
      apply Matrix.ext; unfold tripleCharges sourceA1863 sourceB1863 sourceC1863 difference raw26883; decide +kernel
    rw [ha]
    exact (canonical26883 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1863 + sourceB1863) sourceC1863) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA1863 + sourceB1863) sourceC1863) = raw26884 := by
      apply Matrix.ext; unfold doubleCharges sourceA1863 sourceB1863 sourceC1863 raw26884; decide +kernel
    rw [ha]
    exact (canonical26884 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1863 sourceB1863 sourceC1863
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1863, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1864 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1864 : Charge := ![2, -2, 0, 0, 0, 0]
def sourceC1864 : Charge := ![2, 2, -1, -1, -1, -1]
def sourceForm1864 : Integer.Sparse Master := [(Sum.inr 1187, 1), (Sum.inr 2402, 1), (Sum.inr 2671, 4), (Sum.inr 4087, -1)]

theorem sourceEq1864 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1864 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1864 + difference 0 0) (sourceB1864 + difference 0 0) sourceC1864) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1187) := by
    have ha : (tripleCharges (sourceA1864 + difference 0 0) (sourceB1864 + difference 0 0) sourceC1864) = raw26885 := by
      apply Matrix.ext; unfold tripleCharges sourceA1864 sourceB1864 sourceC1864 difference raw26885; decide +kernel
    rw [ha]
    exact (canonical26885 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1864 + difference 0 1) (sourceB1864 + difference 1 0) sourceC1864) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2402) := by
    have ha : (tripleCharges (sourceA1864 + difference 0 1) (sourceB1864 + difference 1 0) sourceC1864) = raw26886 := by
      apply Matrix.ext; unfold tripleCharges sourceA1864 sourceB1864 sourceC1864 difference raw26886; decide +kernel
    rw [ha]
    exact (canonical26886 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1864 + difference 0 2) (sourceB1864 + difference 2 0) sourceC1864) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2671) := by
    have ha : (tripleCharges (sourceA1864 + difference 0 2) (sourceB1864 + difference 2 0) sourceC1864) = raw26887 := by
      apply Matrix.ext; unfold tripleCharges sourceA1864 sourceB1864 sourceC1864 difference raw26887; decide +kernel
    rw [ha]
    exact (canonical26887 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1864 + difference 0 3) (sourceB1864 + difference 3 0) sourceC1864) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2671) := by
    have ha : (tripleCharges (sourceA1864 + difference 0 3) (sourceB1864 + difference 3 0) sourceC1864) = raw26888 := by
      apply Matrix.ext; unfold tripleCharges sourceA1864 sourceB1864 sourceC1864 difference raw26888; decide +kernel
    rw [ha]
    exact (canonical26888 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1864 + difference 0 4) (sourceB1864 + difference 4 0) sourceC1864) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2671) := by
    have ha : (tripleCharges (sourceA1864 + difference 0 4) (sourceB1864 + difference 4 0) sourceC1864) = raw26889 := by
      apply Matrix.ext; unfold tripleCharges sourceA1864 sourceB1864 sourceC1864 difference raw26889; decide +kernel
    rw [ha]
    exact (canonical26889 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1864 + difference 0 5) (sourceB1864 + difference 5 0) sourceC1864) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2671) := by
    have ha : (tripleCharges (sourceA1864 + difference 0 5) (sourceB1864 + difference 5 0) sourceC1864) = raw26890 := by
      apply Matrix.ext; unfold tripleCharges sourceA1864 sourceB1864 sourceC1864 difference raw26890; decide +kernel
    rw [ha]
    exact (canonical26890 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1864 + sourceB1864) sourceC1864) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4087) := by
    have ha : (doubleCharges (sourceA1864 + sourceB1864) sourceC1864) = raw26891 := by
      apply Matrix.ext; unfold doubleCharges sourceA1864 sourceB1864 sourceC1864 raw26891; decide +kernel
    rw [ha]
    exact (canonical26891 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1864 sourceB1864 sourceC1864
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1864, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1865 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1865 : Charge := ![2, -2, 0, 0, 0, 0]
def sourceC1865 : Charge := ![2, 2, -1, -1, -1, -1]
def sourceForm1865 : Integer.Sparse Master := [(Sum.inr 1100, 4), (Sum.inr 1187, 1), (Sum.inr 2402, 1), (Sum.inr 4087, -1)]

theorem sourceEq1865 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1865 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1865 + difference 0 1) (sourceB1865 + difference 1 0) sourceC1865) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2402) := by
    have ha : (tripleCharges (sourceA1865 + difference 0 1) (sourceB1865 + difference 1 0) sourceC1865) = raw26886 := by
      apply Matrix.ext; unfold tripleCharges sourceA1865 sourceB1865 sourceC1865 difference raw26886; decide +kernel
    rw [ha]
    exact (canonical26886 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1865 + difference 1 1) (sourceB1865 + difference 1 1) sourceC1865) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1187) := by
    have ha : (tripleCharges (sourceA1865 + difference 1 1) (sourceB1865 + difference 1 1) sourceC1865) = raw26885 := by
      apply Matrix.ext; unfold tripleCharges sourceA1865 sourceB1865 sourceC1865 difference raw26885; decide +kernel
    rw [ha]
    exact (canonical26885 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1865 + difference 2 1) (sourceB1865 + difference 1 2) sourceC1865) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1100) := by
    have ha : (tripleCharges (sourceA1865 + difference 2 1) (sourceB1865 + difference 1 2) sourceC1865) = raw26892 := by
      apply Matrix.ext; unfold tripleCharges sourceA1865 sourceB1865 sourceC1865 difference raw26892; decide +kernel
    rw [ha]
    exact (canonical26892 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1865 + difference 3 1) (sourceB1865 + difference 1 3) sourceC1865) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1100) := by
    have ha : (tripleCharges (sourceA1865 + difference 3 1) (sourceB1865 + difference 1 3) sourceC1865) = raw26893 := by
      apply Matrix.ext; unfold tripleCharges sourceA1865 sourceB1865 sourceC1865 difference raw26893; decide +kernel
    rw [ha]
    exact (canonical26893 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1865 + difference 4 1) (sourceB1865 + difference 1 4) sourceC1865) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1100) := by
    have ha : (tripleCharges (sourceA1865 + difference 4 1) (sourceB1865 + difference 1 4) sourceC1865) = raw26894 := by
      apply Matrix.ext; unfold tripleCharges sourceA1865 sourceB1865 sourceC1865 difference raw26894; decide +kernel
    rw [ha]
    exact (canonical26894 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1865 + difference 5 1) (sourceB1865 + difference 1 5) sourceC1865) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1100) := by
    have ha : (tripleCharges (sourceA1865 + difference 5 1) (sourceB1865 + difference 1 5) sourceC1865) = raw26895 := by
      apply Matrix.ext; unfold tripleCharges sourceA1865 sourceB1865 sourceC1865 difference raw26895; decide +kernel
    rw [ha]
    exact (canonical26895 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1865 + sourceB1865) sourceC1865) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4087) := by
    have ha : (doubleCharges (sourceA1865 + sourceB1865) sourceC1865) = raw26891 := by
      apply Matrix.ext; unfold doubleCharges sourceA1865 sourceB1865 sourceC1865 raw26891; decide +kernel
    rw [ha]
    exact (canonical26891 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1865 sourceB1865 sourceC1865
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1865, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1866 : Charge := ![2, -2, 0, 0, 0, 0]
def sourceB1866 : Charge := ![2, 2, -1, -1, -1, -1]
def sourceC1866 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceForm1866 : Integer.Sparse Master := [(Sum.inr 1545, 4), (Sum.inr 1621, 1), (Sum.inr 3244, 1), (Sum.inr 4068, -1)]

theorem sourceEq1866 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1866 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1866 + difference 0 0) (sourceB1866 + difference 0 0) sourceC1866) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3244) := by
    have ha : (tripleCharges (sourceA1866 + difference 0 0) (sourceB1866 + difference 0 0) sourceC1866) = raw26896 := by
      apply Matrix.ext; unfold tripleCharges sourceA1866 sourceB1866 sourceC1866 difference raw26896; decide +kernel
    rw [ha]
    exact (canonical26896 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1866 + difference 1 0) (sourceB1866 + difference 0 1) sourceC1866) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1621) := by
    have ha : (tripleCharges (sourceA1866 + difference 1 0) (sourceB1866 + difference 0 1) sourceC1866) = raw26897 := by
      apply Matrix.ext; unfold tripleCharges sourceA1866 sourceB1866 sourceC1866 difference raw26897; decide +kernel
    rw [ha]
    exact (canonical26897 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1866 + difference 2 0) (sourceB1866 + difference 0 2) sourceC1866) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1545) := by
    have ha : (tripleCharges (sourceA1866 + difference 2 0) (sourceB1866 + difference 0 2) sourceC1866) = raw26898 := by
      apply Matrix.ext; unfold tripleCharges sourceA1866 sourceB1866 sourceC1866 difference raw26898; decide +kernel
    rw [ha]
    exact (canonical26898 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1866 + difference 3 0) (sourceB1866 + difference 0 3) sourceC1866) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1545) := by
    have ha : (tripleCharges (sourceA1866 + difference 3 0) (sourceB1866 + difference 0 3) sourceC1866) = raw26899 := by
      apply Matrix.ext; unfold tripleCharges sourceA1866 sourceB1866 sourceC1866 difference raw26899; decide +kernel
    rw [ha]
    exact (canonical26899 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1866 + difference 4 0) (sourceB1866 + difference 0 4) sourceC1866) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1545) := by
    have ha : (tripleCharges (sourceA1866 + difference 4 0) (sourceB1866 + difference 0 4) sourceC1866) = raw26900 := by
      apply Matrix.ext; unfold tripleCharges sourceA1866 sourceB1866 sourceC1866 difference raw26900; decide +kernel
    rw [ha]
    exact (canonical26900 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1866 + difference 5 0) (sourceB1866 + difference 0 5) sourceC1866) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1545) := by
    have ha : (tripleCharges (sourceA1866 + difference 5 0) (sourceB1866 + difference 0 5) sourceC1866) = raw26901 := by
      apply Matrix.ext; unfold tripleCharges sourceA1866 sourceB1866 sourceC1866 difference raw26901; decide +kernel
    rw [ha]
    exact (canonical26901 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1866 + sourceB1866) sourceC1866) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (doubleCharges (sourceA1866 + sourceB1866) sourceC1866) = raw26370 := by
      apply Matrix.ext; unfold doubleCharges sourceA1866 sourceB1866 sourceC1866 raw26370; decide +kernel
    rw [ha]
    exact (canonical26370 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1866 sourceB1866 sourceC1866
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1866, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1867 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1867 : Charge := ![1, 2, 0, 0, -1, -2]
def sourceC1867 : Charge := ![3, -2, -1, -1, 0, 1]
def sourceForm1867 : Integer.Sparse Master := [(Sum.inr 1052, 1), (Sum.inr 2127, 1), (Sum.inr 2214, 1), (Sum.inr 2250, 2), (Sum.inr 2275, 1), (Sum.inr 4080, -1)]

theorem sourceEq1867 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1867 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1867 + difference 0 0) (sourceB1867 + difference 0 0) sourceC1867) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1052) := by
    have ha : (tripleCharges (sourceA1867 + difference 0 0) (sourceB1867 + difference 0 0) sourceC1867) = raw26902 := by
      apply Matrix.ext; unfold tripleCharges sourceA1867 sourceB1867 sourceC1867 difference raw26902; decide +kernel
    rw [ha]
    exact (canonical26902 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1867 + difference 0 1) (sourceB1867 + difference 1 0) sourceC1867) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2127) := by
    have ha : (tripleCharges (sourceA1867 + difference 0 1) (sourceB1867 + difference 1 0) sourceC1867) = raw26903 := by
      apply Matrix.ext; unfold tripleCharges sourceA1867 sourceB1867 sourceC1867 difference raw26903; decide +kernel
    rw [ha]
    exact (canonical26903 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1867 + difference 0 2) (sourceB1867 + difference 2 0) sourceC1867) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2250) := by
    have ha : (tripleCharges (sourceA1867 + difference 0 2) (sourceB1867 + difference 2 0) sourceC1867) = raw26904 := by
      apply Matrix.ext; unfold tripleCharges sourceA1867 sourceB1867 sourceC1867 difference raw26904; decide +kernel
    rw [ha]
    exact (canonical26904 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1867 + difference 0 3) (sourceB1867 + difference 3 0) sourceC1867) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2250) := by
    have ha : (tripleCharges (sourceA1867 + difference 0 3) (sourceB1867 + difference 3 0) sourceC1867) = raw26905 := by
      apply Matrix.ext; unfold tripleCharges sourceA1867 sourceB1867 sourceC1867 difference raw26905; decide +kernel
    rw [ha]
    exact (canonical26905 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1867 + difference 0 4) (sourceB1867 + difference 4 0) sourceC1867) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2275) := by
    have ha : (tripleCharges (sourceA1867 + difference 0 4) (sourceB1867 + difference 4 0) sourceC1867) = raw26906 := by
      apply Matrix.ext; unfold tripleCharges sourceA1867 sourceB1867 sourceC1867 difference raw26906; decide +kernel
    rw [ha]
    exact (canonical26906 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1867 + difference 0 5) (sourceB1867 + difference 5 0) sourceC1867) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2214) := by
    have ha : (tripleCharges (sourceA1867 + difference 0 5) (sourceB1867 + difference 5 0) sourceC1867) = raw26907 := by
      apply Matrix.ext; unfold tripleCharges sourceA1867 sourceB1867 sourceC1867 difference raw26907; decide +kernel
    rw [ha]
    exact (canonical26907 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1867 + sourceB1867) sourceC1867) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1867 + sourceB1867) sourceC1867) = raw26908 := by
      apply Matrix.ext; unfold doubleCharges sourceA1867 sourceB1867 sourceC1867 raw26908; decide +kernel
    rw [ha]
    exact (canonical26908 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1867 sourceB1867 sourceC1867
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1867, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1868 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1868 : Charge := ![1, 1, 1, 0, -1, -2]
def sourceC1868 : Charge := ![3, -1, -2, -1, 0, 1]
def sourceForm1868 : Integer.Sparse Master := [(Sum.inr 1032, 1), (Sum.inr 2098, 1), (Sum.inr 2202, 1), (Sum.inr 2240, 1), (Sum.inr 2250, 1), (Sum.inr 2260, 1), (Sum.inr 4080, -1)]

theorem sourceEq1868 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1868 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1868 + difference 0 0) (sourceB1868 + difference 0 0) sourceC1868) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1032) := by
    have ha : (tripleCharges (sourceA1868 + difference 0 0) (sourceB1868 + difference 0 0) sourceC1868) = raw26909 := by
      apply Matrix.ext; unfold tripleCharges sourceA1868 sourceB1868 sourceC1868 difference raw26909; decide +kernel
    rw [ha]
    exact (canonical26909 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1868 + difference 0 1) (sourceB1868 + difference 1 0) sourceC1868) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2098) := by
    have ha : (tripleCharges (sourceA1868 + difference 0 1) (sourceB1868 + difference 1 0) sourceC1868) = raw26910 := by
      apply Matrix.ext; unfold tripleCharges sourceA1868 sourceB1868 sourceC1868 difference raw26910; decide +kernel
    rw [ha]
    exact (canonical26910 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1868 + difference 0 2) (sourceB1868 + difference 2 0) sourceC1868) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2250) := by
    have ha : (tripleCharges (sourceA1868 + difference 0 2) (sourceB1868 + difference 2 0) sourceC1868) = raw26911 := by
      apply Matrix.ext; unfold tripleCharges sourceA1868 sourceB1868 sourceC1868 difference raw26911; decide +kernel
    rw [ha]
    exact (canonical26911 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1868 + difference 0 3) (sourceB1868 + difference 3 0) sourceC1868) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2240) := by
    have ha : (tripleCharges (sourceA1868 + difference 0 3) (sourceB1868 + difference 3 0) sourceC1868) = raw26912 := by
      apply Matrix.ext; unfold tripleCharges sourceA1868 sourceB1868 sourceC1868 difference raw26912; decide +kernel
    rw [ha]
    exact (canonical26912 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1868 + difference 0 4) (sourceB1868 + difference 4 0) sourceC1868) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2260) := by
    have ha : (tripleCharges (sourceA1868 + difference 0 4) (sourceB1868 + difference 4 0) sourceC1868) = raw26913 := by
      apply Matrix.ext; unfold tripleCharges sourceA1868 sourceB1868 sourceC1868 difference raw26913; decide +kernel
    rw [ha]
    exact (canonical26913 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1868 + difference 0 5) (sourceB1868 + difference 5 0) sourceC1868) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2202) := by
    have ha : (tripleCharges (sourceA1868 + difference 0 5) (sourceB1868 + difference 5 0) sourceC1868) = raw26914 := by
      apply Matrix.ext; unfold tripleCharges sourceA1868 sourceB1868 sourceC1868 difference raw26914; decide +kernel
    rw [ha]
    exact (canonical26914 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1868 + sourceB1868) sourceC1868) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1868 + sourceB1868) sourceC1868) = raw26915 := by
      apply Matrix.ext; unfold doubleCharges sourceA1868 sourceB1868 sourceC1868 raw26915; decide +kernel
    rw [ha]
    exact (canonical26915 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1868 sourceB1868 sourceC1868
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1868, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1869 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1869 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC1869 : Charge := ![3, -1, -1, -1, -1, 1]
def sourceForm1869 : Integer.Sparse Master := [(Sum.inr 1034, 1), (Sum.inr 2100, 1), (Sum.inr 2204, 1), (Sum.inr 2241, 3), (Sum.inr 4079, -1)]

theorem sourceEq1869 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1869 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1869 + difference 0 0) (sourceB1869 + difference 0 0) sourceC1869) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1034) := by
    have ha : (tripleCharges (sourceA1869 + difference 0 0) (sourceB1869 + difference 0 0) sourceC1869) = raw24971 := by
      apply Matrix.ext; unfold tripleCharges sourceA1869 sourceB1869 sourceC1869 difference raw24971; decide +kernel
    rw [ha]
    exact (canonical24971 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1869 + difference 0 1) (sourceB1869 + difference 1 0) sourceC1869) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2100) := by
    have ha : (tripleCharges (sourceA1869 + difference 0 1) (sourceB1869 + difference 1 0) sourceC1869) = raw26916 := by
      apply Matrix.ext; unfold tripleCharges sourceA1869 sourceB1869 sourceC1869 difference raw26916; decide +kernel
    rw [ha]
    exact (canonical26916 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1869 + difference 0 2) (sourceB1869 + difference 2 0) sourceC1869) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2241) := by
    have ha : (tripleCharges (sourceA1869 + difference 0 2) (sourceB1869 + difference 2 0) sourceC1869) = raw24968 := by
      apply Matrix.ext; unfold tripleCharges sourceA1869 sourceB1869 sourceC1869 difference raw24968; decide +kernel
    rw [ha]
    exact (canonical24968 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1869 + difference 0 3) (sourceB1869 + difference 3 0) sourceC1869) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2241) := by
    have ha : (tripleCharges (sourceA1869 + difference 0 3) (sourceB1869 + difference 3 0) sourceC1869) = raw26917 := by
      apply Matrix.ext; unfold tripleCharges sourceA1869 sourceB1869 sourceC1869 difference raw26917; decide +kernel
    rw [ha]
    exact (canonical26917 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1869 + difference 0 4) (sourceB1869 + difference 4 0) sourceC1869) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2241) := by
    have ha : (tripleCharges (sourceA1869 + difference 0 4) (sourceB1869 + difference 4 0) sourceC1869) = raw26918 := by
      apply Matrix.ext; unfold tripleCharges sourceA1869 sourceB1869 sourceC1869 difference raw26918; decide +kernel
    rw [ha]
    exact (canonical26918 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1869 + difference 0 5) (sourceB1869 + difference 5 0) sourceC1869) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2204) := by
    have ha : (tripleCharges (sourceA1869 + difference 0 5) (sourceB1869 + difference 5 0) sourceC1869) = raw26919 := by
      apply Matrix.ext; unfold tripleCharges sourceA1869 sourceB1869 sourceC1869 difference raw26919; decide +kernel
    rw [ha]
    exact (canonical26919 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1869 + sourceB1869) sourceC1869) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4079) := by
    have ha : (doubleCharges (sourceA1869 + sourceB1869) sourceC1869) = raw24969 := by
      apply Matrix.ext; unfold doubleCharges sourceA1869 sourceB1869 sourceC1869 raw24969; decide +kernel
    rw [ha]
    exact (canonical24969 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1869 sourceB1869 sourceC1869
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1869, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1870 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceB1870 : Charge := ![3, -1, -1, -1, -1, 1]
def sourceC1870 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceForm1870 : Integer.Sparse Master := [(Sum.inr 732, 3), (Sum.inr 736, 1), (Sum.inr 805, 1), (Sum.inr 1644, 1), (Sum.inr 4068, -1)]

theorem sourceEq1870 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1870 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1870 + difference 0 0) (sourceB1870 + difference 0 0) sourceC1870) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1644) := by
    have ha : (tripleCharges (sourceA1870 + difference 0 0) (sourceB1870 + difference 0 0) sourceC1870) = raw26920 := by
      apply Matrix.ext; unfold tripleCharges sourceA1870 sourceB1870 sourceC1870 difference raw26920; decide +kernel
    rw [ha]
    exact (canonical26920 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1870 + difference 1 0) (sourceB1870 + difference 0 1) sourceC1870) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 736) := by
    have ha : (tripleCharges (sourceA1870 + difference 1 0) (sourceB1870 + difference 0 1) sourceC1870) = raw26921 := by
      apply Matrix.ext; unfold tripleCharges sourceA1870 sourceB1870 sourceC1870 difference raw26921; decide +kernel
    rw [ha]
    exact (canonical26921 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1870 + difference 2 0) (sourceB1870 + difference 0 2) sourceC1870) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 732) := by
    have ha : (tripleCharges (sourceA1870 + difference 2 0) (sourceB1870 + difference 0 2) sourceC1870) = raw26922 := by
      apply Matrix.ext; unfold tripleCharges sourceA1870 sourceB1870 sourceC1870 difference raw26922; decide +kernel
    rw [ha]
    exact (canonical26922 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1870 + difference 3 0) (sourceB1870 + difference 0 3) sourceC1870) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 732) := by
    have ha : (tripleCharges (sourceA1870 + difference 3 0) (sourceB1870 + difference 0 3) sourceC1870) = raw26923 := by
      apply Matrix.ext; unfold tripleCharges sourceA1870 sourceB1870 sourceC1870 difference raw26923; decide +kernel
    rw [ha]
    exact (canonical26923 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1870 + difference 4 0) (sourceB1870 + difference 0 4) sourceC1870) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 732) := by
    have ha : (tripleCharges (sourceA1870 + difference 4 0) (sourceB1870 + difference 0 4) sourceC1870) = raw26924 := by
      apply Matrix.ext; unfold tripleCharges sourceA1870 sourceB1870 sourceC1870 difference raw26924; decide +kernel
    rw [ha]
    exact (canonical26924 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1870 + difference 5 0) (sourceB1870 + difference 0 5) sourceC1870) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 805) := by
    have ha : (tripleCharges (sourceA1870 + difference 5 0) (sourceB1870 + difference 0 5) sourceC1870) = raw26925 := by
      apply Matrix.ext; unfold tripleCharges sourceA1870 sourceB1870 sourceC1870 difference raw26925; decide +kernel
    rw [ha]
    exact (canonical26925 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1870 + sourceB1870) sourceC1870) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (doubleCharges (sourceA1870 + sourceB1870) sourceC1870) = raw26370 := by
      apply Matrix.ext; unfold doubleCharges sourceA1870 sourceB1870 sourceC1870 raw26370; decide +kernel
    rw [ha]
    exact (canonical26370 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1870 sourceB1870 sourceC1870
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1870, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1871 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1871 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1871 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceForm1871 : Integer.Sparse Master := [(Sum.inr 4150, 2), (Sum.inr 4152, 2), (Sum.inr 4171, 1), (Sum.inr 4364, 2), (Sum.inr 4366, 2), (Sum.inr 4438, 2), (Sum.inr 4439, 4), (Sum.inr 4456, 2), (Sum.inr 4458, 4), (Sum.inr 4461, 2), (Sum.inr 4497, 2), (Sum.inr 4864, 1), (Sum.inr 4887, 2), (Sum.inr 4893, 2)]

theorem sourceEq1871 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1871 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1871 + difference 0 1) (sourceB1871 + difference 1 0) sourceC1871) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4864) := by
    have ha : (tripleCharges (sourceA1871 + difference 0 1) (sourceB1871 + difference 1 0) sourceC1871) = raw14273 := by
      apply Matrix.ext; unfold tripleCharges sourceA1871 sourceB1871 sourceC1871 difference raw14273; decide +kernel
    rw [ha]
    exact (canonical14273 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1871 + difference 0 2) (sourceB1871 + difference 2 0) sourceC1871) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4887) := by
    have ha : (tripleCharges (sourceA1871 + difference 0 2) (sourceB1871 + difference 2 0) sourceC1871) = raw5446 := by
      apply Matrix.ext; unfold tripleCharges sourceA1871 sourceB1871 sourceC1871 difference raw5446; decide +kernel
    rw [ha]
    exact (canonical5446 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1871 + difference 0 3) (sourceB1871 + difference 3 0) sourceC1871) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4887) := by
    have ha : (tripleCharges (sourceA1871 + difference 0 3) (sourceB1871 + difference 3 0) sourceC1871) = raw5441 := by
      apply Matrix.ext; unfold tripleCharges sourceA1871 sourceB1871 sourceC1871 difference raw5441; decide +kernel
    rw [ha]
    exact (canonical5441 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1871 + difference 0 4) (sourceB1871 + difference 4 0) sourceC1871) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4893) := by
    have ha : (tripleCharges (sourceA1871 + difference 0 4) (sourceB1871 + difference 4 0) sourceC1871) = raw14274 := by
      apply Matrix.ext; unfold tripleCharges sourceA1871 sourceB1871 sourceC1871 difference raw14274; decide +kernel
    rw [ha]
    exact (canonical14274 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1871 + difference 0 5) (sourceB1871 + difference 5 0) sourceC1871) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4893) := by
    have ha : (tripleCharges (sourceA1871 + difference 0 5) (sourceB1871 + difference 5 0) sourceC1871) = raw14275 := by
      apply Matrix.ext; unfold tripleCharges sourceA1871 sourceB1871 sourceC1871 difference raw14275; decide +kernel
    rw [ha]
    exact (canonical14275 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1871 + difference 1 0) (sourceB1871 + difference 0 1) sourceC1871) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4171) := by
    have ha : (tripleCharges (sourceA1871 + difference 1 0) (sourceB1871 + difference 0 1) sourceC1871) = raw26926 := by
      apply Matrix.ext; unfold tripleCharges sourceA1871 sourceB1871 sourceC1871 difference raw26926; decide +kernel
    rw [ha]
    exact (canonical26926 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1871 + difference 1 2) (sourceB1871 + difference 2 1) sourceC1871) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4456) := by
    have ha : (tripleCharges (sourceA1871 + difference 1 2) (sourceB1871 + difference 2 1) sourceC1871) = raw14268 := by
      apply Matrix.ext; unfold tripleCharges sourceA1871 sourceB1871 sourceC1871 difference raw14268; decide +kernel
    rw [ha]
    exact (canonical14268 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1871 + difference 1 3) (sourceB1871 + difference 3 1) sourceC1871) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4456) := by
    have ha : (tripleCharges (sourceA1871 + difference 1 3) (sourceB1871 + difference 3 1) sourceC1871) = raw26927 := by
      apply Matrix.ext; unfold tripleCharges sourceA1871 sourceB1871 sourceC1871 difference raw26927; decide +kernel
    rw [ha]
    exact (canonical26927 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1871 + difference 1 4) (sourceB1871 + difference 4 1) sourceC1871) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4497) := by
    have ha : (tripleCharges (sourceA1871 + difference 1 4) (sourceB1871 + difference 4 1) sourceC1871) = raw26928 := by
      apply Matrix.ext; unfold tripleCharges sourceA1871 sourceB1871 sourceC1871 difference raw26928; decide +kernel
    rw [ha]
    exact (canonical26928 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1871 + difference 1 5) (sourceB1871 + difference 5 1) sourceC1871) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4497) := by
    have ha : (tripleCharges (sourceA1871 + difference 1 5) (sourceB1871 + difference 5 1) sourceC1871) = raw26929 := by
      apply Matrix.ext; unfold tripleCharges sourceA1871 sourceB1871 sourceC1871 difference raw26929; decide +kernel
    rw [ha]
    exact (canonical26929 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1871 + difference 2 0) (sourceB1871 + difference 0 2) sourceC1871) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4150) := by
    have ha : (tripleCharges (sourceA1871 + difference 2 0) (sourceB1871 + difference 0 2) sourceC1871) = raw26930 := by
      apply Matrix.ext; unfold tripleCharges sourceA1871 sourceB1871 sourceC1871 difference raw26930; decide +kernel
    rw [ha]
    exact (canonical26930 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1871 + difference 2 1) (sourceB1871 + difference 1 2) sourceC1871) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4364) := by
    have ha : (tripleCharges (sourceA1871 + difference 2 1) (sourceB1871 + difference 1 2) sourceC1871) = raw26931 := by
      apply Matrix.ext; unfold tripleCharges sourceA1871 sourceB1871 sourceC1871 difference raw26931; decide +kernel
    rw [ha]
    exact (canonical26931 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1871 + difference 2 3) (sourceB1871 + difference 3 2) sourceC1871) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4438) := by
    have ha : (tripleCharges (sourceA1871 + difference 2 3) (sourceB1871 + difference 3 2) sourceC1871) = raw26932 := by
      apply Matrix.ext; unfold tripleCharges sourceA1871 sourceB1871 sourceC1871 difference raw26932; decide +kernel
    rw [ha]
    exact (canonical26932 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1871 + difference 2 4) (sourceB1871 + difference 4 2) sourceC1871) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1871 + difference 2 4) (sourceB1871 + difference 4 2) sourceC1871) = raw26933 := by
      apply Matrix.ext; unfold tripleCharges sourceA1871 sourceB1871 sourceC1871 difference raw26933; decide +kernel
    rw [ha]
    exact (canonical26933 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1871 + difference 2 5) (sourceB1871 + difference 5 2) sourceC1871) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1871 + difference 2 5) (sourceB1871 + difference 5 2) sourceC1871) = raw26934 := by
      apply Matrix.ext; unfold tripleCharges sourceA1871 sourceB1871 sourceC1871 difference raw26934; decide +kernel
    rw [ha]
    exact (canonical26934 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1871 + difference 3 0) (sourceB1871 + difference 0 3) sourceC1871) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4150) := by
    have ha : (tripleCharges (sourceA1871 + difference 3 0) (sourceB1871 + difference 0 3) sourceC1871) = raw26935 := by
      apply Matrix.ext; unfold tripleCharges sourceA1871 sourceB1871 sourceC1871 difference raw26935; decide +kernel
    rw [ha]
    exact (canonical26935 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1871 + difference 3 1) (sourceB1871 + difference 1 3) sourceC1871) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4364) := by
    have ha : (tripleCharges (sourceA1871 + difference 3 1) (sourceB1871 + difference 1 3) sourceC1871) = raw26936 := by
      apply Matrix.ext; unfold tripleCharges sourceA1871 sourceB1871 sourceC1871 difference raw26936; decide +kernel
    rw [ha]
    exact (canonical26936 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1871 + difference 3 2) (sourceB1871 + difference 2 3) sourceC1871) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4438) := by
    have ha : (tripleCharges (sourceA1871 + difference 3 2) (sourceB1871 + difference 2 3) sourceC1871) = raw14276 := by
      apply Matrix.ext; unfold tripleCharges sourceA1871 sourceB1871 sourceC1871 difference raw14276; decide +kernel
    rw [ha]
    exact (canonical14276 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1871 + difference 3 4) (sourceB1871 + difference 4 3) sourceC1871) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1871 + difference 3 4) (sourceB1871 + difference 4 3) sourceC1871) = raw26937 := by
      apply Matrix.ext; unfold tripleCharges sourceA1871 sourceB1871 sourceC1871 difference raw26937; decide +kernel
    rw [ha]
    exact (canonical26937 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1871 + difference 3 5) (sourceB1871 + difference 5 3) sourceC1871) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1871 + difference 3 5) (sourceB1871 + difference 5 3) sourceC1871) = raw26938 := by
      apply Matrix.ext; unfold tripleCharges sourceA1871 sourceB1871 sourceC1871 difference raw26938; decide +kernel
    rw [ha]
    exact (canonical26938 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1871 + difference 4 0) (sourceB1871 + difference 0 4) sourceC1871) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4152) := by
    have ha : (tripleCharges (sourceA1871 + difference 4 0) (sourceB1871 + difference 0 4) sourceC1871) = raw26939 := by
      apply Matrix.ext; unfold tripleCharges sourceA1871 sourceB1871 sourceC1871 difference raw26939; decide +kernel
    rw [ha]
    exact (canonical26939 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1871 + difference 4 1) (sourceB1871 + difference 1 4) sourceC1871) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4366) := by
    have ha : (tripleCharges (sourceA1871 + difference 4 1) (sourceB1871 + difference 1 4) sourceC1871) = raw26940 := by
      apply Matrix.ext; unfold tripleCharges sourceA1871 sourceB1871 sourceC1871 difference raw26940; decide +kernel
    rw [ha]
    exact (canonical26940 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1871 + difference 4 2) (sourceB1871 + difference 2 4) sourceC1871) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4439) := by
    have ha : (tripleCharges (sourceA1871 + difference 4 2) (sourceB1871 + difference 2 4) sourceC1871) = raw14281 := by
      apply Matrix.ext; unfold tripleCharges sourceA1871 sourceB1871 sourceC1871 difference raw14281; decide +kernel
    rw [ha]
    exact (canonical14281 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1871 + difference 4 3) (sourceB1871 + difference 3 4) sourceC1871) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4439) := by
    have ha : (tripleCharges (sourceA1871 + difference 4 3) (sourceB1871 + difference 3 4) sourceC1871) = raw26941 := by
      apply Matrix.ext; unfold tripleCharges sourceA1871 sourceB1871 sourceC1871 difference raw26941; decide +kernel
    rw [ha]
    exact (canonical26941 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1871 + difference 4 5) (sourceB1871 + difference 5 4) sourceC1871) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4461) := by
    have ha : (tripleCharges (sourceA1871 + difference 4 5) (sourceB1871 + difference 5 4) sourceC1871) = raw26942 := by
      apply Matrix.ext; unfold tripleCharges sourceA1871 sourceB1871 sourceC1871 difference raw26942; decide +kernel
    rw [ha]
    exact (canonical26942 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1871 + difference 5 0) (sourceB1871 + difference 0 5) sourceC1871) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4152) := by
    have ha : (tripleCharges (sourceA1871 + difference 5 0) (sourceB1871 + difference 0 5) sourceC1871) = raw26943 := by
      apply Matrix.ext; unfold tripleCharges sourceA1871 sourceB1871 sourceC1871 difference raw26943; decide +kernel
    rw [ha]
    exact (canonical26943 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1871 + difference 5 1) (sourceB1871 + difference 1 5) sourceC1871) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4366) := by
    have ha : (tripleCharges (sourceA1871 + difference 5 1) (sourceB1871 + difference 1 5) sourceC1871) = raw26944 := by
      apply Matrix.ext; unfold tripleCharges sourceA1871 sourceB1871 sourceC1871 difference raw26944; decide +kernel
    rw [ha]
    exact (canonical26944 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1871 + difference 5 2) (sourceB1871 + difference 2 5) sourceC1871) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4439) := by
    have ha : (tripleCharges (sourceA1871 + difference 5 2) (sourceB1871 + difference 2 5) sourceC1871) = raw5442 := by
      apply Matrix.ext; unfold tripleCharges sourceA1871 sourceB1871 sourceC1871 difference raw5442; decide +kernel
    rw [ha]
    exact (canonical5442 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1871 + difference 5 3) (sourceB1871 + difference 3 5) sourceC1871) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4439) := by
    have ha : (tripleCharges (sourceA1871 + difference 5 3) (sourceB1871 + difference 3 5) sourceC1871) = raw5437 := by
      apply Matrix.ext; unfold tripleCharges sourceA1871 sourceB1871 sourceC1871 difference raw5437; decide +kernel
    rw [ha]
    exact (canonical5437 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1871 + difference 5 4) (sourceB1871 + difference 4 5) sourceC1871) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4461) := by
    have ha : (tripleCharges (sourceA1871 + difference 5 4) (sourceB1871 + difference 4 5) sourceC1871) = raw26945 := by
      apply Matrix.ext; unfold tripleCharges sourceA1871 sourceB1871 sourceC1871 difference raw26945; decide +kernel
    rw [ha]
    exact (canonical26945 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1871 sourceB1871 sourceC1871
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1871, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1872 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1872 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1872 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceForm1872 : Integer.Sparse Master := [(Sum.inr 1504, 2), (Sum.inr 1506, 1), (Sum.inr 1510, 2), (Sum.inr 1703, 2), (Sum.inr 1705, 2), (Sum.inr 1706, 2), (Sum.inr 1711, 2), (Sum.inr 1713, 4), (Sum.inr 1724, 4), (Sum.inr 1726, 2), (Sum.inr 1737, 2), (Sum.inr 2241, 1), (Sum.inr 2243, 2), (Sum.inr 2263, 2)]

theorem sourceEq1872 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1872 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1872 + difference 0 1) (sourceB1872 + difference 1 0) sourceC1872) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2241) := by
    have ha : (tripleCharges (sourceA1872 + difference 0 1) (sourceB1872 + difference 1 0) sourceC1872) = raw14295 := by
      apply Matrix.ext; unfold tripleCharges sourceA1872 sourceB1872 sourceC1872 difference raw14295; decide +kernel
    rw [ha]
    exact (canonical14295 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1872 + difference 0 2) (sourceB1872 + difference 2 0) sourceC1872) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2243) := by
    have ha : (tripleCharges (sourceA1872 + difference 0 2) (sourceB1872 + difference 2 0) sourceC1872) = raw5506 := by
      apply Matrix.ext; unfold tripleCharges sourceA1872 sourceB1872 sourceC1872 difference raw5506; decide +kernel
    rw [ha]
    exact (canonical5506 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1872 + difference 0 3) (sourceB1872 + difference 3 0) sourceC1872) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2243) := by
    have ha : (tripleCharges (sourceA1872 + difference 0 3) (sourceB1872 + difference 3 0) sourceC1872) = raw5501 := by
      apply Matrix.ext; unfold tripleCharges sourceA1872 sourceB1872 sourceC1872 difference raw5501; decide +kernel
    rw [ha]
    exact (canonical5501 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1872 + difference 0 4) (sourceB1872 + difference 4 0) sourceC1872) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2263) := by
    have ha : (tripleCharges (sourceA1872 + difference 0 4) (sourceB1872 + difference 4 0) sourceC1872) = raw14296 := by
      apply Matrix.ext; unfold tripleCharges sourceA1872 sourceB1872 sourceC1872 difference raw14296; decide +kernel
    rw [ha]
    exact (canonical14296 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1872 + difference 0 5) (sourceB1872 + difference 5 0) sourceC1872) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2263) := by
    have ha : (tripleCharges (sourceA1872 + difference 0 5) (sourceB1872 + difference 5 0) sourceC1872) = raw14297 := by
      apply Matrix.ext; unfold tripleCharges sourceA1872 sourceB1872 sourceC1872 difference raw14297; decide +kernel
    rw [ha]
    exact (canonical14297 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1872 + difference 1 0) (sourceB1872 + difference 0 1) sourceC1872) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1506) := by
    have ha : (tripleCharges (sourceA1872 + difference 1 0) (sourceB1872 + difference 0 1) sourceC1872) = raw26946 := by
      apply Matrix.ext; unfold tripleCharges sourceA1872 sourceB1872 sourceC1872 difference raw26946; decide +kernel
    rw [ha]
    exact (canonical26946 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1872 + difference 1 2) (sourceB1872 + difference 2 1) sourceC1872) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1706) := by
    have ha : (tripleCharges (sourceA1872 + difference 1 2) (sourceB1872 + difference 2 1) sourceC1872) = raw14290 := by
      apply Matrix.ext; unfold tripleCharges sourceA1872 sourceB1872 sourceC1872 difference raw14290; decide +kernel
    rw [ha]
    exact (canonical14290 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1872 + difference 1 3) (sourceB1872 + difference 3 1) sourceC1872) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1706) := by
    have ha : (tripleCharges (sourceA1872 + difference 1 3) (sourceB1872 + difference 3 1) sourceC1872) = raw26947 := by
      apply Matrix.ext; unfold tripleCharges sourceA1872 sourceB1872 sourceC1872 difference raw26947; decide +kernel
    rw [ha]
    exact (canonical26947 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1872 + difference 1 4) (sourceB1872 + difference 4 1) sourceC1872) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1726) := by
    have ha : (tripleCharges (sourceA1872 + difference 1 4) (sourceB1872 + difference 4 1) sourceC1872) = raw26948 := by
      apply Matrix.ext; unfold tripleCharges sourceA1872 sourceB1872 sourceC1872 difference raw26948; decide +kernel
    rw [ha]
    exact (canonical26948 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1872 + difference 1 5) (sourceB1872 + difference 5 1) sourceC1872) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1726) := by
    have ha : (tripleCharges (sourceA1872 + difference 1 5) (sourceB1872 + difference 5 1) sourceC1872) = raw26949 := by
      apply Matrix.ext; unfold tripleCharges sourceA1872 sourceB1872 sourceC1872 difference raw26949; decide +kernel
    rw [ha]
    exact (canonical26949 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1872 + difference 2 0) (sourceB1872 + difference 0 2) sourceC1872) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1504) := by
    have ha : (tripleCharges (sourceA1872 + difference 2 0) (sourceB1872 + difference 0 2) sourceC1872) = raw26950 := by
      apply Matrix.ext; unfold tripleCharges sourceA1872 sourceB1872 sourceC1872 difference raw26950; decide +kernel
    rw [ha]
    exact (canonical26950 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1872 + difference 2 1) (sourceB1872 + difference 1 2) sourceC1872) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1703) := by
    have ha : (tripleCharges (sourceA1872 + difference 2 1) (sourceB1872 + difference 1 2) sourceC1872) = raw26951 := by
      apply Matrix.ext; unfold tripleCharges sourceA1872 sourceB1872 sourceC1872 difference raw26951; decide +kernel
    rw [ha]
    exact (canonical26951 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1872 + difference 2 3) (sourceB1872 + difference 3 2) sourceC1872) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1705) := by
    have ha : (tripleCharges (sourceA1872 + difference 2 3) (sourceB1872 + difference 3 2) sourceC1872) = raw26952 := by
      apply Matrix.ext; unfold tripleCharges sourceA1872 sourceB1872 sourceC1872 difference raw26952; decide +kernel
    rw [ha]
    exact (canonical26952 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1872 + difference 2 4) (sourceB1872 + difference 4 2) sourceC1872) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1724) := by
    have ha : (tripleCharges (sourceA1872 + difference 2 4) (sourceB1872 + difference 4 2) sourceC1872) = raw26953 := by
      apply Matrix.ext; unfold tripleCharges sourceA1872 sourceB1872 sourceC1872 difference raw26953; decide +kernel
    rw [ha]
    exact (canonical26953 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1872 + difference 2 5) (sourceB1872 + difference 5 2) sourceC1872) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1724) := by
    have ha : (tripleCharges (sourceA1872 + difference 2 5) (sourceB1872 + difference 5 2) sourceC1872) = raw26954 := by
      apply Matrix.ext; unfold tripleCharges sourceA1872 sourceB1872 sourceC1872 difference raw26954; decide +kernel
    rw [ha]
    exact (canonical26954 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1872 + difference 3 0) (sourceB1872 + difference 0 3) sourceC1872) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1504) := by
    have ha : (tripleCharges (sourceA1872 + difference 3 0) (sourceB1872 + difference 0 3) sourceC1872) = raw26955 := by
      apply Matrix.ext; unfold tripleCharges sourceA1872 sourceB1872 sourceC1872 difference raw26955; decide +kernel
    rw [ha]
    exact (canonical26955 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1872 + difference 3 1) (sourceB1872 + difference 1 3) sourceC1872) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1703) := by
    have ha : (tripleCharges (sourceA1872 + difference 3 1) (sourceB1872 + difference 1 3) sourceC1872) = raw26956 := by
      apply Matrix.ext; unfold tripleCharges sourceA1872 sourceB1872 sourceC1872 difference raw26956; decide +kernel
    rw [ha]
    exact (canonical26956 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1872 + difference 3 2) (sourceB1872 + difference 2 3) sourceC1872) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1705) := by
    have ha : (tripleCharges (sourceA1872 + difference 3 2) (sourceB1872 + difference 2 3) sourceC1872) = raw14298 := by
      apply Matrix.ext; unfold tripleCharges sourceA1872 sourceB1872 sourceC1872 difference raw14298; decide +kernel
    rw [ha]
    exact (canonical14298 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1872 + difference 3 4) (sourceB1872 + difference 4 3) sourceC1872) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1724) := by
    have ha : (tripleCharges (sourceA1872 + difference 3 4) (sourceB1872 + difference 4 3) sourceC1872) = raw26957 := by
      apply Matrix.ext; unfold tripleCharges sourceA1872 sourceB1872 sourceC1872 difference raw26957; decide +kernel
    rw [ha]
    exact (canonical26957 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1872 + difference 3 5) (sourceB1872 + difference 5 3) sourceC1872) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1724) := by
    have ha : (tripleCharges (sourceA1872 + difference 3 5) (sourceB1872 + difference 5 3) sourceC1872) = raw26958 := by
      apply Matrix.ext; unfold tripleCharges sourceA1872 sourceB1872 sourceC1872 difference raw26958; decide +kernel
    rw [ha]
    exact (canonical26958 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1872 + difference 4 0) (sourceB1872 + difference 0 4) sourceC1872) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1510) := by
    have ha : (tripleCharges (sourceA1872 + difference 4 0) (sourceB1872 + difference 0 4) sourceC1872) = raw26959 := by
      apply Matrix.ext; unfold tripleCharges sourceA1872 sourceB1872 sourceC1872 difference raw26959; decide +kernel
    rw [ha]
    exact (canonical26959 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1872 + difference 4 1) (sourceB1872 + difference 1 4) sourceC1872) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1711) := by
    have ha : (tripleCharges (sourceA1872 + difference 4 1) (sourceB1872 + difference 1 4) sourceC1872) = raw26960 := by
      apply Matrix.ext; unfold tripleCharges sourceA1872 sourceB1872 sourceC1872 difference raw26960; decide +kernel
    rw [ha]
    exact (canonical26960 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1872 + difference 4 2) (sourceB1872 + difference 2 4) sourceC1872) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1713) := by
    have ha : (tripleCharges (sourceA1872 + difference 4 2) (sourceB1872 + difference 2 4) sourceC1872) = raw14303 := by
      apply Matrix.ext; unfold tripleCharges sourceA1872 sourceB1872 sourceC1872 difference raw14303; decide +kernel
    rw [ha]
    exact (canonical14303 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1872 + difference 4 3) (sourceB1872 + difference 3 4) sourceC1872) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1713) := by
    have ha : (tripleCharges (sourceA1872 + difference 4 3) (sourceB1872 + difference 3 4) sourceC1872) = raw26961 := by
      apply Matrix.ext; unfold tripleCharges sourceA1872 sourceB1872 sourceC1872 difference raw26961; decide +kernel
    rw [ha]
    exact (canonical26961 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1872 + difference 4 5) (sourceB1872 + difference 5 4) sourceC1872) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1737) := by
    have ha : (tripleCharges (sourceA1872 + difference 4 5) (sourceB1872 + difference 5 4) sourceC1872) = raw26962 := by
      apply Matrix.ext; unfold tripleCharges sourceA1872 sourceB1872 sourceC1872 difference raw26962; decide +kernel
    rw [ha]
    exact (canonical26962 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1872 + difference 5 0) (sourceB1872 + difference 0 5) sourceC1872) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1510) := by
    have ha : (tripleCharges (sourceA1872 + difference 5 0) (sourceB1872 + difference 0 5) sourceC1872) = raw26963 := by
      apply Matrix.ext; unfold tripleCharges sourceA1872 sourceB1872 sourceC1872 difference raw26963; decide +kernel
    rw [ha]
    exact (canonical26963 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1872 + difference 5 1) (sourceB1872 + difference 1 5) sourceC1872) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1711) := by
    have ha : (tripleCharges (sourceA1872 + difference 5 1) (sourceB1872 + difference 1 5) sourceC1872) = raw26964 := by
      apply Matrix.ext; unfold tripleCharges sourceA1872 sourceB1872 sourceC1872 difference raw26964; decide +kernel
    rw [ha]
    exact (canonical26964 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1872 + difference 5 2) (sourceB1872 + difference 2 5) sourceC1872) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1713) := by
    have ha : (tripleCharges (sourceA1872 + difference 5 2) (sourceB1872 + difference 2 5) sourceC1872) = raw5502 := by
      apply Matrix.ext; unfold tripleCharges sourceA1872 sourceB1872 sourceC1872 difference raw5502; decide +kernel
    rw [ha]
    exact (canonical5502 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1872 + difference 5 3) (sourceB1872 + difference 3 5) sourceC1872) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1713) := by
    have ha : (tripleCharges (sourceA1872 + difference 5 3) (sourceB1872 + difference 3 5) sourceC1872) = raw5497 := by
      apply Matrix.ext; unfold tripleCharges sourceA1872 sourceB1872 sourceC1872 difference raw5497; decide +kernel
    rw [ha]
    exact (canonical5497 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1872 + difference 5 4) (sourceB1872 + difference 4 5) sourceC1872) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1737) := by
    have ha : (tripleCharges (sourceA1872 + difference 5 4) (sourceB1872 + difference 4 5) sourceC1872) = raw26965 := by
      apply Matrix.ext; unfold tripleCharges sourceA1872 sourceB1872 sourceC1872 difference raw26965; decide +kernel
    rw [ha]
    exact (canonical26965 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1872 sourceB1872 sourceC1872
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1872, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1873 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1873 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1873 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceForm1873 : Integer.Sparse Master := [(Sum.inr 599, 1), (Sum.inr 1039, 3), (Sum.inr 1081, 2), (Sum.inr 4083, -1)]

theorem sourceEq1873 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1873 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1873 + difference 1 0) (sourceB1873 + difference 0 1) sourceC1873) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 599) := by
    have ha : (tripleCharges (sourceA1873 + difference 1 0) (sourceB1873 + difference 0 1) sourceC1873) = raw26966 := by
      apply Matrix.ext; unfold tripleCharges sourceA1873 sourceB1873 sourceC1873 difference raw26966; decide +kernel
    rw [ha]
    exact (canonical26966 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1873 + difference 1 1) (sourceB1873 + difference 1 1) sourceC1873) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1039) := by
    have ha : (tripleCharges (sourceA1873 + difference 1 1) (sourceB1873 + difference 1 1) sourceC1873) = raw26967 := by
      apply Matrix.ext; unfold tripleCharges sourceA1873 sourceB1873 sourceC1873 difference raw26967; decide +kernel
    rw [ha]
    exact (canonical26967 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1873 + difference 1 2) (sourceB1873 + difference 2 1) sourceC1873) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1039) := by
    have ha : (tripleCharges (sourceA1873 + difference 1 2) (sourceB1873 + difference 2 1) sourceC1873) = raw26968 := by
      apply Matrix.ext; unfold tripleCharges sourceA1873 sourceB1873 sourceC1873 difference raw26968; decide +kernel
    rw [ha]
    exact (canonical26968 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1873 + difference 1 3) (sourceB1873 + difference 3 1) sourceC1873) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1039) := by
    have ha : (tripleCharges (sourceA1873 + difference 1 3) (sourceB1873 + difference 3 1) sourceC1873) = raw26969 := by
      apply Matrix.ext; unfold tripleCharges sourceA1873 sourceB1873 sourceC1873 difference raw26969; decide +kernel
    rw [ha]
    exact (canonical26969 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1873 + difference 1 4) (sourceB1873 + difference 4 1) sourceC1873) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1081) := by
    have ha : (tripleCharges (sourceA1873 + difference 1 4) (sourceB1873 + difference 4 1) sourceC1873) = raw26970 := by
      apply Matrix.ext; unfold tripleCharges sourceA1873 sourceB1873 sourceC1873 difference raw26970; decide +kernel
    rw [ha]
    exact (canonical26970 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1873 + difference 1 5) (sourceB1873 + difference 5 1) sourceC1873) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1081) := by
    have ha : (tripleCharges (sourceA1873 + difference 1 5) (sourceB1873 + difference 5 1) sourceC1873) = raw26971 := by
      apply Matrix.ext; unfold tripleCharges sourceA1873 sourceB1873 sourceC1873 difference raw26971; decide +kernel
    rw [ha]
    exact (canonical26971 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1873 + sourceB1873) sourceC1873) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA1873 + sourceB1873) sourceC1873) = raw5523 := by
      apply Matrix.ext; unfold doubleCharges sourceA1873 sourceB1873 sourceC1873 raw5523; decide +kernel
    rw [ha]
    exact (canonical5523 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1873 sourceB1873 sourceC1873
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1873, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1874 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1874 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceC1874 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceForm1874 : Integer.Sparse Master := [(Sum.inr 4098, 2), (Sum.inr 4100, 2), (Sum.inr 4113, 1), (Sum.inr 4341, 2), (Sum.inr 4344, 2), (Sum.inr 4396, 4), (Sum.inr 4399, 2), (Sum.inr 4417, 2), (Sum.inr 4457, 2), (Sum.inr 4458, 4), (Sum.inr 4495, 2), (Sum.inr 5167, 1), (Sum.inr 5257, 2), (Sum.inr 5292, 2)]

theorem sourceEq1874 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1874 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1874 + difference 0 1) (sourceB1874 + difference 1 0) sourceC1874) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5167) := by
    have ha : (tripleCharges (sourceA1874 + difference 0 1) (sourceB1874 + difference 1 0) sourceC1874) = raw26972 := by
      apply Matrix.ext; unfold tripleCharges sourceA1874 sourceB1874 sourceC1874 difference raw26972; decide +kernel
    rw [ha]
    exact (canonical26972 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1874 + difference 0 2) (sourceB1874 + difference 2 0) sourceC1874) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA1874 + difference 0 2) (sourceB1874 + difference 2 0) sourceC1874) = raw25242 := by
      apply Matrix.ext; unfold tripleCharges sourceA1874 sourceB1874 sourceC1874 difference raw25242; decide +kernel
    rw [ha]
    exact (canonical25242 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1874 + difference 0 3) (sourceB1874 + difference 3 0) sourceC1874) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA1874 + difference 0 3) (sourceB1874 + difference 3 0) sourceC1874) = raw26973 := by
      apply Matrix.ext; unfold tripleCharges sourceA1874 sourceB1874 sourceC1874 difference raw26973; decide +kernel
    rw [ha]
    exact (canonical26973 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1874 + difference 0 4) (sourceB1874 + difference 4 0) sourceC1874) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA1874 + difference 0 4) (sourceB1874 + difference 4 0) sourceC1874) = raw26974 := by
      apply Matrix.ext; unfold tripleCharges sourceA1874 sourceB1874 sourceC1874 difference raw26974; decide +kernel
    rw [ha]
    exact (canonical26974 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1874 + difference 0 5) (sourceB1874 + difference 5 0) sourceC1874) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA1874 + difference 0 5) (sourceB1874 + difference 5 0) sourceC1874) = raw26975 := by
      apply Matrix.ext; unfold tripleCharges sourceA1874 sourceB1874 sourceC1874 difference raw26975; decide +kernel
    rw [ha]
    exact (canonical26975 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1874 + difference 1 0) (sourceB1874 + difference 0 1) sourceC1874) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4113) := by
    have ha : (tripleCharges (sourceA1874 + difference 1 0) (sourceB1874 + difference 0 1) sourceC1874) = raw26976 := by
      apply Matrix.ext; unfold tripleCharges sourceA1874 sourceB1874 sourceC1874 difference raw26976; decide +kernel
    rw [ha]
    exact (canonical26976 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1874 + difference 1 2) (sourceB1874 + difference 2 1) sourceC1874) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4495) := by
    have ha : (tripleCharges (sourceA1874 + difference 1 2) (sourceB1874 + difference 2 1) sourceC1874) = raw25246 := by
      apply Matrix.ext; unfold tripleCharges sourceA1874 sourceB1874 sourceC1874 difference raw25246; decide +kernel
    rw [ha]
    exact (canonical25246 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1874 + difference 1 3) (sourceB1874 + difference 3 1) sourceC1874) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4495) := by
    have ha : (tripleCharges (sourceA1874 + difference 1 3) (sourceB1874 + difference 3 1) sourceC1874) = raw26977 := by
      apply Matrix.ext; unfold tripleCharges sourceA1874 sourceB1874 sourceC1874 difference raw26977; decide +kernel
    rw [ha]
    exact (canonical26977 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1874 + difference 1 4) (sourceB1874 + difference 4 1) sourceC1874) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4417) := by
    have ha : (tripleCharges (sourceA1874 + difference 1 4) (sourceB1874 + difference 4 1) sourceC1874) = raw26978 := by
      apply Matrix.ext; unfold tripleCharges sourceA1874 sourceB1874 sourceC1874 difference raw26978; decide +kernel
    rw [ha]
    exact (canonical26978 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1874 + difference 1 5) (sourceB1874 + difference 5 1) sourceC1874) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4417) := by
    have ha : (tripleCharges (sourceA1874 + difference 1 5) (sourceB1874 + difference 5 1) sourceC1874) = raw26979 := by
      apply Matrix.ext; unfold tripleCharges sourceA1874 sourceB1874 sourceC1874 difference raw26979; decide +kernel
    rw [ha]
    exact (canonical26979 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1874 + difference 2 0) (sourceB1874 + difference 0 2) sourceC1874) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4098) := by
    have ha : (tripleCharges (sourceA1874 + difference 2 0) (sourceB1874 + difference 0 2) sourceC1874) = raw26980 := by
      apply Matrix.ext; unfold tripleCharges sourceA1874 sourceB1874 sourceC1874 difference raw26980; decide +kernel
    rw [ha]
    exact (canonical26980 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1874 + difference 2 1) (sourceB1874 + difference 1 2) sourceC1874) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4341) := by
    have ha : (tripleCharges (sourceA1874 + difference 2 1) (sourceB1874 + difference 1 2) sourceC1874) = raw26981 := by
      apply Matrix.ext; unfold tripleCharges sourceA1874 sourceB1874 sourceC1874 difference raw26981; decide +kernel
    rw [ha]
    exact (canonical26981 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1874 + difference 2 3) (sourceB1874 + difference 3 2) sourceC1874) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4457) := by
    have ha : (tripleCharges (sourceA1874 + difference 2 3) (sourceB1874 + difference 3 2) sourceC1874) = raw26982 := by
      apply Matrix.ext; unfold tripleCharges sourceA1874 sourceB1874 sourceC1874 difference raw26982; decide +kernel
    rw [ha]
    exact (canonical26982 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1874 + difference 2 4) (sourceB1874 + difference 4 2) sourceC1874) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4396) := by
    have ha : (tripleCharges (sourceA1874 + difference 2 4) (sourceB1874 + difference 4 2) sourceC1874) = raw26983 := by
      apply Matrix.ext; unfold tripleCharges sourceA1874 sourceB1874 sourceC1874 difference raw26983; decide +kernel
    rw [ha]
    exact (canonical26983 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1874 + difference 2 5) (sourceB1874 + difference 5 2) sourceC1874) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4396) := by
    have ha : (tripleCharges (sourceA1874 + difference 2 5) (sourceB1874 + difference 5 2) sourceC1874) = raw26984 := by
      apply Matrix.ext; unfold tripleCharges sourceA1874 sourceB1874 sourceC1874 difference raw26984; decide +kernel
    rw [ha]
    exact (canonical26984 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1874 + difference 3 0) (sourceB1874 + difference 0 3) sourceC1874) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4098) := by
    have ha : (tripleCharges (sourceA1874 + difference 3 0) (sourceB1874 + difference 0 3) sourceC1874) = raw26985 := by
      apply Matrix.ext; unfold tripleCharges sourceA1874 sourceB1874 sourceC1874 difference raw26985; decide +kernel
    rw [ha]
    exact (canonical26985 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1874 + difference 3 1) (sourceB1874 + difference 1 3) sourceC1874) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4341) := by
    have ha : (tripleCharges (sourceA1874 + difference 3 1) (sourceB1874 + difference 1 3) sourceC1874) = raw26986 := by
      apply Matrix.ext; unfold tripleCharges sourceA1874 sourceB1874 sourceC1874 difference raw26986; decide +kernel
    rw [ha]
    exact (canonical26986 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1874 + difference 3 2) (sourceB1874 + difference 2 3) sourceC1874) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4457) := by
    have ha : (tripleCharges (sourceA1874 + difference 3 2) (sourceB1874 + difference 2 3) sourceC1874) = raw25255 := by
      apply Matrix.ext; unfold tripleCharges sourceA1874 sourceB1874 sourceC1874 difference raw25255; decide +kernel
    rw [ha]
    exact (canonical25255 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1874 + difference 3 4) (sourceB1874 + difference 4 3) sourceC1874) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4396) := by
    have ha : (tripleCharges (sourceA1874 + difference 3 4) (sourceB1874 + difference 4 3) sourceC1874) = raw26987 := by
      apply Matrix.ext; unfold tripleCharges sourceA1874 sourceB1874 sourceC1874 difference raw26987; decide +kernel
    rw [ha]
    exact (canonical26987 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1874 + difference 3 5) (sourceB1874 + difference 5 3) sourceC1874) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4396) := by
    have ha : (tripleCharges (sourceA1874 + difference 3 5) (sourceB1874 + difference 5 3) sourceC1874) = raw26988 := by
      apply Matrix.ext; unfold tripleCharges sourceA1874 sourceB1874 sourceC1874 difference raw26988; decide +kernel
    rw [ha]
    exact (canonical26988 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1874 + difference 4 0) (sourceB1874 + difference 0 4) sourceC1874) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4100) := by
    have ha : (tripleCharges (sourceA1874 + difference 4 0) (sourceB1874 + difference 0 4) sourceC1874) = raw26989 := by
      apply Matrix.ext; unfold tripleCharges sourceA1874 sourceB1874 sourceC1874 difference raw26989; decide +kernel
    rw [ha]
    exact (canonical26989 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1874 + difference 4 1) (sourceB1874 + difference 1 4) sourceC1874) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4344) := by
    have ha : (tripleCharges (sourceA1874 + difference 4 1) (sourceB1874 + difference 1 4) sourceC1874) = raw26990 := by
      apply Matrix.ext; unfold tripleCharges sourceA1874 sourceB1874 sourceC1874 difference raw26990; decide +kernel
    rw [ha]
    exact (canonical26990 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1874 + difference 4 2) (sourceB1874 + difference 2 4) sourceC1874) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1874 + difference 4 2) (sourceB1874 + difference 2 4) sourceC1874) = raw23233 := by
      apply Matrix.ext; unfold tripleCharges sourceA1874 sourceB1874 sourceC1874 difference raw23233; decide +kernel
    rw [ha]
    exact (canonical23233 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1874 + difference 4 3) (sourceB1874 + difference 3 4) sourceC1874) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1874 + difference 4 3) (sourceB1874 + difference 3 4) sourceC1874) = raw23229 := by
      apply Matrix.ext; unfold tripleCharges sourceA1874 sourceB1874 sourceC1874 difference raw23229; decide +kernel
    rw [ha]
    exact (canonical23229 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1874 + difference 4 5) (sourceB1874 + difference 5 4) sourceC1874) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4399) := by
    have ha : (tripleCharges (sourceA1874 + difference 4 5) (sourceB1874 + difference 5 4) sourceC1874) = raw26991 := by
      apply Matrix.ext; unfold tripleCharges sourceA1874 sourceB1874 sourceC1874 difference raw26991; decide +kernel
    rw [ha]
    exact (canonical26991 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1874 + difference 5 0) (sourceB1874 + difference 0 5) sourceC1874) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4100) := by
    have ha : (tripleCharges (sourceA1874 + difference 5 0) (sourceB1874 + difference 0 5) sourceC1874) = raw25247 := by
      apply Matrix.ext; unfold tripleCharges sourceA1874 sourceB1874 sourceC1874 difference raw25247; decide +kernel
    rw [ha]
    exact (canonical25247 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1874 + difference 5 1) (sourceB1874 + difference 1 5) sourceC1874) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4344) := by
    have ha : (tripleCharges (sourceA1874 + difference 5 1) (sourceB1874 + difference 1 5) sourceC1874) = raw25248 := by
      apply Matrix.ext; unfold tripleCharges sourceA1874 sourceB1874 sourceC1874 difference raw25248; decide +kernel
    rw [ha]
    exact (canonical25248 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1874 + difference 5 2) (sourceB1874 + difference 2 5) sourceC1874) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1874 + difference 5 2) (sourceB1874 + difference 2 5) sourceC1874) = raw21489 := by
      apply Matrix.ext; unfold tripleCharges sourceA1874 sourceB1874 sourceC1874 difference raw21489; decide +kernel
    rw [ha]
    exact (canonical21489 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1874 + difference 5 3) (sourceB1874 + difference 3 5) sourceC1874) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1874 + difference 5 3) (sourceB1874 + difference 3 5) sourceC1874) = raw21485 := by
      apply Matrix.ext; unfold tripleCharges sourceA1874 sourceB1874 sourceC1874 difference raw21485; decide +kernel
    rw [ha]
    exact (canonical21485 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1874 + difference 5 4) (sourceB1874 + difference 4 5) sourceC1874) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4399) := by
    have ha : (tripleCharges (sourceA1874 + difference 5 4) (sourceB1874 + difference 4 5) sourceC1874) = raw25249 := by
      apply Matrix.ext; unfold tripleCharges sourceA1874 sourceB1874 sourceC1874 difference raw25249; decide +kernel
    rw [ha]
    exact (canonical25249 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1874 sourceB1874 sourceC1874
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1874, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1875 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1875 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceC1875 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceForm1875 : Integer.Sparse Master := [(Sum.inr 535, 2), (Sum.inr 537, 2), (Sum.inr 550, 1), (Sum.inr 919, 2), (Sum.inr 922, 2), (Sum.inr 977, 4), (Sum.inr 980, 2), (Sum.inr 998, 2), (Sum.inr 1040, 2), (Sum.inr 1041, 4), (Sum.inr 1079, 2), (Sum.inr 2593, 1), (Sum.inr 2721, 2), (Sum.inr 2766, 2)]

theorem sourceEq1875 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1875 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1875 + difference 0 1) (sourceB1875 + difference 1 0) sourceC1875) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2593) := by
    have ha : (tripleCharges (sourceA1875 + difference 0 1) (sourceB1875 + difference 1 0) sourceC1875) = raw26992 := by
      apply Matrix.ext; unfold tripleCharges sourceA1875 sourceB1875 sourceC1875 difference raw26992; decide +kernel
    rw [ha]
    exact (canonical26992 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1875 + difference 0 2) (sourceB1875 + difference 2 0) sourceC1875) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2766) := by
    have ha : (tripleCharges (sourceA1875 + difference 0 2) (sourceB1875 + difference 2 0) sourceC1875) = raw25258 := by
      apply Matrix.ext; unfold tripleCharges sourceA1875 sourceB1875 sourceC1875 difference raw25258; decide +kernel
    rw [ha]
    exact (canonical25258 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1875 + difference 0 3) (sourceB1875 + difference 3 0) sourceC1875) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2766) := by
    have ha : (tripleCharges (sourceA1875 + difference 0 3) (sourceB1875 + difference 3 0) sourceC1875) = raw26993 := by
      apply Matrix.ext; unfold tripleCharges sourceA1875 sourceB1875 sourceC1875 difference raw26993; decide +kernel
    rw [ha]
    exact (canonical26993 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1875 + difference 0 4) (sourceB1875 + difference 4 0) sourceC1875) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2721) := by
    have ha : (tripleCharges (sourceA1875 + difference 0 4) (sourceB1875 + difference 4 0) sourceC1875) = raw26994 := by
      apply Matrix.ext; unfold tripleCharges sourceA1875 sourceB1875 sourceC1875 difference raw26994; decide +kernel
    rw [ha]
    exact (canonical26994 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1875 + difference 0 5) (sourceB1875 + difference 5 0) sourceC1875) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2721) := by
    have ha : (tripleCharges (sourceA1875 + difference 0 5) (sourceB1875 + difference 5 0) sourceC1875) = raw26995 := by
      apply Matrix.ext; unfold tripleCharges sourceA1875 sourceB1875 sourceC1875 difference raw26995; decide +kernel
    rw [ha]
    exact (canonical26995 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1875 + difference 1 0) (sourceB1875 + difference 0 1) sourceC1875) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 550) := by
    have ha : (tripleCharges (sourceA1875 + difference 1 0) (sourceB1875 + difference 0 1) sourceC1875) = raw26996 := by
      apply Matrix.ext; unfold tripleCharges sourceA1875 sourceB1875 sourceC1875 difference raw26996; decide +kernel
    rw [ha]
    exact (canonical26996 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1875 + difference 1 2) (sourceB1875 + difference 2 1) sourceC1875) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1079) := by
    have ha : (tripleCharges (sourceA1875 + difference 1 2) (sourceB1875 + difference 2 1) sourceC1875) = raw25262 := by
      apply Matrix.ext; unfold tripleCharges sourceA1875 sourceB1875 sourceC1875 difference raw25262; decide +kernel
    rw [ha]
    exact (canonical25262 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1875 + difference 1 3) (sourceB1875 + difference 3 1) sourceC1875) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1079) := by
    have ha : (tripleCharges (sourceA1875 + difference 1 3) (sourceB1875 + difference 3 1) sourceC1875) = raw26997 := by
      apply Matrix.ext; unfold tripleCharges sourceA1875 sourceB1875 sourceC1875 difference raw26997; decide +kernel
    rw [ha]
    exact (canonical26997 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1875 + difference 1 4) (sourceB1875 + difference 4 1) sourceC1875) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 998) := by
    have ha : (tripleCharges (sourceA1875 + difference 1 4) (sourceB1875 + difference 4 1) sourceC1875) = raw26998 := by
      apply Matrix.ext; unfold tripleCharges sourceA1875 sourceB1875 sourceC1875 difference raw26998; decide +kernel
    rw [ha]
    exact (canonical26998 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1875 + difference 1 5) (sourceB1875 + difference 5 1) sourceC1875) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 998) := by
    have ha : (tripleCharges (sourceA1875 + difference 1 5) (sourceB1875 + difference 5 1) sourceC1875) = raw26999 := by
      apply Matrix.ext; unfold tripleCharges sourceA1875 sourceB1875 sourceC1875 difference raw26999; decide +kernel
    rw [ha]
    exact (canonical26999 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1875 + difference 2 0) (sourceB1875 + difference 0 2) sourceC1875) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 535) := by
    have ha : (tripleCharges (sourceA1875 + difference 2 0) (sourceB1875 + difference 0 2) sourceC1875) = raw27000 := by
      apply Matrix.ext; unfold tripleCharges sourceA1875 sourceB1875 sourceC1875 difference raw27000; decide +kernel
    rw [ha]
    exact (canonical27000 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1875 + difference 2 1) (sourceB1875 + difference 1 2) sourceC1875) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 919) := by
    have ha : (tripleCharges (sourceA1875 + difference 2 1) (sourceB1875 + difference 1 2) sourceC1875) = raw27001 := by
      apply Matrix.ext; unfold tripleCharges sourceA1875 sourceB1875 sourceC1875 difference raw27001; decide +kernel
    rw [ha]
    exact (canonical27001 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1875 + difference 2 3) (sourceB1875 + difference 3 2) sourceC1875) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1040) := by
    have ha : (tripleCharges (sourceA1875 + difference 2 3) (sourceB1875 + difference 3 2) sourceC1875) = raw27002 := by
      apply Matrix.ext; unfold tripleCharges sourceA1875 sourceB1875 sourceC1875 difference raw27002; decide +kernel
    rw [ha]
    exact (canonical27002 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1875 + difference 2 4) (sourceB1875 + difference 4 2) sourceC1875) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 977) := by
    have ha : (tripleCharges (sourceA1875 + difference 2 4) (sourceB1875 + difference 4 2) sourceC1875) = raw27003 := by
      apply Matrix.ext; unfold tripleCharges sourceA1875 sourceB1875 sourceC1875 difference raw27003; decide +kernel
    rw [ha]
    exact (canonical27003 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1875 + difference 2 5) (sourceB1875 + difference 5 2) sourceC1875) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 977) := by
    have ha : (tripleCharges (sourceA1875 + difference 2 5) (sourceB1875 + difference 5 2) sourceC1875) = raw27004 := by
      apply Matrix.ext; unfold tripleCharges sourceA1875 sourceB1875 sourceC1875 difference raw27004; decide +kernel
    rw [ha]
    exact (canonical27004 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1875 + difference 3 0) (sourceB1875 + difference 0 3) sourceC1875) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 535) := by
    have ha : (tripleCharges (sourceA1875 + difference 3 0) (sourceB1875 + difference 0 3) sourceC1875) = raw27005 := by
      apply Matrix.ext; unfold tripleCharges sourceA1875 sourceB1875 sourceC1875 difference raw27005; decide +kernel
    rw [ha]
    exact (canonical27005 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1875 + difference 3 1) (sourceB1875 + difference 1 3) sourceC1875) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 919) := by
    have ha : (tripleCharges (sourceA1875 + difference 3 1) (sourceB1875 + difference 1 3) sourceC1875) = raw27006 := by
      apply Matrix.ext; unfold tripleCharges sourceA1875 sourceB1875 sourceC1875 difference raw27006; decide +kernel
    rw [ha]
    exact (canonical27006 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1875 + difference 3 2) (sourceB1875 + difference 2 3) sourceC1875) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1040) := by
    have ha : (tripleCharges (sourceA1875 + difference 3 2) (sourceB1875 + difference 2 3) sourceC1875) = raw25271 := by
      apply Matrix.ext; unfold tripleCharges sourceA1875 sourceB1875 sourceC1875 difference raw25271; decide +kernel
    rw [ha]
    exact (canonical25271 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1875 + difference 3 4) (sourceB1875 + difference 4 3) sourceC1875) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 977) := by
    have ha : (tripleCharges (sourceA1875 + difference 3 4) (sourceB1875 + difference 4 3) sourceC1875) = raw27007 := by
      apply Matrix.ext; unfold tripleCharges sourceA1875 sourceB1875 sourceC1875 difference raw27007; decide +kernel
    rw [ha]
    exact (canonical27007 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1875 + difference 3 5) (sourceB1875 + difference 5 3) sourceC1875) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 977) := by
    have ha : (tripleCharges (sourceA1875 + difference 3 5) (sourceB1875 + difference 5 3) sourceC1875) = raw27008 := by
      apply Matrix.ext; unfold tripleCharges sourceA1875 sourceB1875 sourceC1875 difference raw27008; decide +kernel
    rw [ha]
    exact (canonical27008 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1875 + difference 4 0) (sourceB1875 + difference 0 4) sourceC1875) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 537) := by
    have ha : (tripleCharges (sourceA1875 + difference 4 0) (sourceB1875 + difference 0 4) sourceC1875) = raw27009 := by
      apply Matrix.ext; unfold tripleCharges sourceA1875 sourceB1875 sourceC1875 difference raw27009; decide +kernel
    rw [ha]
    exact (canonical27009 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1875 + difference 4 1) (sourceB1875 + difference 1 4) sourceC1875) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 922) := by
    have ha : (tripleCharges (sourceA1875 + difference 4 1) (sourceB1875 + difference 1 4) sourceC1875) = raw27010 := by
      apply Matrix.ext; unfold tripleCharges sourceA1875 sourceB1875 sourceC1875 difference raw27010; decide +kernel
    rw [ha]
    exact (canonical27010 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1875 + difference 4 2) (sourceB1875 + difference 2 4) sourceC1875) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1041) := by
    have ha : (tripleCharges (sourceA1875 + difference 4 2) (sourceB1875 + difference 2 4) sourceC1875) = raw23254 := by
      apply Matrix.ext; unfold tripleCharges sourceA1875 sourceB1875 sourceC1875 difference raw23254; decide +kernel
    rw [ha]
    exact (canonical23254 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1875 + difference 4 3) (sourceB1875 + difference 3 4) sourceC1875) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1041) := by
    have ha : (tripleCharges (sourceA1875 + difference 4 3) (sourceB1875 + difference 3 4) sourceC1875) = raw23250 := by
      apply Matrix.ext; unfold tripleCharges sourceA1875 sourceB1875 sourceC1875 difference raw23250; decide +kernel
    rw [ha]
    exact (canonical23250 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1875 + difference 4 5) (sourceB1875 + difference 5 4) sourceC1875) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 980) := by
    have ha : (tripleCharges (sourceA1875 + difference 4 5) (sourceB1875 + difference 5 4) sourceC1875) = raw27011 := by
      apply Matrix.ext; unfold tripleCharges sourceA1875 sourceB1875 sourceC1875 difference raw27011; decide +kernel
    rw [ha]
    exact (canonical27011 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1875 + difference 5 0) (sourceB1875 + difference 0 5) sourceC1875) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 537) := by
    have ha : (tripleCharges (sourceA1875 + difference 5 0) (sourceB1875 + difference 0 5) sourceC1875) = raw25263 := by
      apply Matrix.ext; unfold tripleCharges sourceA1875 sourceB1875 sourceC1875 difference raw25263; decide +kernel
    rw [ha]
    exact (canonical25263 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1875 + difference 5 1) (sourceB1875 + difference 1 5) sourceC1875) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 922) := by
    have ha : (tripleCharges (sourceA1875 + difference 5 1) (sourceB1875 + difference 1 5) sourceC1875) = raw25264 := by
      apply Matrix.ext; unfold tripleCharges sourceA1875 sourceB1875 sourceC1875 difference raw25264; decide +kernel
    rw [ha]
    exact (canonical25264 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1875 + difference 5 2) (sourceB1875 + difference 2 5) sourceC1875) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1041) := by
    have ha : (tripleCharges (sourceA1875 + difference 5 2) (sourceB1875 + difference 2 5) sourceC1875) = raw21510 := by
      apply Matrix.ext; unfold tripleCharges sourceA1875 sourceB1875 sourceC1875 difference raw21510; decide +kernel
    rw [ha]
    exact (canonical21510 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1875 + difference 5 3) (sourceB1875 + difference 3 5) sourceC1875) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1041) := by
    have ha : (tripleCharges (sourceA1875 + difference 5 3) (sourceB1875 + difference 3 5) sourceC1875) = raw21506 := by
      apply Matrix.ext; unfold tripleCharges sourceA1875 sourceB1875 sourceC1875 difference raw21506; decide +kernel
    rw [ha]
    exact (canonical21506 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1875 + difference 5 4) (sourceB1875 + difference 4 5) sourceC1875) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 980) := by
    have ha : (tripleCharges (sourceA1875 + difference 5 4) (sourceB1875 + difference 4 5) sourceC1875) = raw25265 := by
      apply Matrix.ext; unfold tripleCharges sourceA1875 sourceB1875 sourceC1875 difference raw25265; decide +kernel
    rw [ha]
    exact (canonical25265 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1875 sourceB1875 sourceC1875
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1875, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1876 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceB1876 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceC1876 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceForm1876 : Integer.Sparse Master := [(Sum.inr 4249, 2), (Sum.inr 4252, 1), (Sum.inr 4263, 2), (Sum.inr 4449, 4), (Sum.inr 4451, 2), (Sum.inr 4455, 2), (Sum.inr 4456, 4), (Sum.inr 4469, 2), (Sum.inr 4473, 2), (Sum.inr 4495, 2), (Sum.inr 4497, 2), (Sum.inr 4599, 2), (Sum.inr 4601, 2), (Sum.inr 4622, 1)]

theorem sourceEq1876 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1876 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1876 + difference 0 1) (sourceB1876 + difference 1 0) sourceC1876) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4622) := by
    have ha : (tripleCharges (sourceA1876 + difference 0 1) (sourceB1876 + difference 1 0) sourceC1876) = raw26858 := by
      apply Matrix.ext; unfold tripleCharges sourceA1876 sourceB1876 sourceC1876 difference raw26858; decide +kernel
    rw [ha]
    exact (canonical26858 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1876 + difference 0 2) (sourceB1876 + difference 2 0) sourceC1876) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4601) := by
    have ha : (tripleCharges (sourceA1876 + difference 0 2) (sourceB1876 + difference 2 0) sourceC1876) = raw27012 := by
      apply Matrix.ext; unfold tripleCharges sourceA1876 sourceB1876 sourceC1876 difference raw27012; decide +kernel
    rw [ha]
    exact (canonical27012 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1876 + difference 0 3) (sourceB1876 + difference 3 0) sourceC1876) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4601) := by
    have ha : (tripleCharges (sourceA1876 + difference 0 3) (sourceB1876 + difference 3 0) sourceC1876) = raw27013 := by
      apply Matrix.ext; unfold tripleCharges sourceA1876 sourceB1876 sourceC1876 difference raw27013; decide +kernel
    rw [ha]
    exact (canonical27013 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1876 + difference 0 4) (sourceB1876 + difference 4 0) sourceC1876) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4599) := by
    have ha : (tripleCharges (sourceA1876 + difference 0 4) (sourceB1876 + difference 4 0) sourceC1876) = raw27014 := by
      apply Matrix.ext; unfold tripleCharges sourceA1876 sourceB1876 sourceC1876 difference raw27014; decide +kernel
    rw [ha]
    exact (canonical27014 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1876 + difference 0 5) (sourceB1876 + difference 5 0) sourceC1876) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4599) := by
    have ha : (tripleCharges (sourceA1876 + difference 0 5) (sourceB1876 + difference 5 0) sourceC1876) = raw27015 := by
      apply Matrix.ext; unfold tripleCharges sourceA1876 sourceB1876 sourceC1876 difference raw27015; decide +kernel
    rw [ha]
    exact (canonical27015 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1876 + difference 1 0) (sourceB1876 + difference 0 1) sourceC1876) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4252) := by
    have ha : (tripleCharges (sourceA1876 + difference 1 0) (sourceB1876 + difference 0 1) sourceC1876) = raw27016 := by
      apply Matrix.ext; unfold tripleCharges sourceA1876 sourceB1876 sourceC1876 difference raw27016; decide +kernel
    rw [ha]
    exact (canonical27016 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1876 + difference 1 2) (sourceB1876 + difference 2 1) sourceC1876) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4473) := by
    have ha : (tripleCharges (sourceA1876 + difference 1 2) (sourceB1876 + difference 2 1) sourceC1876) = raw27017 := by
      apply Matrix.ext; unfold tripleCharges sourceA1876 sourceB1876 sourceC1876 difference raw27017; decide +kernel
    rw [ha]
    exact (canonical27017 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1876 + difference 1 3) (sourceB1876 + difference 3 1) sourceC1876) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4473) := by
    have ha : (tripleCharges (sourceA1876 + difference 1 3) (sourceB1876 + difference 3 1) sourceC1876) = raw27018 := by
      apply Matrix.ext; unfold tripleCharges sourceA1876 sourceB1876 sourceC1876 difference raw27018; decide +kernel
    rw [ha]
    exact (canonical27018 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1876 + difference 1 4) (sourceB1876 + difference 4 1) sourceC1876) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4469) := by
    have ha : (tripleCharges (sourceA1876 + difference 1 4) (sourceB1876 + difference 4 1) sourceC1876) = raw27019 := by
      apply Matrix.ext; unfold tripleCharges sourceA1876 sourceB1876 sourceC1876 difference raw27019; decide +kernel
    rw [ha]
    exact (canonical27019 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1876 + difference 1 5) (sourceB1876 + difference 5 1) sourceC1876) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4469) := by
    have ha : (tripleCharges (sourceA1876 + difference 1 5) (sourceB1876 + difference 5 1) sourceC1876) = raw27020 := by
      apply Matrix.ext; unfold tripleCharges sourceA1876 sourceB1876 sourceC1876 difference raw27020; decide +kernel
    rw [ha]
    exact (canonical27020 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1876 + difference 2 0) (sourceB1876 + difference 0 2) sourceC1876) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4249) := by
    have ha : (tripleCharges (sourceA1876 + difference 2 0) (sourceB1876 + difference 0 2) sourceC1876) = raw27021 := by
      apply Matrix.ext; unfold tripleCharges sourceA1876 sourceB1876 sourceC1876 difference raw27021; decide +kernel
    rw [ha]
    exact (canonical27021 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1876 + difference 2 1) (sourceB1876 + difference 1 2) sourceC1876) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4495) := by
    have ha : (tripleCharges (sourceA1876 + difference 2 1) (sourceB1876 + difference 1 2) sourceC1876) = raw27022 := by
      apply Matrix.ext; unfold tripleCharges sourceA1876 sourceB1876 sourceC1876 difference raw27022; decide +kernel
    rw [ha]
    exact (canonical27022 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1876 + difference 2 3) (sourceB1876 + difference 3 2) sourceC1876) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4455) := by
    have ha : (tripleCharges (sourceA1876 + difference 2 3) (sourceB1876 + difference 3 2) sourceC1876) = raw27023 := by
      apply Matrix.ext; unfold tripleCharges sourceA1876 sourceB1876 sourceC1876 difference raw27023; decide +kernel
    rw [ha]
    exact (canonical27023 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1876 + difference 2 4) (sourceB1876 + difference 4 2) sourceC1876) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4449) := by
    have ha : (tripleCharges (sourceA1876 + difference 2 4) (sourceB1876 + difference 4 2) sourceC1876) = raw27024 := by
      apply Matrix.ext; unfold tripleCharges sourceA1876 sourceB1876 sourceC1876 difference raw27024; decide +kernel
    rw [ha]
    exact (canonical27024 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1876 + difference 2 5) (sourceB1876 + difference 5 2) sourceC1876) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4449) := by
    have ha : (tripleCharges (sourceA1876 + difference 2 5) (sourceB1876 + difference 5 2) sourceC1876) = raw27025 := by
      apply Matrix.ext; unfold tripleCharges sourceA1876 sourceB1876 sourceC1876 difference raw27025; decide +kernel
    rw [ha]
    exact (canonical27025 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1876 + difference 3 0) (sourceB1876 + difference 0 3) sourceC1876) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4249) := by
    have ha : (tripleCharges (sourceA1876 + difference 3 0) (sourceB1876 + difference 0 3) sourceC1876) = raw27026 := by
      apply Matrix.ext; unfold tripleCharges sourceA1876 sourceB1876 sourceC1876 difference raw27026; decide +kernel
    rw [ha]
    exact (canonical27026 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1876 + difference 3 1) (sourceB1876 + difference 1 3) sourceC1876) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4495) := by
    have ha : (tripleCharges (sourceA1876 + difference 3 1) (sourceB1876 + difference 1 3) sourceC1876) = raw27027 := by
      apply Matrix.ext; unfold tripleCharges sourceA1876 sourceB1876 sourceC1876 difference raw27027; decide +kernel
    rw [ha]
    exact (canonical27027 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1876 + difference 3 2) (sourceB1876 + difference 2 3) sourceC1876) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4455) := by
    have ha : (tripleCharges (sourceA1876 + difference 3 2) (sourceB1876 + difference 2 3) sourceC1876) = raw27028 := by
      apply Matrix.ext; unfold tripleCharges sourceA1876 sourceB1876 sourceC1876 difference raw27028; decide +kernel
    rw [ha]
    exact (canonical27028 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1876 + difference 3 4) (sourceB1876 + difference 4 3) sourceC1876) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4449) := by
    have ha : (tripleCharges (sourceA1876 + difference 3 4) (sourceB1876 + difference 4 3) sourceC1876) = raw27029 := by
      apply Matrix.ext; unfold tripleCharges sourceA1876 sourceB1876 sourceC1876 difference raw27029; decide +kernel
    rw [ha]
    exact (canonical27029 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1876 + difference 3 5) (sourceB1876 + difference 5 3) sourceC1876) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4449) := by
    have ha : (tripleCharges (sourceA1876 + difference 3 5) (sourceB1876 + difference 5 3) sourceC1876) = raw27030 := by
      apply Matrix.ext; unfold tripleCharges sourceA1876 sourceB1876 sourceC1876 difference raw27030; decide +kernel
    rw [ha]
    exact (canonical27030 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1876 + difference 4 0) (sourceB1876 + difference 0 4) sourceC1876) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4263) := by
    have ha : (tripleCharges (sourceA1876 + difference 4 0) (sourceB1876 + difference 0 4) sourceC1876) = raw27031 := by
      apply Matrix.ext; unfold tripleCharges sourceA1876 sourceB1876 sourceC1876 difference raw27031; decide +kernel
    rw [ha]
    exact (canonical27031 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1876 + difference 4 1) (sourceB1876 + difference 1 4) sourceC1876) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4497) := by
    have ha : (tripleCharges (sourceA1876 + difference 4 1) (sourceB1876 + difference 1 4) sourceC1876) = raw26857 := by
      apply Matrix.ext; unfold tripleCharges sourceA1876 sourceB1876 sourceC1876 difference raw26857; decide +kernel
    rw [ha]
    exact (canonical26857 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1876 + difference 4 2) (sourceB1876 + difference 2 4) sourceC1876) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4456) := by
    have ha : (tripleCharges (sourceA1876 + difference 4 2) (sourceB1876 + difference 2 4) sourceC1876) = raw27032 := by
      apply Matrix.ext; unfold tripleCharges sourceA1876 sourceB1876 sourceC1876 difference raw27032; decide +kernel
    rw [ha]
    exact (canonical27032 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1876 + difference 4 3) (sourceB1876 + difference 3 4) sourceC1876) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4456) := by
    have ha : (tripleCharges (sourceA1876 + difference 4 3) (sourceB1876 + difference 3 4) sourceC1876) = raw27033 := by
      apply Matrix.ext; unfold tripleCharges sourceA1876 sourceB1876 sourceC1876 difference raw27033; decide +kernel
    rw [ha]
    exact (canonical27033 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1876 + difference 4 5) (sourceB1876 + difference 5 4) sourceC1876) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4451) := by
    have ha : (tripleCharges (sourceA1876 + difference 4 5) (sourceB1876 + difference 5 4) sourceC1876) = raw27034 := by
      apply Matrix.ext; unfold tripleCharges sourceA1876 sourceB1876 sourceC1876 difference raw27034; decide +kernel
    rw [ha]
    exact (canonical27034 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1876 + difference 5 0) (sourceB1876 + difference 0 5) sourceC1876) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4263) := by
    have ha : (tripleCharges (sourceA1876 + difference 5 0) (sourceB1876 + difference 0 5) sourceC1876) = raw27035 := by
      apply Matrix.ext; unfold tripleCharges sourceA1876 sourceB1876 sourceC1876 difference raw27035; decide +kernel
    rw [ha]
    exact (canonical27035 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1876 + difference 5 1) (sourceB1876 + difference 1 5) sourceC1876) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4497) := by
    have ha : (tripleCharges (sourceA1876 + difference 5 1) (sourceB1876 + difference 1 5) sourceC1876) = raw27036 := by
      apply Matrix.ext; unfold tripleCharges sourceA1876 sourceB1876 sourceC1876 difference raw27036; decide +kernel
    rw [ha]
    exact (canonical27036 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1876 + difference 5 2) (sourceB1876 + difference 2 5) sourceC1876) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4456) := by
    have ha : (tripleCharges (sourceA1876 + difference 5 2) (sourceB1876 + difference 2 5) sourceC1876) = raw27037 := by
      apply Matrix.ext; unfold tripleCharges sourceA1876 sourceB1876 sourceC1876 difference raw27037; decide +kernel
    rw [ha]
    exact (canonical27037 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1876 + difference 5 3) (sourceB1876 + difference 3 5) sourceC1876) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4456) := by
    have ha : (tripleCharges (sourceA1876 + difference 5 3) (sourceB1876 + difference 3 5) sourceC1876) = raw27038 := by
      apply Matrix.ext; unfold tripleCharges sourceA1876 sourceB1876 sourceC1876 difference raw27038; decide +kernel
    rw [ha]
    exact (canonical27038 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1876 + difference 5 4) (sourceB1876 + difference 4 5) sourceC1876) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4451) := by
    have ha : (tripleCharges (sourceA1876 + difference 5 4) (sourceB1876 + difference 4 5) sourceC1876) = raw27039 := by
      apply Matrix.ext; unfold tripleCharges sourceA1876 sourceB1876 sourceC1876 difference raw27039; decide +kernel
    rw [ha]
    exact (canonical27039 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1876 sourceB1876 sourceC1876
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1876, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1877 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1877 : Charge := ![1, 0, 2, 0, -1, -2]
def sourceC1877 : Charge := ![3, 0, -3, -1, 0, 1]
def sourceForm1877 : Integer.Sparse Master := [(Sum.inr 1070, 1), (Sum.inr 2043, 1), (Sum.inr 2220, 1), (Sum.inr 2224, 1), (Sum.inr 2259, 1), (Sum.inr 2287, 1), (Sum.inr 4081, -1)]

theorem sourceEq1877 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1877 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1877 + difference 0 0) (sourceB1877 + difference 0 0) sourceC1877) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1070) := by
    have ha : (tripleCharges (sourceA1877 + difference 0 0) (sourceB1877 + difference 0 0) sourceC1877) = raw27040 := by
      apply Matrix.ext; unfold tripleCharges sourceA1877 sourceB1877 sourceC1877 difference raw27040; decide +kernel
    rw [ha]
    exact (canonical27040 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1877 + difference 0 1) (sourceB1877 + difference 1 0) sourceC1877) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2043) := by
    have ha : (tripleCharges (sourceA1877 + difference 0 1) (sourceB1877 + difference 1 0) sourceC1877) = raw27041 := by
      apply Matrix.ext; unfold tripleCharges sourceA1877 sourceB1877 sourceC1877 difference raw27041; decide +kernel
    rw [ha]
    exact (canonical27041 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1877 + difference 0 2) (sourceB1877 + difference 2 0) sourceC1877) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2220) := by
    have ha : (tripleCharges (sourceA1877 + difference 0 2) (sourceB1877 + difference 2 0) sourceC1877) = raw27042 := by
      apply Matrix.ext; unfold tripleCharges sourceA1877 sourceB1877 sourceC1877 difference raw27042; decide +kernel
    rw [ha]
    exact (canonical27042 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1877 + difference 0 3) (sourceB1877 + difference 3 0) sourceC1877) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2259) := by
    have ha : (tripleCharges (sourceA1877 + difference 0 3) (sourceB1877 + difference 3 0) sourceC1877) = raw27043 := by
      apply Matrix.ext; unfold tripleCharges sourceA1877 sourceB1877 sourceC1877 difference raw27043; decide +kernel
    rw [ha]
    exact (canonical27043 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1877 + difference 0 4) (sourceB1877 + difference 4 0) sourceC1877) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2287) := by
    have ha : (tripleCharges (sourceA1877 + difference 0 4) (sourceB1877 + difference 4 0) sourceC1877) = raw27044 := by
      apply Matrix.ext; unfold tripleCharges sourceA1877 sourceB1877 sourceC1877 difference raw27044; decide +kernel
    rw [ha]
    exact (canonical27044 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1877 + difference 0 5) (sourceB1877 + difference 5 0) sourceC1877) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2224) := by
    have ha : (tripleCharges (sourceA1877 + difference 0 5) (sourceB1877 + difference 5 0) sourceC1877) = raw27045 := by
      apply Matrix.ext; unfold tripleCharges sourceA1877 sourceB1877 sourceC1877 difference raw27045; decide +kernel
    rw [ha]
    exact (canonical27045 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1877 + sourceB1877) sourceC1877) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1877 + sourceB1877) sourceC1877) = raw27046 := by
      apply Matrix.ext; unfold doubleCharges sourceA1877 sourceB1877 sourceC1877 raw27046; decide +kernel
    rw [ha]
    exact (canonical27046 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1877 sourceB1877 sourceC1877
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1877, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1878 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1878 : Charge := ![1, 0, 1, 1, -1, -2]
def sourceC1878 : Charge := ![3, 0, -2, -2, 0, 1]
def sourceForm1878 : Integer.Sparse Master := [(Sum.inr 1071, 1), (Sum.inr 2044, 1), (Sum.inr 2225, 1), (Sum.inr 2274, 2), (Sum.inr 2288, 1), (Sum.inr 4082, -1)]

theorem sourceEq1878 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1878 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1878 + difference 0 0) (sourceB1878 + difference 0 0) sourceC1878) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1071) := by
    have ha : (tripleCharges (sourceA1878 + difference 0 0) (sourceB1878 + difference 0 0) sourceC1878) = raw27047 := by
      apply Matrix.ext; unfold tripleCharges sourceA1878 sourceB1878 sourceC1878 difference raw27047; decide +kernel
    rw [ha]
    exact (canonical27047 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1878 + difference 0 1) (sourceB1878 + difference 1 0) sourceC1878) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2044) := by
    have ha : (tripleCharges (sourceA1878 + difference 0 1) (sourceB1878 + difference 1 0) sourceC1878) = raw27048 := by
      apply Matrix.ext; unfold tripleCharges sourceA1878 sourceB1878 sourceC1878 difference raw27048; decide +kernel
    rw [ha]
    exact (canonical27048 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1878 + difference 0 2) (sourceB1878 + difference 2 0) sourceC1878) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2274) := by
    have ha : (tripleCharges (sourceA1878 + difference 0 2) (sourceB1878 + difference 2 0) sourceC1878) = raw27049 := by
      apply Matrix.ext; unfold tripleCharges sourceA1878 sourceB1878 sourceC1878 difference raw27049; decide +kernel
    rw [ha]
    exact (canonical27049 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1878 + difference 0 3) (sourceB1878 + difference 3 0) sourceC1878) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2274) := by
    have ha : (tripleCharges (sourceA1878 + difference 0 3) (sourceB1878 + difference 3 0) sourceC1878) = raw27050 := by
      apply Matrix.ext; unfold tripleCharges sourceA1878 sourceB1878 sourceC1878 difference raw27050; decide +kernel
    rw [ha]
    exact (canonical27050 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1878 + difference 0 4) (sourceB1878 + difference 4 0) sourceC1878) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2288) := by
    have ha : (tripleCharges (sourceA1878 + difference 0 4) (sourceB1878 + difference 4 0) sourceC1878) = raw27051 := by
      apply Matrix.ext; unfold tripleCharges sourceA1878 sourceB1878 sourceC1878 difference raw27051; decide +kernel
    rw [ha]
    exact (canonical27051 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1878 + difference 0 5) (sourceB1878 + difference 5 0) sourceC1878) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2225) := by
    have ha : (tripleCharges (sourceA1878 + difference 0 5) (sourceB1878 + difference 5 0) sourceC1878) = raw27052 := by
      apply Matrix.ext; unfold tripleCharges sourceA1878 sourceB1878 sourceC1878 difference raw27052; decide +kernel
    rw [ha]
    exact (canonical27052 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1878 + sourceB1878) sourceC1878) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA1878 + sourceB1878) sourceC1878) = raw27053 := by
      apply Matrix.ext; unfold doubleCharges sourceA1878 sourceB1878 sourceC1878 raw27053; decide +kernel
    rw [ha]
    exact (canonical27053 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1878 sourceB1878 sourceC1878
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1878, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1879 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1879 : Charge := ![1, 0, 1, 0, 0, -2]
def sourceC1879 : Charge := ![3, 0, -2, -1, -1, 1]
def sourceForm1879 : Integer.Sparse Master := [(Sum.inr 1073, 1), (Sum.inr 2046, 1), (Sum.inr 2227, 1), (Sum.inr 2260, 2), (Sum.inr 2275, 1), (Sum.inr 4080, -1)]

theorem sourceEq1879 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1879 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1879 + difference 0 0) (sourceB1879 + difference 0 0) sourceC1879) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1073) := by
    have ha : (tripleCharges (sourceA1879 + difference 0 0) (sourceB1879 + difference 0 0) sourceC1879) = raw27054 := by
      apply Matrix.ext; unfold tripleCharges sourceA1879 sourceB1879 sourceC1879 difference raw27054; decide +kernel
    rw [ha]
    exact (canonical27054 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1879 + difference 0 1) (sourceB1879 + difference 1 0) sourceC1879) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2046) := by
    have ha : (tripleCharges (sourceA1879 + difference 0 1) (sourceB1879 + difference 1 0) sourceC1879) = raw27055 := by
      apply Matrix.ext; unfold tripleCharges sourceA1879 sourceB1879 sourceC1879 difference raw27055; decide +kernel
    rw [ha]
    exact (canonical27055 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1879 + difference 0 2) (sourceB1879 + difference 2 0) sourceC1879) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2275) := by
    have ha : (tripleCharges (sourceA1879 + difference 0 2) (sourceB1879 + difference 2 0) sourceC1879) = raw27056 := by
      apply Matrix.ext; unfold tripleCharges sourceA1879 sourceB1879 sourceC1879 difference raw27056; decide +kernel
    rw [ha]
    exact (canonical27056 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1879 + difference 0 3) (sourceB1879 + difference 3 0) sourceC1879) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2260) := by
    have ha : (tripleCharges (sourceA1879 + difference 0 3) (sourceB1879 + difference 3 0) sourceC1879) = raw27057 := by
      apply Matrix.ext; unfold tripleCharges sourceA1879 sourceB1879 sourceC1879 difference raw27057; decide +kernel
    rw [ha]
    exact (canonical27057 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1879 + difference 0 4) (sourceB1879 + difference 4 0) sourceC1879) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2260) := by
    have ha : (tripleCharges (sourceA1879 + difference 0 4) (sourceB1879 + difference 4 0) sourceC1879) = raw27058 := by
      apply Matrix.ext; unfold tripleCharges sourceA1879 sourceB1879 sourceC1879 difference raw27058; decide +kernel
    rw [ha]
    exact (canonical27058 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1879 + difference 0 5) (sourceB1879 + difference 5 0) sourceC1879) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2227) := by
    have ha : (tripleCharges (sourceA1879 + difference 0 5) (sourceB1879 + difference 5 0) sourceC1879) = raw27059 := by
      apply Matrix.ext; unfold tripleCharges sourceA1879 sourceB1879 sourceC1879 difference raw27059; decide +kernel
    rw [ha]
    exact (canonical27059 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1879 + sourceB1879) sourceC1879) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1879 + sourceB1879) sourceC1879) = raw27060 := by
      apply Matrix.ext; unfold doubleCharges sourceA1879 sourceB1879 sourceC1879 raw27060; decide +kernel
    rw [ha]
    exact (canonical27060 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1879 sourceB1879 sourceC1879
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1879, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1880 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1880 : Charge := ![1, 0, 1, 0, -1, -1]
def sourceC1880 : Charge := ![3, 0, -2, -1, 0, 0]
def sourceForm1880 : Integer.Sparse Master := [(Sum.inr 4169, 1), (Sum.inr 4172, 1), (Sum.inr 4173, 1), (Sum.inr 4176, 2), (Sum.inr 4341, 1), (Sum.inr 4342, 1), (Sum.inr 4345, 2), (Sum.inr 4455, 1), (Sum.inr 4457, 1), (Sum.inr 4459, 2), (Sum.inr 4473, 1), (Sum.inr 4474, 1), (Sum.inr 4475, 2), (Sum.inr 4495, 2), (Sum.inr 4498, 2), (Sum.inr 4499, 2), (Sum.inr 4503, 2), (Sum.inr 4831, 1), (Sum.inr 4888, 1), (Sum.inr 4889, 1), (Sum.inr 4895, 2)]

theorem sourceEq1880 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1880 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1880 + difference 0 1) (sourceB1880 + difference 1 0) sourceC1880) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4831) := by
    have ha : (tripleCharges (sourceA1880 + difference 0 1) (sourceB1880 + difference 1 0) sourceC1880) = raw27061 := by
      apply Matrix.ext; unfold tripleCharges sourceA1880 sourceB1880 sourceC1880 difference raw27061; decide +kernel
    rw [ha]
    exact (canonical27061 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1880 + difference 0 2) (sourceB1880 + difference 2 0) sourceC1880) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA1880 + difference 0 2) (sourceB1880 + difference 2 0) sourceC1880) = raw27062 := by
      apply Matrix.ext; unfold tripleCharges sourceA1880 sourceB1880 sourceC1880 difference raw27062; decide +kernel
    rw [ha]
    exact (canonical27062 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1880 + difference 0 3) (sourceB1880 + difference 3 0) sourceC1880) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA1880 + difference 0 3) (sourceB1880 + difference 3 0) sourceC1880) = raw27063 := by
      apply Matrix.ext; unfold tripleCharges sourceA1880 sourceB1880 sourceC1880 difference raw27063; decide +kernel
    rw [ha]
    exact (canonical27063 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1880 + difference 0 4) (sourceB1880 + difference 4 0) sourceC1880) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA1880 + difference 0 4) (sourceB1880 + difference 4 0) sourceC1880) = raw27064 := by
      apply Matrix.ext; unfold tripleCharges sourceA1880 sourceB1880 sourceC1880 difference raw27064; decide +kernel
    rw [ha]
    exact (canonical27064 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1880 + difference 0 5) (sourceB1880 + difference 5 0) sourceC1880) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA1880 + difference 0 5) (sourceB1880 + difference 5 0) sourceC1880) = raw27065 := by
      apply Matrix.ext; unfold tripleCharges sourceA1880 sourceB1880 sourceC1880 difference raw27065; decide +kernel
    rw [ha]
    exact (canonical27065 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1880 + difference 1 0) (sourceB1880 + difference 0 1) sourceC1880) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4169) := by
    have ha : (tripleCharges (sourceA1880 + difference 1 0) (sourceB1880 + difference 0 1) sourceC1880) = raw27066 := by
      apply Matrix.ext; unfold tripleCharges sourceA1880 sourceB1880 sourceC1880 difference raw27066; decide +kernel
    rw [ha]
    exact (canonical27066 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1880 + difference 1 2) (sourceB1880 + difference 2 1) sourceC1880) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4473) := by
    have ha : (tripleCharges (sourceA1880 + difference 1 2) (sourceB1880 + difference 2 1) sourceC1880) = raw27067 := by
      apply Matrix.ext; unfold tripleCharges sourceA1880 sourceB1880 sourceC1880 difference raw27067; decide +kernel
    rw [ha]
    exact (canonical27067 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1880 + difference 1 3) (sourceB1880 + difference 3 1) sourceC1880) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4455) := by
    have ha : (tripleCharges (sourceA1880 + difference 1 3) (sourceB1880 + difference 3 1) sourceC1880) = raw27068 := by
      apply Matrix.ext; unfold tripleCharges sourceA1880 sourceB1880 sourceC1880 difference raw27068; decide +kernel
    rw [ha]
    exact (canonical27068 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1880 + difference 1 4) (sourceB1880 + difference 4 1) sourceC1880) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4495) := by
    have ha : (tripleCharges (sourceA1880 + difference 1 4) (sourceB1880 + difference 4 1) sourceC1880) = raw27069 := by
      apply Matrix.ext; unfold tripleCharges sourceA1880 sourceB1880 sourceC1880 difference raw27069; decide +kernel
    rw [ha]
    exact (canonical27069 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1880 + difference 1 5) (sourceB1880 + difference 5 1) sourceC1880) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4495) := by
    have ha : (tripleCharges (sourceA1880 + difference 1 5) (sourceB1880 + difference 5 1) sourceC1880) = raw27070 := by
      apply Matrix.ext; unfold tripleCharges sourceA1880 sourceB1880 sourceC1880 difference raw27070; decide +kernel
    rw [ha]
    exact (canonical27070 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1880 + difference 2 0) (sourceB1880 + difference 0 2) sourceC1880) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4172) := by
    have ha : (tripleCharges (sourceA1880 + difference 2 0) (sourceB1880 + difference 0 2) sourceC1880) = raw27071 := by
      apply Matrix.ext; unfold tripleCharges sourceA1880 sourceB1880 sourceC1880 difference raw27071; decide +kernel
    rw [ha]
    exact (canonical27071 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1880 + difference 2 1) (sourceB1880 + difference 1 2) sourceC1880) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4341) := by
    have ha : (tripleCharges (sourceA1880 + difference 2 1) (sourceB1880 + difference 1 2) sourceC1880) = raw27072 := by
      apply Matrix.ext; unfold tripleCharges sourceA1880 sourceB1880 sourceC1880 difference raw27072; decide +kernel
    rw [ha]
    exact (canonical27072 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1880 + difference 2 3) (sourceB1880 + difference 3 2) sourceC1880) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4457) := by
    have ha : (tripleCharges (sourceA1880 + difference 2 3) (sourceB1880 + difference 3 2) sourceC1880) = raw27073 := by
      apply Matrix.ext; unfold tripleCharges sourceA1880 sourceB1880 sourceC1880 difference raw27073; decide +kernel
    rw [ha]
    exact (canonical27073 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1880 + difference 2 4) (sourceB1880 + difference 4 2) sourceC1880) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4498) := by
    have ha : (tripleCharges (sourceA1880 + difference 2 4) (sourceB1880 + difference 4 2) sourceC1880) = raw27074 := by
      apply Matrix.ext; unfold tripleCharges sourceA1880 sourceB1880 sourceC1880 difference raw27074; decide +kernel
    rw [ha]
    exact (canonical27074 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1880 + difference 2 5) (sourceB1880 + difference 5 2) sourceC1880) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4498) := by
    have ha : (tripleCharges (sourceA1880 + difference 2 5) (sourceB1880 + difference 5 2) sourceC1880) = raw27075 := by
      apply Matrix.ext; unfold tripleCharges sourceA1880 sourceB1880 sourceC1880 difference raw27075; decide +kernel
    rw [ha]
    exact (canonical27075 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1880 + difference 3 0) (sourceB1880 + difference 0 3) sourceC1880) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4173) := by
    have ha : (tripleCharges (sourceA1880 + difference 3 0) (sourceB1880 + difference 0 3) sourceC1880) = raw27076 := by
      apply Matrix.ext; unfold tripleCharges sourceA1880 sourceB1880 sourceC1880 difference raw27076; decide +kernel
    rw [ha]
    exact (canonical27076 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1880 + difference 3 1) (sourceB1880 + difference 1 3) sourceC1880) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4342) := by
    have ha : (tripleCharges (sourceA1880 + difference 3 1) (sourceB1880 + difference 1 3) sourceC1880) = raw27077 := by
      apply Matrix.ext; unfold tripleCharges sourceA1880 sourceB1880 sourceC1880 difference raw27077; decide +kernel
    rw [ha]
    exact (canonical27077 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1880 + difference 3 2) (sourceB1880 + difference 2 3) sourceC1880) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4474) := by
    have ha : (tripleCharges (sourceA1880 + difference 3 2) (sourceB1880 + difference 2 3) sourceC1880) = raw27078 := by
      apply Matrix.ext; unfold tripleCharges sourceA1880 sourceB1880 sourceC1880 difference raw27078; decide +kernel
    rw [ha]
    exact (canonical27078 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1880 + difference 3 4) (sourceB1880 + difference 4 3) sourceC1880) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4499) := by
    have ha : (tripleCharges (sourceA1880 + difference 3 4) (sourceB1880 + difference 4 3) sourceC1880) = raw27079 := by
      apply Matrix.ext; unfold tripleCharges sourceA1880 sourceB1880 sourceC1880 difference raw27079; decide +kernel
    rw [ha]
    exact (canonical27079 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1880 + difference 3 5) (sourceB1880 + difference 5 3) sourceC1880) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4499) := by
    have ha : (tripleCharges (sourceA1880 + difference 3 5) (sourceB1880 + difference 5 3) sourceC1880) = raw27080 := by
      apply Matrix.ext; unfold tripleCharges sourceA1880 sourceB1880 sourceC1880 difference raw27080; decide +kernel
    rw [ha]
    exact (canonical27080 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1880 + difference 4 0) (sourceB1880 + difference 0 4) sourceC1880) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4176) := by
    have ha : (tripleCharges (sourceA1880 + difference 4 0) (sourceB1880 + difference 0 4) sourceC1880) = raw27081 := by
      apply Matrix.ext; unfold tripleCharges sourceA1880 sourceB1880 sourceC1880 difference raw27081; decide +kernel
    rw [ha]
    exact (canonical27081 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1880 + difference 4 1) (sourceB1880 + difference 1 4) sourceC1880) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4345) := by
    have ha : (tripleCharges (sourceA1880 + difference 4 1) (sourceB1880 + difference 1 4) sourceC1880) = raw27082 := by
      apply Matrix.ext; unfold tripleCharges sourceA1880 sourceB1880 sourceC1880 difference raw27082; decide +kernel
    rw [ha]
    exact (canonical27082 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1880 + difference 4 2) (sourceB1880 + difference 2 4) sourceC1880) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4475) := by
    have ha : (tripleCharges (sourceA1880 + difference 4 2) (sourceB1880 + difference 2 4) sourceC1880) = raw27083 := by
      apply Matrix.ext; unfold tripleCharges sourceA1880 sourceB1880 sourceC1880 difference raw27083; decide +kernel
    rw [ha]
    exact (canonical27083 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1880 + difference 4 3) (sourceB1880 + difference 3 4) sourceC1880) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4459) := by
    have ha : (tripleCharges (sourceA1880 + difference 4 3) (sourceB1880 + difference 3 4) sourceC1880) = raw27084 := by
      apply Matrix.ext; unfold tripleCharges sourceA1880 sourceB1880 sourceC1880 difference raw27084; decide +kernel
    rw [ha]
    exact (canonical27084 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1880 + difference 4 5) (sourceB1880 + difference 5 4) sourceC1880) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4503) := by
    have ha : (tripleCharges (sourceA1880 + difference 4 5) (sourceB1880 + difference 5 4) sourceC1880) = raw27085 := by
      apply Matrix.ext; unfold tripleCharges sourceA1880 sourceB1880 sourceC1880 difference raw27085; decide +kernel
    rw [ha]
    exact (canonical27085 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1880 + difference 5 0) (sourceB1880 + difference 0 5) sourceC1880) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4176) := by
    have ha : (tripleCharges (sourceA1880 + difference 5 0) (sourceB1880 + difference 0 5) sourceC1880) = raw27086 := by
      apply Matrix.ext; unfold tripleCharges sourceA1880 sourceB1880 sourceC1880 difference raw27086; decide +kernel
    rw [ha]
    exact (canonical27086 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1880 + difference 5 1) (sourceB1880 + difference 1 5) sourceC1880) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4345) := by
    have ha : (tripleCharges (sourceA1880 + difference 5 1) (sourceB1880 + difference 1 5) sourceC1880) = raw27087 := by
      apply Matrix.ext; unfold tripleCharges sourceA1880 sourceB1880 sourceC1880 difference raw27087; decide +kernel
    rw [ha]
    exact (canonical27087 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1880 + difference 5 2) (sourceB1880 + difference 2 5) sourceC1880) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4475) := by
    have ha : (tripleCharges (sourceA1880 + difference 5 2) (sourceB1880 + difference 2 5) sourceC1880) = raw27088 := by
      apply Matrix.ext; unfold tripleCharges sourceA1880 sourceB1880 sourceC1880 difference raw27088; decide +kernel
    rw [ha]
    exact (canonical27088 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1880 + difference 5 3) (sourceB1880 + difference 3 5) sourceC1880) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4459) := by
    have ha : (tripleCharges (sourceA1880 + difference 5 3) (sourceB1880 + difference 3 5) sourceC1880) = raw27089 := by
      apply Matrix.ext; unfold tripleCharges sourceA1880 sourceB1880 sourceC1880 difference raw27089; decide +kernel
    rw [ha]
    exact (canonical27089 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1880 + difference 5 4) (sourceB1880 + difference 4 5) sourceC1880) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4503) := by
    have ha : (tripleCharges (sourceA1880 + difference 5 4) (sourceB1880 + difference 4 5) sourceC1880) = raw27090 := by
      apply Matrix.ext; unfold tripleCharges sourceA1880 sourceB1880 sourceC1880 difference raw27090; decide +kernel
    rw [ha]
    exact (canonical27090 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1880 sourceB1880 sourceC1880
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1880, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1881 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1881 : Charge := ![1, 0, 1, 0, -1, -1]
def sourceC1881 : Charge := ![3, 0, -2, -1, 0, 0]
def sourceForm1881 : Integer.Sparse Master := [(Sum.inr 1502, 1), (Sum.inr 1507, 1), (Sum.inr 1508, 1), (Sum.inr 1512, 2), (Sum.inr 1664, 1), (Sum.inr 1665, 1), (Sum.inr 1668, 2), (Sum.inr 1698, 1), (Sum.inr 1699, 1), (Sum.inr 1707, 1), (Sum.inr 1708, 2), (Sum.inr 1709, 1), (Sum.inr 1714, 2), (Sum.inr 1715, 2), (Sum.inr 1727, 2), (Sum.inr 1728, 2), (Sum.inr 1739, 2), (Sum.inr 2191, 1), (Sum.inr 2244, 1), (Sum.inr 2245, 1), (Sum.inr 2265, 2)]

theorem sourceEq1881 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1881 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1881 + difference 0 1) (sourceB1881 + difference 1 0) sourceC1881) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2191) := by
    have ha : (tripleCharges (sourceA1881 + difference 0 1) (sourceB1881 + difference 1 0) sourceC1881) = raw27091 := by
      apply Matrix.ext; unfold tripleCharges sourceA1881 sourceB1881 sourceC1881 difference raw27091; decide +kernel
    rw [ha]
    exact (canonical27091 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1881 + difference 0 2) (sourceB1881 + difference 2 0) sourceC1881) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2245) := by
    have ha : (tripleCharges (sourceA1881 + difference 0 2) (sourceB1881 + difference 2 0) sourceC1881) = raw27092 := by
      apply Matrix.ext; unfold tripleCharges sourceA1881 sourceB1881 sourceC1881 difference raw27092; decide +kernel
    rw [ha]
    exact (canonical27092 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1881 + difference 0 3) (sourceB1881 + difference 3 0) sourceC1881) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2244) := by
    have ha : (tripleCharges (sourceA1881 + difference 0 3) (sourceB1881 + difference 3 0) sourceC1881) = raw27093 := by
      apply Matrix.ext; unfold tripleCharges sourceA1881 sourceB1881 sourceC1881 difference raw27093; decide +kernel
    rw [ha]
    exact (canonical27093 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1881 + difference 0 4) (sourceB1881 + difference 4 0) sourceC1881) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2265) := by
    have ha : (tripleCharges (sourceA1881 + difference 0 4) (sourceB1881 + difference 4 0) sourceC1881) = raw27094 := by
      apply Matrix.ext; unfold tripleCharges sourceA1881 sourceB1881 sourceC1881 difference raw27094; decide +kernel
    rw [ha]
    exact (canonical27094 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1881 + difference 0 5) (sourceB1881 + difference 5 0) sourceC1881) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2265) := by
    have ha : (tripleCharges (sourceA1881 + difference 0 5) (sourceB1881 + difference 5 0) sourceC1881) = raw27095 := by
      apply Matrix.ext; unfold tripleCharges sourceA1881 sourceB1881 sourceC1881 difference raw27095; decide +kernel
    rw [ha]
    exact (canonical27095 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1881 + difference 1 0) (sourceB1881 + difference 0 1) sourceC1881) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1502) := by
    have ha : (tripleCharges (sourceA1881 + difference 1 0) (sourceB1881 + difference 0 1) sourceC1881) = raw27096 := by
      apply Matrix.ext; unfold tripleCharges sourceA1881 sourceB1881 sourceC1881 difference raw27096; decide +kernel
    rw [ha]
    exact (canonical27096 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1881 + difference 1 2) (sourceB1881 + difference 2 1) sourceC1881) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1699) := by
    have ha : (tripleCharges (sourceA1881 + difference 1 2) (sourceB1881 + difference 2 1) sourceC1881) = raw27097 := by
      apply Matrix.ext; unfold tripleCharges sourceA1881 sourceB1881 sourceC1881 difference raw27097; decide +kernel
    rw [ha]
    exact (canonical27097 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1881 + difference 1 3) (sourceB1881 + difference 3 1) sourceC1881) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1698) := by
    have ha : (tripleCharges (sourceA1881 + difference 1 3) (sourceB1881 + difference 3 1) sourceC1881) = raw27098 := by
      apply Matrix.ext; unfold tripleCharges sourceA1881 sourceB1881 sourceC1881 difference raw27098; decide +kernel
    rw [ha]
    exact (canonical27098 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1881 + difference 1 4) (sourceB1881 + difference 4 1) sourceC1881) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1708) := by
    have ha : (tripleCharges (sourceA1881 + difference 1 4) (sourceB1881 + difference 4 1) sourceC1881) = raw27099 := by
      apply Matrix.ext; unfold tripleCharges sourceA1881 sourceB1881 sourceC1881 difference raw27099; decide +kernel
    rw [ha]
    exact (canonical27099 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1881 + difference 1 5) (sourceB1881 + difference 5 1) sourceC1881) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1708) := by
    have ha : (tripleCharges (sourceA1881 + difference 1 5) (sourceB1881 + difference 5 1) sourceC1881) = raw27100 := by
      apply Matrix.ext; unfold tripleCharges sourceA1881 sourceB1881 sourceC1881 difference raw27100; decide +kernel
    rw [ha]
    exact (canonical27100 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1881 + difference 2 0) (sourceB1881 + difference 0 2) sourceC1881) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1507) := by
    have ha : (tripleCharges (sourceA1881 + difference 2 0) (sourceB1881 + difference 0 2) sourceC1881) = raw27101 := by
      apply Matrix.ext; unfold tripleCharges sourceA1881 sourceB1881 sourceC1881 difference raw27101; decide +kernel
    rw [ha]
    exact (canonical27101 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1881 + difference 2 1) (sourceB1881 + difference 1 2) sourceC1881) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1664) := by
    have ha : (tripleCharges (sourceA1881 + difference 2 1) (sourceB1881 + difference 1 2) sourceC1881) = raw27102 := by
      apply Matrix.ext; unfold tripleCharges sourceA1881 sourceB1881 sourceC1881 difference raw27102; decide +kernel
    rw [ha]
    exact (canonical27102 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1881 + difference 2 3) (sourceB1881 + difference 3 2) sourceC1881) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1707) := by
    have ha : (tripleCharges (sourceA1881 + difference 2 3) (sourceB1881 + difference 3 2) sourceC1881) = raw27103 := by
      apply Matrix.ext; unfold tripleCharges sourceA1881 sourceB1881 sourceC1881 difference raw27103; decide +kernel
    rw [ha]
    exact (canonical27103 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1881 + difference 2 4) (sourceB1881 + difference 4 2) sourceC1881) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1727) := by
    have ha : (tripleCharges (sourceA1881 + difference 2 4) (sourceB1881 + difference 4 2) sourceC1881) = raw27104 := by
      apply Matrix.ext; unfold tripleCharges sourceA1881 sourceB1881 sourceC1881 difference raw27104; decide +kernel
    rw [ha]
    exact (canonical27104 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1881 + difference 2 5) (sourceB1881 + difference 5 2) sourceC1881) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1727) := by
    have ha : (tripleCharges (sourceA1881 + difference 2 5) (sourceB1881 + difference 5 2) sourceC1881) = raw27105 := by
      apply Matrix.ext; unfold tripleCharges sourceA1881 sourceB1881 sourceC1881 difference raw27105; decide +kernel
    rw [ha]
    exact (canonical27105 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1881 + difference 3 0) (sourceB1881 + difference 0 3) sourceC1881) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1508) := by
    have ha : (tripleCharges (sourceA1881 + difference 3 0) (sourceB1881 + difference 0 3) sourceC1881) = raw27106 := by
      apply Matrix.ext; unfold tripleCharges sourceA1881 sourceB1881 sourceC1881 difference raw27106; decide +kernel
    rw [ha]
    exact (canonical27106 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1881 + difference 3 1) (sourceB1881 + difference 1 3) sourceC1881) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1665) := by
    have ha : (tripleCharges (sourceA1881 + difference 3 1) (sourceB1881 + difference 1 3) sourceC1881) = raw27107 := by
      apply Matrix.ext; unfold tripleCharges sourceA1881 sourceB1881 sourceC1881 difference raw27107; decide +kernel
    rw [ha]
    exact (canonical27107 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1881 + difference 3 2) (sourceB1881 + difference 2 3) sourceC1881) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1709) := by
    have ha : (tripleCharges (sourceA1881 + difference 3 2) (sourceB1881 + difference 2 3) sourceC1881) = raw27108 := by
      apply Matrix.ext; unfold tripleCharges sourceA1881 sourceB1881 sourceC1881 difference raw27108; decide +kernel
    rw [ha]
    exact (canonical27108 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1881 + difference 3 4) (sourceB1881 + difference 4 3) sourceC1881) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1728) := by
    have ha : (tripleCharges (sourceA1881 + difference 3 4) (sourceB1881 + difference 4 3) sourceC1881) = raw27109 := by
      apply Matrix.ext; unfold tripleCharges sourceA1881 sourceB1881 sourceC1881 difference raw27109; decide +kernel
    rw [ha]
    exact (canonical27109 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1881 + difference 3 5) (sourceB1881 + difference 5 3) sourceC1881) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1728) := by
    have ha : (tripleCharges (sourceA1881 + difference 3 5) (sourceB1881 + difference 5 3) sourceC1881) = raw27110 := by
      apply Matrix.ext; unfold tripleCharges sourceA1881 sourceB1881 sourceC1881 difference raw27110; decide +kernel
    rw [ha]
    exact (canonical27110 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1881 + difference 4 0) (sourceB1881 + difference 0 4) sourceC1881) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1512) := by
    have ha : (tripleCharges (sourceA1881 + difference 4 0) (sourceB1881 + difference 0 4) sourceC1881) = raw27111 := by
      apply Matrix.ext; unfold tripleCharges sourceA1881 sourceB1881 sourceC1881 difference raw27111; decide +kernel
    rw [ha]
    exact (canonical27111 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1881 + difference 4 1) (sourceB1881 + difference 1 4) sourceC1881) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1668) := by
    have ha : (tripleCharges (sourceA1881 + difference 4 1) (sourceB1881 + difference 1 4) sourceC1881) = raw27112 := by
      apply Matrix.ext; unfold tripleCharges sourceA1881 sourceB1881 sourceC1881 difference raw27112; decide +kernel
    rw [ha]
    exact (canonical27112 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1881 + difference 4 2) (sourceB1881 + difference 2 4) sourceC1881) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1715) := by
    have ha : (tripleCharges (sourceA1881 + difference 4 2) (sourceB1881 + difference 2 4) sourceC1881) = raw27113 := by
      apply Matrix.ext; unfold tripleCharges sourceA1881 sourceB1881 sourceC1881 difference raw27113; decide +kernel
    rw [ha]
    exact (canonical27113 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1881 + difference 4 3) (sourceB1881 + difference 3 4) sourceC1881) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1714) := by
    have ha : (tripleCharges (sourceA1881 + difference 4 3) (sourceB1881 + difference 3 4) sourceC1881) = raw27114 := by
      apply Matrix.ext; unfold tripleCharges sourceA1881 sourceB1881 sourceC1881 difference raw27114; decide +kernel
    rw [ha]
    exact (canonical27114 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1881 + difference 4 5) (sourceB1881 + difference 5 4) sourceC1881) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1739) := by
    have ha : (tripleCharges (sourceA1881 + difference 4 5) (sourceB1881 + difference 5 4) sourceC1881) = raw27115 := by
      apply Matrix.ext; unfold tripleCharges sourceA1881 sourceB1881 sourceC1881 difference raw27115; decide +kernel
    rw [ha]
    exact (canonical27115 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1881 + difference 5 0) (sourceB1881 + difference 0 5) sourceC1881) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1512) := by
    have ha : (tripleCharges (sourceA1881 + difference 5 0) (sourceB1881 + difference 0 5) sourceC1881) = raw27116 := by
      apply Matrix.ext; unfold tripleCharges sourceA1881 sourceB1881 sourceC1881 difference raw27116; decide +kernel
    rw [ha]
    exact (canonical27116 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1881 + difference 5 1) (sourceB1881 + difference 1 5) sourceC1881) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1668) := by
    have ha : (tripleCharges (sourceA1881 + difference 5 1) (sourceB1881 + difference 1 5) sourceC1881) = raw27117 := by
      apply Matrix.ext; unfold tripleCharges sourceA1881 sourceB1881 sourceC1881 difference raw27117; decide +kernel
    rw [ha]
    exact (canonical27117 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1881 + difference 5 2) (sourceB1881 + difference 2 5) sourceC1881) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1715) := by
    have ha : (tripleCharges (sourceA1881 + difference 5 2) (sourceB1881 + difference 2 5) sourceC1881) = raw27118 := by
      apply Matrix.ext; unfold tripleCharges sourceA1881 sourceB1881 sourceC1881 difference raw27118; decide +kernel
    rw [ha]
    exact (canonical27118 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1881 + difference 5 3) (sourceB1881 + difference 3 5) sourceC1881) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1714) := by
    have ha : (tripleCharges (sourceA1881 + difference 5 3) (sourceB1881 + difference 3 5) sourceC1881) = raw27119 := by
      apply Matrix.ext; unfold tripleCharges sourceA1881 sourceB1881 sourceC1881 difference raw27119; decide +kernel
    rw [ha]
    exact (canonical27119 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1881 + difference 5 4) (sourceB1881 + difference 4 5) sourceC1881) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1739) := by
    have ha : (tripleCharges (sourceA1881 + difference 5 4) (sourceB1881 + difference 4 5) sourceC1881) = raw27120 := by
      apply Matrix.ext; unfold tripleCharges sourceA1881 sourceB1881 sourceC1881 difference raw27120; decide +kernel
    rw [ha]
    exact (canonical27120 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1881 sourceB1881 sourceC1881
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1881, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1882 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1882 : Charge := ![3, 0, -2, -1, 0, 0]
def sourceC1882 : Charge := ![1, 0, 1, 0, -1, -1]
def sourceForm1882 : Integer.Sparse Master := [(Sum.inr 4113, 1), (Sum.inr 4114, 1), (Sum.inr 4115, 1), (Sum.inr 4119, 2), (Sum.inr 4297, 1), (Sum.inr 4298, 1), (Sum.inr 4301, 2), (Sum.inr 4417, 2), (Sum.inr 4418, 2), (Sum.inr 4419, 2), (Sum.inr 4424, 2), (Sum.inr 4456, 1), (Sum.inr 4457, 1), (Sum.inr 4458, 2), (Sum.inr 4495, 1), (Sum.inr 4496, 1), (Sum.inr 4499, 2), (Sum.inr 5098, 1), (Sum.inr 5271, 2), (Sum.inr 5292, 1), (Sum.inr 5306, 1)]

theorem sourceEq1882 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1882 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1882 + difference 0 1) (sourceB1882 + difference 1 0) sourceC1882) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5098) := by
    have ha : (tripleCharges (sourceA1882 + difference 0 1) (sourceB1882 + difference 1 0) sourceC1882) = raw27121 := by
      apply Matrix.ext; unfold tripleCharges sourceA1882 sourceB1882 sourceC1882 difference raw27121; decide +kernel
    rw [ha]
    exact (canonical27121 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1882 + difference 0 2) (sourceB1882 + difference 2 0) sourceC1882) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA1882 + difference 0 2) (sourceB1882 + difference 2 0) sourceC1882) = raw27122 := by
      apply Matrix.ext; unfold tripleCharges sourceA1882 sourceB1882 sourceC1882 difference raw27122; decide +kernel
    rw [ha]
    exact (canonical27122 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1882 + difference 0 3) (sourceB1882 + difference 3 0) sourceC1882) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5306) := by
    have ha : (tripleCharges (sourceA1882 + difference 0 3) (sourceB1882 + difference 3 0) sourceC1882) = raw27123 := by
      apply Matrix.ext; unfold tripleCharges sourceA1882 sourceB1882 sourceC1882 difference raw27123; decide +kernel
    rw [ha]
    exact (canonical27123 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1882 + difference 0 4) (sourceB1882 + difference 4 0) sourceC1882) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA1882 + difference 0 4) (sourceB1882 + difference 4 0) sourceC1882) = raw27124 := by
      apply Matrix.ext; unfold tripleCharges sourceA1882 sourceB1882 sourceC1882 difference raw27124; decide +kernel
    rw [ha]
    exact (canonical27124 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1882 + difference 0 5) (sourceB1882 + difference 5 0) sourceC1882) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA1882 + difference 0 5) (sourceB1882 + difference 5 0) sourceC1882) = raw27125 := by
      apply Matrix.ext; unfold tripleCharges sourceA1882 sourceB1882 sourceC1882 difference raw27125; decide +kernel
    rw [ha]
    exact (canonical27125 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1882 + difference 1 0) (sourceB1882 + difference 0 1) sourceC1882) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4113) := by
    have ha : (tripleCharges (sourceA1882 + difference 1 0) (sourceB1882 + difference 0 1) sourceC1882) = raw27126 := by
      apply Matrix.ext; unfold tripleCharges sourceA1882 sourceB1882 sourceC1882 difference raw27126; decide +kernel
    rw [ha]
    exact (canonical27126 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1882 + difference 1 2) (sourceB1882 + difference 2 1) sourceC1882) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4456) := by
    have ha : (tripleCharges (sourceA1882 + difference 1 2) (sourceB1882 + difference 2 1) sourceC1882) = raw27127 := by
      apply Matrix.ext; unfold tripleCharges sourceA1882 sourceB1882 sourceC1882 difference raw27127; decide +kernel
    rw [ha]
    exact (canonical27127 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1882 + difference 1 3) (sourceB1882 + difference 3 1) sourceC1882) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4495) := by
    have ha : (tripleCharges (sourceA1882 + difference 1 3) (sourceB1882 + difference 3 1) sourceC1882) = raw27128 := by
      apply Matrix.ext; unfold tripleCharges sourceA1882 sourceB1882 sourceC1882 difference raw27128; decide +kernel
    rw [ha]
    exact (canonical27128 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1882 + difference 1 4) (sourceB1882 + difference 4 1) sourceC1882) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4417) := by
    have ha : (tripleCharges (sourceA1882 + difference 1 4) (sourceB1882 + difference 4 1) sourceC1882) = raw27129 := by
      apply Matrix.ext; unfold tripleCharges sourceA1882 sourceB1882 sourceC1882 difference raw27129; decide +kernel
    rw [ha]
    exact (canonical27129 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1882 + difference 1 5) (sourceB1882 + difference 5 1) sourceC1882) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4417) := by
    have ha : (tripleCharges (sourceA1882 + difference 1 5) (sourceB1882 + difference 5 1) sourceC1882) = raw27130 := by
      apply Matrix.ext; unfold tripleCharges sourceA1882 sourceB1882 sourceC1882 difference raw27130; decide +kernel
    rw [ha]
    exact (canonical27130 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1882 + difference 2 0) (sourceB1882 + difference 0 2) sourceC1882) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4114) := by
    have ha : (tripleCharges (sourceA1882 + difference 2 0) (sourceB1882 + difference 0 2) sourceC1882) = raw27131 := by
      apply Matrix.ext; unfold tripleCharges sourceA1882 sourceB1882 sourceC1882 difference raw27131; decide +kernel
    rw [ha]
    exact (canonical27131 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1882 + difference 2 1) (sourceB1882 + difference 1 2) sourceC1882) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4297) := by
    have ha : (tripleCharges (sourceA1882 + difference 2 1) (sourceB1882 + difference 1 2) sourceC1882) = raw27132 := by
      apply Matrix.ext; unfold tripleCharges sourceA1882 sourceB1882 sourceC1882 difference raw27132; decide +kernel
    rw [ha]
    exact (canonical27132 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1882 + difference 2 3) (sourceB1882 + difference 3 2) sourceC1882) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4496) := by
    have ha : (tripleCharges (sourceA1882 + difference 2 3) (sourceB1882 + difference 3 2) sourceC1882) = raw27133 := by
      apply Matrix.ext; unfold tripleCharges sourceA1882 sourceB1882 sourceC1882 difference raw27133; decide +kernel
    rw [ha]
    exact (canonical27133 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1882 + difference 2 4) (sourceB1882 + difference 4 2) sourceC1882) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4418) := by
    have ha : (tripleCharges (sourceA1882 + difference 2 4) (sourceB1882 + difference 4 2) sourceC1882) = raw27134 := by
      apply Matrix.ext; unfold tripleCharges sourceA1882 sourceB1882 sourceC1882 difference raw27134; decide +kernel
    rw [ha]
    exact (canonical27134 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1882 + difference 2 5) (sourceB1882 + difference 5 2) sourceC1882) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4418) := by
    have ha : (tripleCharges (sourceA1882 + difference 2 5) (sourceB1882 + difference 5 2) sourceC1882) = raw27135 := by
      apply Matrix.ext; unfold tripleCharges sourceA1882 sourceB1882 sourceC1882 difference raw27135; decide +kernel
    rw [ha]
    exact (canonical27135 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1882 + difference 3 0) (sourceB1882 + difference 0 3) sourceC1882) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4115) := by
    have ha : (tripleCharges (sourceA1882 + difference 3 0) (sourceB1882 + difference 0 3) sourceC1882) = raw27136 := by
      apply Matrix.ext; unfold tripleCharges sourceA1882 sourceB1882 sourceC1882 difference raw27136; decide +kernel
    rw [ha]
    exact (canonical27136 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1882 + difference 3 1) (sourceB1882 + difference 1 3) sourceC1882) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4298) := by
    have ha : (tripleCharges (sourceA1882 + difference 3 1) (sourceB1882 + difference 1 3) sourceC1882) = raw27137 := by
      apply Matrix.ext; unfold tripleCharges sourceA1882 sourceB1882 sourceC1882 difference raw27137; decide +kernel
    rw [ha]
    exact (canonical27137 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1882 + difference 3 2) (sourceB1882 + difference 2 3) sourceC1882) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4457) := by
    have ha : (tripleCharges (sourceA1882 + difference 3 2) (sourceB1882 + difference 2 3) sourceC1882) = raw27138 := by
      apply Matrix.ext; unfold tripleCharges sourceA1882 sourceB1882 sourceC1882 difference raw27138; decide +kernel
    rw [ha]
    exact (canonical27138 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1882 + difference 3 4) (sourceB1882 + difference 4 3) sourceC1882) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4419) := by
    have ha : (tripleCharges (sourceA1882 + difference 3 4) (sourceB1882 + difference 4 3) sourceC1882) = raw27139 := by
      apply Matrix.ext; unfold tripleCharges sourceA1882 sourceB1882 sourceC1882 difference raw27139; decide +kernel
    rw [ha]
    exact (canonical27139 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1882 + difference 3 5) (sourceB1882 + difference 5 3) sourceC1882) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4419) := by
    have ha : (tripleCharges (sourceA1882 + difference 3 5) (sourceB1882 + difference 5 3) sourceC1882) = raw27140 := by
      apply Matrix.ext; unfold tripleCharges sourceA1882 sourceB1882 sourceC1882 difference raw27140; decide +kernel
    rw [ha]
    exact (canonical27140 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1882 + difference 4 0) (sourceB1882 + difference 0 4) sourceC1882) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4119) := by
    have ha : (tripleCharges (sourceA1882 + difference 4 0) (sourceB1882 + difference 0 4) sourceC1882) = raw27141 := by
      apply Matrix.ext; unfold tripleCharges sourceA1882 sourceB1882 sourceC1882 difference raw27141; decide +kernel
    rw [ha]
    exact (canonical27141 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1882 + difference 4 1) (sourceB1882 + difference 1 4) sourceC1882) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4301) := by
    have ha : (tripleCharges (sourceA1882 + difference 4 1) (sourceB1882 + difference 1 4) sourceC1882) = raw27142 := by
      apply Matrix.ext; unfold tripleCharges sourceA1882 sourceB1882 sourceC1882 difference raw27142; decide +kernel
    rw [ha]
    exact (canonical27142 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1882 + difference 4 2) (sourceB1882 + difference 2 4) sourceC1882) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1882 + difference 4 2) (sourceB1882 + difference 2 4) sourceC1882) = raw27143 := by
      apply Matrix.ext; unfold tripleCharges sourceA1882 sourceB1882 sourceC1882 difference raw27143; decide +kernel
    rw [ha]
    exact (canonical27143 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1882 + difference 4 3) (sourceB1882 + difference 3 4) sourceC1882) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4499) := by
    have ha : (tripleCharges (sourceA1882 + difference 4 3) (sourceB1882 + difference 3 4) sourceC1882) = raw27144 := by
      apply Matrix.ext; unfold tripleCharges sourceA1882 sourceB1882 sourceC1882 difference raw27144; decide +kernel
    rw [ha]
    exact (canonical27144 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1882 + difference 4 5) (sourceB1882 + difference 5 4) sourceC1882) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4424) := by
    have ha : (tripleCharges (sourceA1882 + difference 4 5) (sourceB1882 + difference 5 4) sourceC1882) = raw27145 := by
      apply Matrix.ext; unfold tripleCharges sourceA1882 sourceB1882 sourceC1882 difference raw27145; decide +kernel
    rw [ha]
    exact (canonical27145 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1882 + difference 5 0) (sourceB1882 + difference 0 5) sourceC1882) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4119) := by
    have ha : (tripleCharges (sourceA1882 + difference 5 0) (sourceB1882 + difference 0 5) sourceC1882) = raw27146 := by
      apply Matrix.ext; unfold tripleCharges sourceA1882 sourceB1882 sourceC1882 difference raw27146; decide +kernel
    rw [ha]
    exact (canonical27146 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1882 + difference 5 1) (sourceB1882 + difference 1 5) sourceC1882) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4301) := by
    have ha : (tripleCharges (sourceA1882 + difference 5 1) (sourceB1882 + difference 1 5) sourceC1882) = raw27147 := by
      apply Matrix.ext; unfold tripleCharges sourceA1882 sourceB1882 sourceC1882 difference raw27147; decide +kernel
    rw [ha]
    exact (canonical27147 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1882 + difference 5 2) (sourceB1882 + difference 2 5) sourceC1882) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1882 + difference 5 2) (sourceB1882 + difference 2 5) sourceC1882) = raw27148 := by
      apply Matrix.ext; unfold tripleCharges sourceA1882 sourceB1882 sourceC1882 difference raw27148; decide +kernel
    rw [ha]
    exact (canonical27148 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1882 + difference 5 3) (sourceB1882 + difference 3 5) sourceC1882) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4499) := by
    have ha : (tripleCharges (sourceA1882 + difference 5 3) (sourceB1882 + difference 3 5) sourceC1882) = raw27149 := by
      apply Matrix.ext; unfold tripleCharges sourceA1882 sourceB1882 sourceC1882 difference raw27149; decide +kernel
    rw [ha]
    exact (canonical27149 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1882 + difference 5 4) (sourceB1882 + difference 4 5) sourceC1882) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4424) := by
    have ha : (tripleCharges (sourceA1882 + difference 5 4) (sourceB1882 + difference 4 5) sourceC1882) = raw27150 := by
      apply Matrix.ext; unfold tripleCharges sourceA1882 sourceB1882 sourceC1882 difference raw27150; decide +kernel
    rw [ha]
    exact (canonical27150 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1882 sourceB1882 sourceC1882
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1882, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1883 : Charge := ![1, 0, 1, 0, -1, -1]
def sourceB1883 : Charge := ![3, 0, -2, -1, 0, 0]
def sourceC1883 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceForm1883 : Integer.Sparse Master := [(Sum.inr 4249, 1), (Sum.inr 4253, 1), (Sum.inr 4256, 1), (Sum.inr 4267, 2), (Sum.inr 4414, 1), (Sum.inr 4415, 1), (Sum.inr 4417, 2), (Sum.inr 4449, 2), (Sum.inr 4455, 1), (Sum.inr 4456, 1), (Sum.inr 4486, 2), (Sum.inr 4487, 2), (Sum.inr 4489, 2), (Sum.inr 4494, 1), (Sum.inr 4495, 3), (Sum.inr 4497, 2), (Sum.inr 4599, 1), (Sum.inr 4616, 2), (Sum.inr 4618, 1), (Sum.inr 4622, 1)]

theorem sourceEq1883 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1883 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1883 + difference 0 1) (sourceB1883 + difference 1 0) sourceC1883) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4599) := by
    have ha : (tripleCharges (sourceA1883 + difference 0 1) (sourceB1883 + difference 1 0) sourceC1883) = raw26863 := by
      apply Matrix.ext; unfold tripleCharges sourceA1883 sourceB1883 sourceC1883 difference raw26863; decide +kernel
    rw [ha]
    exact (canonical26863 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1883 + difference 0 2) (sourceB1883 + difference 2 0) sourceC1883) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4622) := by
    have ha : (tripleCharges (sourceA1883 + difference 0 2) (sourceB1883 + difference 2 0) sourceC1883) = raw26858 := by
      apply Matrix.ext; unfold tripleCharges sourceA1883 sourceB1883 sourceC1883 difference raw26858; decide +kernel
    rw [ha]
    exact (canonical26858 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1883 + difference 0 3) (sourceB1883 + difference 3 0) sourceC1883) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4618) := by
    have ha : (tripleCharges (sourceA1883 + difference 0 3) (sourceB1883 + difference 3 0) sourceC1883) = raw27151 := by
      apply Matrix.ext; unfold tripleCharges sourceA1883 sourceB1883 sourceC1883 difference raw27151; decide +kernel
    rw [ha]
    exact (canonical27151 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1883 + difference 0 4) (sourceB1883 + difference 4 0) sourceC1883) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4616) := by
    have ha : (tripleCharges (sourceA1883 + difference 0 4) (sourceB1883 + difference 4 0) sourceC1883) = raw27152 := by
      apply Matrix.ext; unfold tripleCharges sourceA1883 sourceB1883 sourceC1883 difference raw27152; decide +kernel
    rw [ha]
    exact (canonical27152 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1883 + difference 0 5) (sourceB1883 + difference 5 0) sourceC1883) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4616) := by
    have ha : (tripleCharges (sourceA1883 + difference 0 5) (sourceB1883 + difference 5 0) sourceC1883) = raw27153 := by
      apply Matrix.ext; unfold tripleCharges sourceA1883 sourceB1883 sourceC1883 difference raw27153; decide +kernel
    rw [ha]
    exact (canonical27153 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1883 + difference 1 0) (sourceB1883 + difference 0 1) sourceC1883) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4249) := by
    have ha : (tripleCharges (sourceA1883 + difference 1 0) (sourceB1883 + difference 0 1) sourceC1883) = raw27021 := by
      apply Matrix.ext; unfold tripleCharges sourceA1883 sourceB1883 sourceC1883 difference raw27021; decide +kernel
    rw [ha]
    exact (canonical27021 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1883 + difference 1 2) (sourceB1883 + difference 2 1) sourceC1883) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4456) := by
    have ha : (tripleCharges (sourceA1883 + difference 1 2) (sourceB1883 + difference 2 1) sourceC1883) = raw27154 := by
      apply Matrix.ext; unfold tripleCharges sourceA1883 sourceB1883 sourceC1883 difference raw27154; decide +kernel
    rw [ha]
    exact (canonical27154 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1883 + difference 1 3) (sourceB1883 + difference 3 1) sourceC1883) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4455) := by
    have ha : (tripleCharges (sourceA1883 + difference 1 3) (sourceB1883 + difference 3 1) sourceC1883) = raw27023 := by
      apply Matrix.ext; unfold tripleCharges sourceA1883 sourceB1883 sourceC1883 difference raw27023; decide +kernel
    rw [ha]
    exact (canonical27023 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1883 + difference 1 4) (sourceB1883 + difference 4 1) sourceC1883) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4449) := by
    have ha : (tripleCharges (sourceA1883 + difference 1 4) (sourceB1883 + difference 4 1) sourceC1883) = raw27024 := by
      apply Matrix.ext; unfold tripleCharges sourceA1883 sourceB1883 sourceC1883 difference raw27024; decide +kernel
    rw [ha]
    exact (canonical27024 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1883 + difference 1 5) (sourceB1883 + difference 5 1) sourceC1883) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4449) := by
    have ha : (tripleCharges (sourceA1883 + difference 1 5) (sourceB1883 + difference 5 1) sourceC1883) = raw27025 := by
      apply Matrix.ext; unfold tripleCharges sourceA1883 sourceB1883 sourceC1883 difference raw27025; decide +kernel
    rw [ha]
    exact (canonical27025 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1883 + difference 2 0) (sourceB1883 + difference 0 2) sourceC1883) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4253) := by
    have ha : (tripleCharges (sourceA1883 + difference 2 0) (sourceB1883 + difference 0 2) sourceC1883) = raw27155 := by
      apply Matrix.ext; unfold tripleCharges sourceA1883 sourceB1883 sourceC1883 difference raw27155; decide +kernel
    rw [ha]
    exact (canonical27155 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1883 + difference 2 1) (sourceB1883 + difference 1 2) sourceC1883) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4414) := by
    have ha : (tripleCharges (sourceA1883 + difference 2 1) (sourceB1883 + difference 1 2) sourceC1883) = raw27156 := by
      apply Matrix.ext; unfold tripleCharges sourceA1883 sourceB1883 sourceC1883 difference raw27156; decide +kernel
    rw [ha]
    exact (canonical27156 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1883 + difference 2 3) (sourceB1883 + difference 3 2) sourceC1883) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4494) := by
    have ha : (tripleCharges (sourceA1883 + difference 2 3) (sourceB1883 + difference 3 2) sourceC1883) = raw27157 := by
      apply Matrix.ext; unfold tripleCharges sourceA1883 sourceB1883 sourceC1883 difference raw27157; decide +kernel
    rw [ha]
    exact (canonical27157 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1883 + difference 2 4) (sourceB1883 + difference 4 2) sourceC1883) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4486) := by
    have ha : (tripleCharges (sourceA1883 + difference 2 4) (sourceB1883 + difference 4 2) sourceC1883) = raw27158 := by
      apply Matrix.ext; unfold tripleCharges sourceA1883 sourceB1883 sourceC1883 difference raw27158; decide +kernel
    rw [ha]
    exact (canonical27158 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1883 + difference 2 5) (sourceB1883 + difference 5 2) sourceC1883) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4486) := by
    have ha : (tripleCharges (sourceA1883 + difference 2 5) (sourceB1883 + difference 5 2) sourceC1883) = raw27159 := by
      apply Matrix.ext; unfold tripleCharges sourceA1883 sourceB1883 sourceC1883 difference raw27159; decide +kernel
    rw [ha]
    exact (canonical27159 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1883 + difference 3 0) (sourceB1883 + difference 0 3) sourceC1883) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4256) := by
    have ha : (tripleCharges (sourceA1883 + difference 3 0) (sourceB1883 + difference 0 3) sourceC1883) = raw27160 := by
      apply Matrix.ext; unfold tripleCharges sourceA1883 sourceB1883 sourceC1883 difference raw27160; decide +kernel
    rw [ha]
    exact (canonical27160 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1883 + difference 3 1) (sourceB1883 + difference 1 3) sourceC1883) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4415) := by
    have ha : (tripleCharges (sourceA1883 + difference 3 1) (sourceB1883 + difference 1 3) sourceC1883) = raw27161 := by
      apply Matrix.ext; unfold tripleCharges sourceA1883 sourceB1883 sourceC1883 difference raw27161; decide +kernel
    rw [ha]
    exact (canonical27161 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1883 + difference 3 2) (sourceB1883 + difference 2 3) sourceC1883) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4495) := by
    have ha : (tripleCharges (sourceA1883 + difference 3 2) (sourceB1883 + difference 2 3) sourceC1883) = raw27027 := by
      apply Matrix.ext; unfold tripleCharges sourceA1883 sourceB1883 sourceC1883 difference raw27027; decide +kernel
    rw [ha]
    exact (canonical27027 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1883 + difference 3 4) (sourceB1883 + difference 4 3) sourceC1883) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4487) := by
    have ha : (tripleCharges (sourceA1883 + difference 3 4) (sourceB1883 + difference 4 3) sourceC1883) = raw27162 := by
      apply Matrix.ext; unfold tripleCharges sourceA1883 sourceB1883 sourceC1883 difference raw27162; decide +kernel
    rw [ha]
    exact (canonical27162 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1883 + difference 3 5) (sourceB1883 + difference 5 3) sourceC1883) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4487) := by
    have ha : (tripleCharges (sourceA1883 + difference 3 5) (sourceB1883 + difference 5 3) sourceC1883) = raw27163 := by
      apply Matrix.ext; unfold tripleCharges sourceA1883 sourceB1883 sourceC1883 difference raw27163; decide +kernel
    rw [ha]
    exact (canonical27163 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1883 + difference 4 0) (sourceB1883 + difference 0 4) sourceC1883) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4267) := by
    have ha : (tripleCharges (sourceA1883 + difference 4 0) (sourceB1883 + difference 0 4) sourceC1883) = raw27164 := by
      apply Matrix.ext; unfold tripleCharges sourceA1883 sourceB1883 sourceC1883 difference raw27164; decide +kernel
    rw [ha]
    exact (canonical27164 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1883 + difference 4 1) (sourceB1883 + difference 1 4) sourceC1883) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4417) := by
    have ha : (tripleCharges (sourceA1883 + difference 4 1) (sourceB1883 + difference 1 4) sourceC1883) = raw26860 := by
      apply Matrix.ext; unfold tripleCharges sourceA1883 sourceB1883 sourceC1883 difference raw26860; decide +kernel
    rw [ha]
    exact (canonical26860 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1883 + difference 4 2) (sourceB1883 + difference 2 4) sourceC1883) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4497) := by
    have ha : (tripleCharges (sourceA1883 + difference 4 2) (sourceB1883 + difference 2 4) sourceC1883) = raw26857 := by
      apply Matrix.ext; unfold tripleCharges sourceA1883 sourceB1883 sourceC1883 difference raw26857; decide +kernel
    rw [ha]
    exact (canonical26857 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1883 + difference 4 3) (sourceB1883 + difference 3 4) sourceC1883) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4495) := by
    have ha : (tripleCharges (sourceA1883 + difference 4 3) (sourceB1883 + difference 3 4) sourceC1883) = raw27165 := by
      apply Matrix.ext; unfold tripleCharges sourceA1883 sourceB1883 sourceC1883 difference raw27165; decide +kernel
    rw [ha]
    exact (canonical27165 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1883 + difference 4 5) (sourceB1883 + difference 5 4) sourceC1883) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4489) := by
    have ha : (tripleCharges (sourceA1883 + difference 4 5) (sourceB1883 + difference 5 4) sourceC1883) = raw27166 := by
      apply Matrix.ext; unfold tripleCharges sourceA1883 sourceB1883 sourceC1883 difference raw27166; decide +kernel
    rw [ha]
    exact (canonical27166 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1883 + difference 5 0) (sourceB1883 + difference 0 5) sourceC1883) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4267) := by
    have ha : (tripleCharges (sourceA1883 + difference 5 0) (sourceB1883 + difference 0 5) sourceC1883) = raw27167 := by
      apply Matrix.ext; unfold tripleCharges sourceA1883 sourceB1883 sourceC1883 difference raw27167; decide +kernel
    rw [ha]
    exact (canonical27167 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1883 + difference 5 1) (sourceB1883 + difference 1 5) sourceC1883) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4417) := by
    have ha : (tripleCharges (sourceA1883 + difference 5 1) (sourceB1883 + difference 1 5) sourceC1883) = raw27168 := by
      apply Matrix.ext; unfold tripleCharges sourceA1883 sourceB1883 sourceC1883 difference raw27168; decide +kernel
    rw [ha]
    exact (canonical27168 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1883 + difference 5 2) (sourceB1883 + difference 2 5) sourceC1883) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4497) := by
    have ha : (tripleCharges (sourceA1883 + difference 5 2) (sourceB1883 + difference 2 5) sourceC1883) = raw27036 := by
      apply Matrix.ext; unfold tripleCharges sourceA1883 sourceB1883 sourceC1883 difference raw27036; decide +kernel
    rw [ha]
    exact (canonical27036 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1883 + difference 5 3) (sourceB1883 + difference 3 5) sourceC1883) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4495) := by
    have ha : (tripleCharges (sourceA1883 + difference 5 3) (sourceB1883 + difference 3 5) sourceC1883) = raw27169 := by
      apply Matrix.ext; unfold tripleCharges sourceA1883 sourceB1883 sourceC1883 difference raw27169; decide +kernel
    rw [ha]
    exact (canonical27169 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1883 + difference 5 4) (sourceB1883 + difference 4 5) sourceC1883) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4489) := by
    have ha : (tripleCharges (sourceA1883 + difference 5 4) (sourceB1883 + difference 4 5) sourceC1883) = raw27170 := by
      apply Matrix.ext; unfold tripleCharges sourceA1883 sourceB1883 sourceC1883 difference raw27170; decide +kernel
    rw [ha]
    exact (canonical27170 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1883 sourceB1883 sourceC1883
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1883, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1884 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1884 : Charge := ![1, 0, 0, 0, 0, -1]
def sourceC1884 : Charge := ![3, 0, -1, -1, -1, 0]
def sourceForm1884 : Integer.Sparse Master := [(Sum.inr 4083, 1), (Sum.inr 4171, 1), (Sum.inr 4175, 3), (Sum.inr 4182, 1), (Sum.inr 4344, 3), (Sum.inr 4351, 1), (Sum.inr 4456, 3), (Sum.inr 4458, 6), (Sum.inr 4461, 3), (Sum.inr 4497, 1), (Sum.inr 4502, 3), (Sum.inr 4833, 1), (Sum.inr 4893, 3)]

theorem sourceEq1884 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1884 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1884 + difference 0 1) (sourceB1884 + difference 1 0) sourceC1884) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4833) := by
    have ha : (tripleCharges (sourceA1884 + difference 0 1) (sourceB1884 + difference 1 0) sourceC1884) = raw27171 := by
      apply Matrix.ext; unfold tripleCharges sourceA1884 sourceB1884 sourceC1884 difference raw27171; decide +kernel
    rw [ha]
    exact (canonical27171 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1884 + difference 0 2) (sourceB1884 + difference 2 0) sourceC1884) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4893) := by
    have ha : (tripleCharges (sourceA1884 + difference 0 2) (sourceB1884 + difference 2 0) sourceC1884) = raw27172 := by
      apply Matrix.ext; unfold tripleCharges sourceA1884 sourceB1884 sourceC1884 difference raw27172; decide +kernel
    rw [ha]
    exact (canonical27172 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1884 + difference 0 3) (sourceB1884 + difference 3 0) sourceC1884) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4893) := by
    have ha : (tripleCharges (sourceA1884 + difference 0 3) (sourceB1884 + difference 3 0) sourceC1884) = raw27173 := by
      apply Matrix.ext; unfold tripleCharges sourceA1884 sourceB1884 sourceC1884 difference raw27173; decide +kernel
    rw [ha]
    exact (canonical27173 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1884 + difference 0 4) (sourceB1884 + difference 4 0) sourceC1884) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4893) := by
    have ha : (tripleCharges (sourceA1884 + difference 0 4) (sourceB1884 + difference 4 0) sourceC1884) = raw27174 := by
      apply Matrix.ext; unfold tripleCharges sourceA1884 sourceB1884 sourceC1884 difference raw27174; decide +kernel
    rw [ha]
    exact (canonical27174 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1884 + difference 0 5) (sourceB1884 + difference 5 0) sourceC1884) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (tripleCharges (sourceA1884 + difference 0 5) (sourceB1884 + difference 5 0) sourceC1884) = raw27175 := by
      apply Matrix.ext; unfold tripleCharges sourceA1884 sourceB1884 sourceC1884 difference raw27175; decide +kernel
    rw [ha]
    exact (canonical27175 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1884 + difference 1 0) (sourceB1884 + difference 0 1) sourceC1884) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4171) := by
    have ha : (tripleCharges (sourceA1884 + difference 1 0) (sourceB1884 + difference 0 1) sourceC1884) = raw27176 := by
      apply Matrix.ext; unfold tripleCharges sourceA1884 sourceB1884 sourceC1884 difference raw27176; decide +kernel
    rw [ha]
    exact (canonical27176 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1884 + difference 1 2) (sourceB1884 + difference 2 1) sourceC1884) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4456) := by
    have ha : (tripleCharges (sourceA1884 + difference 1 2) (sourceB1884 + difference 2 1) sourceC1884) = raw27177 := by
      apply Matrix.ext; unfold tripleCharges sourceA1884 sourceB1884 sourceC1884 difference raw27177; decide +kernel
    rw [ha]
    exact (canonical27177 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1884 + difference 1 3) (sourceB1884 + difference 3 1) sourceC1884) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4456) := by
    have ha : (tripleCharges (sourceA1884 + difference 1 3) (sourceB1884 + difference 3 1) sourceC1884) = raw27178 := by
      apply Matrix.ext; unfold tripleCharges sourceA1884 sourceB1884 sourceC1884 difference raw27178; decide +kernel
    rw [ha]
    exact (canonical27178 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1884 + difference 1 4) (sourceB1884 + difference 4 1) sourceC1884) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4456) := by
    have ha : (tripleCharges (sourceA1884 + difference 1 4) (sourceB1884 + difference 4 1) sourceC1884) = raw27179 := by
      apply Matrix.ext; unfold tripleCharges sourceA1884 sourceB1884 sourceC1884 difference raw27179; decide +kernel
    rw [ha]
    exact (canonical27179 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1884 + difference 1 5) (sourceB1884 + difference 5 1) sourceC1884) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4497) := by
    have ha : (tripleCharges (sourceA1884 + difference 1 5) (sourceB1884 + difference 5 1) sourceC1884) = raw27180 := by
      apply Matrix.ext; unfold tripleCharges sourceA1884 sourceB1884 sourceC1884 difference raw27180; decide +kernel
    rw [ha]
    exact (canonical27180 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1884 + difference 2 0) (sourceB1884 + difference 0 2) sourceC1884) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4175) := by
    have ha : (tripleCharges (sourceA1884 + difference 2 0) (sourceB1884 + difference 0 2) sourceC1884) = raw27181 := by
      apply Matrix.ext; unfold tripleCharges sourceA1884 sourceB1884 sourceC1884 difference raw27181; decide +kernel
    rw [ha]
    exact (canonical27181 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1884 + difference 2 1) (sourceB1884 + difference 1 2) sourceC1884) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4344) := by
    have ha : (tripleCharges (sourceA1884 + difference 2 1) (sourceB1884 + difference 1 2) sourceC1884) = raw27182 := by
      apply Matrix.ext; unfold tripleCharges sourceA1884 sourceB1884 sourceC1884 difference raw27182; decide +kernel
    rw [ha]
    exact (canonical27182 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1884 + difference 2 3) (sourceB1884 + difference 3 2) sourceC1884) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1884 + difference 2 3) (sourceB1884 + difference 3 2) sourceC1884) = raw27183 := by
      apply Matrix.ext; unfold tripleCharges sourceA1884 sourceB1884 sourceC1884 difference raw27183; decide +kernel
    rw [ha]
    exact (canonical27183 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1884 + difference 2 4) (sourceB1884 + difference 4 2) sourceC1884) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1884 + difference 2 4) (sourceB1884 + difference 4 2) sourceC1884) = raw27184 := by
      apply Matrix.ext; unfold tripleCharges sourceA1884 sourceB1884 sourceC1884 difference raw27184; decide +kernel
    rw [ha]
    exact (canonical27184 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1884 + difference 2 5) (sourceB1884 + difference 5 2) sourceC1884) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4502) := by
    have ha : (tripleCharges (sourceA1884 + difference 2 5) (sourceB1884 + difference 5 2) sourceC1884) = raw27185 := by
      apply Matrix.ext; unfold tripleCharges sourceA1884 sourceB1884 sourceC1884 difference raw27185; decide +kernel
    rw [ha]
    exact (canonical27185 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1884 + difference 3 0) (sourceB1884 + difference 0 3) sourceC1884) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4175) := by
    have ha : (tripleCharges (sourceA1884 + difference 3 0) (sourceB1884 + difference 0 3) sourceC1884) = raw27186 := by
      apply Matrix.ext; unfold tripleCharges sourceA1884 sourceB1884 sourceC1884 difference raw27186; decide +kernel
    rw [ha]
    exact (canonical27186 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1884 + difference 3 1) (sourceB1884 + difference 1 3) sourceC1884) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4344) := by
    have ha : (tripleCharges (sourceA1884 + difference 3 1) (sourceB1884 + difference 1 3) sourceC1884) = raw27187 := by
      apply Matrix.ext; unfold tripleCharges sourceA1884 sourceB1884 sourceC1884 difference raw27187; decide +kernel
    rw [ha]
    exact (canonical27187 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1884 + difference 3 2) (sourceB1884 + difference 2 3) sourceC1884) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1884 + difference 3 2) (sourceB1884 + difference 2 3) sourceC1884) = raw27188 := by
      apply Matrix.ext; unfold tripleCharges sourceA1884 sourceB1884 sourceC1884 difference raw27188; decide +kernel
    rw [ha]
    exact (canonical27188 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1884 + difference 3 4) (sourceB1884 + difference 4 3) sourceC1884) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1884 + difference 3 4) (sourceB1884 + difference 4 3) sourceC1884) = raw27189 := by
      apply Matrix.ext; unfold tripleCharges sourceA1884 sourceB1884 sourceC1884 difference raw27189; decide +kernel
    rw [ha]
    exact (canonical27189 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1884 + difference 3 5) (sourceB1884 + difference 5 3) sourceC1884) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4502) := by
    have ha : (tripleCharges (sourceA1884 + difference 3 5) (sourceB1884 + difference 5 3) sourceC1884) = raw27190 := by
      apply Matrix.ext; unfold tripleCharges sourceA1884 sourceB1884 sourceC1884 difference raw27190; decide +kernel
    rw [ha]
    exact (canonical27190 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1884 + difference 4 0) (sourceB1884 + difference 0 4) sourceC1884) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4175) := by
    have ha : (tripleCharges (sourceA1884 + difference 4 0) (sourceB1884 + difference 0 4) sourceC1884) = raw27191 := by
      apply Matrix.ext; unfold tripleCharges sourceA1884 sourceB1884 sourceC1884 difference raw27191; decide +kernel
    rw [ha]
    exact (canonical27191 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1884 + difference 4 1) (sourceB1884 + difference 1 4) sourceC1884) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4344) := by
    have ha : (tripleCharges (sourceA1884 + difference 4 1) (sourceB1884 + difference 1 4) sourceC1884) = raw27192 := by
      apply Matrix.ext; unfold tripleCharges sourceA1884 sourceB1884 sourceC1884 difference raw27192; decide +kernel
    rw [ha]
    exact (canonical27192 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1884 + difference 4 2) (sourceB1884 + difference 2 4) sourceC1884) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1884 + difference 4 2) (sourceB1884 + difference 2 4) sourceC1884) = raw27193 := by
      apply Matrix.ext; unfold tripleCharges sourceA1884 sourceB1884 sourceC1884 difference raw27193; decide +kernel
    rw [ha]
    exact (canonical27193 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1884 + difference 4 3) (sourceB1884 + difference 3 4) sourceC1884) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1884 + difference 4 3) (sourceB1884 + difference 3 4) sourceC1884) = raw27194 := by
      apply Matrix.ext; unfold tripleCharges sourceA1884 sourceB1884 sourceC1884 difference raw27194; decide +kernel
    rw [ha]
    exact (canonical27194 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1884 + difference 4 5) (sourceB1884 + difference 5 4) sourceC1884) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4502) := by
    have ha : (tripleCharges (sourceA1884 + difference 4 5) (sourceB1884 + difference 5 4) sourceC1884) = raw27195 := by
      apply Matrix.ext; unfold tripleCharges sourceA1884 sourceB1884 sourceC1884 difference raw27195; decide +kernel
    rw [ha]
    exact (canonical27195 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1884 + difference 5 0) (sourceB1884 + difference 0 5) sourceC1884) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4182) := by
    have ha : (tripleCharges (sourceA1884 + difference 5 0) (sourceB1884 + difference 0 5) sourceC1884) = raw27196 := by
      apply Matrix.ext; unfold tripleCharges sourceA1884 sourceB1884 sourceC1884 difference raw27196; decide +kernel
    rw [ha]
    exact (canonical27196 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1884 + difference 5 1) (sourceB1884 + difference 1 5) sourceC1884) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4351) := by
    have ha : (tripleCharges (sourceA1884 + difference 5 1) (sourceB1884 + difference 1 5) sourceC1884) = raw27197 := by
      apply Matrix.ext; unfold tripleCharges sourceA1884 sourceB1884 sourceC1884 difference raw27197; decide +kernel
    rw [ha]
    exact (canonical27197 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1884 + difference 5 2) (sourceB1884 + difference 2 5) sourceC1884) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4461) := by
    have ha : (tripleCharges (sourceA1884 + difference 5 2) (sourceB1884 + difference 2 5) sourceC1884) = raw27198 := by
      apply Matrix.ext; unfold tripleCharges sourceA1884 sourceB1884 sourceC1884 difference raw27198; decide +kernel
    rw [ha]
    exact (canonical27198 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1884 + difference 5 3) (sourceB1884 + difference 3 5) sourceC1884) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4461) := by
    have ha : (tripleCharges (sourceA1884 + difference 5 3) (sourceB1884 + difference 3 5) sourceC1884) = raw27199 := by
      apply Matrix.ext; unfold tripleCharges sourceA1884 sourceB1884 sourceC1884 difference raw27199; decide +kernel
    rw [ha]
    exact (canonical27199 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1884 + difference 5 4) (sourceB1884 + difference 4 5) sourceC1884) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4461) := by
    have ha : (tripleCharges (sourceA1884 + difference 5 4) (sourceB1884 + difference 4 5) sourceC1884) = raw27200 := by
      apply Matrix.ext; unfold tripleCharges sourceA1884 sourceB1884 sourceC1884 difference raw27200; decide +kernel
    rw [ha]
    exact (canonical27200 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1884 sourceB1884 sourceC1884
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1884, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1885 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1885 : Charge := ![1, -1, 2, 0, -1, -1]
def sourceC1885 : Charge := ![3, 1, -3, -1, 0, 0]
def sourceForm1885 : Integer.Sparse Master := [(Sum.inr 995, 1), (Sum.inr 1940, 1), (Sum.inr 2201, 1), (Sum.inr 2219, 1), (Sum.inr 2224, 2), (Sum.inr 4081, -1)]

theorem sourceEq1885 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1885 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1885 + difference 0 0) (sourceB1885 + difference 0 0) sourceC1885) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 995) := by
    have ha : (tripleCharges (sourceA1885 + difference 0 0) (sourceB1885 + difference 0 0) sourceC1885) = raw27201 := by
      apply Matrix.ext; unfold tripleCharges sourceA1885 sourceB1885 sourceC1885 difference raw27201; decide +kernel
    rw [ha]
    exact (canonical27201 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1885 + difference 0 1) (sourceB1885 + difference 1 0) sourceC1885) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1940) := by
    have ha : (tripleCharges (sourceA1885 + difference 0 1) (sourceB1885 + difference 1 0) sourceC1885) = raw27202 := by
      apply Matrix.ext; unfold tripleCharges sourceA1885 sourceB1885 sourceC1885 difference raw27202; decide +kernel
    rw [ha]
    exact (canonical27202 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1885 + difference 0 2) (sourceB1885 + difference 2 0) sourceC1885) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2219) := by
    have ha : (tripleCharges (sourceA1885 + difference 0 2) (sourceB1885 + difference 2 0) sourceC1885) = raw27203 := by
      apply Matrix.ext; unfold tripleCharges sourceA1885 sourceB1885 sourceC1885 difference raw27203; decide +kernel
    rw [ha]
    exact (canonical27203 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1885 + difference 0 3) (sourceB1885 + difference 3 0) sourceC1885) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2201) := by
    have ha : (tripleCharges (sourceA1885 + difference 0 3) (sourceB1885 + difference 3 0) sourceC1885) = raw27204 := by
      apply Matrix.ext; unfold tripleCharges sourceA1885 sourceB1885 sourceC1885 difference raw27204; decide +kernel
    rw [ha]
    exact (canonical27204 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1885 + difference 0 4) (sourceB1885 + difference 4 0) sourceC1885) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2224) := by
    have ha : (tripleCharges (sourceA1885 + difference 0 4) (sourceB1885 + difference 4 0) sourceC1885) = raw27205 := by
      apply Matrix.ext; unfold tripleCharges sourceA1885 sourceB1885 sourceC1885 difference raw27205; decide +kernel
    rw [ha]
    exact (canonical27205 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1885 + difference 0 5) (sourceB1885 + difference 5 0) sourceC1885) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2224) := by
    have ha : (tripleCharges (sourceA1885 + difference 0 5) (sourceB1885 + difference 5 0) sourceC1885) = raw27206 := by
      apply Matrix.ext; unfold tripleCharges sourceA1885 sourceB1885 sourceC1885 difference raw27206; decide +kernel
    rw [ha]
    exact (canonical27206 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1885 + sourceB1885) sourceC1885) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1885 + sourceB1885) sourceC1885) = raw27207 := by
      apply Matrix.ext; unfold doubleCharges sourceA1885 sourceB1885 sourceC1885 raw27207; decide +kernel
    rw [ha]
    exact (canonical27207 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1885 sourceB1885 sourceC1885
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1885, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1886 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1886 : Charge := ![1, -1, 1, 1, -1, -1]
def sourceC1886 : Charge := ![3, 1, -2, -2, 0, 0]
def sourceForm1886 : Integer.Sparse Master := [(Sum.inr 996, 1), (Sum.inr 1941, 1), (Sum.inr 2213, 2), (Sum.inr 2225, 2), (Sum.inr 4082, -1)]

theorem sourceEq1886 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1886 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1886 + difference 0 0) (sourceB1886 + difference 0 0) sourceC1886) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 996) := by
    have ha : (tripleCharges (sourceA1886 + difference 0 0) (sourceB1886 + difference 0 0) sourceC1886) = raw27208 := by
      apply Matrix.ext; unfold tripleCharges sourceA1886 sourceB1886 sourceC1886 difference raw27208; decide +kernel
    rw [ha]
    exact (canonical27208 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1886 + difference 0 1) (sourceB1886 + difference 1 0) sourceC1886) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1941) := by
    have ha : (tripleCharges (sourceA1886 + difference 0 1) (sourceB1886 + difference 1 0) sourceC1886) = raw27209 := by
      apply Matrix.ext; unfold tripleCharges sourceA1886 sourceB1886 sourceC1886 difference raw27209; decide +kernel
    rw [ha]
    exact (canonical27209 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1886 + difference 0 2) (sourceB1886 + difference 2 0) sourceC1886) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2213) := by
    have ha : (tripleCharges (sourceA1886 + difference 0 2) (sourceB1886 + difference 2 0) sourceC1886) = raw27210 := by
      apply Matrix.ext; unfold tripleCharges sourceA1886 sourceB1886 sourceC1886 difference raw27210; decide +kernel
    rw [ha]
    exact (canonical27210 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1886 + difference 0 3) (sourceB1886 + difference 3 0) sourceC1886) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2213) := by
    have ha : (tripleCharges (sourceA1886 + difference 0 3) (sourceB1886 + difference 3 0) sourceC1886) = raw27211 := by
      apply Matrix.ext; unfold tripleCharges sourceA1886 sourceB1886 sourceC1886 difference raw27211; decide +kernel
    rw [ha]
    exact (canonical27211 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1886 + difference 0 4) (sourceB1886 + difference 4 0) sourceC1886) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2225) := by
    have ha : (tripleCharges (sourceA1886 + difference 0 4) (sourceB1886 + difference 4 0) sourceC1886) = raw27212 := by
      apply Matrix.ext; unfold tripleCharges sourceA1886 sourceB1886 sourceC1886 difference raw27212; decide +kernel
    rw [ha]
    exact (canonical27212 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1886 + difference 0 5) (sourceB1886 + difference 5 0) sourceC1886) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2225) := by
    have ha : (tripleCharges (sourceA1886 + difference 0 5) (sourceB1886 + difference 5 0) sourceC1886) = raw27213 := by
      apply Matrix.ext; unfold tripleCharges sourceA1886 sourceB1886 sourceC1886 difference raw27213; decide +kernel
    rw [ha]
    exact (canonical27213 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1886 + sourceB1886) sourceC1886) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA1886 + sourceB1886) sourceC1886) = raw27214 := by
      apply Matrix.ext; unfold doubleCharges sourceA1886 sourceB1886 sourceC1886 raw27214; decide +kernel
    rw [ha]
    exact (canonical27214 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1886 sourceB1886 sourceC1886
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1886, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1887 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1887 : Charge := ![1, -1, 0, 0, 0, 0]
def sourceC1887 : Charge := ![3, 1, -1, -1, -1, -1]
def sourceForm1887 : Integer.Sparse Master := [(Sum.inr 4079, 1), (Sum.inr 4143, 4), (Sum.inr 4164, 1), (Sum.inr 4306, 4), (Sum.inr 4399, 12), (Sum.inr 4451, 4), (Sum.inr 4833, 4)]

theorem sourceEq1887 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1887 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1887 + difference 0 1) (sourceB1887 + difference 1 0) sourceC1887) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4079) := by
    have ha : (tripleCharges (sourceA1887 + difference 0 1) (sourceB1887 + difference 1 0) sourceC1887) = raw27215 := by
      apply Matrix.ext; unfold tripleCharges sourceA1887 sourceB1887 sourceC1887 difference raw27215; decide +kernel
    rw [ha]
    exact (canonical27215 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1887 + difference 0 2) (sourceB1887 + difference 2 0) sourceC1887) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4833) := by
    have ha : (tripleCharges (sourceA1887 + difference 0 2) (sourceB1887 + difference 2 0) sourceC1887) = raw27216 := by
      apply Matrix.ext; unfold tripleCharges sourceA1887 sourceB1887 sourceC1887 difference raw27216; decide +kernel
    rw [ha]
    exact (canonical27216 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1887 + difference 0 3) (sourceB1887 + difference 3 0) sourceC1887) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4833) := by
    have ha : (tripleCharges (sourceA1887 + difference 0 3) (sourceB1887 + difference 3 0) sourceC1887) = raw27217 := by
      apply Matrix.ext; unfold tripleCharges sourceA1887 sourceB1887 sourceC1887 difference raw27217; decide +kernel
    rw [ha]
    exact (canonical27217 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1887 + difference 0 4) (sourceB1887 + difference 4 0) sourceC1887) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4833) := by
    have ha : (tripleCharges (sourceA1887 + difference 0 4) (sourceB1887 + difference 4 0) sourceC1887) = raw27218 := by
      apply Matrix.ext; unfold tripleCharges sourceA1887 sourceB1887 sourceC1887 difference raw27218; decide +kernel
    rw [ha]
    exact (canonical27218 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1887 + difference 0 5) (sourceB1887 + difference 5 0) sourceC1887) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4833) := by
    have ha : (tripleCharges (sourceA1887 + difference 0 5) (sourceB1887 + difference 5 0) sourceC1887) = raw27219 := by
      apply Matrix.ext; unfold tripleCharges sourceA1887 sourceB1887 sourceC1887 difference raw27219; decide +kernel
    rw [ha]
    exact (canonical27219 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1887 + difference 1 0) (sourceB1887 + difference 0 1) sourceC1887) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4164) := by
    have ha : (tripleCharges (sourceA1887 + difference 1 0) (sourceB1887 + difference 0 1) sourceC1887) = raw27220 := by
      apply Matrix.ext; unfold tripleCharges sourceA1887 sourceB1887 sourceC1887 difference raw27220; decide +kernel
    rw [ha]
    exact (canonical27220 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1887 + difference 1 2) (sourceB1887 + difference 2 1) sourceC1887) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4451) := by
    have ha : (tripleCharges (sourceA1887 + difference 1 2) (sourceB1887 + difference 2 1) sourceC1887) = raw27221 := by
      apply Matrix.ext; unfold tripleCharges sourceA1887 sourceB1887 sourceC1887 difference raw27221; decide +kernel
    rw [ha]
    exact (canonical27221 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1887 + difference 1 3) (sourceB1887 + difference 3 1) sourceC1887) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4451) := by
    have ha : (tripleCharges (sourceA1887 + difference 1 3) (sourceB1887 + difference 3 1) sourceC1887) = raw27222 := by
      apply Matrix.ext; unfold tripleCharges sourceA1887 sourceB1887 sourceC1887 difference raw27222; decide +kernel
    rw [ha]
    exact (canonical27222 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1887 + difference 1 4) (sourceB1887 + difference 4 1) sourceC1887) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4451) := by
    have ha : (tripleCharges (sourceA1887 + difference 1 4) (sourceB1887 + difference 4 1) sourceC1887) = raw27223 := by
      apply Matrix.ext; unfold tripleCharges sourceA1887 sourceB1887 sourceC1887 difference raw27223; decide +kernel
    rw [ha]
    exact (canonical27223 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1887 + difference 1 5) (sourceB1887 + difference 5 1) sourceC1887) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4451) := by
    have ha : (tripleCharges (sourceA1887 + difference 1 5) (sourceB1887 + difference 5 1) sourceC1887) = raw27224 := by
      apply Matrix.ext; unfold tripleCharges sourceA1887 sourceB1887 sourceC1887 difference raw27224; decide +kernel
    rw [ha]
    exact (canonical27224 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1887 + difference 2 0) (sourceB1887 + difference 0 2) sourceC1887) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4143) := by
    have ha : (tripleCharges (sourceA1887 + difference 2 0) (sourceB1887 + difference 0 2) sourceC1887) = raw27225 := by
      apply Matrix.ext; unfold tripleCharges sourceA1887 sourceB1887 sourceC1887 difference raw27225; decide +kernel
    rw [ha]
    exact (canonical27225 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1887 + difference 2 1) (sourceB1887 + difference 1 2) sourceC1887) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4306) := by
    have ha : (tripleCharges (sourceA1887 + difference 2 1) (sourceB1887 + difference 1 2) sourceC1887) = raw27226 := by
      apply Matrix.ext; unfold tripleCharges sourceA1887 sourceB1887 sourceC1887 difference raw27226; decide +kernel
    rw [ha]
    exact (canonical27226 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1887 + difference 2 3) (sourceB1887 + difference 3 2) sourceC1887) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4399) := by
    have ha : (tripleCharges (sourceA1887 + difference 2 3) (sourceB1887 + difference 3 2) sourceC1887) = raw27227 := by
      apply Matrix.ext; unfold tripleCharges sourceA1887 sourceB1887 sourceC1887 difference raw27227; decide +kernel
    rw [ha]
    exact (canonical27227 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1887 + difference 2 4) (sourceB1887 + difference 4 2) sourceC1887) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4399) := by
    have ha : (tripleCharges (sourceA1887 + difference 2 4) (sourceB1887 + difference 4 2) sourceC1887) = raw27228 := by
      apply Matrix.ext; unfold tripleCharges sourceA1887 sourceB1887 sourceC1887 difference raw27228; decide +kernel
    rw [ha]
    exact (canonical27228 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1887 + difference 2 5) (sourceB1887 + difference 5 2) sourceC1887) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4399) := by
    have ha : (tripleCharges (sourceA1887 + difference 2 5) (sourceB1887 + difference 5 2) sourceC1887) = raw27229 := by
      apply Matrix.ext; unfold tripleCharges sourceA1887 sourceB1887 sourceC1887 difference raw27229; decide +kernel
    rw [ha]
    exact (canonical27229 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1887 + difference 3 0) (sourceB1887 + difference 0 3) sourceC1887) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4143) := by
    have ha : (tripleCharges (sourceA1887 + difference 3 0) (sourceB1887 + difference 0 3) sourceC1887) = raw27230 := by
      apply Matrix.ext; unfold tripleCharges sourceA1887 sourceB1887 sourceC1887 difference raw27230; decide +kernel
    rw [ha]
    exact (canonical27230 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1887 + difference 3 1) (sourceB1887 + difference 1 3) sourceC1887) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4306) := by
    have ha : (tripleCharges (sourceA1887 + difference 3 1) (sourceB1887 + difference 1 3) sourceC1887) = raw27231 := by
      apply Matrix.ext; unfold tripleCharges sourceA1887 sourceB1887 sourceC1887 difference raw27231; decide +kernel
    rw [ha]
    exact (canonical27231 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1887 + difference 3 2) (sourceB1887 + difference 2 3) sourceC1887) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4399) := by
    have ha : (tripleCharges (sourceA1887 + difference 3 2) (sourceB1887 + difference 2 3) sourceC1887) = raw27232 := by
      apply Matrix.ext; unfold tripleCharges sourceA1887 sourceB1887 sourceC1887 difference raw27232; decide +kernel
    rw [ha]
    exact (canonical27232 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1887 + difference 3 4) (sourceB1887 + difference 4 3) sourceC1887) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4399) := by
    have ha : (tripleCharges (sourceA1887 + difference 3 4) (sourceB1887 + difference 4 3) sourceC1887) = raw27233 := by
      apply Matrix.ext; unfold tripleCharges sourceA1887 sourceB1887 sourceC1887 difference raw27233; decide +kernel
    rw [ha]
    exact (canonical27233 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1887 + difference 3 5) (sourceB1887 + difference 5 3) sourceC1887) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4399) := by
    have ha : (tripleCharges (sourceA1887 + difference 3 5) (sourceB1887 + difference 5 3) sourceC1887) = raw27234 := by
      apply Matrix.ext; unfold tripleCharges sourceA1887 sourceB1887 sourceC1887 difference raw27234; decide +kernel
    rw [ha]
    exact (canonical27234 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1887 + difference 4 0) (sourceB1887 + difference 0 4) sourceC1887) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4143) := by
    have ha : (tripleCharges (sourceA1887 + difference 4 0) (sourceB1887 + difference 0 4) sourceC1887) = raw27235 := by
      apply Matrix.ext; unfold tripleCharges sourceA1887 sourceB1887 sourceC1887 difference raw27235; decide +kernel
    rw [ha]
    exact (canonical27235 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1887 + difference 4 1) (sourceB1887 + difference 1 4) sourceC1887) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4306) := by
    have ha : (tripleCharges (sourceA1887 + difference 4 1) (sourceB1887 + difference 1 4) sourceC1887) = raw27236 := by
      apply Matrix.ext; unfold tripleCharges sourceA1887 sourceB1887 sourceC1887 difference raw27236; decide +kernel
    rw [ha]
    exact (canonical27236 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1887 + difference 4 2) (sourceB1887 + difference 2 4) sourceC1887) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4399) := by
    have ha : (tripleCharges (sourceA1887 + difference 4 2) (sourceB1887 + difference 2 4) sourceC1887) = raw27237 := by
      apply Matrix.ext; unfold tripleCharges sourceA1887 sourceB1887 sourceC1887 difference raw27237; decide +kernel
    rw [ha]
    exact (canonical27237 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1887 + difference 4 3) (sourceB1887 + difference 3 4) sourceC1887) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4399) := by
    have ha : (tripleCharges (sourceA1887 + difference 4 3) (sourceB1887 + difference 3 4) sourceC1887) = raw27238 := by
      apply Matrix.ext; unfold tripleCharges sourceA1887 sourceB1887 sourceC1887 difference raw27238; decide +kernel
    rw [ha]
    exact (canonical27238 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1887 + difference 4 5) (sourceB1887 + difference 5 4) sourceC1887) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4399) := by
    have ha : (tripleCharges (sourceA1887 + difference 4 5) (sourceB1887 + difference 5 4) sourceC1887) = raw27239 := by
      apply Matrix.ext; unfold tripleCharges sourceA1887 sourceB1887 sourceC1887 difference raw27239; decide +kernel
    rw [ha]
    exact (canonical27239 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1887 + difference 5 0) (sourceB1887 + difference 0 5) sourceC1887) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4143) := by
    have ha : (tripleCharges (sourceA1887 + difference 5 0) (sourceB1887 + difference 0 5) sourceC1887) = raw27240 := by
      apply Matrix.ext; unfold tripleCharges sourceA1887 sourceB1887 sourceC1887 difference raw27240; decide +kernel
    rw [ha]
    exact (canonical27240 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1887 + difference 5 1) (sourceB1887 + difference 1 5) sourceC1887) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4306) := by
    have ha : (tripleCharges (sourceA1887 + difference 5 1) (sourceB1887 + difference 1 5) sourceC1887) = raw27241 := by
      apply Matrix.ext; unfold tripleCharges sourceA1887 sourceB1887 sourceC1887 difference raw27241; decide +kernel
    rw [ha]
    exact (canonical27241 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1887 + difference 5 2) (sourceB1887 + difference 2 5) sourceC1887) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4399) := by
    have ha : (tripleCharges (sourceA1887 + difference 5 2) (sourceB1887 + difference 2 5) sourceC1887) = raw27242 := by
      apply Matrix.ext; unfold tripleCharges sourceA1887 sourceB1887 sourceC1887 difference raw27242; decide +kernel
    rw [ha]
    exact (canonical27242 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1887 + difference 5 3) (sourceB1887 + difference 3 5) sourceC1887) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4399) := by
    have ha : (tripleCharges (sourceA1887 + difference 5 3) (sourceB1887 + difference 3 5) sourceC1887) = raw27243 := by
      apply Matrix.ext; unfold tripleCharges sourceA1887 sourceB1887 sourceC1887 difference raw27243; decide +kernel
    rw [ha]
    exact (canonical27243 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1887 + difference 5 4) (sourceB1887 + difference 4 5) sourceC1887) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4399) := by
    have ha : (tripleCharges (sourceA1887 + difference 5 4) (sourceB1887 + difference 4 5) sourceC1887) = raw27244 := by
      apply Matrix.ext; unfold tripleCharges sourceA1887 sourceB1887 sourceC1887 difference raw27244; decide +kernel
    rw [ha]
    exact (canonical27244 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1887 sourceB1887 sourceC1887
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1887, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
