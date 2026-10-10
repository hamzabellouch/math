import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical86
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical87
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical88
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical89
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical90
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical111
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical116
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical169
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical182
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical183
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical184
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical186
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical213
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical229
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical231
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical233
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical234
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical235
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical237
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical238
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical239
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical242
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical243
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical244
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical245
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical246
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical247
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical248

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA2272 : Charge := ![0, 2, 0, -1, 0, -1]
def sourceB2272 : Charge := ![3, -1, 0, 1, -2, -1]
def sourceC2272 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceForm2272 : Integer.Sparse Master := [(Sum.inr 917, 1), (Sum.inr 1800, 1), (Sum.inr 1958, 1), (Sum.inr 2007, 1), (Sum.inr 2048, 2), (Sum.inr 4082, -1)]

theorem sourceEq2272 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2272 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2272 + difference 5 0) (sourceB2272 + difference 0 5) sourceC2272) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 917) := by
    have ha : (tripleCharges (sourceA2272 + difference 5 0) (sourceB2272 + difference 0 5) sourceC2272) = raw31273 := by
      apply Matrix.ext; unfold tripleCharges sourceA2272 sourceB2272 sourceC2272 difference raw31273; decide +kernel
    rw [ha]
    exact (canonical31273 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2272 + difference 5 1) (sourceB2272 + difference 1 5) sourceC2272) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2007) := by
    have ha : (tripleCharges (sourceA2272 + difference 5 1) (sourceB2272 + difference 1 5) sourceC2272) = raw30196 := by
      apply Matrix.ext; unfold tripleCharges sourceA2272 sourceB2272 sourceC2272 difference raw30196; decide +kernel
    rw [ha]
    exact (canonical30196 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2272 + difference 5 2) (sourceB2272 + difference 2 5) sourceC2272) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1958) := by
    have ha : (tripleCharges (sourceA2272 + difference 5 2) (sourceB2272 + difference 2 5) sourceC2272) = raw30207 := by
      apply Matrix.ext; unfold tripleCharges sourceA2272 sourceB2272 sourceC2272 difference raw30207; decide +kernel
    rw [ha]
    exact (canonical30207 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2272 + difference 5 3) (sourceB2272 + difference 3 5) sourceC2272) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1800) := by
    have ha : (tripleCharges (sourceA2272 + difference 5 3) (sourceB2272 + difference 3 5) sourceC2272) = raw30194 := by
      apply Matrix.ext; unfold tripleCharges sourceA2272 sourceB2272 sourceC2272 difference raw30194; decide +kernel
    rw [ha]
    exact (canonical30194 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2272 + difference 5 4) (sourceB2272 + difference 4 5) sourceC2272) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2048) := by
    have ha : (tripleCharges (sourceA2272 + difference 5 4) (sourceB2272 + difference 4 5) sourceC2272) = raw31274 := by
      apply Matrix.ext; unfold tripleCharges sourceA2272 sourceB2272 sourceC2272 difference raw31274; decide +kernel
    rw [ha]
    exact (canonical31274 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2272 + difference 5 5) (sourceB2272 + difference 5 5) sourceC2272) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2048) := by
    have ha : (tripleCharges (sourceA2272 + difference 5 5) (sourceB2272 + difference 5 5) sourceC2272) = raw31275 := by
      apply Matrix.ext; unfold tripleCharges sourceA2272 sourceB2272 sourceC2272 difference raw31275; decide +kernel
    rw [ha]
    exact (canonical31275 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2272 + sourceB2272) sourceC2272) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2272 + sourceB2272) sourceC2272) = raw29319 := by
      apply Matrix.ext; unfold doubleCharges sourceA2272 sourceB2272 sourceC2272 raw29319; decide +kernel
    rw [ha]
    exact (canonical29319 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2272 sourceB2272 sourceC2272
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2272, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2273 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2273 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC2273 : Charge := ![3, 0, -1, 0, -2, 0]
def sourceForm2273 : Integer.Sparse Master := [(Sum.inr 4328, 1), (Sum.inr 4334, 1), (Sum.inr 4336, 1), (Sum.inr 4354, 1), (Sum.inr 4466, 1), (Sum.inr 4665, 1), (Sum.inr 4667, 1), (Sum.inr 4669, 1), (Sum.inr 4671, 1), (Sum.inr 4687, 1), (Sum.inr 4688, 1), (Sum.inr 4756, 1), (Sum.inr 4766, 1), (Sum.inr 4773, 1), (Sum.inr 4776, 1), (Sum.inr 4801, 1), (Sum.inr 4803, 1), (Sum.inr 4804, 1), (Sum.inr 4808, 1), (Sum.inr 4810, 1), (Sum.inr 4834, 1), (Sum.inr 4839, 1), (Sum.inr 4874, 1), (Sum.inr 4894, 1), (Sum.inr 4896, 1), (Sum.inr 5232, 1), (Sum.inr 5243, 1), (Sum.inr 5258, 1), (Sum.inr 5264, 1), (Sum.inr 5266, 1)]

theorem sourceEq2273 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2273 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2273 + difference 0 1) (sourceB2273 + difference 1 0) sourceC2273) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5232) := by
    have ha : (tripleCharges (sourceA2273 + difference 0 1) (sourceB2273 + difference 1 0) sourceC2273) = raw31276 := by
      apply Matrix.ext; unfold tripleCharges sourceA2273 sourceB2273 sourceC2273 difference raw31276; decide +kernel
    rw [ha]
    exact (canonical31276 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2273 + difference 0 2) (sourceB2273 + difference 2 0) sourceC2273) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5264) := by
    have ha : (tripleCharges (sourceA2273 + difference 0 2) (sourceB2273 + difference 2 0) sourceC2273) = raw31277 := by
      apply Matrix.ext; unfold tripleCharges sourceA2273 sourceB2273 sourceC2273 difference raw31277; decide +kernel
    rw [ha]
    exact (canonical31277 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2273 + difference 0 3) (sourceB2273 + difference 3 0) sourceC2273) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5243) := by
    have ha : (tripleCharges (sourceA2273 + difference 0 3) (sourceB2273 + difference 3 0) sourceC2273) = raw31278 := by
      apply Matrix.ext; unfold tripleCharges sourceA2273 sourceB2273 sourceC2273 difference raw31278; decide +kernel
    rw [ha]
    exact (canonical31278 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2273 + difference 0 4) (sourceB2273 + difference 4 0) sourceC2273) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA2273 + difference 0 4) (sourceB2273 + difference 4 0) sourceC2273) = raw31279 := by
      apply Matrix.ext; unfold tripleCharges sourceA2273 sourceB2273 sourceC2273 difference raw31279; decide +kernel
    rw [ha]
    exact (canonical31279 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2273 + difference 0 5) (sourceB2273 + difference 5 0) sourceC2273) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA2273 + difference 0 5) (sourceB2273 + difference 5 0) sourceC2273) = raw31280 := by
      apply Matrix.ext; unfold tripleCharges sourceA2273 sourceB2273 sourceC2273 difference raw31280; decide +kernel
    rw [ha]
    exact (canonical31280 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2273 + difference 1 0) (sourceB2273 + difference 0 1) sourceC2273) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4466) := by
    have ha : (tripleCharges (sourceA2273 + difference 1 0) (sourceB2273 + difference 0 1) sourceC2273) = raw31281 := by
      apply Matrix.ext; unfold tripleCharges sourceA2273 sourceB2273 sourceC2273 difference raw31281; decide +kernel
    rw [ha]
    exact (canonical31281 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2273 + difference 1 2) (sourceB2273 + difference 2 1) sourceC2273) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4874) := by
    have ha : (tripleCharges (sourceA2273 + difference 1 2) (sourceB2273 + difference 2 1) sourceC2273) = raw31282 := by
      apply Matrix.ext; unfold tripleCharges sourceA2273 sourceB2273 sourceC2273 difference raw31282; decide +kernel
    rw [ha]
    exact (canonical31282 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2273 + difference 1 3) (sourceB2273 + difference 3 1) sourceC2273) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4810) := by
    have ha : (tripleCharges (sourceA2273 + difference 1 3) (sourceB2273 + difference 3 1) sourceC2273) = raw31283 := by
      apply Matrix.ext; unfold tripleCharges sourceA2273 sourceB2273 sourceC2273 difference raw31283; decide +kernel
    rw [ha]
    exact (canonical31283 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2273 + difference 1 4) (sourceB2273 + difference 4 1) sourceC2273) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4896) := by
    have ha : (tripleCharges (sourceA2273 + difference 1 4) (sourceB2273 + difference 4 1) sourceC2273) = raw31284 := by
      apply Matrix.ext; unfold tripleCharges sourceA2273 sourceB2273 sourceC2273 difference raw31284; decide +kernel
    rw [ha]
    exact (canonical31284 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2273 + difference 1 5) (sourceB2273 + difference 5 1) sourceC2273) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4894) := by
    have ha : (tripleCharges (sourceA2273 + difference 1 5) (sourceB2273 + difference 5 1) sourceC2273) = raw31285 := by
      apply Matrix.ext; unfold tripleCharges sourceA2273 sourceB2273 sourceC2273 difference raw31285; decide +kernel
    rw [ha]
    exact (canonical31285 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2273 + difference 2 0) (sourceB2273 + difference 0 2) sourceC2273) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4354) := by
    have ha : (tripleCharges (sourceA2273 + difference 2 0) (sourceB2273 + difference 0 2) sourceC2273) = raw31286 := by
      apply Matrix.ext; unfold tripleCharges sourceA2273 sourceB2273 sourceC2273 difference raw31286; decide +kernel
    rw [ha]
    exact (canonical31286 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2273 + difference 2 1) (sourceB2273 + difference 1 2) sourceC2273) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4688) := by
    have ha : (tripleCharges (sourceA2273 + difference 2 1) (sourceB2273 + difference 1 2) sourceC2273) = raw31287 := by
      apply Matrix.ext; unfold tripleCharges sourceA2273 sourceB2273 sourceC2273 difference raw31287; decide +kernel
    rw [ha]
    exact (canonical31287 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2273 + difference 2 3) (sourceB2273 + difference 3 2) sourceC2273) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4766) := by
    have ha : (tripleCharges (sourceA2273 + difference 2 3) (sourceB2273 + difference 3 2) sourceC2273) = raw31288 := by
      apply Matrix.ext; unfold tripleCharges sourceA2273 sourceB2273 sourceC2273 difference raw31288; decide +kernel
    rw [ha]
    exact (canonical31288 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2273 + difference 2 4) (sourceB2273 + difference 4 2) sourceC2273) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4839) := by
    have ha : (tripleCharges (sourceA2273 + difference 2 4) (sourceB2273 + difference 4 2) sourceC2273) = raw31289 := by
      apply Matrix.ext; unfold tripleCharges sourceA2273 sourceB2273 sourceC2273 difference raw31289; decide +kernel
    rw [ha]
    exact (canonical31289 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2273 + difference 2 5) (sourceB2273 + difference 5 2) sourceC2273) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4834) := by
    have ha : (tripleCharges (sourceA2273 + difference 2 5) (sourceB2273 + difference 5 2) sourceC2273) = raw31290 := by
      apply Matrix.ext; unfold tripleCharges sourceA2273 sourceB2273 sourceC2273 difference raw31290; decide +kernel
    rw [ha]
    exact (canonical31290 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2273 + difference 3 0) (sourceB2273 + difference 0 3) sourceC2273) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4328) := by
    have ha : (tripleCharges (sourceA2273 + difference 3 0) (sourceB2273 + difference 0 3) sourceC2273) = raw31291 := by
      apply Matrix.ext; unfold tripleCharges sourceA2273 sourceB2273 sourceC2273 difference raw31291; decide +kernel
    rw [ha]
    exact (canonical31291 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2273 + difference 3 1) (sourceB2273 + difference 1 3) sourceC2273) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4665) := by
    have ha : (tripleCharges (sourceA2273 + difference 3 1) (sourceB2273 + difference 1 3) sourceC2273) = raw31292 := by
      apply Matrix.ext; unfold tripleCharges sourceA2273 sourceB2273 sourceC2273 difference raw31292; decide +kernel
    rw [ha]
    exact (canonical31292 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2273 + difference 3 2) (sourceB2273 + difference 2 3) sourceC2273) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4773) := by
    have ha : (tripleCharges (sourceA2273 + difference 3 2) (sourceB2273 + difference 2 3) sourceC2273) = raw31293 := by
      apply Matrix.ext; unfold tripleCharges sourceA2273 sourceB2273 sourceC2273 difference raw31293; decide +kernel
    rw [ha]
    exact (canonical31293 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2273 + difference 3 4) (sourceB2273 + difference 4 3) sourceC2273) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4803) := by
    have ha : (tripleCharges (sourceA2273 + difference 3 4) (sourceB2273 + difference 4 3) sourceC2273) = raw31294 := by
      apply Matrix.ext; unfold tripleCharges sourceA2273 sourceB2273 sourceC2273 difference raw31294; decide +kernel
    rw [ha]
    exact (canonical31294 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2273 + difference 3 5) (sourceB2273 + difference 5 3) sourceC2273) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4801) := by
    have ha : (tripleCharges (sourceA2273 + difference 3 5) (sourceB2273 + difference 5 3) sourceC2273) = raw31295 := by
      apply Matrix.ext; unfold tripleCharges sourceA2273 sourceB2273 sourceC2273 difference raw31295; decide +kernel
    rw [ha]
    exact (canonical31295 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2273 + difference 4 0) (sourceB2273 + difference 0 4) sourceC2273) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4334) := by
    have ha : (tripleCharges (sourceA2273 + difference 4 0) (sourceB2273 + difference 0 4) sourceC2273) = raw31296 := by
      apply Matrix.ext; unfold tripleCharges sourceA2273 sourceB2273 sourceC2273 difference raw31296; decide +kernel
    rw [ha]
    exact (canonical31296 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2273 + difference 4 1) (sourceB2273 + difference 1 4) sourceC2273) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4669) := by
    have ha : (tripleCharges (sourceA2273 + difference 4 1) (sourceB2273 + difference 1 4) sourceC2273) = raw31297 := by
      apply Matrix.ext; unfold tripleCharges sourceA2273 sourceB2273 sourceC2273 difference raw31297; decide +kernel
    rw [ha]
    exact (canonical31297 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2273 + difference 4 2) (sourceB2273 + difference 2 4) sourceC2273) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4776) := by
    have ha : (tripleCharges (sourceA2273 + difference 4 2) (sourceB2273 + difference 2 4) sourceC2273) = raw31298 := by
      apply Matrix.ext; unfold tripleCharges sourceA2273 sourceB2273 sourceC2273 difference raw31298; decide +kernel
    rw [ha]
    exact (canonical31298 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2273 + difference 4 3) (sourceB2273 + difference 3 4) sourceC2273) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4756) := by
    have ha : (tripleCharges (sourceA2273 + difference 4 3) (sourceB2273 + difference 3 4) sourceC2273) = raw31299 := by
      apply Matrix.ext; unfold tripleCharges sourceA2273 sourceB2273 sourceC2273 difference raw31299; decide +kernel
    rw [ha]
    exact (canonical31299 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2273 + difference 4 5) (sourceB2273 + difference 5 4) sourceC2273) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA2273 + difference 4 5) (sourceB2273 + difference 5 4) sourceC2273) = raw31300 := by
      apply Matrix.ext; unfold tripleCharges sourceA2273 sourceB2273 sourceC2273 difference raw31300; decide +kernel
    rw [ha]
    exact (canonical31300 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2273 + difference 5 0) (sourceB2273 + difference 0 5) sourceC2273) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4336) := by
    have ha : (tripleCharges (sourceA2273 + difference 5 0) (sourceB2273 + difference 0 5) sourceC2273) = raw31301 := by
      apply Matrix.ext; unfold tripleCharges sourceA2273 sourceB2273 sourceC2273 difference raw31301; decide +kernel
    rw [ha]
    exact (canonical31301 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2273 + difference 5 1) (sourceB2273 + difference 1 5) sourceC2273) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4671) := by
    have ha : (tripleCharges (sourceA2273 + difference 5 1) (sourceB2273 + difference 1 5) sourceC2273) = raw31302 := by
      apply Matrix.ext; unfold tripleCharges sourceA2273 sourceB2273 sourceC2273 difference raw31302; decide +kernel
    rw [ha]
    exact (canonical31302 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2273 + difference 5 2) (sourceB2273 + difference 2 5) sourceC2273) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4687) := by
    have ha : (tripleCharges (sourceA2273 + difference 5 2) (sourceB2273 + difference 2 5) sourceC2273) = raw31303 := by
      apply Matrix.ext; unfold tripleCharges sourceA2273 sourceB2273 sourceC2273 difference raw31303; decide +kernel
    rw [ha]
    exact (canonical31303 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2273 + difference 5 3) (sourceB2273 + difference 3 5) sourceC2273) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4667) := by
    have ha : (tripleCharges (sourceA2273 + difference 5 3) (sourceB2273 + difference 3 5) sourceC2273) = raw31304 := by
      apply Matrix.ext; unfold tripleCharges sourceA2273 sourceB2273 sourceC2273 difference raw31304; decide +kernel
    rw [ha]
    exact (canonical31304 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2273 + difference 5 4) (sourceB2273 + difference 4 5) sourceC2273) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4808) := by
    have ha : (tripleCharges (sourceA2273 + difference 5 4) (sourceB2273 + difference 4 5) sourceC2273) = raw31305 := by
      apply Matrix.ext; unfold tripleCharges sourceA2273 sourceB2273 sourceC2273 difference raw31305; decide +kernel
    rw [ha]
    exact (canonical31305 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2273 sourceB2273 sourceC2273
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2273, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2274 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2274 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC2274 : Charge := ![3, 0, -1, 0, -2, 0]
def sourceForm2274 : Integer.Sparse Master := [(Sum.inr 1330, 1), (Sum.inr 1332, 1), (Sum.inr 1334, 1), (Sum.inr 1343, 1), (Sum.inr 1419, 1), (Sum.inr 1793, 1), (Sum.inr 1797, 1), (Sum.inr 1813, 1), (Sum.inr 2092, 1), (Sum.inr 2800, 1), (Sum.inr 2803, 1), (Sum.inr 2816, 1), (Sum.inr 2941, 1), (Sum.inr 3030, 1), (Sum.inr 3039, 1), (Sum.inr 3040, 1), (Sum.inr 3045, 1), (Sum.inr 3089, 1), (Sum.inr 3134, 1), (Sum.inr 3141, 1), (Sum.inr 3163, 1), (Sum.inr 3187, 1), (Sum.inr 3190, 1), (Sum.inr 3202, 1), (Sum.inr 3205, 1), (Sum.inr 3206, 1), (Sum.inr 3210, 1), (Sum.inr 3214, 1), (Sum.inr 3225, 1), (Sum.inr 3230, 1)]

theorem sourceEq2274 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2274 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2274 + difference 0 1) (sourceB2274 + difference 1 0) sourceC2274) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3045) := by
    have ha : (tripleCharges (sourceA2274 + difference 0 1) (sourceB2274 + difference 1 0) sourceC2274) = raw31306 := by
      apply Matrix.ext; unfold tripleCharges sourceA2274 sourceB2274 sourceC2274 difference raw31306; decide +kernel
    rw [ha]
    exact (canonical31306 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2274 + difference 0 2) (sourceB2274 + difference 2 0) sourceC2274) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3040) := by
    have ha : (tripleCharges (sourceA2274 + difference 0 2) (sourceB2274 + difference 2 0) sourceC2274) = raw31307 := by
      apply Matrix.ext; unfold tripleCharges sourceA2274 sourceB2274 sourceC2274 difference raw31307; decide +kernel
    rw [ha]
    exact (canonical31307 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2274 + difference 0 3) (sourceB2274 + difference 3 0) sourceC2274) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3030) := by
    have ha : (tripleCharges (sourceA2274 + difference 0 3) (sourceB2274 + difference 3 0) sourceC2274) = raw31308 := by
      apply Matrix.ext; unfold tripleCharges sourceA2274 sourceB2274 sourceC2274 difference raw31308; decide +kernel
    rw [ha]
    exact (canonical31308 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2274 + difference 0 4) (sourceB2274 + difference 4 0) sourceC2274) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3039) := by
    have ha : (tripleCharges (sourceA2274 + difference 0 4) (sourceB2274 + difference 4 0) sourceC2274) = raw31309 := by
      apply Matrix.ext; unfold tripleCharges sourceA2274 sourceB2274 sourceC2274 difference raw31309; decide +kernel
    rw [ha]
    exact (canonical31309 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2274 + difference 0 5) (sourceB2274 + difference 5 0) sourceC2274) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3089) := by
    have ha : (tripleCharges (sourceA2274 + difference 0 5) (sourceB2274 + difference 5 0) sourceC2274) = raw31310 := by
      apply Matrix.ext; unfold tripleCharges sourceA2274 sourceB2274 sourceC2274 difference raw31310; decide +kernel
    rw [ha]
    exact (canonical31310 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2274 + difference 1 0) (sourceB2274 + difference 0 1) sourceC2274) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1419) := by
    have ha : (tripleCharges (sourceA2274 + difference 1 0) (sourceB2274 + difference 0 1) sourceC2274) = raw31311 := by
      apply Matrix.ext; unfold tripleCharges sourceA2274 sourceB2274 sourceC2274 difference raw31311; decide +kernel
    rw [ha]
    exact (canonical31311 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2274 + difference 1 2) (sourceB2274 + difference 2 1) sourceC2274) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3187) := by
    have ha : (tripleCharges (sourceA2274 + difference 1 2) (sourceB2274 + difference 2 1) sourceC2274) = raw31312 := by
      apply Matrix.ext; unfold tripleCharges sourceA2274 sourceB2274 sourceC2274 difference raw31312; decide +kernel
    rw [ha]
    exact (canonical31312 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2274 + difference 1 3) (sourceB2274 + difference 3 1) sourceC2274) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3206) := by
    have ha : (tripleCharges (sourceA2274 + difference 1 3) (sourceB2274 + difference 3 1) sourceC2274) = raw31313 := by
      apply Matrix.ext; unfold tripleCharges sourceA2274 sourceB2274 sourceC2274 difference raw31313; decide +kernel
    rw [ha]
    exact (canonical31313 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2274 + difference 1 4) (sourceB2274 + difference 4 1) sourceC2274) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3225) := by
    have ha : (tripleCharges (sourceA2274 + difference 1 4) (sourceB2274 + difference 4 1) sourceC2274) = raw31314 := by
      apply Matrix.ext; unfold tripleCharges sourceA2274 sourceB2274 sourceC2274 difference raw31314; decide +kernel
    rw [ha]
    exact (canonical31314 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2274 + difference 1 5) (sourceB2274 + difference 5 1) sourceC2274) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3230) := by
    have ha : (tripleCharges (sourceA2274 + difference 1 5) (sourceB2274 + difference 5 1) sourceC2274) = raw31315 := by
      apply Matrix.ext; unfold tripleCharges sourceA2274 sourceB2274 sourceC2274 difference raw31315; decide +kernel
    rw [ha]
    exact (canonical31315 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2274 + difference 2 0) (sourceB2274 + difference 0 2) sourceC2274) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1343) := by
    have ha : (tripleCharges (sourceA2274 + difference 2 0) (sourceB2274 + difference 0 2) sourceC2274) = raw31316 := by
      apply Matrix.ext; unfold tripleCharges sourceA2274 sourceB2274 sourceC2274 difference raw31316; decide +kernel
    rw [ha]
    exact (canonical31316 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2274 + difference 2 1) (sourceB2274 + difference 1 2) sourceC2274) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3141) := by
    have ha : (tripleCharges (sourceA2274 + difference 2 1) (sourceB2274 + difference 1 2) sourceC2274) = raw31317 := by
      apply Matrix.ext; unfold tripleCharges sourceA2274 sourceB2274 sourceC2274 difference raw31317; decide +kernel
    rw [ha]
    exact (canonical31317 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2274 + difference 2 3) (sourceB2274 + difference 3 2) sourceC2274) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3190) := by
    have ha : (tripleCharges (sourceA2274 + difference 2 3) (sourceB2274 + difference 3 2) sourceC2274) = raw31318 := by
      apply Matrix.ext; unfold tripleCharges sourceA2274 sourceB2274 sourceC2274 difference raw31318; decide +kernel
    rw [ha]
    exact (canonical31318 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2274 + difference 2 4) (sourceB2274 + difference 4 2) sourceC2274) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3210) := by
    have ha : (tripleCharges (sourceA2274 + difference 2 4) (sourceB2274 + difference 4 2) sourceC2274) = raw31319 := by
      apply Matrix.ext; unfold tripleCharges sourceA2274 sourceB2274 sourceC2274 difference raw31319; decide +kernel
    rw [ha]
    exact (canonical31319 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2274 + difference 2 5) (sourceB2274 + difference 5 2) sourceC2274) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3214) := by
    have ha : (tripleCharges (sourceA2274 + difference 2 5) (sourceB2274 + difference 5 2) sourceC2274) = raw31320 := by
      apply Matrix.ext; unfold tripleCharges sourceA2274 sourceB2274 sourceC2274 difference raw31320; decide +kernel
    rw [ha]
    exact (canonical31320 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2274 + difference 3 0) (sourceB2274 + difference 0 3) sourceC2274) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1330) := by
    have ha : (tripleCharges (sourceA2274 + difference 3 0) (sourceB2274 + difference 0 3) sourceC2274) = raw31321 := by
      apply Matrix.ext; unfold tripleCharges sourceA2274 sourceB2274 sourceC2274 difference raw31321; decide +kernel
    rw [ha]
    exact (canonical31321 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2274 + difference 3 1) (sourceB2274 + difference 1 3) sourceC2274) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3134) := by
    have ha : (tripleCharges (sourceA2274 + difference 3 1) (sourceB2274 + difference 1 3) sourceC2274) = raw31322 := by
      apply Matrix.ext; unfold tripleCharges sourceA2274 sourceB2274 sourceC2274 difference raw31322; decide +kernel
    rw [ha]
    exact (canonical31322 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2274 + difference 3 2) (sourceB2274 + difference 2 3) sourceC2274) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3163) := by
    have ha : (tripleCharges (sourceA2274 + difference 3 2) (sourceB2274 + difference 2 3) sourceC2274) = raw31323 := by
      apply Matrix.ext; unfold tripleCharges sourceA2274 sourceB2274 sourceC2274 difference raw31323; decide +kernel
    rw [ha]
    exact (canonical31323 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2274 + difference 3 4) (sourceB2274 + difference 4 3) sourceC2274) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3202) := by
    have ha : (tripleCharges (sourceA2274 + difference 3 4) (sourceB2274 + difference 4 3) sourceC2274) = raw31324 := by
      apply Matrix.ext; unfold tripleCharges sourceA2274 sourceB2274 sourceC2274 difference raw31324; decide +kernel
    rw [ha]
    exact (canonical31324 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2274 + difference 3 5) (sourceB2274 + difference 5 3) sourceC2274) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3205) := by
    have ha : (tripleCharges (sourceA2274 + difference 3 5) (sourceB2274 + difference 5 3) sourceC2274) = raw31325 := by
      apply Matrix.ext; unfold tripleCharges sourceA2274 sourceB2274 sourceC2274 difference raw31325; decide +kernel
    rw [ha]
    exact (canonical31325 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2274 + difference 4 0) (sourceB2274 + difference 0 4) sourceC2274) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1334) := by
    have ha : (tripleCharges (sourceA2274 + difference 4 0) (sourceB2274 + difference 0 4) sourceC2274) = raw31326 := by
      apply Matrix.ext; unfold tripleCharges sourceA2274 sourceB2274 sourceC2274 difference raw31326; decide +kernel
    rw [ha]
    exact (canonical31326 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2274 + difference 4 1) (sourceB2274 + difference 1 4) sourceC2274) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2803) := by
    have ha : (tripleCharges (sourceA2274 + difference 4 1) (sourceB2274 + difference 1 4) sourceC2274) = raw31327 := by
      apply Matrix.ext; unfold tripleCharges sourceA2274 sourceB2274 sourceC2274 difference raw31327; decide +kernel
    rw [ha]
    exact (canonical31327 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2274 + difference 4 2) (sourceB2274 + difference 2 4) sourceC2274) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2816) := by
    have ha : (tripleCharges (sourceA2274 + difference 4 2) (sourceB2274 + difference 2 4) sourceC2274) = raw31328 := by
      apply Matrix.ext; unfold tripleCharges sourceA2274 sourceB2274 sourceC2274 difference raw31328; decide +kernel
    rw [ha]
    exact (canonical31328 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2274 + difference 4 3) (sourceB2274 + difference 3 4) sourceC2274) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2800) := by
    have ha : (tripleCharges (sourceA2274 + difference 4 3) (sourceB2274 + difference 3 4) sourceC2274) = raw31329 := by
      apply Matrix.ext; unfold tripleCharges sourceA2274 sourceB2274 sourceC2274 difference raw31329; decide +kernel
    rw [ha]
    exact (canonical31329 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2274 + difference 4 5) (sourceB2274 + difference 5 4) sourceC2274) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2941) := by
    have ha : (tripleCharges (sourceA2274 + difference 4 5) (sourceB2274 + difference 5 4) sourceC2274) = raw31330 := by
      apply Matrix.ext; unfold tripleCharges sourceA2274 sourceB2274 sourceC2274 difference raw31330; decide +kernel
    rw [ha]
    exact (canonical31330 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2274 + difference 5 0) (sourceB2274 + difference 0 5) sourceC2274) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1332) := by
    have ha : (tripleCharges (sourceA2274 + difference 5 0) (sourceB2274 + difference 0 5) sourceC2274) = raw31331 := by
      apply Matrix.ext; unfold tripleCharges sourceA2274 sourceB2274 sourceC2274 difference raw31331; decide +kernel
    rw [ha]
    exact (canonical31331 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2274 + difference 5 1) (sourceB2274 + difference 1 5) sourceC2274) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1797) := by
    have ha : (tripleCharges (sourceA2274 + difference 5 1) (sourceB2274 + difference 1 5) sourceC2274) = raw31332 := by
      apply Matrix.ext; unfold tripleCharges sourceA2274 sourceB2274 sourceC2274 difference raw31332; decide +kernel
    rw [ha]
    exact (canonical31332 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2274 + difference 5 2) (sourceB2274 + difference 2 5) sourceC2274) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1813) := by
    have ha : (tripleCharges (sourceA2274 + difference 5 2) (sourceB2274 + difference 2 5) sourceC2274) = raw31333 := by
      apply Matrix.ext; unfold tripleCharges sourceA2274 sourceB2274 sourceC2274 difference raw31333; decide +kernel
    rw [ha]
    exact (canonical31333 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2274 + difference 5 3) (sourceB2274 + difference 3 5) sourceC2274) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1793) := by
    have ha : (tripleCharges (sourceA2274 + difference 5 3) (sourceB2274 + difference 3 5) sourceC2274) = raw31334 := by
      apply Matrix.ext; unfold tripleCharges sourceA2274 sourceB2274 sourceC2274 difference raw31334; decide +kernel
    rw [ha]
    exact (canonical31334 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2274 + difference 5 4) (sourceB2274 + difference 4 5) sourceC2274) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2092) := by
    have ha : (tripleCharges (sourceA2274 + difference 5 4) (sourceB2274 + difference 4 5) sourceC2274) = raw31335 := by
      apply Matrix.ext; unfold tripleCharges sourceA2274 sourceB2274 sourceC2274 difference raw31335; decide +kernel
    rw [ha]
    exact (canonical31335 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2274 sourceB2274 sourceC2274
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2274, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2275 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2275 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC2275 : Charge := ![3, 0, -1, 0, -2, 0]
def sourceForm2275 : Integer.Sparse Master := [(Sum.inr 1667, 1), (Sum.inr 1679, 1), (Sum.inr 1681, 1), (Sum.inr 1685, 1), (Sum.inr 1738, 1), (Sum.inr 2144, 1), (Sum.inr 2155, 1), (Sum.inr 2157, 1), (Sum.inr 2160, 1), (Sum.inr 2161, 1), (Sum.inr 2162, 1), (Sum.inr 2176, 1), (Sum.inr 2177, 1), (Sum.inr 2190, 1), (Sum.inr 2194, 1), (Sum.inr 2195, 1), (Sum.inr 2203, 1), (Sum.inr 2205, 1), (Sum.inr 2212, 1), (Sum.inr 2215, 1), (Sum.inr 2216, 1), (Sum.inr 2220, 1), (Sum.inr 2264, 1), (Sum.inr 2276, 1), (Sum.inr 2278, 1), (Sum.inr 2677, 1), (Sum.inr 2697, 1), (Sum.inr 2722, 1), (Sum.inr 2729, 1), (Sum.inr 2731, 1)]

theorem sourceEq2275 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2275 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2275 + difference 0 1) (sourceB2275 + difference 1 0) sourceC2275) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2677) := by
    have ha : (tripleCharges (sourceA2275 + difference 0 1) (sourceB2275 + difference 1 0) sourceC2275) = raw31336 := by
      apply Matrix.ext; unfold tripleCharges sourceA2275 sourceB2275 sourceC2275 difference raw31336; decide +kernel
    rw [ha]
    exact (canonical31336 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2275 + difference 0 2) (sourceB2275 + difference 2 0) sourceC2275) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2729) := by
    have ha : (tripleCharges (sourceA2275 + difference 0 2) (sourceB2275 + difference 2 0) sourceC2275) = raw31337 := by
      apply Matrix.ext; unfold tripleCharges sourceA2275 sourceB2275 sourceC2275 difference raw31337; decide +kernel
    rw [ha]
    exact (canonical31337 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2275 + difference 0 3) (sourceB2275 + difference 3 0) sourceC2275) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2697) := by
    have ha : (tripleCharges (sourceA2275 + difference 0 3) (sourceB2275 + difference 3 0) sourceC2275) = raw31338 := by
      apply Matrix.ext; unfold tripleCharges sourceA2275 sourceB2275 sourceC2275 difference raw31338; decide +kernel
    rw [ha]
    exact (canonical31338 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2275 + difference 0 4) (sourceB2275 + difference 4 0) sourceC2275) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2731) := by
    have ha : (tripleCharges (sourceA2275 + difference 0 4) (sourceB2275 + difference 4 0) sourceC2275) = raw31339 := by
      apply Matrix.ext; unfold tripleCharges sourceA2275 sourceB2275 sourceC2275 difference raw31339; decide +kernel
    rw [ha]
    exact (canonical31339 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2275 + difference 0 5) (sourceB2275 + difference 5 0) sourceC2275) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA2275 + difference 0 5) (sourceB2275 + difference 5 0) sourceC2275) = raw31340 := by
      apply Matrix.ext; unfold tripleCharges sourceA2275 sourceB2275 sourceC2275 difference raw31340; decide +kernel
    rw [ha]
    exact (canonical31340 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2275 + difference 1 0) (sourceB2275 + difference 0 1) sourceC2275) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1738) := by
    have ha : (tripleCharges (sourceA2275 + difference 1 0) (sourceB2275 + difference 0 1) sourceC2275) = raw31341 := by
      apply Matrix.ext; unfold tripleCharges sourceA2275 sourceB2275 sourceC2275 difference raw31341; decide +kernel
    rw [ha]
    exact (canonical31341 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2275 + difference 1 2) (sourceB2275 + difference 2 1) sourceC2275) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2276) := by
    have ha : (tripleCharges (sourceA2275 + difference 1 2) (sourceB2275 + difference 2 1) sourceC2275) = raw31342 := by
      apply Matrix.ext; unfold tripleCharges sourceA2275 sourceB2275 sourceC2275 difference raw31342; decide +kernel
    rw [ha]
    exact (canonical31342 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2275 + difference 1 3) (sourceB2275 + difference 3 1) sourceC2275) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2215) := by
    have ha : (tripleCharges (sourceA2275 + difference 1 3) (sourceB2275 + difference 3 1) sourceC2275) = raw31343 := by
      apply Matrix.ext; unfold tripleCharges sourceA2275 sourceB2275 sourceC2275 difference raw31343; decide +kernel
    rw [ha]
    exact (canonical31343 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2275 + difference 1 4) (sourceB2275 + difference 4 1) sourceC2275) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2278) := by
    have ha : (tripleCharges (sourceA2275 + difference 1 4) (sourceB2275 + difference 4 1) sourceC2275) = raw31344 := by
      apply Matrix.ext; unfold tripleCharges sourceA2275 sourceB2275 sourceC2275 difference raw31344; decide +kernel
    rw [ha]
    exact (canonical31344 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2275 + difference 1 5) (sourceB2275 + difference 5 1) sourceC2275) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2264) := by
    have ha : (tripleCharges (sourceA2275 + difference 1 5) (sourceB2275 + difference 5 1) sourceC2275) = raw31345 := by
      apply Matrix.ext; unfold tripleCharges sourceA2275 sourceB2275 sourceC2275 difference raw31345; decide +kernel
    rw [ha]
    exact (canonical31345 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2275 + difference 2 0) (sourceB2275 + difference 0 2) sourceC2275) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1681) := by
    have ha : (tripleCharges (sourceA2275 + difference 2 0) (sourceB2275 + difference 0 2) sourceC2275) = raw31346 := by
      apply Matrix.ext; unfold tripleCharges sourceA2275 sourceB2275 sourceC2275 difference raw31346; decide +kernel
    rw [ha]
    exact (canonical31346 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2275 + difference 2 1) (sourceB2275 + difference 1 2) sourceC2275) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2157) := by
    have ha : (tripleCharges (sourceA2275 + difference 2 1) (sourceB2275 + difference 1 2) sourceC2275) = raw31347 := by
      apply Matrix.ext; unfold tripleCharges sourceA2275 sourceB2275 sourceC2275 difference raw31347; decide +kernel
    rw [ha]
    exact (canonical31347 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2275 + difference 2 3) (sourceB2275 + difference 3 2) sourceC2275) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2177) := by
    have ha : (tripleCharges (sourceA2275 + difference 2 3) (sourceB2275 + difference 3 2) sourceC2275) = raw31348 := by
      apply Matrix.ext; unfold tripleCharges sourceA2275 sourceB2275 sourceC2275 difference raw31348; decide +kernel
    rw [ha]
    exact (canonical31348 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2275 + difference 2 4) (sourceB2275 + difference 4 2) sourceC2275) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2216) := by
    have ha : (tripleCharges (sourceA2275 + difference 2 4) (sourceB2275 + difference 4 2) sourceC2275) = raw31349 := by
      apply Matrix.ext; unfold tripleCharges sourceA2275 sourceB2275 sourceC2275 difference raw31349; decide +kernel
    rw [ha]
    exact (canonical31349 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2275 + difference 2 5) (sourceB2275 + difference 5 2) sourceC2275) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2205) := by
    have ha : (tripleCharges (sourceA2275 + difference 2 5) (sourceB2275 + difference 5 2) sourceC2275) = raw31350 := by
      apply Matrix.ext; unfold tripleCharges sourceA2275 sourceB2275 sourceC2275 difference raw31350; decide +kernel
    rw [ha]
    exact (canonical31350 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2275 + difference 3 0) (sourceB2275 + difference 0 3) sourceC2275) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1667) := by
    have ha : (tripleCharges (sourceA2275 + difference 3 0) (sourceB2275 + difference 0 3) sourceC2275) = raw31351 := by
      apply Matrix.ext; unfold tripleCharges sourceA2275 sourceB2275 sourceC2275 difference raw31351; decide +kernel
    rw [ha]
    exact (canonical31351 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2275 + difference 3 1) (sourceB2275 + difference 1 3) sourceC2275) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2144) := by
    have ha : (tripleCharges (sourceA2275 + difference 3 1) (sourceB2275 + difference 1 3) sourceC2275) = raw31352 := by
      apply Matrix.ext; unfold tripleCharges sourceA2275 sourceB2275 sourceC2275 difference raw31352; decide +kernel
    rw [ha]
    exact (canonical31352 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2275 + difference 3 2) (sourceB2275 + difference 2 3) sourceC2275) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2194) := by
    have ha : (tripleCharges (sourceA2275 + difference 3 2) (sourceB2275 + difference 2 3) sourceC2275) = raw31353 := by
      apply Matrix.ext; unfold tripleCharges sourceA2275 sourceB2275 sourceC2275 difference raw31353; decide +kernel
    rw [ha]
    exact (canonical31353 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2275 + difference 3 4) (sourceB2275 + difference 4 3) sourceC2275) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2195) := by
    have ha : (tripleCharges (sourceA2275 + difference 3 4) (sourceB2275 + difference 4 3) sourceC2275) = raw31354 := by
      apply Matrix.ext; unfold tripleCharges sourceA2275 sourceB2275 sourceC2275 difference raw31354; decide +kernel
    rw [ha]
    exact (canonical31354 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2275 + difference 3 5) (sourceB2275 + difference 5 3) sourceC2275) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2190) := by
    have ha : (tripleCharges (sourceA2275 + difference 3 5) (sourceB2275 + difference 5 3) sourceC2275) = raw31355 := by
      apply Matrix.ext; unfold tripleCharges sourceA2275 sourceB2275 sourceC2275 difference raw31355; decide +kernel
    rw [ha]
    exact (canonical31355 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2275 + difference 4 0) (sourceB2275 + difference 0 4) sourceC2275) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1679) := by
    have ha : (tripleCharges (sourceA2275 + difference 4 0) (sourceB2275 + difference 0 4) sourceC2275) = raw31356 := by
      apply Matrix.ext; unfold tripleCharges sourceA2275 sourceB2275 sourceC2275 difference raw31356; decide +kernel
    rw [ha]
    exact (canonical31356 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2275 + difference 4 1) (sourceB2275 + difference 1 4) sourceC2275) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2155) := by
    have ha : (tripleCharges (sourceA2275 + difference 4 1) (sourceB2275 + difference 1 4) sourceC2275) = raw31357 := by
      apply Matrix.ext; unfold tripleCharges sourceA2275 sourceB2275 sourceC2275 difference raw31357; decide +kernel
    rw [ha]
    exact (canonical31357 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2275 + difference 4 2) (sourceB2275 + difference 2 4) sourceC2275) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2212) := by
    have ha : (tripleCharges (sourceA2275 + difference 4 2) (sourceB2275 + difference 2 4) sourceC2275) = raw31358 := by
      apply Matrix.ext; unfold tripleCharges sourceA2275 sourceB2275 sourceC2275 difference raw31358; decide +kernel
    rw [ha]
    exact (canonical31358 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2275 + difference 4 3) (sourceB2275 + difference 3 4) sourceC2275) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2176) := by
    have ha : (tripleCharges (sourceA2275 + difference 4 3) (sourceB2275 + difference 3 4) sourceC2275) = raw31359 := by
      apply Matrix.ext; unfold tripleCharges sourceA2275 sourceB2275 sourceC2275 difference raw31359; decide +kernel
    rw [ha]
    exact (canonical31359 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2275 + difference 4 5) (sourceB2275 + difference 5 4) sourceC2275) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2203) := by
    have ha : (tripleCharges (sourceA2275 + difference 4 5) (sourceB2275 + difference 5 4) sourceC2275) = raw31360 := by
      apply Matrix.ext; unfold tripleCharges sourceA2275 sourceB2275 sourceC2275 difference raw31360; decide +kernel
    rw [ha]
    exact (canonical31360 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2275 + difference 5 0) (sourceB2275 + difference 0 5) sourceC2275) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1685) := by
    have ha : (tripleCharges (sourceA2275 + difference 5 0) (sourceB2275 + difference 0 5) sourceC2275) = raw31361 := by
      apply Matrix.ext; unfold tripleCharges sourceA2275 sourceB2275 sourceC2275 difference raw31361; decide +kernel
    rw [ha]
    exact (canonical31361 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2275 + difference 5 1) (sourceB2275 + difference 1 5) sourceC2275) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2161) := by
    have ha : (tripleCharges (sourceA2275 + difference 5 1) (sourceB2275 + difference 1 5) sourceC2275) = raw31362 := by
      apply Matrix.ext; unfold tripleCharges sourceA2275 sourceB2275 sourceC2275 difference raw31362; decide +kernel
    rw [ha]
    exact (canonical31362 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2275 + difference 5 2) (sourceB2275 + difference 2 5) sourceC2275) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2162) := by
    have ha : (tripleCharges (sourceA2275 + difference 5 2) (sourceB2275 + difference 2 5) sourceC2275) = raw31363 := by
      apply Matrix.ext; unfold tripleCharges sourceA2275 sourceB2275 sourceC2275 difference raw31363; decide +kernel
    rw [ha]
    exact (canonical31363 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2275 + difference 5 3) (sourceB2275 + difference 3 5) sourceC2275) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2160) := by
    have ha : (tripleCharges (sourceA2275 + difference 5 3) (sourceB2275 + difference 3 5) sourceC2275) = raw31364 := by
      apply Matrix.ext; unfold tripleCharges sourceA2275 sourceB2275 sourceC2275 difference raw31364; decide +kernel
    rw [ha]
    exact (canonical31364 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2275 + difference 5 4) (sourceB2275 + difference 4 5) sourceC2275) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2220) := by
    have ha : (tripleCharges (sourceA2275 + difference 5 4) (sourceB2275 + difference 4 5) sourceC2275) = raw31365 := by
      apply Matrix.ext; unfold tripleCharges sourceA2275 sourceB2275 sourceC2275 difference raw31365; decide +kernel
    rw [ha]
    exact (canonical31365 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2275 sourceB2275 sourceC2275
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2275, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2276 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2276 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC2276 : Charge := ![3, 0, -1, 0, -2, 0]
def sourceForm2276 : Integer.Sparse Master := [(Sum.inr 1791, 1), (Sum.inr 1795, 1), (Sum.inr 1797, 1), (Sum.inr 1814, 1), (Sum.inr 2028, 1), (Sum.inr 3379, 1), (Sum.inr 4084, -1)]

theorem sourceEq2276 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2276 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2276 + difference 0 1) (sourceB2276 + difference 1 0) sourceC2276) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3379) := by
    have ha : (tripleCharges (sourceA2276 + difference 0 1) (sourceB2276 + difference 1 0) sourceC2276) = raw31366 := by
      apply Matrix.ext; unfold tripleCharges sourceA2276 sourceB2276 sourceC2276 difference raw31366; decide +kernel
    rw [ha]
    exact (canonical31366 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2276 + difference 1 1) (sourceB2276 + difference 1 1) sourceC2276) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2028) := by
    have ha : (tripleCharges (sourceA2276 + difference 1 1) (sourceB2276 + difference 1 1) sourceC2276) = raw31367 := by
      apply Matrix.ext; unfold tripleCharges sourceA2276 sourceB2276 sourceC2276 difference raw31367; decide +kernel
    rw [ha]
    exact (canonical31367 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2276 + difference 2 1) (sourceB2276 + difference 1 2) sourceC2276) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1814) := by
    have ha : (tripleCharges (sourceA2276 + difference 2 1) (sourceB2276 + difference 1 2) sourceC2276) = raw31368 := by
      apply Matrix.ext; unfold tripleCharges sourceA2276 sourceB2276 sourceC2276 difference raw31368; decide +kernel
    rw [ha]
    exact (canonical31368 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2276 + difference 3 1) (sourceB2276 + difference 1 3) sourceC2276) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1791) := by
    have ha : (tripleCharges (sourceA2276 + difference 3 1) (sourceB2276 + difference 1 3) sourceC2276) = raw31369 := by
      apply Matrix.ext; unfold tripleCharges sourceA2276 sourceB2276 sourceC2276 difference raw31369; decide +kernel
    rw [ha]
    exact (canonical31369 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2276 + difference 4 1) (sourceB2276 + difference 1 4) sourceC2276) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1795) := by
    have ha : (tripleCharges (sourceA2276 + difference 4 1) (sourceB2276 + difference 1 4) sourceC2276) = raw31370 := by
      apply Matrix.ext; unfold tripleCharges sourceA2276 sourceB2276 sourceC2276 difference raw31370; decide +kernel
    rw [ha]
    exact (canonical31370 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2276 + difference 5 1) (sourceB2276 + difference 1 5) sourceC2276) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1797) := by
    have ha : (tripleCharges (sourceA2276 + difference 5 1) (sourceB2276 + difference 1 5) sourceC2276) = raw31371 := by
      apply Matrix.ext; unfold tripleCharges sourceA2276 sourceB2276 sourceC2276 difference raw31371; decide +kernel
    rw [ha]
    exact (canonical31371 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2276 + sourceB2276) sourceC2276) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA2276 + sourceB2276) sourceC2276) = raw23810 := by
      apply Matrix.ext; unfold doubleCharges sourceA2276 sourceB2276 sourceC2276 raw23810; decide +kernel
    rw [ha]
    exact (canonical23810 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2276 sourceB2276 sourceC2276
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2276, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2277 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2277 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC2277 : Charge := ![3, 0, -1, 0, -2, 0]
def sourceForm2277 : Integer.Sparse Master := [(Sum.inr 932, 1), (Sum.inr 1814, 1), (Sum.inr 1966, 1), (Sum.inr 2028, 1), (Sum.inr 2053, 1), (Sum.inr 2058, 1), (Sum.inr 4084, -1)]

theorem sourceEq2277 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2277 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2277 + difference 2 0) (sourceB2277 + difference 0 2) sourceC2277) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 932) := by
    have ha : (tripleCharges (sourceA2277 + difference 2 0) (sourceB2277 + difference 0 2) sourceC2277) = raw31372 := by
      apply Matrix.ext; unfold tripleCharges sourceA2277 sourceB2277 sourceC2277 difference raw31372; decide +kernel
    rw [ha]
    exact (canonical31372 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2277 + difference 2 1) (sourceB2277 + difference 1 2) sourceC2277) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1814) := by
    have ha : (tripleCharges (sourceA2277 + difference 2 1) (sourceB2277 + difference 1 2) sourceC2277) = raw31368 := by
      apply Matrix.ext; unfold tripleCharges sourceA2277 sourceB2277 sourceC2277 difference raw31368; decide +kernel
    rw [ha]
    exact (canonical31368 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2277 + difference 2 2) (sourceB2277 + difference 2 2) sourceC2277) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2028) := by
    have ha : (tripleCharges (sourceA2277 + difference 2 2) (sourceB2277 + difference 2 2) sourceC2277) = raw31367 := by
      apply Matrix.ext; unfold tripleCharges sourceA2277 sourceB2277 sourceC2277 difference raw31367; decide +kernel
    rw [ha]
    exact (canonical31367 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2277 + difference 2 3) (sourceB2277 + difference 3 2) sourceC2277) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1966) := by
    have ha : (tripleCharges (sourceA2277 + difference 2 3) (sourceB2277 + difference 3 2) sourceC2277) = raw31373 := by
      apply Matrix.ext; unfold tripleCharges sourceA2277 sourceB2277 sourceC2277 difference raw31373; decide +kernel
    rw [ha]
    exact (canonical31373 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2277 + difference 2 4) (sourceB2277 + difference 4 2) sourceC2277) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2058) := by
    have ha : (tripleCharges (sourceA2277 + difference 2 4) (sourceB2277 + difference 4 2) sourceC2277) = raw31374 := by
      apply Matrix.ext; unfold tripleCharges sourceA2277 sourceB2277 sourceC2277 difference raw31374; decide +kernel
    rw [ha]
    exact (canonical31374 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2277 + difference 2 5) (sourceB2277 + difference 5 2) sourceC2277) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2053) := by
    have ha : (tripleCharges (sourceA2277 + difference 2 5) (sourceB2277 + difference 5 2) sourceC2277) = raw31375 := by
      apply Matrix.ext; unfold tripleCharges sourceA2277 sourceB2277 sourceC2277 difference raw31375; decide +kernel
    rw [ha]
    exact (canonical31375 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2277 + sourceB2277) sourceC2277) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA2277 + sourceB2277) sourceC2277) = raw23810 := by
      apply Matrix.ext; unfold doubleCharges sourceA2277 sourceB2277 sourceC2277 raw23810; decide +kernel
    rw [ha]
    exact (canonical23810 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2277 sourceB2277 sourceC2277
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2277, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2278 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2278 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC2278 : Charge := ![3, 0, -1, 0, -2, 0]
def sourceForm2278 : Integer.Sparse Master := [(Sum.inr 906, 1), (Sum.inr 1791, 1), (Sum.inr 1974, 1), (Sum.inr 2019, 1), (Sum.inr 2021, 1), (Sum.inr 2028, 1), (Sum.inr 4084, -1)]

theorem sourceEq2278 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2278 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2278 + difference 3 0) (sourceB2278 + difference 0 3) sourceC2278) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 906) := by
    have ha : (tripleCharges (sourceA2278 + difference 3 0) (sourceB2278 + difference 0 3) sourceC2278) = raw31376 := by
      apply Matrix.ext; unfold tripleCharges sourceA2278 sourceB2278 sourceC2278 difference raw31376; decide +kernel
    rw [ha]
    exact (canonical31376 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2278 + difference 3 1) (sourceB2278 + difference 1 3) sourceC2278) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1791) := by
    have ha : (tripleCharges (sourceA2278 + difference 3 1) (sourceB2278 + difference 1 3) sourceC2278) = raw31369 := by
      apply Matrix.ext; unfold tripleCharges sourceA2278 sourceB2278 sourceC2278 difference raw31369; decide +kernel
    rw [ha]
    exact (canonical31369 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2278 + difference 3 2) (sourceB2278 + difference 2 3) sourceC2278) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1974) := by
    have ha : (tripleCharges (sourceA2278 + difference 3 2) (sourceB2278 + difference 2 3) sourceC2278) = raw31377 := by
      apply Matrix.ext; unfold tripleCharges sourceA2278 sourceB2278 sourceC2278 difference raw31377; decide +kernel
    rw [ha]
    exact (canonical31377 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2278 + difference 3 3) (sourceB2278 + difference 3 3) sourceC2278) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2028) := by
    have ha : (tripleCharges (sourceA2278 + difference 3 3) (sourceB2278 + difference 3 3) sourceC2278) = raw31367 := by
      apply Matrix.ext; unfold tripleCharges sourceA2278 sourceB2278 sourceC2278 difference raw31367; decide +kernel
    rw [ha]
    exact (canonical31367 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2278 + difference 3 4) (sourceB2278 + difference 4 3) sourceC2278) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2021) := by
    have ha : (tripleCharges (sourceA2278 + difference 3 4) (sourceB2278 + difference 4 3) sourceC2278) = raw31378 := by
      apply Matrix.ext; unfold tripleCharges sourceA2278 sourceB2278 sourceC2278 difference raw31378; decide +kernel
    rw [ha]
    exact (canonical31378 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2278 + difference 3 5) (sourceB2278 + difference 5 3) sourceC2278) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2019) := by
    have ha : (tripleCharges (sourceA2278 + difference 3 5) (sourceB2278 + difference 5 3) sourceC2278) = raw31379 := by
      apply Matrix.ext; unfold tripleCharges sourceA2278 sourceB2278 sourceC2278 difference raw31379; decide +kernel
    rw [ha]
    exact (canonical31379 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2278 + sourceB2278) sourceC2278) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA2278 + sourceB2278) sourceC2278) = raw23810 := by
      apply Matrix.ext; unfold doubleCharges sourceA2278 sourceB2278 sourceC2278 raw23810; decide +kernel
    rw [ha]
    exact (canonical23810 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2278 sourceB2278 sourceC2278
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2278, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2279 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2279 : Charge := ![3, 0, -1, 0, -2, 0]
def sourceC2279 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceForm2279 : Integer.Sparse Master := [(Sum.inr 4200, 1), (Sum.inr 4203, 1), (Sum.inr 4205, 1), (Sum.inr 4223, 1), (Sum.inr 4255, 1), (Sum.inr 4634, 1), (Sum.inr 4636, 1), (Sum.inr 4638, 1), (Sum.inr 4653, 1), (Sum.inr 4658, 1), (Sum.inr 4678, 1), (Sum.inr 4707, 1), (Sum.inr 4716, 1), (Sum.inr 4731, 1), (Sum.inr 4766, 1), (Sum.inr 4770, 1), (Sum.inr 4798, 1), (Sum.inr 4800, 1), (Sum.inr 4805, 1), (Sum.inr 4807, 1), (Sum.inr 4810, 1), (Sum.inr 4828, 1), (Sum.inr 4839, 1), (Sum.inr 4865, 1), (Sum.inr 4889, 1), (Sum.inr 5355, 1), (Sum.inr 5378, 1), (Sum.inr 5387, 1), (Sum.inr 5432, 1), (Sum.inr 5435, 1)]

theorem sourceEq2279 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2279 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2279 + difference 0 1) (sourceB2279 + difference 1 0) sourceC2279) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5355) := by
    have ha : (tripleCharges (sourceA2279 + difference 0 1) (sourceB2279 + difference 1 0) sourceC2279) = raw31380 := by
      apply Matrix.ext; unfold tripleCharges sourceA2279 sourceB2279 sourceC2279 difference raw31380; decide +kernel
    rw [ha]
    exact (canonical31380 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2279 + difference 0 2) (sourceB2279 + difference 2 0) sourceC2279) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5387) := by
    have ha : (tripleCharges (sourceA2279 + difference 0 2) (sourceB2279 + difference 2 0) sourceC2279) = raw31381 := by
      apply Matrix.ext; unfold tripleCharges sourceA2279 sourceB2279 sourceC2279 difference raw31381; decide +kernel
    rw [ha]
    exact (canonical31381 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2279 + difference 0 3) (sourceB2279 + difference 3 0) sourceC2279) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA2279 + difference 0 3) (sourceB2279 + difference 3 0) sourceC2279) = raw31382 := by
      apply Matrix.ext; unfold tripleCharges sourceA2279 sourceB2279 sourceC2279 difference raw31382; decide +kernel
    rw [ha]
    exact (canonical31382 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2279 + difference 0 4) (sourceB2279 + difference 4 0) sourceC2279) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA2279 + difference 0 4) (sourceB2279 + difference 4 0) sourceC2279) = raw11102 := by
      apply Matrix.ext; unfold tripleCharges sourceA2279 sourceB2279 sourceC2279 difference raw11102; decide +kernel
    rw [ha]
    exact (canonical11102 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2279 + difference 0 5) (sourceB2279 + difference 5 0) sourceC2279) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5432) := by
    have ha : (tripleCharges (sourceA2279 + difference 0 5) (sourceB2279 + difference 5 0) sourceC2279) = raw31383 := by
      apply Matrix.ext; unfold tripleCharges sourceA2279 sourceB2279 sourceC2279 difference raw31383; decide +kernel
    rw [ha]
    exact (canonical31383 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2279 + difference 1 0) (sourceB2279 + difference 0 1) sourceC2279) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4255) := by
    have ha : (tripleCharges (sourceA2279 + difference 1 0) (sourceB2279 + difference 0 1) sourceC2279) = raw11122 := by
      apply Matrix.ext; unfold tripleCharges sourceA2279 sourceB2279 sourceC2279 difference raw11122; decide +kernel
    rw [ha]
    exact (canonical11122 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2279 + difference 1 2) (sourceB2279 + difference 2 1) sourceC2279) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4810) := by
    have ha : (tripleCharges (sourceA2279 + difference 1 2) (sourceB2279 + difference 2 1) sourceC2279) = raw11124 := by
      apply Matrix.ext; unfold tripleCharges sourceA2279 sourceB2279 sourceC2279 difference raw11124; decide +kernel
    rw [ha]
    exact (canonical11124 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2279 + difference 1 3) (sourceB2279 + difference 3 1) sourceC2279) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4731) := by
    have ha : (tripleCharges (sourceA2279 + difference 1 3) (sourceB2279 + difference 3 1) sourceC2279) = raw11125 := by
      apply Matrix.ext; unfold tripleCharges sourceA2279 sourceB2279 sourceC2279 difference raw11125; decide +kernel
    rw [ha]
    exact (canonical11125 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2279 + difference 1 4) (sourceB2279 + difference 4 1) sourceC2279) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA2279 + difference 1 4) (sourceB2279 + difference 4 1) sourceC2279) = raw31384 := by
      apply Matrix.ext; unfold tripleCharges sourceA2279 sourceB2279 sourceC2279 difference raw31384; decide +kernel
    rw [ha]
    exact (canonical31384 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2279 + difference 1 5) (sourceB2279 + difference 5 1) sourceC2279) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4865) := by
    have ha : (tripleCharges (sourceA2279 + difference 1 5) (sourceB2279 + difference 5 1) sourceC2279) = raw11126 := by
      apply Matrix.ext; unfold tripleCharges sourceA2279 sourceB2279 sourceC2279 difference raw11126; decide +kernel
    rw [ha]
    exact (canonical11126 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2279 + difference 2 0) (sourceB2279 + difference 0 2) sourceC2279) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4223) := by
    have ha : (tripleCharges (sourceA2279 + difference 2 0) (sourceB2279 + difference 0 2) sourceC2279) = raw31385 := by
      apply Matrix.ext; unfold tripleCharges sourceA2279 sourceB2279 sourceC2279 difference raw31385; decide +kernel
    rw [ha]
    exact (canonical31385 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2279 + difference 2 1) (sourceB2279 + difference 1 2) sourceC2279) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4653) := by
    have ha : (tripleCharges (sourceA2279 + difference 2 1) (sourceB2279 + difference 1 2) sourceC2279) = raw31386 := by
      apply Matrix.ext; unfold tripleCharges sourceA2279 sourceB2279 sourceC2279 difference raw31386; decide +kernel
    rw [ha]
    exact (canonical31386 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2279 + difference 2 3) (sourceB2279 + difference 3 2) sourceC2279) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4716) := by
    have ha : (tripleCharges (sourceA2279 + difference 2 3) (sourceB2279 + difference 3 2) sourceC2279) = raw31387 := by
      apply Matrix.ext; unfold tripleCharges sourceA2279 sourceB2279 sourceC2279 difference raw31387; decide +kernel
    rw [ha]
    exact (canonical31387 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2279 + difference 2 4) (sourceB2279 + difference 4 2) sourceC2279) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4839) := by
    have ha : (tripleCharges (sourceA2279 + difference 2 4) (sourceB2279 + difference 4 2) sourceC2279) = raw11113 := by
      apply Matrix.ext; unfold tripleCharges sourceA2279 sourceB2279 sourceC2279 difference raw11113; decide +kernel
    rw [ha]
    exact (canonical11113 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2279 + difference 2 5) (sourceB2279 + difference 5 2) sourceC2279) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4828) := by
    have ha : (tripleCharges (sourceA2279 + difference 2 5) (sourceB2279 + difference 5 2) sourceC2279) = raw31388 := by
      apply Matrix.ext; unfold tripleCharges sourceA2279 sourceB2279 sourceC2279 difference raw31388; decide +kernel
    rw [ha]
    exact (canonical31388 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2279 + difference 3 0) (sourceB2279 + difference 0 3) sourceC2279) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4200) := by
    have ha : (tripleCharges (sourceA2279 + difference 3 0) (sourceB2279 + difference 0 3) sourceC2279) = raw31389 := by
      apply Matrix.ext; unfold tripleCharges sourceA2279 sourceB2279 sourceC2279 difference raw31389; decide +kernel
    rw [ha]
    exact (canonical31389 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2279 + difference 3 1) (sourceB2279 + difference 1 3) sourceC2279) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4634) := by
    have ha : (tripleCharges (sourceA2279 + difference 3 1) (sourceB2279 + difference 1 3) sourceC2279) = raw31390 := by
      apply Matrix.ext; unfold tripleCharges sourceA2279 sourceB2279 sourceC2279 difference raw31390; decide +kernel
    rw [ha]
    exact (canonical31390 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2279 + difference 3 2) (sourceB2279 + difference 2 3) sourceC2279) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4766) := by
    have ha : (tripleCharges (sourceA2279 + difference 3 2) (sourceB2279 + difference 2 3) sourceC2279) = raw31391 := by
      apply Matrix.ext; unfold tripleCharges sourceA2279 sourceB2279 sourceC2279 difference raw31391; decide +kernel
    rw [ha]
    exact (canonical31391 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2279 + difference 3 4) (sourceB2279 + difference 4 3) sourceC2279) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4805) := by
    have ha : (tripleCharges (sourceA2279 + difference 3 4) (sourceB2279 + difference 4 3) sourceC2279) = raw11118 := by
      apply Matrix.ext; unfold tripleCharges sourceA2279 sourceB2279 sourceC2279 difference raw11118; decide +kernel
    rw [ha]
    exact (canonical11118 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2279 + difference 3 5) (sourceB2279 + difference 5 3) sourceC2279) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4798) := by
    have ha : (tripleCharges (sourceA2279 + difference 3 5) (sourceB2279 + difference 5 3) sourceC2279) = raw31392 := by
      apply Matrix.ext; unfold tripleCharges sourceA2279 sourceB2279 sourceC2279 difference raw31392; decide +kernel
    rw [ha]
    exact (canonical31392 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2279 + difference 4 0) (sourceB2279 + difference 0 4) sourceC2279) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4203) := by
    have ha : (tripleCharges (sourceA2279 + difference 4 0) (sourceB2279 + difference 0 4) sourceC2279) = raw31393 := by
      apply Matrix.ext; unfold tripleCharges sourceA2279 sourceB2279 sourceC2279 difference raw31393; decide +kernel
    rw [ha]
    exact (canonical31393 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2279 + difference 4 1) (sourceB2279 + difference 1 4) sourceC2279) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4636) := by
    have ha : (tripleCharges (sourceA2279 + difference 4 1) (sourceB2279 + difference 1 4) sourceC2279) = raw31394 := by
      apply Matrix.ext; unfold tripleCharges sourceA2279 sourceB2279 sourceC2279 difference raw31394; decide +kernel
    rw [ha]
    exact (canonical31394 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2279 + difference 4 2) (sourceB2279 + difference 2 4) sourceC2279) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4678) := by
    have ha : (tripleCharges (sourceA2279 + difference 4 2) (sourceB2279 + difference 2 4) sourceC2279) = raw31395 := by
      apply Matrix.ext; unfold tripleCharges sourceA2279 sourceB2279 sourceC2279 difference raw31395; decide +kernel
    rw [ha]
    exact (canonical31395 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2279 + difference 4 3) (sourceB2279 + difference 3 4) sourceC2279) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4658) := by
    have ha : (tripleCharges (sourceA2279 + difference 4 3) (sourceB2279 + difference 3 4) sourceC2279) = raw31396 := by
      apply Matrix.ext; unfold tripleCharges sourceA2279 sourceB2279 sourceC2279 difference raw31396; decide +kernel
    rw [ha]
    exact (canonical31396 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2279 + difference 4 5) (sourceB2279 + difference 5 4) sourceC2279) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4800) := by
    have ha : (tripleCharges (sourceA2279 + difference 4 5) (sourceB2279 + difference 5 4) sourceC2279) = raw31397 := by
      apply Matrix.ext; unfold tripleCharges sourceA2279 sourceB2279 sourceC2279 difference raw31397; decide +kernel
    rw [ha]
    exact (canonical31397 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2279 + difference 5 0) (sourceB2279 + difference 0 5) sourceC2279) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4205) := by
    have ha : (tripleCharges (sourceA2279 + difference 5 0) (sourceB2279 + difference 0 5) sourceC2279) = raw31398 := by
      apply Matrix.ext; unfold tripleCharges sourceA2279 sourceB2279 sourceC2279 difference raw31398; decide +kernel
    rw [ha]
    exact (canonical31398 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2279 + difference 5 1) (sourceB2279 + difference 1 5) sourceC2279) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4638) := by
    have ha : (tripleCharges (sourceA2279 + difference 5 1) (sourceB2279 + difference 1 5) sourceC2279) = raw31399 := by
      apply Matrix.ext; unfold tripleCharges sourceA2279 sourceB2279 sourceC2279 difference raw31399; decide +kernel
    rw [ha]
    exact (canonical31399 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2279 + difference 5 2) (sourceB2279 + difference 2 5) sourceC2279) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4770) := by
    have ha : (tripleCharges (sourceA2279 + difference 5 2) (sourceB2279 + difference 2 5) sourceC2279) = raw31400 := by
      apply Matrix.ext; unfold tripleCharges sourceA2279 sourceB2279 sourceC2279 difference raw31400; decide +kernel
    rw [ha]
    exact (canonical31400 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2279 + difference 5 3) (sourceB2279 + difference 3 5) sourceC2279) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4707) := by
    have ha : (tripleCharges (sourceA2279 + difference 5 3) (sourceB2279 + difference 3 5) sourceC2279) = raw31401 := by
      apply Matrix.ext; unfold tripleCharges sourceA2279 sourceB2279 sourceC2279 difference raw31401; decide +kernel
    rw [ha]
    exact (canonical31401 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2279 + difference 5 4) (sourceB2279 + difference 4 5) sourceC2279) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA2279 + difference 5 4) (sourceB2279 + difference 4 5) sourceC2279) = raw11128 := by
      apply Matrix.ext; unfold tripleCharges sourceA2279 sourceB2279 sourceC2279 difference raw11128; decide +kernel
    rw [ha]
    exact (canonical11128 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2279 sourceB2279 sourceC2279
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2279, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2280 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2280 : Charge := ![3, 0, -1, 0, -2, 0]
def sourceC2280 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceForm2280 : Integer.Sparse Master := [(Sum.inr 703, 1), (Sum.inr 706, 1), (Sum.inr 708, 1), (Sum.inr 724, 1), (Sum.inr 789, 1), (Sum.inr 1763, 1), (Sum.inr 1765, 1), (Sum.inr 1767, 1), (Sum.inr 1781, 1), (Sum.inr 1784, 1), (Sum.inr 1804, 1), (Sum.inr 1861, 1), (Sum.inr 1870, 1), (Sum.inr 1900, 1), (Sum.inr 1966, 1), (Sum.inr 1970, 1), (Sum.inr 2016, 1), (Sum.inr 2018, 1), (Sum.inr 2023, 1), (Sum.inr 2025, 1), (Sum.inr 2028, 1), (Sum.inr 2048, 1), (Sum.inr 2058, 1), (Sum.inr 2242, 1), (Sum.inr 2245, 1), (Sum.inr 3693, 1), (Sum.inr 3719, 1), (Sum.inr 3736, 1), (Sum.inr 3850, 1), (Sum.inr 3853, 1)]

theorem sourceEq2280 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2280 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2280 + difference 0 1) (sourceB2280 + difference 1 0) sourceC2280) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3693) := by
    have ha : (tripleCharges (sourceA2280 + difference 0 1) (sourceB2280 + difference 1 0) sourceC2280) = raw31402 := by
      apply Matrix.ext; unfold tripleCharges sourceA2280 sourceB2280 sourceC2280 difference raw31402; decide +kernel
    rw [ha]
    exact (canonical31402 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2280 + difference 0 2) (sourceB2280 + difference 2 0) sourceC2280) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3736) := by
    have ha : (tripleCharges (sourceA2280 + difference 0 2) (sourceB2280 + difference 2 0) sourceC2280) = raw31403 := by
      apply Matrix.ext; unfold tripleCharges sourceA2280 sourceB2280 sourceC2280 difference raw31403; decide +kernel
    rw [ha]
    exact (canonical31403 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2280 + difference 0 3) (sourceB2280 + difference 3 0) sourceC2280) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3719) := by
    have ha : (tripleCharges (sourceA2280 + difference 0 3) (sourceB2280 + difference 3 0) sourceC2280) = raw31404 := by
      apply Matrix.ext; unfold tripleCharges sourceA2280 sourceB2280 sourceC2280 difference raw31404; decide +kernel
    rw [ha]
    exact (canonical31404 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2280 + difference 0 4) (sourceB2280 + difference 4 0) sourceC2280) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3853) := by
    have ha : (tripleCharges (sourceA2280 + difference 0 4) (sourceB2280 + difference 4 0) sourceC2280) = raw11132 := by
      apply Matrix.ext; unfold tripleCharges sourceA2280 sourceB2280 sourceC2280 difference raw11132; decide +kernel
    rw [ha]
    exact (canonical11132 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2280 + difference 0 5) (sourceB2280 + difference 5 0) sourceC2280) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3850) := by
    have ha : (tripleCharges (sourceA2280 + difference 0 5) (sourceB2280 + difference 5 0) sourceC2280) = raw31405 := by
      apply Matrix.ext; unfold tripleCharges sourceA2280 sourceB2280 sourceC2280 difference raw31405; decide +kernel
    rw [ha]
    exact (canonical31405 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2280 + difference 1 0) (sourceB2280 + difference 0 1) sourceC2280) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 789) := by
    have ha : (tripleCharges (sourceA2280 + difference 1 0) (sourceB2280 + difference 0 1) sourceC2280) = raw11152 := by
      apply Matrix.ext; unfold tripleCharges sourceA2280 sourceB2280 sourceC2280 difference raw11152; decide +kernel
    rw [ha]
    exact (canonical11152 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2280 + difference 1 2) (sourceB2280 + difference 2 1) sourceC2280) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2028) := by
    have ha : (tripleCharges (sourceA2280 + difference 1 2) (sourceB2280 + difference 2 1) sourceC2280) = raw11154 := by
      apply Matrix.ext; unfold tripleCharges sourceA2280 sourceB2280 sourceC2280 difference raw11154; decide +kernel
    rw [ha]
    exact (canonical11154 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2280 + difference 1 3) (sourceB2280 + difference 3 1) sourceC2280) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1900) := by
    have ha : (tripleCharges (sourceA2280 + difference 1 3) (sourceB2280 + difference 3 1) sourceC2280) = raw11155 := by
      apply Matrix.ext; unfold tripleCharges sourceA2280 sourceB2280 sourceC2280 difference raw11155; decide +kernel
    rw [ha]
    exact (canonical11155 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2280 + difference 1 4) (sourceB2280 + difference 4 1) sourceC2280) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2245) := by
    have ha : (tripleCharges (sourceA2280 + difference 1 4) (sourceB2280 + difference 4 1) sourceC2280) = raw31406 := by
      apply Matrix.ext; unfold tripleCharges sourceA2280 sourceB2280 sourceC2280 difference raw31406; decide +kernel
    rw [ha]
    exact (canonical31406 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2280 + difference 1 5) (sourceB2280 + difference 5 1) sourceC2280) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2242) := by
    have ha : (tripleCharges (sourceA2280 + difference 1 5) (sourceB2280 + difference 5 1) sourceC2280) = raw11156 := by
      apply Matrix.ext; unfold tripleCharges sourceA2280 sourceB2280 sourceC2280 difference raw11156; decide +kernel
    rw [ha]
    exact (canonical11156 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2280 + difference 2 0) (sourceB2280 + difference 0 2) sourceC2280) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 724) := by
    have ha : (tripleCharges (sourceA2280 + difference 2 0) (sourceB2280 + difference 0 2) sourceC2280) = raw31407 := by
      apply Matrix.ext; unfold tripleCharges sourceA2280 sourceB2280 sourceC2280 difference raw31407; decide +kernel
    rw [ha]
    exact (canonical31407 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2280 + difference 2 1) (sourceB2280 + difference 1 2) sourceC2280) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1781) := by
    have ha : (tripleCharges (sourceA2280 + difference 2 1) (sourceB2280 + difference 1 2) sourceC2280) = raw31408 := by
      apply Matrix.ext; unfold tripleCharges sourceA2280 sourceB2280 sourceC2280 difference raw31408; decide +kernel
    rw [ha]
    exact (canonical31408 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2280 + difference 2 3) (sourceB2280 + difference 3 2) sourceC2280) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1870) := by
    have ha : (tripleCharges (sourceA2280 + difference 2 3) (sourceB2280 + difference 3 2) sourceC2280) = raw31409 := by
      apply Matrix.ext; unfold tripleCharges sourceA2280 sourceB2280 sourceC2280 difference raw31409; decide +kernel
    rw [ha]
    exact (canonical31409 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2280 + difference 2 4) (sourceB2280 + difference 4 2) sourceC2280) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2058) := by
    have ha : (tripleCharges (sourceA2280 + difference 2 4) (sourceB2280 + difference 4 2) sourceC2280) = raw11143 := by
      apply Matrix.ext; unfold tripleCharges sourceA2280 sourceB2280 sourceC2280 difference raw11143; decide +kernel
    rw [ha]
    exact (canonical11143 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2280 + difference 2 5) (sourceB2280 + difference 5 2) sourceC2280) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2048) := by
    have ha : (tripleCharges (sourceA2280 + difference 2 5) (sourceB2280 + difference 5 2) sourceC2280) = raw31410 := by
      apply Matrix.ext; unfold tripleCharges sourceA2280 sourceB2280 sourceC2280 difference raw31410; decide +kernel
    rw [ha]
    exact (canonical31410 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2280 + difference 3 0) (sourceB2280 + difference 0 3) sourceC2280) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 703) := by
    have ha : (tripleCharges (sourceA2280 + difference 3 0) (sourceB2280 + difference 0 3) sourceC2280) = raw31411 := by
      apply Matrix.ext; unfold tripleCharges sourceA2280 sourceB2280 sourceC2280 difference raw31411; decide +kernel
    rw [ha]
    exact (canonical31411 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2280 + difference 3 1) (sourceB2280 + difference 1 3) sourceC2280) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1763) := by
    have ha : (tripleCharges (sourceA2280 + difference 3 1) (sourceB2280 + difference 1 3) sourceC2280) = raw31412 := by
      apply Matrix.ext; unfold tripleCharges sourceA2280 sourceB2280 sourceC2280 difference raw31412; decide +kernel
    rw [ha]
    exact (canonical31412 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2280 + difference 3 2) (sourceB2280 + difference 2 3) sourceC2280) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1966) := by
    have ha : (tripleCharges (sourceA2280 + difference 3 2) (sourceB2280 + difference 2 3) sourceC2280) = raw31413 := by
      apply Matrix.ext; unfold tripleCharges sourceA2280 sourceB2280 sourceC2280 difference raw31413; decide +kernel
    rw [ha]
    exact (canonical31413 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2280 + difference 3 4) (sourceB2280 + difference 4 3) sourceC2280) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2023) := by
    have ha : (tripleCharges (sourceA2280 + difference 3 4) (sourceB2280 + difference 4 3) sourceC2280) = raw11148 := by
      apply Matrix.ext; unfold tripleCharges sourceA2280 sourceB2280 sourceC2280 difference raw11148; decide +kernel
    rw [ha]
    exact (canonical11148 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2280 + difference 3 5) (sourceB2280 + difference 5 3) sourceC2280) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2016) := by
    have ha : (tripleCharges (sourceA2280 + difference 3 5) (sourceB2280 + difference 5 3) sourceC2280) = raw31414 := by
      apply Matrix.ext; unfold tripleCharges sourceA2280 sourceB2280 sourceC2280 difference raw31414; decide +kernel
    rw [ha]
    exact (canonical31414 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2280 + difference 4 0) (sourceB2280 + difference 0 4) sourceC2280) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 706) := by
    have ha : (tripleCharges (sourceA2280 + difference 4 0) (sourceB2280 + difference 0 4) sourceC2280) = raw31415 := by
      apply Matrix.ext; unfold tripleCharges sourceA2280 sourceB2280 sourceC2280 difference raw31415; decide +kernel
    rw [ha]
    exact (canonical31415 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2280 + difference 4 1) (sourceB2280 + difference 1 4) sourceC2280) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1765) := by
    have ha : (tripleCharges (sourceA2280 + difference 4 1) (sourceB2280 + difference 1 4) sourceC2280) = raw31416 := by
      apply Matrix.ext; unfold tripleCharges sourceA2280 sourceB2280 sourceC2280 difference raw31416; decide +kernel
    rw [ha]
    exact (canonical31416 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2280 + difference 4 2) (sourceB2280 + difference 2 4) sourceC2280) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1804) := by
    have ha : (tripleCharges (sourceA2280 + difference 4 2) (sourceB2280 + difference 2 4) sourceC2280) = raw31417 := by
      apply Matrix.ext; unfold tripleCharges sourceA2280 sourceB2280 sourceC2280 difference raw31417; decide +kernel
    rw [ha]
    exact (canonical31417 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2280 + difference 4 3) (sourceB2280 + difference 3 4) sourceC2280) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1784) := by
    have ha : (tripleCharges (sourceA2280 + difference 4 3) (sourceB2280 + difference 3 4) sourceC2280) = raw31418 := by
      apply Matrix.ext; unfold tripleCharges sourceA2280 sourceB2280 sourceC2280 difference raw31418; decide +kernel
    rw [ha]
    exact (canonical31418 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2280 + difference 4 5) (sourceB2280 + difference 5 4) sourceC2280) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2018) := by
    have ha : (tripleCharges (sourceA2280 + difference 4 5) (sourceB2280 + difference 5 4) sourceC2280) = raw31419 := by
      apply Matrix.ext; unfold tripleCharges sourceA2280 sourceB2280 sourceC2280 difference raw31419; decide +kernel
    rw [ha]
    exact (canonical31419 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2280 + difference 5 0) (sourceB2280 + difference 0 5) sourceC2280) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 708) := by
    have ha : (tripleCharges (sourceA2280 + difference 5 0) (sourceB2280 + difference 0 5) sourceC2280) = raw31420 := by
      apply Matrix.ext; unfold tripleCharges sourceA2280 sourceB2280 sourceC2280 difference raw31420; decide +kernel
    rw [ha]
    exact (canonical31420 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2280 + difference 5 1) (sourceB2280 + difference 1 5) sourceC2280) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1767) := by
    have ha : (tripleCharges (sourceA2280 + difference 5 1) (sourceB2280 + difference 1 5) sourceC2280) = raw31421 := by
      apply Matrix.ext; unfold tripleCharges sourceA2280 sourceB2280 sourceC2280 difference raw31421; decide +kernel
    rw [ha]
    exact (canonical31421 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2280 + difference 5 2) (sourceB2280 + difference 2 5) sourceC2280) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1970) := by
    have ha : (tripleCharges (sourceA2280 + difference 5 2) (sourceB2280 + difference 2 5) sourceC2280) = raw31422 := by
      apply Matrix.ext; unfold tripleCharges sourceA2280 sourceB2280 sourceC2280 difference raw31422; decide +kernel
    rw [ha]
    exact (canonical31422 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2280 + difference 5 3) (sourceB2280 + difference 3 5) sourceC2280) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1861) := by
    have ha : (tripleCharges (sourceA2280 + difference 5 3) (sourceB2280 + difference 3 5) sourceC2280) = raw31423 := by
      apply Matrix.ext; unfold tripleCharges sourceA2280 sourceB2280 sourceC2280 difference raw31423; decide +kernel
    rw [ha]
    exact (canonical31423 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2280 + difference 5 4) (sourceB2280 + difference 4 5) sourceC2280) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2025) := by
    have ha : (tripleCharges (sourceA2280 + difference 5 4) (sourceB2280 + difference 4 5) sourceC2280) = raw11158 := by
      apply Matrix.ext; unfold tripleCharges sourceA2280 sourceB2280 sourceC2280 difference raw11158; decide +kernel
    rw [ha]
    exact (canonical11158 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2280 sourceB2280 sourceC2280
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2280, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2281 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceB2281 : Charge := ![3, 0, -1, 0, -2, 0]
def sourceC2281 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceForm2281 : Integer.Sparse Master := [(Sum.inr 4406, 1), (Sum.inr 4408, 1), (Sum.inr 4411, 1), (Sum.inr 4419, 1), (Sum.inr 4470, 1), (Sum.inr 4731, 1), (Sum.inr 4744, 1), (Sum.inr 4745, 1), (Sum.inr 4749, 1), (Sum.inr 4781, 1), (Sum.inr 4782, 1), (Sum.inr 4784, 1), (Sum.inr 4794, 1), (Sum.inr 4795, 1), (Sum.inr 4809, 1), (Sum.inr 4810, 1), (Sum.inr 4811, 1), (Sum.inr 4812, 1), (Sum.inr 4820, 1), (Sum.inr 4821, 1), (Sum.inr 4845, 1), (Sum.inr 4846, 1), (Sum.inr 4855, 1), (Sum.inr 4856, 1), (Sum.inr 4874, 1), (Sum.inr 5080, 1), (Sum.inr 5129, 1), (Sum.inr 5151, 1), (Sum.inr 5152, 1), (Sum.inr 5176, 1)]

theorem sourceEq2281 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2281 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2281 + difference 0 1) (sourceB2281 + difference 1 0) sourceC2281) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5080) := by
    have ha : (tripleCharges (sourceA2281 + difference 0 1) (sourceB2281 + difference 1 0) sourceC2281) = raw30547 := by
      apply Matrix.ext; unfold tripleCharges sourceA2281 sourceB2281 sourceC2281 difference raw30547; decide +kernel
    rw [ha]
    exact (canonical30547 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2281 + difference 0 2) (sourceB2281 + difference 2 0) sourceC2281) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5176) := by
    have ha : (tripleCharges (sourceA2281 + difference 0 2) (sourceB2281 + difference 2 0) sourceC2281) = raw29694 := by
      apply Matrix.ext; unfold tripleCharges sourceA2281 sourceB2281 sourceC2281 difference raw29694; decide +kernel
    rw [ha]
    exact (canonical29694 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2281 + difference 0 3) (sourceB2281 + difference 3 0) sourceC2281) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5129) := by
    have ha : (tripleCharges (sourceA2281 + difference 0 3) (sourceB2281 + difference 3 0) sourceC2281) = raw30176 := by
      apply Matrix.ext; unfold tripleCharges sourceA2281 sourceB2281 sourceC2281 difference raw30176; decide +kernel
    rw [ha]
    exact (canonical30176 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2281 + difference 0 4) (sourceB2281 + difference 4 0) sourceC2281) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5152) := by
    have ha : (tripleCharges (sourceA2281 + difference 0 4) (sourceB2281 + difference 4 0) sourceC2281) = raw29685 := by
      apply Matrix.ext; unfold tripleCharges sourceA2281 sourceB2281 sourceC2281 difference raw29685; decide +kernel
    rw [ha]
    exact (canonical29685 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2281 + difference 0 5) (sourceB2281 + difference 5 0) sourceC2281) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5151) := by
    have ha : (tripleCharges (sourceA2281 + difference 0 5) (sourceB2281 + difference 5 0) sourceC2281) = raw30364 := by
      apply Matrix.ext; unfold tripleCharges sourceA2281 sourceB2281 sourceC2281 difference raw30364; decide +kernel
    rw [ha]
    exact (canonical30364 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2281 + difference 1 0) (sourceB2281 + difference 0 1) sourceC2281) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4470) := by
    have ha : (tripleCharges (sourceA2281 + difference 1 0) (sourceB2281 + difference 0 1) sourceC2281) = raw31066 := by
      apply Matrix.ext; unfold tripleCharges sourceA2281 sourceB2281 sourceC2281 difference raw31066; decide +kernel
    rw [ha]
    exact (canonical31066 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2281 + difference 1 2) (sourceB2281 + difference 2 1) sourceC2281) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4874) := by
    have ha : (tripleCharges (sourceA2281 + difference 1 2) (sourceB2281 + difference 2 1) sourceC2281) = raw31241 := by
      apply Matrix.ext; unfold tripleCharges sourceA2281 sourceB2281 sourceC2281 difference raw31241; decide +kernel
    rw [ha]
    exact (canonical31241 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2281 + difference 1 3) (sourceB2281 + difference 3 1) sourceC2281) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4812) := by
    have ha : (tripleCharges (sourceA2281 + difference 1 3) (sourceB2281 + difference 3 1) sourceC2281) = raw31067 := by
      apply Matrix.ext; unfold tripleCharges sourceA2281 sourceB2281 sourceC2281 difference raw31067; decide +kernel
    rw [ha]
    exact (canonical31067 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2281 + difference 1 4) (sourceB2281 + difference 4 1) sourceC2281) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4856) := by
    have ha : (tripleCharges (sourceA2281 + difference 1 4) (sourceB2281 + difference 4 1) sourceC2281) = raw31068 := by
      apply Matrix.ext; unfold tripleCharges sourceA2281 sourceB2281 sourceC2281 difference raw31068; decide +kernel
    rw [ha]
    exact (canonical31068 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2281 + difference 1 5) (sourceB2281 + difference 5 1) sourceC2281) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4855) := by
    have ha : (tripleCharges (sourceA2281 + difference 1 5) (sourceB2281 + difference 5 1) sourceC2281) = raw31069 := by
      apply Matrix.ext; unfold tripleCharges sourceA2281 sourceB2281 sourceC2281 difference raw31069; decide +kernel
    rw [ha]
    exact (canonical31069 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2281 + difference 2 0) (sourceB2281 + difference 0 2) sourceC2281) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4411) := by
    have ha : (tripleCharges (sourceA2281 + difference 2 0) (sourceB2281 + difference 0 2) sourceC2281) = raw31424 := by
      apply Matrix.ext; unfold tripleCharges sourceA2281 sourceB2281 sourceC2281 difference raw31424; decide +kernel
    rw [ha]
    exact (canonical31424 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2281 + difference 2 1) (sourceB2281 + difference 1 2) sourceC2281) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4749) := by
    have ha : (tripleCharges (sourceA2281 + difference 2 1) (sourceB2281 + difference 1 2) sourceC2281) = raw30365 := by
      apply Matrix.ext; unfold tripleCharges sourceA2281 sourceB2281 sourceC2281 difference raw30365; decide +kernel
    rw [ha]
    exact (canonical30365 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2281 + difference 2 3) (sourceB2281 + difference 3 2) sourceC2281) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4784) := by
    have ha : (tripleCharges (sourceA2281 + difference 2 3) (sourceB2281 + difference 3 2) sourceC2281) = raw31425 := by
      apply Matrix.ext; unfold tripleCharges sourceA2281 sourceB2281 sourceC2281 difference raw31425; decide +kernel
    rw [ha]
    exact (canonical31425 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2281 + difference 2 4) (sourceB2281 + difference 4 2) sourceC2281) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4821) := by
    have ha : (tripleCharges (sourceA2281 + difference 2 4) (sourceB2281 + difference 4 2) sourceC2281) = raw31426 := by
      apply Matrix.ext; unfold tripleCharges sourceA2281 sourceB2281 sourceC2281 difference raw31426; decide +kernel
    rw [ha]
    exact (canonical31426 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2281 + difference 2 5) (sourceB2281 + difference 5 2) sourceC2281) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4820) := by
    have ha : (tripleCharges (sourceA2281 + difference 2 5) (sourceB2281 + difference 5 2) sourceC2281) = raw31427 := by
      apply Matrix.ext; unfold tripleCharges sourceA2281 sourceB2281 sourceC2281 difference raw31427; decide +kernel
    rw [ha]
    exact (canonical31427 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2281 + difference 3 0) (sourceB2281 + difference 0 3) sourceC2281) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4406) := by
    have ha : (tripleCharges (sourceA2281 + difference 3 0) (sourceB2281 + difference 0 3) sourceC2281) = raw31428 := by
      apply Matrix.ext; unfold tripleCharges sourceA2281 sourceB2281 sourceC2281 difference raw31428; decide +kernel
    rw [ha]
    exact (canonical31428 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2281 + difference 3 1) (sourceB2281 + difference 1 3) sourceC2281) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4731) := by
    have ha : (tripleCharges (sourceA2281 + difference 3 1) (sourceB2281 + difference 1 3) sourceC2281) = raw30370 := by
      apply Matrix.ext; unfold tripleCharges sourceA2281 sourceB2281 sourceC2281 difference raw30370; decide +kernel
    rw [ha]
    exact (canonical30370 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2281 + difference 3 2) (sourceB2281 + difference 2 3) sourceC2281) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4810) := by
    have ha : (tripleCharges (sourceA2281 + difference 3 2) (sourceB2281 + difference 2 3) sourceC2281) = raw31071 := by
      apply Matrix.ext; unfold tripleCharges sourceA2281 sourceB2281 sourceC2281 difference raw31071; decide +kernel
    rw [ha]
    exact (canonical31071 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2281 + difference 3 4) (sourceB2281 + difference 4 3) sourceC2281) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4795) := by
    have ha : (tripleCharges (sourceA2281 + difference 3 4) (sourceB2281 + difference 4 3) sourceC2281) = raw31429 := by
      apply Matrix.ext; unfold tripleCharges sourceA2281 sourceB2281 sourceC2281 difference raw31429; decide +kernel
    rw [ha]
    exact (canonical31429 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2281 + difference 3 5) (sourceB2281 + difference 5 3) sourceC2281) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4794) := by
    have ha : (tripleCharges (sourceA2281 + difference 3 5) (sourceB2281 + difference 5 3) sourceC2281) = raw31430 := by
      apply Matrix.ext; unfold tripleCharges sourceA2281 sourceB2281 sourceC2281 difference raw31430; decide +kernel
    rw [ha]
    exact (canonical31430 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2281 + difference 4 0) (sourceB2281 + difference 0 4) sourceC2281) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4408) := by
    have ha : (tripleCharges (sourceA2281 + difference 4 0) (sourceB2281 + difference 0 4) sourceC2281) = raw31431 := by
      apply Matrix.ext; unfold tripleCharges sourceA2281 sourceB2281 sourceC2281 difference raw31431; decide +kernel
    rw [ha]
    exact (canonical31431 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2281 + difference 4 1) (sourceB2281 + difference 1 4) sourceC2281) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4744) := by
    have ha : (tripleCharges (sourceA2281 + difference 4 1) (sourceB2281 + difference 1 4) sourceC2281) = raw30375 := by
      apply Matrix.ext; unfold tripleCharges sourceA2281 sourceB2281 sourceC2281 difference raw30375; decide +kernel
    rw [ha]
    exact (canonical30375 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2281 + difference 4 2) (sourceB2281 + difference 2 4) sourceC2281) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4845) := by
    have ha : (tripleCharges (sourceA2281 + difference 4 2) (sourceB2281 + difference 2 4) sourceC2281) = raw30687 := by
      apply Matrix.ext; unfold tripleCharges sourceA2281 sourceB2281 sourceC2281 difference raw30687; decide +kernel
    rw [ha]
    exact (canonical30687 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2281 + difference 4 3) (sourceB2281 + difference 3 4) sourceC2281) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4781) := by
    have ha : (tripleCharges (sourceA2281 + difference 4 3) (sourceB2281 + difference 3 4) sourceC2281) = raw31432 := by
      apply Matrix.ext; unfold tripleCharges sourceA2281 sourceB2281 sourceC2281 difference raw31432; decide +kernel
    rw [ha]
    exact (canonical31432 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2281 + difference 4 5) (sourceB2281 + difference 5 4) sourceC2281) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4809) := by
    have ha : (tripleCharges (sourceA2281 + difference 4 5) (sourceB2281 + difference 5 4) sourceC2281) = raw31433 := by
      apply Matrix.ext; unfold tripleCharges sourceA2281 sourceB2281 sourceC2281 difference raw31433; decide +kernel
    rw [ha]
    exact (canonical31433 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2281 + difference 5 0) (sourceB2281 + difference 0 5) sourceC2281) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4419) := by
    have ha : (tripleCharges (sourceA2281 + difference 5 0) (sourceB2281 + difference 0 5) sourceC2281) = raw31434 := by
      apply Matrix.ext; unfold tripleCharges sourceA2281 sourceB2281 sourceC2281 difference raw31434; decide +kernel
    rw [ha]
    exact (canonical31434 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2281 + difference 5 1) (sourceB2281 + difference 1 5) sourceC2281) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4745) := by
    have ha : (tripleCharges (sourceA2281 + difference 5 1) (sourceB2281 + difference 1 5) sourceC2281) = raw30380 := by
      apply Matrix.ext; unfold tripleCharges sourceA2281 sourceB2281 sourceC2281 difference raw30380; decide +kernel
    rw [ha]
    exact (canonical30380 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2281 + difference 5 2) (sourceB2281 + difference 2 5) sourceC2281) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4846) := by
    have ha : (tripleCharges (sourceA2281 + difference 5 2) (sourceB2281 + difference 2 5) sourceC2281) = raw29690 := by
      apply Matrix.ext; unfold tripleCharges sourceA2281 sourceB2281 sourceC2281 difference raw29690; decide +kernel
    rw [ha]
    exact (canonical29690 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2281 + difference 5 3) (sourceB2281 + difference 3 5) sourceC2281) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4782) := by
    have ha : (tripleCharges (sourceA2281 + difference 5 3) (sourceB2281 + difference 3 5) sourceC2281) = raw30173 := by
      apply Matrix.ext; unfold tripleCharges sourceA2281 sourceB2281 sourceC2281 difference raw30173; decide +kernel
    rw [ha]
    exact (canonical30173 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2281 + difference 5 4) (sourceB2281 + difference 4 5) sourceC2281) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4811) := by
    have ha : (tripleCharges (sourceA2281 + difference 5 4) (sourceB2281 + difference 4 5) sourceC2281) = raw29682 := by
      apply Matrix.ext; unfold tripleCharges sourceA2281 sourceB2281 sourceC2281 difference raw29682; decide +kernel
    rw [ha]
    exact (canonical29682 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2281 sourceB2281 sourceC2281
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2281, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2282 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceB2282 : Charge := ![3, 0, -1, 0, -2, 0]
def sourceC2282 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceForm2282 : Integer.Sparse Master := [(Sum.inr 1360, 1), (Sum.inr 1361, 1), (Sum.inr 1362, 1), (Sum.inr 1371, 1), (Sum.inr 1426, 1), (Sum.inr 2916, 1), (Sum.inr 2919, 1), (Sum.inr 2929, 1), (Sum.inr 2930, 1), (Sum.inr 2931, 1), (Sum.inr 2948, 1), (Sum.inr 2968, 1), (Sum.inr 2990, 1), (Sum.inr 3095, 1), (Sum.inr 3150, 1), (Sum.inr 3151, 1), (Sum.inr 3159, 1), (Sum.inr 3168, 1), (Sum.inr 3174, 1), (Sum.inr 3187, 1), (Sum.inr 3194, 1), (Sum.inr 3198, 1), (Sum.inr 3199, 1), (Sum.inr 3201, 1), (Sum.inr 3206, 1), (Sum.inr 3207, 1), (Sum.inr 3216, 1), (Sum.inr 3218, 1), (Sum.inr 3219, 1), (Sum.inr 3220, 1)]

theorem sourceEq2282 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2282 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2282 + difference 0 1) (sourceB2282 + difference 1 0) sourceC2282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2990) := by
    have ha : (tripleCharges (sourceA2282 + difference 0 1) (sourceB2282 + difference 1 0) sourceC2282) = raw31435 := by
      apply Matrix.ext; unfold tripleCharges sourceA2282 sourceB2282 sourceC2282 difference raw31435; decide +kernel
    rw [ha]
    exact (canonical31435 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2282 + difference 0 2) (sourceB2282 + difference 2 0) sourceC2282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2968) := by
    have ha : (tripleCharges (sourceA2282 + difference 0 2) (sourceB2282 + difference 2 0) sourceC2282) = raw31109 := by
      apply Matrix.ext; unfold tripleCharges sourceA2282 sourceB2282 sourceC2282 difference raw31109; decide +kernel
    rw [ha]
    exact (canonical31109 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2282 + difference 0 3) (sourceB2282 + difference 3 0) sourceC2282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2916) := by
    have ha : (tripleCharges (sourceA2282 + difference 0 3) (sourceB2282 + difference 3 0) sourceC2282) = raw31436 := by
      apply Matrix.ext; unfold tripleCharges sourceA2282 sourceB2282 sourceC2282 difference raw31436; decide +kernel
    rw [ha]
    exact (canonical31436 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2282 + difference 0 4) (sourceB2282 + difference 4 0) sourceC2282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2931) := by
    have ha : (tripleCharges (sourceA2282 + difference 0 4) (sourceB2282 + difference 4 0) sourceC2282) = raw31437 := by
      apply Matrix.ext; unfold tripleCharges sourceA2282 sourceB2282 sourceC2282 difference raw31437; decide +kernel
    rw [ha]
    exact (canonical31437 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2282 + difference 0 5) (sourceB2282 + difference 5 0) sourceC2282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2930) := by
    have ha : (tripleCharges (sourceA2282 + difference 0 5) (sourceB2282 + difference 5 0) sourceC2282) = raw31438 := by
      apply Matrix.ext; unfold tripleCharges sourceA2282 sourceB2282 sourceC2282 difference raw31438; decide +kernel
    rw [ha]
    exact (canonical31438 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2282 + difference 1 0) (sourceB2282 + difference 0 1) sourceC2282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1371) := by
    have ha : (tripleCharges (sourceA2282 + difference 1 0) (sourceB2282 + difference 0 1) sourceC2282) = raw31119 := by
      apply Matrix.ext; unfold tripleCharges sourceA2282 sourceB2282 sourceC2282 difference raw31119; decide +kernel
    rw [ha]
    exact (canonical31119 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2282 + difference 1 2) (sourceB2282 + difference 2 1) sourceC2282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3187) := by
    have ha : (tripleCharges (sourceA2282 + difference 1 2) (sourceB2282 + difference 2 1) sourceC2282) = raw31439 := by
      apply Matrix.ext; unfold tripleCharges sourceA2282 sourceB2282 sourceC2282 difference raw31439; decide +kernel
    rw [ha]
    exact (canonical31439 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2282 + difference 1 3) (sourceB2282 + difference 3 1) sourceC2282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3168) := by
    have ha : (tripleCharges (sourceA2282 + difference 1 3) (sourceB2282 + difference 3 1) sourceC2282) = raw31121 := by
      apply Matrix.ext; unfold tripleCharges sourceA2282 sourceB2282 sourceC2282 difference raw31121; decide +kernel
    rw [ha]
    exact (canonical31121 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2282 + difference 1 4) (sourceB2282 + difference 4 1) sourceC2282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3174) := by
    have ha : (tripleCharges (sourceA2282 + difference 1 4) (sourceB2282 + difference 4 1) sourceC2282) = raw31122 := by
      apply Matrix.ext; unfold tripleCharges sourceA2282 sourceB2282 sourceC2282 difference raw31122; decide +kernel
    rw [ha]
    exact (canonical31122 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2282 + difference 1 5) (sourceB2282 + difference 5 1) sourceC2282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3159) := by
    have ha : (tripleCharges (sourceA2282 + difference 1 5) (sourceB2282 + difference 5 1) sourceC2282) = raw31123 := by
      apply Matrix.ext; unfold tripleCharges sourceA2282 sourceB2282 sourceC2282 difference raw31123; decide +kernel
    rw [ha]
    exact (canonical31123 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2282 + difference 2 0) (sourceB2282 + difference 0 2) sourceC2282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1362) := by
    have ha : (tripleCharges (sourceA2282 + difference 2 0) (sourceB2282 + difference 0 2) sourceC2282) = raw31440 := by
      apply Matrix.ext; unfold tripleCharges sourceA2282 sourceB2282 sourceC2282 difference raw31440; decide +kernel
    rw [ha]
    exact (canonical31440 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2282 + difference 2 1) (sourceB2282 + difference 1 2) sourceC2282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3219) := by
    have ha : (tripleCharges (sourceA2282 + difference 2 1) (sourceB2282 + difference 1 2) sourceC2282) = raw31441 := by
      apply Matrix.ext; unfold tripleCharges sourceA2282 sourceB2282 sourceC2282 difference raw31441; decide +kernel
    rw [ha]
    exact (canonical31441 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2282 + difference 2 3) (sourceB2282 + difference 3 2) sourceC2282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3194) := by
    have ha : (tripleCharges (sourceA2282 + difference 2 3) (sourceB2282 + difference 3 2) sourceC2282) = raw31442 := by
      apply Matrix.ext; unfold tripleCharges sourceA2282 sourceB2282 sourceC2282 difference raw31442; decide +kernel
    rw [ha]
    exact (canonical31442 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2282 + difference 2 4) (sourceB2282 + difference 4 2) sourceC2282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3198) := by
    have ha : (tripleCharges (sourceA2282 + difference 2 4) (sourceB2282 + difference 4 2) sourceC2282) = raw31443 := by
      apply Matrix.ext; unfold tripleCharges sourceA2282 sourceB2282 sourceC2282 difference raw31443; decide +kernel
    rw [ha]
    exact (canonical31443 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2282 + difference 2 5) (sourceB2282 + difference 5 2) sourceC2282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3151) := by
    have ha : (tripleCharges (sourceA2282 + difference 2 5) (sourceB2282 + difference 5 2) sourceC2282) = raw31444 := by
      apply Matrix.ext; unfold tripleCharges sourceA2282 sourceB2282 sourceC2282 difference raw31444; decide +kernel
    rw [ha]
    exact (canonical31444 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2282 + difference 3 0) (sourceB2282 + difference 0 3) sourceC2282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1360) := by
    have ha : (tripleCharges (sourceA2282 + difference 3 0) (sourceB2282 + difference 0 3) sourceC2282) = raw31445 := by
      apply Matrix.ext; unfold tripleCharges sourceA2282 sourceB2282 sourceC2282 difference raw31445; decide +kernel
    rw [ha]
    exact (canonical31445 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2282 + difference 3 1) (sourceB2282 + difference 1 3) sourceC2282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3218) := by
    have ha : (tripleCharges (sourceA2282 + difference 3 1) (sourceB2282 + difference 1 3) sourceC2282) = raw31446 := by
      apply Matrix.ext; unfold tripleCharges sourceA2282 sourceB2282 sourceC2282 difference raw31446; decide +kernel
    rw [ha]
    exact (canonical31446 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2282 + difference 3 2) (sourceB2282 + difference 2 3) sourceC2282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3206) := by
    have ha : (tripleCharges (sourceA2282 + difference 3 2) (sourceB2282 + difference 2 3) sourceC2282) = raw31125 := by
      apply Matrix.ext; unfold tripleCharges sourceA2282 sourceB2282 sourceC2282 difference raw31125; decide +kernel
    rw [ha]
    exact (canonical31125 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2282 + difference 3 4) (sourceB2282 + difference 4 3) sourceC2282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3199) := by
    have ha : (tripleCharges (sourceA2282 + difference 3 4) (sourceB2282 + difference 4 3) sourceC2282) = raw31447 := by
      apply Matrix.ext; unfold tripleCharges sourceA2282 sourceB2282 sourceC2282 difference raw31447; decide +kernel
    rw [ha]
    exact (canonical31447 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2282 + difference 3 5) (sourceB2282 + difference 5 3) sourceC2282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3150) := by
    have ha : (tripleCharges (sourceA2282 + difference 3 5) (sourceB2282 + difference 5 3) sourceC2282) = raw31448 := by
      apply Matrix.ext; unfold tripleCharges sourceA2282 sourceB2282 sourceC2282 difference raw31448; decide +kernel
    rw [ha]
    exact (canonical31448 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2282 + difference 4 0) (sourceB2282 + difference 0 4) sourceC2282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1361) := by
    have ha : (tripleCharges (sourceA2282 + difference 4 0) (sourceB2282 + difference 0 4) sourceC2282) = raw31449 := by
      apply Matrix.ext; unfold tripleCharges sourceA2282 sourceB2282 sourceC2282 difference raw31449; decide +kernel
    rw [ha]
    exact (canonical31449 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2282 + difference 4 1) (sourceB2282 + difference 1 4) sourceC2282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2948) := by
    have ha : (tripleCharges (sourceA2282 + difference 4 1) (sourceB2282 + difference 1 4) sourceC2282) = raw31450 := by
      apply Matrix.ext; unfold tripleCharges sourceA2282 sourceB2282 sourceC2282 difference raw31450; decide +kernel
    rw [ha]
    exact (canonical31450 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2282 + difference 4 2) (sourceB2282 + difference 2 4) sourceC2282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3095) := by
    have ha : (tripleCharges (sourceA2282 + difference 4 2) (sourceB2282 + difference 2 4) sourceC2282) = raw31130 := by
      apply Matrix.ext; unfold tripleCharges sourceA2282 sourceB2282 sourceC2282 difference raw31130; decide +kernel
    rw [ha]
    exact (canonical31130 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2282 + difference 4 3) (sourceB2282 + difference 3 4) sourceC2282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2919) := by
    have ha : (tripleCharges (sourceA2282 + difference 4 3) (sourceB2282 + difference 3 4) sourceC2282) = raw31451 := by
      apply Matrix.ext; unfold tripleCharges sourceA2282 sourceB2282 sourceC2282 difference raw31451; decide +kernel
    rw [ha]
    exact (canonical31451 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2282 + difference 4 5) (sourceB2282 + difference 5 4) sourceC2282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2929) := by
    have ha : (tripleCharges (sourceA2282 + difference 4 5) (sourceB2282 + difference 5 4) sourceC2282) = raw31452 := by
      apply Matrix.ext; unfold tripleCharges sourceA2282 sourceB2282 sourceC2282 difference raw31452; decide +kernel
    rw [ha]
    exact (canonical31452 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2282 + difference 5 0) (sourceB2282 + difference 0 5) sourceC2282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1426) := by
    have ha : (tripleCharges (sourceA2282 + difference 5 0) (sourceB2282 + difference 0 5) sourceC2282) = raw31453 := by
      apply Matrix.ext; unfold tripleCharges sourceA2282 sourceB2282 sourceC2282 difference raw31453; decide +kernel
    rw [ha]
    exact (canonical31453 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2282 + difference 5 1) (sourceB2282 + difference 1 5) sourceC2282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3220) := by
    have ha : (tripleCharges (sourceA2282 + difference 5 1) (sourceB2282 + difference 1 5) sourceC2282) = raw31454 := by
      apply Matrix.ext; unfold tripleCharges sourceA2282 sourceB2282 sourceC2282 difference raw31454; decide +kernel
    rw [ha]
    exact (canonical31454 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2282 + difference 5 2) (sourceB2282 + difference 2 5) sourceC2282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3216) := by
    have ha : (tripleCharges (sourceA2282 + difference 5 2) (sourceB2282 + difference 2 5) sourceC2282) = raw31135 := by
      apply Matrix.ext; unfold tripleCharges sourceA2282 sourceB2282 sourceC2282 difference raw31135; decide +kernel
    rw [ha]
    exact (canonical31135 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2282 + difference 5 3) (sourceB2282 + difference 3 5) sourceC2282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3201) := by
    have ha : (tripleCharges (sourceA2282 + difference 5 3) (sourceB2282 + difference 3 5) sourceC2282) = raw31455 := by
      apply Matrix.ext; unfold tripleCharges sourceA2282 sourceB2282 sourceC2282 difference raw31455; decide +kernel
    rw [ha]
    exact (canonical31455 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2282 + difference 5 4) (sourceB2282 + difference 4 5) sourceC2282) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3207) := by
    have ha : (tripleCharges (sourceA2282 + difference 5 4) (sourceB2282 + difference 4 5) sourceC2282) = raw31456 := by
      apply Matrix.ext; unfold tripleCharges sourceA2282 sourceB2282 sourceC2282 difference raw31456; decide +kernel
    rw [ha]
    exact (canonical31456 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2282 sourceB2282 sourceC2282
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2282, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2283 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2283 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC2283 : Charge := ![3, 0, -1, 0, -1, -1]
def sourceForm2283 : Integer.Sparse Master := [(Sum.inr 4329, 1), (Sum.inr 4335, 2), (Sum.inr 4355, 1), (Sum.inr 4467, 1), (Sum.inr 4666, 1), (Sum.inr 4670, 2), (Sum.inr 4689, 1), (Sum.inr 4757, 2), (Sum.inr 4767, 1), (Sum.inr 4774, 1), (Sum.inr 4777, 2), (Sum.inr 4802, 2), (Sum.inr 4807, 2), (Sum.inr 4811, 1), (Sum.inr 4838, 2), (Sum.inr 4875, 1), (Sum.inr 4895, 2), (Sum.inr 5236, 1), (Sum.inr 5246, 1), (Sum.inr 5269, 1), (Sum.inr 5271, 2)]

theorem sourceEq2283 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2283 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2283 + difference 0 1) (sourceB2283 + difference 1 0) sourceC2283) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5236) := by
    have ha : (tripleCharges (sourceA2283 + difference 0 1) (sourceB2283 + difference 1 0) sourceC2283) = raw31457 := by
      apply Matrix.ext; unfold tripleCharges sourceA2283 sourceB2283 sourceC2283 difference raw31457; decide +kernel
    rw [ha]
    exact (canonical31457 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2283 + difference 0 2) (sourceB2283 + difference 2 0) sourceC2283) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5269) := by
    have ha : (tripleCharges (sourceA2283 + difference 0 2) (sourceB2283 + difference 2 0) sourceC2283) = raw31458 := by
      apply Matrix.ext; unfold tripleCharges sourceA2283 sourceB2283 sourceC2283 difference raw31458; decide +kernel
    rw [ha]
    exact (canonical31458 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2283 + difference 0 3) (sourceB2283 + difference 3 0) sourceC2283) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5246) := by
    have ha : (tripleCharges (sourceA2283 + difference 0 3) (sourceB2283 + difference 3 0) sourceC2283) = raw31459 := by
      apply Matrix.ext; unfold tripleCharges sourceA2283 sourceB2283 sourceC2283 difference raw31459; decide +kernel
    rw [ha]
    exact (canonical31459 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2283 + difference 0 4) (sourceB2283 + difference 4 0) sourceC2283) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA2283 + difference 0 4) (sourceB2283 + difference 4 0) sourceC2283) = raw31460 := by
      apply Matrix.ext; unfold tripleCharges sourceA2283 sourceB2283 sourceC2283 difference raw31460; decide +kernel
    rw [ha]
    exact (canonical31460 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2283 + difference 0 5) (sourceB2283 + difference 5 0) sourceC2283) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA2283 + difference 0 5) (sourceB2283 + difference 5 0) sourceC2283) = raw31461 := by
      apply Matrix.ext; unfold tripleCharges sourceA2283 sourceB2283 sourceC2283 difference raw31461; decide +kernel
    rw [ha]
    exact (canonical31461 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2283 + difference 1 0) (sourceB2283 + difference 0 1) sourceC2283) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4467) := by
    have ha : (tripleCharges (sourceA2283 + difference 1 0) (sourceB2283 + difference 0 1) sourceC2283) = raw31462 := by
      apply Matrix.ext; unfold tripleCharges sourceA2283 sourceB2283 sourceC2283 difference raw31462; decide +kernel
    rw [ha]
    exact (canonical31462 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2283 + difference 1 2) (sourceB2283 + difference 2 1) sourceC2283) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4875) := by
    have ha : (tripleCharges (sourceA2283 + difference 1 2) (sourceB2283 + difference 2 1) sourceC2283) = raw31463 := by
      apply Matrix.ext; unfold tripleCharges sourceA2283 sourceB2283 sourceC2283 difference raw31463; decide +kernel
    rw [ha]
    exact (canonical31463 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2283 + difference 1 3) (sourceB2283 + difference 3 1) sourceC2283) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4811) := by
    have ha : (tripleCharges (sourceA2283 + difference 1 3) (sourceB2283 + difference 3 1) sourceC2283) = raw31464 := by
      apply Matrix.ext; unfold tripleCharges sourceA2283 sourceB2283 sourceC2283 difference raw31464; decide +kernel
    rw [ha]
    exact (canonical31464 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2283 + difference 1 4) (sourceB2283 + difference 4 1) sourceC2283) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA2283 + difference 1 4) (sourceB2283 + difference 4 1) sourceC2283) = raw31465 := by
      apply Matrix.ext; unfold tripleCharges sourceA2283 sourceB2283 sourceC2283 difference raw31465; decide +kernel
    rw [ha]
    exact (canonical31465 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2283 + difference 1 5) (sourceB2283 + difference 5 1) sourceC2283) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA2283 + difference 1 5) (sourceB2283 + difference 5 1) sourceC2283) = raw31466 := by
      apply Matrix.ext; unfold tripleCharges sourceA2283 sourceB2283 sourceC2283 difference raw31466; decide +kernel
    rw [ha]
    exact (canonical31466 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2283 + difference 2 0) (sourceB2283 + difference 0 2) sourceC2283) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4355) := by
    have ha : (tripleCharges (sourceA2283 + difference 2 0) (sourceB2283 + difference 0 2) sourceC2283) = raw31467 := by
      apply Matrix.ext; unfold tripleCharges sourceA2283 sourceB2283 sourceC2283 difference raw31467; decide +kernel
    rw [ha]
    exact (canonical31467 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2283 + difference 2 1) (sourceB2283 + difference 1 2) sourceC2283) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4689) := by
    have ha : (tripleCharges (sourceA2283 + difference 2 1) (sourceB2283 + difference 1 2) sourceC2283) = raw31468 := by
      apply Matrix.ext; unfold tripleCharges sourceA2283 sourceB2283 sourceC2283 difference raw31468; decide +kernel
    rw [ha]
    exact (canonical31468 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2283 + difference 2 3) (sourceB2283 + difference 3 2) sourceC2283) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4767) := by
    have ha : (tripleCharges (sourceA2283 + difference 2 3) (sourceB2283 + difference 3 2) sourceC2283) = raw31469 := by
      apply Matrix.ext; unfold tripleCharges sourceA2283 sourceB2283 sourceC2283 difference raw31469; decide +kernel
    rw [ha]
    exact (canonical31469 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2283 + difference 2 4) (sourceB2283 + difference 4 2) sourceC2283) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4838) := by
    have ha : (tripleCharges (sourceA2283 + difference 2 4) (sourceB2283 + difference 4 2) sourceC2283) = raw31470 := by
      apply Matrix.ext; unfold tripleCharges sourceA2283 sourceB2283 sourceC2283 difference raw31470; decide +kernel
    rw [ha]
    exact (canonical31470 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2283 + difference 2 5) (sourceB2283 + difference 5 2) sourceC2283) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4838) := by
    have ha : (tripleCharges (sourceA2283 + difference 2 5) (sourceB2283 + difference 5 2) sourceC2283) = raw31471 := by
      apply Matrix.ext; unfold tripleCharges sourceA2283 sourceB2283 sourceC2283 difference raw31471; decide +kernel
    rw [ha]
    exact (canonical31471 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2283 + difference 3 0) (sourceB2283 + difference 0 3) sourceC2283) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4329) := by
    have ha : (tripleCharges (sourceA2283 + difference 3 0) (sourceB2283 + difference 0 3) sourceC2283) = raw31472 := by
      apply Matrix.ext; unfold tripleCharges sourceA2283 sourceB2283 sourceC2283 difference raw31472; decide +kernel
    rw [ha]
    exact (canonical31472 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2283 + difference 3 1) (sourceB2283 + difference 1 3) sourceC2283) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4666) := by
    have ha : (tripleCharges (sourceA2283 + difference 3 1) (sourceB2283 + difference 1 3) sourceC2283) = raw31473 := by
      apply Matrix.ext; unfold tripleCharges sourceA2283 sourceB2283 sourceC2283 difference raw31473; decide +kernel
    rw [ha]
    exact (canonical31473 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2283 + difference 3 2) (sourceB2283 + difference 2 3) sourceC2283) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4774) := by
    have ha : (tripleCharges (sourceA2283 + difference 3 2) (sourceB2283 + difference 2 3) sourceC2283) = raw31474 := by
      apply Matrix.ext; unfold tripleCharges sourceA2283 sourceB2283 sourceC2283 difference raw31474; decide +kernel
    rw [ha]
    exact (canonical31474 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2283 + difference 3 4) (sourceB2283 + difference 4 3) sourceC2283) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA2283 + difference 3 4) (sourceB2283 + difference 4 3) sourceC2283) = raw31475 := by
      apply Matrix.ext; unfold tripleCharges sourceA2283 sourceB2283 sourceC2283 difference raw31475; decide +kernel
    rw [ha]
    exact (canonical31475 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2283 + difference 3 5) (sourceB2283 + difference 5 3) sourceC2283) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA2283 + difference 3 5) (sourceB2283 + difference 5 3) sourceC2283) = raw31476 := by
      apply Matrix.ext; unfold tripleCharges sourceA2283 sourceB2283 sourceC2283 difference raw31476; decide +kernel
    rw [ha]
    exact (canonical31476 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2283 + difference 4 0) (sourceB2283 + difference 0 4) sourceC2283) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4335) := by
    have ha : (tripleCharges (sourceA2283 + difference 4 0) (sourceB2283 + difference 0 4) sourceC2283) = raw31477 := by
      apply Matrix.ext; unfold tripleCharges sourceA2283 sourceB2283 sourceC2283 difference raw31477; decide +kernel
    rw [ha]
    exact (canonical31477 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2283 + difference 4 1) (sourceB2283 + difference 1 4) sourceC2283) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4670) := by
    have ha : (tripleCharges (sourceA2283 + difference 4 1) (sourceB2283 + difference 1 4) sourceC2283) = raw31478 := by
      apply Matrix.ext; unfold tripleCharges sourceA2283 sourceB2283 sourceC2283 difference raw31478; decide +kernel
    rw [ha]
    exact (canonical31478 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2283 + difference 4 2) (sourceB2283 + difference 2 4) sourceC2283) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4777) := by
    have ha : (tripleCharges (sourceA2283 + difference 4 2) (sourceB2283 + difference 2 4) sourceC2283) = raw31479 := by
      apply Matrix.ext; unfold tripleCharges sourceA2283 sourceB2283 sourceC2283 difference raw31479; decide +kernel
    rw [ha]
    exact (canonical31479 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2283 + difference 4 3) (sourceB2283 + difference 3 4) sourceC2283) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4757) := by
    have ha : (tripleCharges (sourceA2283 + difference 4 3) (sourceB2283 + difference 3 4) sourceC2283) = raw31480 := by
      apply Matrix.ext; unfold tripleCharges sourceA2283 sourceB2283 sourceC2283 difference raw31480; decide +kernel
    rw [ha]
    exact (canonical31480 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2283 + difference 4 5) (sourceB2283 + difference 5 4) sourceC2283) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA2283 + difference 4 5) (sourceB2283 + difference 5 4) sourceC2283) = raw31481 := by
      apply Matrix.ext; unfold tripleCharges sourceA2283 sourceB2283 sourceC2283 difference raw31481; decide +kernel
    rw [ha]
    exact (canonical31481 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2283 + difference 5 0) (sourceB2283 + difference 0 5) sourceC2283) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4335) := by
    have ha : (tripleCharges (sourceA2283 + difference 5 0) (sourceB2283 + difference 0 5) sourceC2283) = raw31482 := by
      apply Matrix.ext; unfold tripleCharges sourceA2283 sourceB2283 sourceC2283 difference raw31482; decide +kernel
    rw [ha]
    exact (canonical31482 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2283 + difference 5 1) (sourceB2283 + difference 1 5) sourceC2283) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4670) := by
    have ha : (tripleCharges (sourceA2283 + difference 5 1) (sourceB2283 + difference 1 5) sourceC2283) = raw31483 := by
      apply Matrix.ext; unfold tripleCharges sourceA2283 sourceB2283 sourceC2283 difference raw31483; decide +kernel
    rw [ha]
    exact (canonical31483 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2283 + difference 5 2) (sourceB2283 + difference 2 5) sourceC2283) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4777) := by
    have ha : (tripleCharges (sourceA2283 + difference 5 2) (sourceB2283 + difference 2 5) sourceC2283) = raw31484 := by
      apply Matrix.ext; unfold tripleCharges sourceA2283 sourceB2283 sourceC2283 difference raw31484; decide +kernel
    rw [ha]
    exact (canonical31484 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2283 + difference 5 3) (sourceB2283 + difference 3 5) sourceC2283) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4757) := by
    have ha : (tripleCharges (sourceA2283 + difference 5 3) (sourceB2283 + difference 3 5) sourceC2283) = raw31485 := by
      apply Matrix.ext; unfold tripleCharges sourceA2283 sourceB2283 sourceC2283 difference raw31485; decide +kernel
    rw [ha]
    exact (canonical31485 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2283 + difference 5 4) (sourceB2283 + difference 4 5) sourceC2283) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA2283 + difference 5 4) (sourceB2283 + difference 4 5) sourceC2283) = raw31486 := by
      apply Matrix.ext; unfold tripleCharges sourceA2283 sourceB2283 sourceC2283 difference raw31486; decide +kernel
    rw [ha]
    exact (canonical31486 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2283 sourceB2283 sourceC2283
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2283, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2284 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2284 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC2284 : Charge := ![3, 0, -1, 0, -1, -1]
def sourceForm2284 : Integer.Sparse Master := [(Sum.inr 1331, 1), (Sum.inr 1333, 2), (Sum.inr 1344, 1), (Sum.inr 1420, 1), (Sum.inr 2323, 2), (Sum.inr 2327, 2), (Sum.inr 2340, 2), (Sum.inr 2574, 2), (Sum.inr 3104, 1), (Sum.inr 3108, 1), (Sum.inr 3109, 2), (Sum.inr 3115, 1), (Sum.inr 3135, 1), (Sum.inr 3142, 1), (Sum.inr 3164, 1), (Sum.inr 3188, 1), (Sum.inr 3191, 1), (Sum.inr 3204, 2), (Sum.inr 3207, 1), (Sum.inr 3213, 2), (Sum.inr 3229, 2)]

theorem sourceEq2284 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2284 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2284 + difference 0 1) (sourceB2284 + difference 1 0) sourceC2284) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3115) := by
    have ha : (tripleCharges (sourceA2284 + difference 0 1) (sourceB2284 + difference 1 0) sourceC2284) = raw31487 := by
      apply Matrix.ext; unfold tripleCharges sourceA2284 sourceB2284 sourceC2284 difference raw31487; decide +kernel
    rw [ha]
    exact (canonical31487 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2284 + difference 0 2) (sourceB2284 + difference 2 0) sourceC2284) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3108) := by
    have ha : (tripleCharges (sourceA2284 + difference 0 2) (sourceB2284 + difference 2 0) sourceC2284) = raw31488 := by
      apply Matrix.ext; unfold tripleCharges sourceA2284 sourceB2284 sourceC2284 difference raw31488; decide +kernel
    rw [ha]
    exact (canonical31488 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2284 + difference 0 3) (sourceB2284 + difference 3 0) sourceC2284) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3104) := by
    have ha : (tripleCharges (sourceA2284 + difference 0 3) (sourceB2284 + difference 3 0) sourceC2284) = raw31489 := by
      apply Matrix.ext; unfold tripleCharges sourceA2284 sourceB2284 sourceC2284 difference raw31489; decide +kernel
    rw [ha]
    exact (canonical31489 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2284 + difference 0 4) (sourceB2284 + difference 4 0) sourceC2284) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3109) := by
    have ha : (tripleCharges (sourceA2284 + difference 0 4) (sourceB2284 + difference 4 0) sourceC2284) = raw31490 := by
      apply Matrix.ext; unfold tripleCharges sourceA2284 sourceB2284 sourceC2284 difference raw31490; decide +kernel
    rw [ha]
    exact (canonical31490 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2284 + difference 0 5) (sourceB2284 + difference 5 0) sourceC2284) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3109) := by
    have ha : (tripleCharges (sourceA2284 + difference 0 5) (sourceB2284 + difference 5 0) sourceC2284) = raw31491 := by
      apply Matrix.ext; unfold tripleCharges sourceA2284 sourceB2284 sourceC2284 difference raw31491; decide +kernel
    rw [ha]
    exact (canonical31491 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2284 + difference 1 0) (sourceB2284 + difference 0 1) sourceC2284) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1420) := by
    have ha : (tripleCharges (sourceA2284 + difference 1 0) (sourceB2284 + difference 0 1) sourceC2284) = raw31492 := by
      apply Matrix.ext; unfold tripleCharges sourceA2284 sourceB2284 sourceC2284 difference raw31492; decide +kernel
    rw [ha]
    exact (canonical31492 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2284 + difference 1 2) (sourceB2284 + difference 2 1) sourceC2284) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3188) := by
    have ha : (tripleCharges (sourceA2284 + difference 1 2) (sourceB2284 + difference 2 1) sourceC2284) = raw31493 := by
      apply Matrix.ext; unfold tripleCharges sourceA2284 sourceB2284 sourceC2284 difference raw31493; decide +kernel
    rw [ha]
    exact (canonical31493 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2284 + difference 1 3) (sourceB2284 + difference 3 1) sourceC2284) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3207) := by
    have ha : (tripleCharges (sourceA2284 + difference 1 3) (sourceB2284 + difference 3 1) sourceC2284) = raw31494 := by
      apply Matrix.ext; unfold tripleCharges sourceA2284 sourceB2284 sourceC2284 difference raw31494; decide +kernel
    rw [ha]
    exact (canonical31494 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2284 + difference 1 4) (sourceB2284 + difference 4 1) sourceC2284) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3229) := by
    have ha : (tripleCharges (sourceA2284 + difference 1 4) (sourceB2284 + difference 4 1) sourceC2284) = raw31495 := by
      apply Matrix.ext; unfold tripleCharges sourceA2284 sourceB2284 sourceC2284 difference raw31495; decide +kernel
    rw [ha]
    exact (canonical31495 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2284 + difference 1 5) (sourceB2284 + difference 5 1) sourceC2284) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3229) := by
    have ha : (tripleCharges (sourceA2284 + difference 1 5) (sourceB2284 + difference 5 1) sourceC2284) = raw31496 := by
      apply Matrix.ext; unfold tripleCharges sourceA2284 sourceB2284 sourceC2284 difference raw31496; decide +kernel
    rw [ha]
    exact (canonical31496 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2284 + difference 2 0) (sourceB2284 + difference 0 2) sourceC2284) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1344) := by
    have ha : (tripleCharges (sourceA2284 + difference 2 0) (sourceB2284 + difference 0 2) sourceC2284) = raw31497 := by
      apply Matrix.ext; unfold tripleCharges sourceA2284 sourceB2284 sourceC2284 difference raw31497; decide +kernel
    rw [ha]
    exact (canonical31497 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2284 + difference 2 1) (sourceB2284 + difference 1 2) sourceC2284) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3142) := by
    have ha : (tripleCharges (sourceA2284 + difference 2 1) (sourceB2284 + difference 1 2) sourceC2284) = raw31498 := by
      apply Matrix.ext; unfold tripleCharges sourceA2284 sourceB2284 sourceC2284 difference raw31498; decide +kernel
    rw [ha]
    exact (canonical31498 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2284 + difference 2 3) (sourceB2284 + difference 3 2) sourceC2284) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3191) := by
    have ha : (tripleCharges (sourceA2284 + difference 2 3) (sourceB2284 + difference 3 2) sourceC2284) = raw31499 := by
      apply Matrix.ext; unfold tripleCharges sourceA2284 sourceB2284 sourceC2284 difference raw31499; decide +kernel
    rw [ha]
    exact (canonical31499 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2284 + difference 2 4) (sourceB2284 + difference 4 2) sourceC2284) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3213) := by
    have ha : (tripleCharges (sourceA2284 + difference 2 4) (sourceB2284 + difference 4 2) sourceC2284) = raw31500 := by
      apply Matrix.ext; unfold tripleCharges sourceA2284 sourceB2284 sourceC2284 difference raw31500; decide +kernel
    rw [ha]
    exact (canonical31500 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2284 + difference 2 5) (sourceB2284 + difference 5 2) sourceC2284) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3213) := by
    have ha : (tripleCharges (sourceA2284 + difference 2 5) (sourceB2284 + difference 5 2) sourceC2284) = raw31501 := by
      apply Matrix.ext; unfold tripleCharges sourceA2284 sourceB2284 sourceC2284 difference raw31501; decide +kernel
    rw [ha]
    exact (canonical31501 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2284 + difference 3 0) (sourceB2284 + difference 0 3) sourceC2284) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1331) := by
    have ha : (tripleCharges (sourceA2284 + difference 3 0) (sourceB2284 + difference 0 3) sourceC2284) = raw31502 := by
      apply Matrix.ext; unfold tripleCharges sourceA2284 sourceB2284 sourceC2284 difference raw31502; decide +kernel
    rw [ha]
    exact (canonical31502 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2284 + difference 3 1) (sourceB2284 + difference 1 3) sourceC2284) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3135) := by
    have ha : (tripleCharges (sourceA2284 + difference 3 1) (sourceB2284 + difference 1 3) sourceC2284) = raw31503 := by
      apply Matrix.ext; unfold tripleCharges sourceA2284 sourceB2284 sourceC2284 difference raw31503; decide +kernel
    rw [ha]
    exact (canonical31503 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2284 + difference 3 2) (sourceB2284 + difference 2 3) sourceC2284) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3164) := by
    have ha : (tripleCharges (sourceA2284 + difference 3 2) (sourceB2284 + difference 2 3) sourceC2284) = raw31504 := by
      apply Matrix.ext; unfold tripleCharges sourceA2284 sourceB2284 sourceC2284 difference raw31504; decide +kernel
    rw [ha]
    exact (canonical31504 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2284 + difference 3 4) (sourceB2284 + difference 4 3) sourceC2284) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3204) := by
    have ha : (tripleCharges (sourceA2284 + difference 3 4) (sourceB2284 + difference 4 3) sourceC2284) = raw31505 := by
      apply Matrix.ext; unfold tripleCharges sourceA2284 sourceB2284 sourceC2284 difference raw31505; decide +kernel
    rw [ha]
    exact (canonical31505 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2284 + difference 3 5) (sourceB2284 + difference 5 3) sourceC2284) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3204) := by
    have ha : (tripleCharges (sourceA2284 + difference 3 5) (sourceB2284 + difference 5 3) sourceC2284) = raw31506 := by
      apply Matrix.ext; unfold tripleCharges sourceA2284 sourceB2284 sourceC2284 difference raw31506; decide +kernel
    rw [ha]
    exact (canonical31506 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2284 + difference 4 0) (sourceB2284 + difference 0 4) sourceC2284) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1333) := by
    have ha : (tripleCharges (sourceA2284 + difference 4 0) (sourceB2284 + difference 0 4) sourceC2284) = raw31507 := by
      apply Matrix.ext; unfold tripleCharges sourceA2284 sourceB2284 sourceC2284 difference raw31507; decide +kernel
    rw [ha]
    exact (canonical31507 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2284 + difference 4 1) (sourceB2284 + difference 1 4) sourceC2284) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2327) := by
    have ha : (tripleCharges (sourceA2284 + difference 4 1) (sourceB2284 + difference 1 4) sourceC2284) = raw31508 := by
      apply Matrix.ext; unfold tripleCharges sourceA2284 sourceB2284 sourceC2284 difference raw31508; decide +kernel
    rw [ha]
    exact (canonical31508 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2284 + difference 4 2) (sourceB2284 + difference 2 4) sourceC2284) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2340) := by
    have ha : (tripleCharges (sourceA2284 + difference 4 2) (sourceB2284 + difference 2 4) sourceC2284) = raw31509 := by
      apply Matrix.ext; unfold tripleCharges sourceA2284 sourceB2284 sourceC2284 difference raw31509; decide +kernel
    rw [ha]
    exact (canonical31509 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2284 + difference 4 3) (sourceB2284 + difference 3 4) sourceC2284) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2323) := by
    have ha : (tripleCharges (sourceA2284 + difference 4 3) (sourceB2284 + difference 3 4) sourceC2284) = raw31510 := by
      apply Matrix.ext; unfold tripleCharges sourceA2284 sourceB2284 sourceC2284 difference raw31510; decide +kernel
    rw [ha]
    exact (canonical31510 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2284 + difference 4 5) (sourceB2284 + difference 5 4) sourceC2284) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2574) := by
    have ha : (tripleCharges (sourceA2284 + difference 4 5) (sourceB2284 + difference 5 4) sourceC2284) = raw31511 := by
      apply Matrix.ext; unfold tripleCharges sourceA2284 sourceB2284 sourceC2284 difference raw31511; decide +kernel
    rw [ha]
    exact (canonical31511 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2284 + difference 5 0) (sourceB2284 + difference 0 5) sourceC2284) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1333) := by
    have ha : (tripleCharges (sourceA2284 + difference 5 0) (sourceB2284 + difference 0 5) sourceC2284) = raw31512 := by
      apply Matrix.ext; unfold tripleCharges sourceA2284 sourceB2284 sourceC2284 difference raw31512; decide +kernel
    rw [ha]
    exact (canonical31512 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2284 + difference 5 1) (sourceB2284 + difference 1 5) sourceC2284) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2327) := by
    have ha : (tripleCharges (sourceA2284 + difference 5 1) (sourceB2284 + difference 1 5) sourceC2284) = raw31513 := by
      apply Matrix.ext; unfold tripleCharges sourceA2284 sourceB2284 sourceC2284 difference raw31513; decide +kernel
    rw [ha]
    exact (canonical31513 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2284 + difference 5 2) (sourceB2284 + difference 2 5) sourceC2284) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2340) := by
    have ha : (tripleCharges (sourceA2284 + difference 5 2) (sourceB2284 + difference 2 5) sourceC2284) = raw31514 := by
      apply Matrix.ext; unfold tripleCharges sourceA2284 sourceB2284 sourceC2284 difference raw31514; decide +kernel
    rw [ha]
    exact (canonical31514 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2284 + difference 5 3) (sourceB2284 + difference 3 5) sourceC2284) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2323) := by
    have ha : (tripleCharges (sourceA2284 + difference 5 3) (sourceB2284 + difference 3 5) sourceC2284) = raw31515 := by
      apply Matrix.ext; unfold tripleCharges sourceA2284 sourceB2284 sourceC2284 difference raw31515; decide +kernel
    rw [ha]
    exact (canonical31515 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2284 + difference 5 4) (sourceB2284 + difference 4 5) sourceC2284) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2574) := by
    have ha : (tripleCharges (sourceA2284 + difference 5 4) (sourceB2284 + difference 4 5) sourceC2284) = raw31516 := by
      apply Matrix.ext; unfold tripleCharges sourceA2284 sourceB2284 sourceC2284 difference raw31516; decide +kernel
    rw [ha]
    exact (canonical31516 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2284 sourceB2284 sourceC2284
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2284, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2285 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2285 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC2285 : Charge := ![3, 0, -1, 0, -1, -1]
def sourceForm2285 : Integer.Sparse Master := [(Sum.inr 1671, 1), (Sum.inr 1689, 2), (Sum.inr 1691, 1), (Sum.inr 1751, 1), (Sum.inr 2148, 1), (Sum.inr 2164, 2), (Sum.inr 2166, 1), (Sum.inr 2181, 2), (Sum.inr 2183, 1), (Sum.inr 2199, 1), (Sum.inr 2202, 2), (Sum.inr 2223, 2), (Sum.inr 2224, 2), (Sum.inr 2225, 1), (Sum.inr 2227, 2), (Sum.inr 2288, 1), (Sum.inr 2291, 2), (Sum.inr 2682, 1), (Sum.inr 2701, 1), (Sum.inr 2736, 1), (Sum.inr 2739, 2)]

theorem sourceEq2285 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2285 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2285 + difference 0 1) (sourceB2285 + difference 1 0) sourceC2285) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2682) := by
    have ha : (tripleCharges (sourceA2285 + difference 0 1) (sourceB2285 + difference 1 0) sourceC2285) = raw31517 := by
      apply Matrix.ext; unfold tripleCharges sourceA2285 sourceB2285 sourceC2285 difference raw31517; decide +kernel
    rw [ha]
    exact (canonical31517 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2285 + difference 0 2) (sourceB2285 + difference 2 0) sourceC2285) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2736) := by
    have ha : (tripleCharges (sourceA2285 + difference 0 2) (sourceB2285 + difference 2 0) sourceC2285) = raw31518 := by
      apply Matrix.ext; unfold tripleCharges sourceA2285 sourceB2285 sourceC2285 difference raw31518; decide +kernel
    rw [ha]
    exact (canonical31518 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2285 + difference 0 3) (sourceB2285 + difference 3 0) sourceC2285) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2701) := by
    have ha : (tripleCharges (sourceA2285 + difference 0 3) (sourceB2285 + difference 3 0) sourceC2285) = raw31519 := by
      apply Matrix.ext; unfold tripleCharges sourceA2285 sourceB2285 sourceC2285 difference raw31519; decide +kernel
    rw [ha]
    exact (canonical31519 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2285 + difference 0 4) (sourceB2285 + difference 4 0) sourceC2285) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2739) := by
    have ha : (tripleCharges (sourceA2285 + difference 0 4) (sourceB2285 + difference 4 0) sourceC2285) = raw31520 := by
      apply Matrix.ext; unfold tripleCharges sourceA2285 sourceB2285 sourceC2285 difference raw31520; decide +kernel
    rw [ha]
    exact (canonical31520 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2285 + difference 0 5) (sourceB2285 + difference 5 0) sourceC2285) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2739) := by
    have ha : (tripleCharges (sourceA2285 + difference 0 5) (sourceB2285 + difference 5 0) sourceC2285) = raw31521 := by
      apply Matrix.ext; unfold tripleCharges sourceA2285 sourceB2285 sourceC2285 difference raw31521; decide +kernel
    rw [ha]
    exact (canonical31521 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2285 + difference 1 0) (sourceB2285 + difference 0 1) sourceC2285) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1751) := by
    have ha : (tripleCharges (sourceA2285 + difference 1 0) (sourceB2285 + difference 0 1) sourceC2285) = raw31522 := by
      apply Matrix.ext; unfold tripleCharges sourceA2285 sourceB2285 sourceC2285 difference raw31522; decide +kernel
    rw [ha]
    exact (canonical31522 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2285 + difference 1 2) (sourceB2285 + difference 2 1) sourceC2285) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2288) := by
    have ha : (tripleCharges (sourceA2285 + difference 1 2) (sourceB2285 + difference 2 1) sourceC2285) = raw31523 := by
      apply Matrix.ext; unfold tripleCharges sourceA2285 sourceB2285 sourceC2285 difference raw31523; decide +kernel
    rw [ha]
    exact (canonical31523 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2285 + difference 1 3) (sourceB2285 + difference 3 1) sourceC2285) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2225) := by
    have ha : (tripleCharges (sourceA2285 + difference 1 3) (sourceB2285 + difference 3 1) sourceC2285) = raw31524 := by
      apply Matrix.ext; unfold tripleCharges sourceA2285 sourceB2285 sourceC2285 difference raw31524; decide +kernel
    rw [ha]
    exact (canonical31524 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2285 + difference 1 4) (sourceB2285 + difference 4 1) sourceC2285) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2291) := by
    have ha : (tripleCharges (sourceA2285 + difference 1 4) (sourceB2285 + difference 4 1) sourceC2285) = raw31525 := by
      apply Matrix.ext; unfold tripleCharges sourceA2285 sourceB2285 sourceC2285 difference raw31525; decide +kernel
    rw [ha]
    exact (canonical31525 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2285 + difference 1 5) (sourceB2285 + difference 5 1) sourceC2285) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2291) := by
    have ha : (tripleCharges (sourceA2285 + difference 1 5) (sourceB2285 + difference 5 1) sourceC2285) = raw31526 := by
      apply Matrix.ext; unfold tripleCharges sourceA2285 sourceB2285 sourceC2285 difference raw31526; decide +kernel
    rw [ha]
    exact (canonical31526 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2285 + difference 2 0) (sourceB2285 + difference 0 2) sourceC2285) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1691) := by
    have ha : (tripleCharges (sourceA2285 + difference 2 0) (sourceB2285 + difference 0 2) sourceC2285) = raw31527 := by
      apply Matrix.ext; unfold tripleCharges sourceA2285 sourceB2285 sourceC2285 difference raw31527; decide +kernel
    rw [ha]
    exact (canonical31527 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2285 + difference 2 1) (sourceB2285 + difference 1 2) sourceC2285) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2166) := by
    have ha : (tripleCharges (sourceA2285 + difference 2 1) (sourceB2285 + difference 1 2) sourceC2285) = raw31528 := by
      apply Matrix.ext; unfold tripleCharges sourceA2285 sourceB2285 sourceC2285 difference raw31528; decide +kernel
    rw [ha]
    exact (canonical31528 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2285 + difference 2 3) (sourceB2285 + difference 3 2) sourceC2285) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2183) := by
    have ha : (tripleCharges (sourceA2285 + difference 2 3) (sourceB2285 + difference 3 2) sourceC2285) = raw31529 := by
      apply Matrix.ext; unfold tripleCharges sourceA2285 sourceB2285 sourceC2285 difference raw31529; decide +kernel
    rw [ha]
    exact (canonical31529 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2285 + difference 2 4) (sourceB2285 + difference 4 2) sourceC2285) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2227) := by
    have ha : (tripleCharges (sourceA2285 + difference 2 4) (sourceB2285 + difference 4 2) sourceC2285) = raw31530 := by
      apply Matrix.ext; unfold tripleCharges sourceA2285 sourceB2285 sourceC2285 difference raw31530; decide +kernel
    rw [ha]
    exact (canonical31530 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2285 + difference 2 5) (sourceB2285 + difference 5 2) sourceC2285) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2227) := by
    have ha : (tripleCharges (sourceA2285 + difference 2 5) (sourceB2285 + difference 5 2) sourceC2285) = raw31531 := by
      apply Matrix.ext; unfold tripleCharges sourceA2285 sourceB2285 sourceC2285 difference raw31531; decide +kernel
    rw [ha]
    exact (canonical31531 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2285 + difference 3 0) (sourceB2285 + difference 0 3) sourceC2285) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1671) := by
    have ha : (tripleCharges (sourceA2285 + difference 3 0) (sourceB2285 + difference 0 3) sourceC2285) = raw31532 := by
      apply Matrix.ext; unfold tripleCharges sourceA2285 sourceB2285 sourceC2285 difference raw31532; decide +kernel
    rw [ha]
    exact (canonical31532 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2285 + difference 3 1) (sourceB2285 + difference 1 3) sourceC2285) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2148) := by
    have ha : (tripleCharges (sourceA2285 + difference 3 1) (sourceB2285 + difference 1 3) sourceC2285) = raw31533 := by
      apply Matrix.ext; unfold tripleCharges sourceA2285 sourceB2285 sourceC2285 difference raw31533; decide +kernel
    rw [ha]
    exact (canonical31533 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2285 + difference 3 2) (sourceB2285 + difference 2 3) sourceC2285) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2199) := by
    have ha : (tripleCharges (sourceA2285 + difference 3 2) (sourceB2285 + difference 2 3) sourceC2285) = raw31534 := by
      apply Matrix.ext; unfold tripleCharges sourceA2285 sourceB2285 sourceC2285 difference raw31534; decide +kernel
    rw [ha]
    exact (canonical31534 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2285 + difference 3 4) (sourceB2285 + difference 4 3) sourceC2285) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2202) := by
    have ha : (tripleCharges (sourceA2285 + difference 3 4) (sourceB2285 + difference 4 3) sourceC2285) = raw31535 := by
      apply Matrix.ext; unfold tripleCharges sourceA2285 sourceB2285 sourceC2285 difference raw31535; decide +kernel
    rw [ha]
    exact (canonical31535 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2285 + difference 3 5) (sourceB2285 + difference 5 3) sourceC2285) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2202) := by
    have ha : (tripleCharges (sourceA2285 + difference 3 5) (sourceB2285 + difference 5 3) sourceC2285) = raw31536 := by
      apply Matrix.ext; unfold tripleCharges sourceA2285 sourceB2285 sourceC2285 difference raw31536; decide +kernel
    rw [ha]
    exact (canonical31536 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2285 + difference 4 0) (sourceB2285 + difference 0 4) sourceC2285) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1689) := by
    have ha : (tripleCharges (sourceA2285 + difference 4 0) (sourceB2285 + difference 0 4) sourceC2285) = raw31537 := by
      apply Matrix.ext; unfold tripleCharges sourceA2285 sourceB2285 sourceC2285 difference raw31537; decide +kernel
    rw [ha]
    exact (canonical31537 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2285 + difference 4 1) (sourceB2285 + difference 1 4) sourceC2285) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2164) := by
    have ha : (tripleCharges (sourceA2285 + difference 4 1) (sourceB2285 + difference 1 4) sourceC2285) = raw31538 := by
      apply Matrix.ext; unfold tripleCharges sourceA2285 sourceB2285 sourceC2285 difference raw31538; decide +kernel
    rw [ha]
    exact (canonical31538 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2285 + difference 4 2) (sourceB2285 + difference 2 4) sourceC2285) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2223) := by
    have ha : (tripleCharges (sourceA2285 + difference 4 2) (sourceB2285 + difference 2 4) sourceC2285) = raw31539 := by
      apply Matrix.ext; unfold tripleCharges sourceA2285 sourceB2285 sourceC2285 difference raw31539; decide +kernel
    rw [ha]
    exact (canonical31539 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2285 + difference 4 3) (sourceB2285 + difference 3 4) sourceC2285) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2181) := by
    have ha : (tripleCharges (sourceA2285 + difference 4 3) (sourceB2285 + difference 3 4) sourceC2285) = raw31540 := by
      apply Matrix.ext; unfold tripleCharges sourceA2285 sourceB2285 sourceC2285 difference raw31540; decide +kernel
    rw [ha]
    exact (canonical31540 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2285 + difference 4 5) (sourceB2285 + difference 5 4) sourceC2285) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2224) := by
    have ha : (tripleCharges (sourceA2285 + difference 4 5) (sourceB2285 + difference 5 4) sourceC2285) = raw31541 := by
      apply Matrix.ext; unfold tripleCharges sourceA2285 sourceB2285 sourceC2285 difference raw31541; decide +kernel
    rw [ha]
    exact (canonical31541 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2285 + difference 5 0) (sourceB2285 + difference 0 5) sourceC2285) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1689) := by
    have ha : (tripleCharges (sourceA2285 + difference 5 0) (sourceB2285 + difference 0 5) sourceC2285) = raw31542 := by
      apply Matrix.ext; unfold tripleCharges sourceA2285 sourceB2285 sourceC2285 difference raw31542; decide +kernel
    rw [ha]
    exact (canonical31542 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2285 + difference 5 1) (sourceB2285 + difference 1 5) sourceC2285) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2164) := by
    have ha : (tripleCharges (sourceA2285 + difference 5 1) (sourceB2285 + difference 1 5) sourceC2285) = raw31543 := by
      apply Matrix.ext; unfold tripleCharges sourceA2285 sourceB2285 sourceC2285 difference raw31543; decide +kernel
    rw [ha]
    exact (canonical31543 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2285 + difference 5 2) (sourceB2285 + difference 2 5) sourceC2285) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2223) := by
    have ha : (tripleCharges (sourceA2285 + difference 5 2) (sourceB2285 + difference 2 5) sourceC2285) = raw31544 := by
      apply Matrix.ext; unfold tripleCharges sourceA2285 sourceB2285 sourceC2285 difference raw31544; decide +kernel
    rw [ha]
    exact (canonical31544 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2285 + difference 5 3) (sourceB2285 + difference 3 5) sourceC2285) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2181) := by
    have ha : (tripleCharges (sourceA2285 + difference 5 3) (sourceB2285 + difference 3 5) sourceC2285) = raw31545 := by
      apply Matrix.ext; unfold tripleCharges sourceA2285 sourceB2285 sourceC2285 difference raw31545; decide +kernel
    rw [ha]
    exact (canonical31545 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2285 + difference 5 4) (sourceB2285 + difference 4 5) sourceC2285) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2224) := by
    have ha : (tripleCharges (sourceA2285 + difference 5 4) (sourceB2285 + difference 4 5) sourceC2285) = raw31546 := by
      apply Matrix.ext; unfold tripleCharges sourceA2285 sourceB2285 sourceC2285 difference raw31546; decide +kernel
    rw [ha]
    exact (canonical31546 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2285 sourceB2285 sourceC2285
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2285, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2286 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2286 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC2286 : Charge := ![3, 0, -1, 0, -1, -1]
def sourceForm2286 : Integer.Sparse Master := [(Sum.inr 1792, 1), (Sum.inr 1796, 2), (Sum.inr 1815, 1), (Sum.inr 2029, 1), (Sum.inr 3380, 1), (Sum.inr 4083, -1)]

theorem sourceEq2286 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2286 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2286 + difference 0 1) (sourceB2286 + difference 1 0) sourceC2286) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3380) := by
    have ha : (tripleCharges (sourceA2286 + difference 0 1) (sourceB2286 + difference 1 0) sourceC2286) = raw31547 := by
      apply Matrix.ext; unfold tripleCharges sourceA2286 sourceB2286 sourceC2286 difference raw31547; decide +kernel
    rw [ha]
    exact (canonical31547 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2286 + difference 1 1) (sourceB2286 + difference 1 1) sourceC2286) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2029) := by
    have ha : (tripleCharges (sourceA2286 + difference 1 1) (sourceB2286 + difference 1 1) sourceC2286) = raw31548 := by
      apply Matrix.ext; unfold tripleCharges sourceA2286 sourceB2286 sourceC2286 difference raw31548; decide +kernel
    rw [ha]
    exact (canonical31548 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2286 + difference 2 1) (sourceB2286 + difference 1 2) sourceC2286) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1815) := by
    have ha : (tripleCharges (sourceA2286 + difference 2 1) (sourceB2286 + difference 1 2) sourceC2286) = raw31549 := by
      apply Matrix.ext; unfold tripleCharges sourceA2286 sourceB2286 sourceC2286 difference raw31549; decide +kernel
    rw [ha]
    exact (canonical31549 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2286 + difference 3 1) (sourceB2286 + difference 1 3) sourceC2286) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1792) := by
    have ha : (tripleCharges (sourceA2286 + difference 3 1) (sourceB2286 + difference 1 3) sourceC2286) = raw31550 := by
      apply Matrix.ext; unfold tripleCharges sourceA2286 sourceB2286 sourceC2286 difference raw31550; decide +kernel
    rw [ha]
    exact (canonical31550 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2286 + difference 4 1) (sourceB2286 + difference 1 4) sourceC2286) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1796) := by
    have ha : (tripleCharges (sourceA2286 + difference 4 1) (sourceB2286 + difference 1 4) sourceC2286) = raw31551 := by
      apply Matrix.ext; unfold tripleCharges sourceA2286 sourceB2286 sourceC2286 difference raw31551; decide +kernel
    rw [ha]
    exact (canonical31551 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2286 + difference 5 1) (sourceB2286 + difference 1 5) sourceC2286) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1796) := by
    have ha : (tripleCharges (sourceA2286 + difference 5 1) (sourceB2286 + difference 1 5) sourceC2286) = raw31552 := by
      apply Matrix.ext; unfold tripleCharges sourceA2286 sourceB2286 sourceC2286 difference raw31552; decide +kernel
    rw [ha]
    exact (canonical31552 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2286 + sourceB2286) sourceC2286) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA2286 + sourceB2286) sourceC2286) = raw31553 := by
      apply Matrix.ext; unfold doubleCharges sourceA2286 sourceB2286 sourceC2286 raw31553; decide +kernel
    rw [ha]
    exact (canonical31553 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2286 sourceB2286 sourceC2286
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2286, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2287 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2287 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC2287 : Charge := ![3, 0, -1, 0, -1, -1]
def sourceForm2287 : Integer.Sparse Master := [(Sum.inr 933, 1), (Sum.inr 1815, 1), (Sum.inr 1967, 1), (Sum.inr 2029, 1), (Sum.inr 2057, 2), (Sum.inr 4083, -1)]

theorem sourceEq2287 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2287 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2287 + difference 2 0) (sourceB2287 + difference 0 2) sourceC2287) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 933) := by
    have ha : (tripleCharges (sourceA2287 + difference 2 0) (sourceB2287 + difference 0 2) sourceC2287) = raw31554 := by
      apply Matrix.ext; unfold tripleCharges sourceA2287 sourceB2287 sourceC2287 difference raw31554; decide +kernel
    rw [ha]
    exact (canonical31554 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2287 + difference 2 1) (sourceB2287 + difference 1 2) sourceC2287) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1815) := by
    have ha : (tripleCharges (sourceA2287 + difference 2 1) (sourceB2287 + difference 1 2) sourceC2287) = raw31549 := by
      apply Matrix.ext; unfold tripleCharges sourceA2287 sourceB2287 sourceC2287 difference raw31549; decide +kernel
    rw [ha]
    exact (canonical31549 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2287 + difference 2 2) (sourceB2287 + difference 2 2) sourceC2287) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2029) := by
    have ha : (tripleCharges (sourceA2287 + difference 2 2) (sourceB2287 + difference 2 2) sourceC2287) = raw31548 := by
      apply Matrix.ext; unfold tripleCharges sourceA2287 sourceB2287 sourceC2287 difference raw31548; decide +kernel
    rw [ha]
    exact (canonical31548 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2287 + difference 2 3) (sourceB2287 + difference 3 2) sourceC2287) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1967) := by
    have ha : (tripleCharges (sourceA2287 + difference 2 3) (sourceB2287 + difference 3 2) sourceC2287) = raw31555 := by
      apply Matrix.ext; unfold tripleCharges sourceA2287 sourceB2287 sourceC2287 difference raw31555; decide +kernel
    rw [ha]
    exact (canonical31555 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2287 + difference 2 4) (sourceB2287 + difference 4 2) sourceC2287) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2057) := by
    have ha : (tripleCharges (sourceA2287 + difference 2 4) (sourceB2287 + difference 4 2) sourceC2287) = raw31556 := by
      apply Matrix.ext; unfold tripleCharges sourceA2287 sourceB2287 sourceC2287 difference raw31556; decide +kernel
    rw [ha]
    exact (canonical31556 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2287 + difference 2 5) (sourceB2287 + difference 5 2) sourceC2287) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2057) := by
    have ha : (tripleCharges (sourceA2287 + difference 2 5) (sourceB2287 + difference 5 2) sourceC2287) = raw31557 := by
      apply Matrix.ext; unfold tripleCharges sourceA2287 sourceB2287 sourceC2287 difference raw31557; decide +kernel
    rw [ha]
    exact (canonical31557 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2287 + sourceB2287) sourceC2287) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA2287 + sourceB2287) sourceC2287) = raw31553 := by
      apply Matrix.ext; unfold doubleCharges sourceA2287 sourceB2287 sourceC2287 raw31553; decide +kernel
    rw [ha]
    exact (canonical31553 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2287 sourceB2287 sourceC2287
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2287, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2288 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2288 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC2288 : Charge := ![3, 0, -1, 0, -1, -1]
def sourceForm2288 : Integer.Sparse Master := [(Sum.inr 907, 1), (Sum.inr 1792, 1), (Sum.inr 1975, 1), (Sum.inr 2020, 2), (Sum.inr 2029, 1), (Sum.inr 4083, -1)]

theorem sourceEq2288 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2288 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2288 + difference 3 0) (sourceB2288 + difference 0 3) sourceC2288) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 907) := by
    have ha : (tripleCharges (sourceA2288 + difference 3 0) (sourceB2288 + difference 0 3) sourceC2288) = raw31558 := by
      apply Matrix.ext; unfold tripleCharges sourceA2288 sourceB2288 sourceC2288 difference raw31558; decide +kernel
    rw [ha]
    exact (canonical31558 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2288 + difference 3 1) (sourceB2288 + difference 1 3) sourceC2288) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1792) := by
    have ha : (tripleCharges (sourceA2288 + difference 3 1) (sourceB2288 + difference 1 3) sourceC2288) = raw31550 := by
      apply Matrix.ext; unfold tripleCharges sourceA2288 sourceB2288 sourceC2288 difference raw31550; decide +kernel
    rw [ha]
    exact (canonical31550 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2288 + difference 3 2) (sourceB2288 + difference 2 3) sourceC2288) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1975) := by
    have ha : (tripleCharges (sourceA2288 + difference 3 2) (sourceB2288 + difference 2 3) sourceC2288) = raw31559 := by
      apply Matrix.ext; unfold tripleCharges sourceA2288 sourceB2288 sourceC2288 difference raw31559; decide +kernel
    rw [ha]
    exact (canonical31559 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2288 + difference 3 3) (sourceB2288 + difference 3 3) sourceC2288) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2029) := by
    have ha : (tripleCharges (sourceA2288 + difference 3 3) (sourceB2288 + difference 3 3) sourceC2288) = raw31548 := by
      apply Matrix.ext; unfold tripleCharges sourceA2288 sourceB2288 sourceC2288 difference raw31548; decide +kernel
    rw [ha]
    exact (canonical31548 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2288 + difference 3 4) (sourceB2288 + difference 4 3) sourceC2288) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2020) := by
    have ha : (tripleCharges (sourceA2288 + difference 3 4) (sourceB2288 + difference 4 3) sourceC2288) = raw31560 := by
      apply Matrix.ext; unfold tripleCharges sourceA2288 sourceB2288 sourceC2288 difference raw31560; decide +kernel
    rw [ha]
    exact (canonical31560 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2288 + difference 3 5) (sourceB2288 + difference 5 3) sourceC2288) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2020) := by
    have ha : (tripleCharges (sourceA2288 + difference 3 5) (sourceB2288 + difference 5 3) sourceC2288) = raw31561 := by
      apply Matrix.ext; unfold tripleCharges sourceA2288 sourceB2288 sourceC2288 difference raw31561; decide +kernel
    rw [ha]
    exact (canonical31561 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2288 + sourceB2288) sourceC2288) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA2288 + sourceB2288) sourceC2288) = raw31553 := by
      apply Matrix.ext; unfold doubleCharges sourceA2288 sourceB2288 sourceC2288 raw31553; decide +kernel
    rw [ha]
    exact (canonical31553 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2288 sourceB2288 sourceC2288
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2288, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2289 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2289 : Charge := ![3, 0, -1, 0, -1, -1]
def sourceC2289 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceForm2289 : Integer.Sparse Master := [(Sum.inr 4201, 1), (Sum.inr 4204, 2), (Sum.inr 4224, 1), (Sum.inr 4256, 1), (Sum.inr 4635, 1), (Sum.inr 4637, 2), (Sum.inr 4654, 1), (Sum.inr 4706, 2), (Sum.inr 4717, 1), (Sum.inr 4732, 1), (Sum.inr 4767, 1), (Sum.inr 4769, 2), (Sum.inr 4802, 2), (Sum.inr 4804, 2), (Sum.inr 4811, 1), (Sum.inr 4835, 2), (Sum.inr 4888, 2), (Sum.inr 5356, 1), (Sum.inr 5393, 1), (Sum.inr 5418, 1), (Sum.inr 5434, 2)]

theorem sourceEq2289 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2289 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2289 + difference 0 1) (sourceB2289 + difference 1 0) sourceC2289) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5356) := by
    have ha : (tripleCharges (sourceA2289 + difference 0 1) (sourceB2289 + difference 1 0) sourceC2289) = raw31562 := by
      apply Matrix.ext; unfold tripleCharges sourceA2289 sourceB2289 sourceC2289 difference raw31562; decide +kernel
    rw [ha]
    exact (canonical31562 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2289 + difference 0 2) (sourceB2289 + difference 2 0) sourceC2289) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5418) := by
    have ha : (tripleCharges (sourceA2289 + difference 0 2) (sourceB2289 + difference 2 0) sourceC2289) = raw31563 := by
      apply Matrix.ext; unfold tripleCharges sourceA2289 sourceB2289 sourceC2289 difference raw31563; decide +kernel
    rw [ha]
    exact (canonical31563 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2289 + difference 0 3) (sourceB2289 + difference 3 0) sourceC2289) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5393) := by
    have ha : (tripleCharges (sourceA2289 + difference 0 3) (sourceB2289 + difference 3 0) sourceC2289) = raw31564 := by
      apply Matrix.ext; unfold tripleCharges sourceA2289 sourceB2289 sourceC2289 difference raw31564; decide +kernel
    rw [ha]
    exact (canonical31564 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2289 + difference 0 4) (sourceB2289 + difference 4 0) sourceC2289) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA2289 + difference 0 4) (sourceB2289 + difference 4 0) sourceC2289) = raw11315 := by
      apply Matrix.ext; unfold tripleCharges sourceA2289 sourceB2289 sourceC2289 difference raw11315; decide +kernel
    rw [ha]
    exact (canonical11315 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2289 + difference 0 5) (sourceB2289 + difference 5 0) sourceC2289) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA2289 + difference 0 5) (sourceB2289 + difference 5 0) sourceC2289) = raw31565 := by
      apply Matrix.ext; unfold tripleCharges sourceA2289 sourceB2289 sourceC2289 difference raw31565; decide +kernel
    rw [ha]
    exact (canonical31565 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2289 + difference 1 0) (sourceB2289 + difference 0 1) sourceC2289) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4256) := by
    have ha : (tripleCharges (sourceA2289 + difference 1 0) (sourceB2289 + difference 0 1) sourceC2289) = raw11335 := by
      apply Matrix.ext; unfold tripleCharges sourceA2289 sourceB2289 sourceC2289 difference raw11335; decide +kernel
    rw [ha]
    exact (canonical11335 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2289 + difference 1 2) (sourceB2289 + difference 2 1) sourceC2289) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4811) := by
    have ha : (tripleCharges (sourceA2289 + difference 1 2) (sourceB2289 + difference 2 1) sourceC2289) = raw11337 := by
      apply Matrix.ext; unfold tripleCharges sourceA2289 sourceB2289 sourceC2289 difference raw11337; decide +kernel
    rw [ha]
    exact (canonical11337 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2289 + difference 1 3) (sourceB2289 + difference 3 1) sourceC2289) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4732) := by
    have ha : (tripleCharges (sourceA2289 + difference 1 3) (sourceB2289 + difference 3 1) sourceC2289) = raw11338 := by
      apply Matrix.ext; unfold tripleCharges sourceA2289 sourceB2289 sourceC2289 difference raw11338; decide +kernel
    rw [ha]
    exact (canonical11338 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2289 + difference 1 4) (sourceB2289 + difference 4 1) sourceC2289) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA2289 + difference 1 4) (sourceB2289 + difference 4 1) sourceC2289) = raw14329 := by
      apply Matrix.ext; unfold tripleCharges sourceA2289 sourceB2289 sourceC2289 difference raw14329; decide +kernel
    rw [ha]
    exact (canonical14329 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2289 + difference 1 5) (sourceB2289 + difference 5 1) sourceC2289) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA2289 + difference 1 5) (sourceB2289 + difference 5 1) sourceC2289) = raw11339 := by
      apply Matrix.ext; unfold tripleCharges sourceA2289 sourceB2289 sourceC2289 difference raw11339; decide +kernel
    rw [ha]
    exact (canonical11339 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2289 + difference 2 0) (sourceB2289 + difference 0 2) sourceC2289) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4224) := by
    have ha : (tripleCharges (sourceA2289 + difference 2 0) (sourceB2289 + difference 0 2) sourceC2289) = raw31566 := by
      apply Matrix.ext; unfold tripleCharges sourceA2289 sourceB2289 sourceC2289 difference raw31566; decide +kernel
    rw [ha]
    exact (canonical31566 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2289 + difference 2 1) (sourceB2289 + difference 1 2) sourceC2289) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4654) := by
    have ha : (tripleCharges (sourceA2289 + difference 2 1) (sourceB2289 + difference 1 2) sourceC2289) = raw31567 := by
      apply Matrix.ext; unfold tripleCharges sourceA2289 sourceB2289 sourceC2289 difference raw31567; decide +kernel
    rw [ha]
    exact (canonical31567 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2289 + difference 2 3) (sourceB2289 + difference 3 2) sourceC2289) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4717) := by
    have ha : (tripleCharges (sourceA2289 + difference 2 3) (sourceB2289 + difference 3 2) sourceC2289) = raw31568 := by
      apply Matrix.ext; unfold tripleCharges sourceA2289 sourceB2289 sourceC2289 difference raw31568; decide +kernel
    rw [ha]
    exact (canonical31568 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2289 + difference 2 4) (sourceB2289 + difference 4 2) sourceC2289) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4835) := by
    have ha : (tripleCharges (sourceA2289 + difference 2 4) (sourceB2289 + difference 4 2) sourceC2289) = raw11326 := by
      apply Matrix.ext; unfold tripleCharges sourceA2289 sourceB2289 sourceC2289 difference raw11326; decide +kernel
    rw [ha]
    exact (canonical11326 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2289 + difference 2 5) (sourceB2289 + difference 5 2) sourceC2289) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4835) := by
    have ha : (tripleCharges (sourceA2289 + difference 2 5) (sourceB2289 + difference 5 2) sourceC2289) = raw31569 := by
      apply Matrix.ext; unfold tripleCharges sourceA2289 sourceB2289 sourceC2289 difference raw31569; decide +kernel
    rw [ha]
    exact (canonical31569 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2289 + difference 3 0) (sourceB2289 + difference 0 3) sourceC2289) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4201) := by
    have ha : (tripleCharges (sourceA2289 + difference 3 0) (sourceB2289 + difference 0 3) sourceC2289) = raw31570 := by
      apply Matrix.ext; unfold tripleCharges sourceA2289 sourceB2289 sourceC2289 difference raw31570; decide +kernel
    rw [ha]
    exact (canonical31570 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2289 + difference 3 1) (sourceB2289 + difference 1 3) sourceC2289) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4635) := by
    have ha : (tripleCharges (sourceA2289 + difference 3 1) (sourceB2289 + difference 1 3) sourceC2289) = raw31571 := by
      apply Matrix.ext; unfold tripleCharges sourceA2289 sourceB2289 sourceC2289 difference raw31571; decide +kernel
    rw [ha]
    exact (canonical31571 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2289 + difference 3 2) (sourceB2289 + difference 2 3) sourceC2289) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4767) := by
    have ha : (tripleCharges (sourceA2289 + difference 3 2) (sourceB2289 + difference 2 3) sourceC2289) = raw31572 := by
      apply Matrix.ext; unfold tripleCharges sourceA2289 sourceB2289 sourceC2289 difference raw31572; decide +kernel
    rw [ha]
    exact (canonical31572 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2289 + difference 3 4) (sourceB2289 + difference 4 3) sourceC2289) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA2289 + difference 3 4) (sourceB2289 + difference 4 3) sourceC2289) = raw11331 := by
      apply Matrix.ext; unfold tripleCharges sourceA2289 sourceB2289 sourceC2289 difference raw11331; decide +kernel
    rw [ha]
    exact (canonical11331 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2289 + difference 3 5) (sourceB2289 + difference 5 3) sourceC2289) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA2289 + difference 3 5) (sourceB2289 + difference 5 3) sourceC2289) = raw14326 := by
      apply Matrix.ext; unfold tripleCharges sourceA2289 sourceB2289 sourceC2289 difference raw14326; decide +kernel
    rw [ha]
    exact (canonical14326 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2289 + difference 4 0) (sourceB2289 + difference 0 4) sourceC2289) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4204) := by
    have ha : (tripleCharges (sourceA2289 + difference 4 0) (sourceB2289 + difference 0 4) sourceC2289) = raw31573 := by
      apply Matrix.ext; unfold tripleCharges sourceA2289 sourceB2289 sourceC2289 difference raw31573; decide +kernel
    rw [ha]
    exact (canonical31573 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2289 + difference 4 1) (sourceB2289 + difference 1 4) sourceC2289) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4637) := by
    have ha : (tripleCharges (sourceA2289 + difference 4 1) (sourceB2289 + difference 1 4) sourceC2289) = raw31574 := by
      apply Matrix.ext; unfold tripleCharges sourceA2289 sourceB2289 sourceC2289 difference raw31574; decide +kernel
    rw [ha]
    exact (canonical31574 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2289 + difference 4 2) (sourceB2289 + difference 2 4) sourceC2289) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4769) := by
    have ha : (tripleCharges (sourceA2289 + difference 4 2) (sourceB2289 + difference 2 4) sourceC2289) = raw31575 := by
      apply Matrix.ext; unfold tripleCharges sourceA2289 sourceB2289 sourceC2289 difference raw31575; decide +kernel
    rw [ha]
    exact (canonical31575 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2289 + difference 4 3) (sourceB2289 + difference 3 4) sourceC2289) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4706) := by
    have ha : (tripleCharges (sourceA2289 + difference 4 3) (sourceB2289 + difference 3 4) sourceC2289) = raw31576 := by
      apply Matrix.ext; unfold tripleCharges sourceA2289 sourceB2289 sourceC2289 difference raw31576; decide +kernel
    rw [ha]
    exact (canonical31576 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2289 + difference 4 5) (sourceB2289 + difference 5 4) sourceC2289) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA2289 + difference 4 5) (sourceB2289 + difference 5 4) sourceC2289) = raw31577 := by
      apply Matrix.ext; unfold tripleCharges sourceA2289 sourceB2289 sourceC2289 difference raw31577; decide +kernel
    rw [ha]
    exact (canonical31577 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2289 + difference 5 0) (sourceB2289 + difference 0 5) sourceC2289) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4204) := by
    have ha : (tripleCharges (sourceA2289 + difference 5 0) (sourceB2289 + difference 0 5) sourceC2289) = raw31578 := by
      apply Matrix.ext; unfold tripleCharges sourceA2289 sourceB2289 sourceC2289 difference raw31578; decide +kernel
    rw [ha]
    exact (canonical31578 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2289 + difference 5 1) (sourceB2289 + difference 1 5) sourceC2289) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4637) := by
    have ha : (tripleCharges (sourceA2289 + difference 5 1) (sourceB2289 + difference 1 5) sourceC2289) = raw31579 := by
      apply Matrix.ext; unfold tripleCharges sourceA2289 sourceB2289 sourceC2289 difference raw31579; decide +kernel
    rw [ha]
    exact (canonical31579 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2289 + difference 5 2) (sourceB2289 + difference 2 5) sourceC2289) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4769) := by
    have ha : (tripleCharges (sourceA2289 + difference 5 2) (sourceB2289 + difference 2 5) sourceC2289) = raw31580 := by
      apply Matrix.ext; unfold tripleCharges sourceA2289 sourceB2289 sourceC2289 difference raw31580; decide +kernel
    rw [ha]
    exact (canonical31580 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2289 + difference 5 3) (sourceB2289 + difference 3 5) sourceC2289) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4706) := by
    have ha : (tripleCharges (sourceA2289 + difference 5 3) (sourceB2289 + difference 3 5) sourceC2289) = raw31581 := by
      apply Matrix.ext; unfold tripleCharges sourceA2289 sourceB2289 sourceC2289 difference raw31581; decide +kernel
    rw [ha]
    exact (canonical31581 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2289 + difference 5 4) (sourceB2289 + difference 4 5) sourceC2289) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA2289 + difference 5 4) (sourceB2289 + difference 4 5) sourceC2289) = raw11341 := by
      apply Matrix.ext; unfold tripleCharges sourceA2289 sourceB2289 sourceC2289 difference raw11341; decide +kernel
    rw [ha]
    exact (canonical11341 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2289 sourceB2289 sourceC2289
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2289, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2290 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2290 : Charge := ![3, 0, -1, 0, -1, -1]
def sourceC2290 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceForm2290 : Integer.Sparse Master := [(Sum.inr 704, 1), (Sum.inr 707, 2), (Sum.inr 725, 1), (Sum.inr 790, 1), (Sum.inr 1764, 1), (Sum.inr 1766, 2), (Sum.inr 1782, 1), (Sum.inr 1860, 2), (Sum.inr 1871, 1), (Sum.inr 1901, 1), (Sum.inr 1967, 1), (Sum.inr 1969, 2), (Sum.inr 2020, 2), (Sum.inr 2022, 2), (Sum.inr 2029, 1), (Sum.inr 2054, 2), (Sum.inr 2244, 2), (Sum.inr 3694, 1), (Sum.inr 3779, 1), (Sum.inr 3824, 1), (Sum.inr 3852, 2)]

theorem sourceEq2290 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2290 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2290 + difference 0 1) (sourceB2290 + difference 1 0) sourceC2290) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3694) := by
    have ha : (tripleCharges (sourceA2290 + difference 0 1) (sourceB2290 + difference 1 0) sourceC2290) = raw31582 := by
      apply Matrix.ext; unfold tripleCharges sourceA2290 sourceB2290 sourceC2290 difference raw31582; decide +kernel
    rw [ha]
    exact (canonical31582 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2290 + difference 0 2) (sourceB2290 + difference 2 0) sourceC2290) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3824) := by
    have ha : (tripleCharges (sourceA2290 + difference 0 2) (sourceB2290 + difference 2 0) sourceC2290) = raw31583 := by
      apply Matrix.ext; unfold tripleCharges sourceA2290 sourceB2290 sourceC2290 difference raw31583; decide +kernel
    rw [ha]
    exact (canonical31583 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2290 + difference 0 3) (sourceB2290 + difference 3 0) sourceC2290) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3779) := by
    have ha : (tripleCharges (sourceA2290 + difference 0 3) (sourceB2290 + difference 3 0) sourceC2290) = raw31584 := by
      apply Matrix.ext; unfold tripleCharges sourceA2290 sourceB2290 sourceC2290 difference raw31584; decide +kernel
    rw [ha]
    exact (canonical31584 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2290 + difference 0 4) (sourceB2290 + difference 4 0) sourceC2290) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3852) := by
    have ha : (tripleCharges (sourceA2290 + difference 0 4) (sourceB2290 + difference 4 0) sourceC2290) = raw11345 := by
      apply Matrix.ext; unfold tripleCharges sourceA2290 sourceB2290 sourceC2290 difference raw11345; decide +kernel
    rw [ha]
    exact (canonical11345 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2290 + difference 0 5) (sourceB2290 + difference 5 0) sourceC2290) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3852) := by
    have ha : (tripleCharges (sourceA2290 + difference 0 5) (sourceB2290 + difference 5 0) sourceC2290) = raw31585 := by
      apply Matrix.ext; unfold tripleCharges sourceA2290 sourceB2290 sourceC2290 difference raw31585; decide +kernel
    rw [ha]
    exact (canonical31585 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2290 + difference 1 0) (sourceB2290 + difference 0 1) sourceC2290) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 790) := by
    have ha : (tripleCharges (sourceA2290 + difference 1 0) (sourceB2290 + difference 0 1) sourceC2290) = raw11365 := by
      apply Matrix.ext; unfold tripleCharges sourceA2290 sourceB2290 sourceC2290 difference raw11365; decide +kernel
    rw [ha]
    exact (canonical11365 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2290 + difference 1 2) (sourceB2290 + difference 2 1) sourceC2290) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2029) := by
    have ha : (tripleCharges (sourceA2290 + difference 1 2) (sourceB2290 + difference 2 1) sourceC2290) = raw11367 := by
      apply Matrix.ext; unfold tripleCharges sourceA2290 sourceB2290 sourceC2290 difference raw11367; decide +kernel
    rw [ha]
    exact (canonical11367 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2290 + difference 1 3) (sourceB2290 + difference 3 1) sourceC2290) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1901) := by
    have ha : (tripleCharges (sourceA2290 + difference 1 3) (sourceB2290 + difference 3 1) sourceC2290) = raw11368 := by
      apply Matrix.ext; unfold tripleCharges sourceA2290 sourceB2290 sourceC2290 difference raw11368; decide +kernel
    rw [ha]
    exact (canonical11368 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2290 + difference 1 4) (sourceB2290 + difference 4 1) sourceC2290) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2244) := by
    have ha : (tripleCharges (sourceA2290 + difference 1 4) (sourceB2290 + difference 4 1) sourceC2290) = raw31586 := by
      apply Matrix.ext; unfold tripleCharges sourceA2290 sourceB2290 sourceC2290 difference raw31586; decide +kernel
    rw [ha]
    exact (canonical31586 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2290 + difference 1 5) (sourceB2290 + difference 5 1) sourceC2290) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2244) := by
    have ha : (tripleCharges (sourceA2290 + difference 1 5) (sourceB2290 + difference 5 1) sourceC2290) = raw11369 := by
      apply Matrix.ext; unfold tripleCharges sourceA2290 sourceB2290 sourceC2290 difference raw11369; decide +kernel
    rw [ha]
    exact (canonical11369 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2290 + difference 2 0) (sourceB2290 + difference 0 2) sourceC2290) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 725) := by
    have ha : (tripleCharges (sourceA2290 + difference 2 0) (sourceB2290 + difference 0 2) sourceC2290) = raw31587 := by
      apply Matrix.ext; unfold tripleCharges sourceA2290 sourceB2290 sourceC2290 difference raw31587; decide +kernel
    rw [ha]
    exact (canonical31587 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2290 + difference 2 1) (sourceB2290 + difference 1 2) sourceC2290) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1782) := by
    have ha : (tripleCharges (sourceA2290 + difference 2 1) (sourceB2290 + difference 1 2) sourceC2290) = raw31588 := by
      apply Matrix.ext; unfold tripleCharges sourceA2290 sourceB2290 sourceC2290 difference raw31588; decide +kernel
    rw [ha]
    exact (canonical31588 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2290 + difference 2 3) (sourceB2290 + difference 3 2) sourceC2290) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1871) := by
    have ha : (tripleCharges (sourceA2290 + difference 2 3) (sourceB2290 + difference 3 2) sourceC2290) = raw31589 := by
      apply Matrix.ext; unfold tripleCharges sourceA2290 sourceB2290 sourceC2290 difference raw31589; decide +kernel
    rw [ha]
    exact (canonical31589 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2290 + difference 2 4) (sourceB2290 + difference 4 2) sourceC2290) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2054) := by
    have ha : (tripleCharges (sourceA2290 + difference 2 4) (sourceB2290 + difference 4 2) sourceC2290) = raw11356 := by
      apply Matrix.ext; unfold tripleCharges sourceA2290 sourceB2290 sourceC2290 difference raw11356; decide +kernel
    rw [ha]
    exact (canonical11356 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2290 + difference 2 5) (sourceB2290 + difference 5 2) sourceC2290) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2054) := by
    have ha : (tripleCharges (sourceA2290 + difference 2 5) (sourceB2290 + difference 5 2) sourceC2290) = raw31590 := by
      apply Matrix.ext; unfold tripleCharges sourceA2290 sourceB2290 sourceC2290 difference raw31590; decide +kernel
    rw [ha]
    exact (canonical31590 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2290 + difference 3 0) (sourceB2290 + difference 0 3) sourceC2290) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 704) := by
    have ha : (tripleCharges (sourceA2290 + difference 3 0) (sourceB2290 + difference 0 3) sourceC2290) = raw31591 := by
      apply Matrix.ext; unfold tripleCharges sourceA2290 sourceB2290 sourceC2290 difference raw31591; decide +kernel
    rw [ha]
    exact (canonical31591 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2290 + difference 3 1) (sourceB2290 + difference 1 3) sourceC2290) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1764) := by
    have ha : (tripleCharges (sourceA2290 + difference 3 1) (sourceB2290 + difference 1 3) sourceC2290) = raw31592 := by
      apply Matrix.ext; unfold tripleCharges sourceA2290 sourceB2290 sourceC2290 difference raw31592; decide +kernel
    rw [ha]
    exact (canonical31592 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2290 + difference 3 2) (sourceB2290 + difference 2 3) sourceC2290) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1967) := by
    have ha : (tripleCharges (sourceA2290 + difference 3 2) (sourceB2290 + difference 2 3) sourceC2290) = raw31593 := by
      apply Matrix.ext; unfold tripleCharges sourceA2290 sourceB2290 sourceC2290 difference raw31593; decide +kernel
    rw [ha]
    exact (canonical31593 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2290 + difference 3 4) (sourceB2290 + difference 4 3) sourceC2290) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2020) := by
    have ha : (tripleCharges (sourceA2290 + difference 3 4) (sourceB2290 + difference 4 3) sourceC2290) = raw11361 := by
      apply Matrix.ext; unfold tripleCharges sourceA2290 sourceB2290 sourceC2290 difference raw11361; decide +kernel
    rw [ha]
    exact (canonical11361 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2290 + difference 3 5) (sourceB2290 + difference 5 3) sourceC2290) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2020) := by
    have ha : (tripleCharges (sourceA2290 + difference 3 5) (sourceB2290 + difference 5 3) sourceC2290) = raw31594 := by
      apply Matrix.ext; unfold tripleCharges sourceA2290 sourceB2290 sourceC2290 difference raw31594; decide +kernel
    rw [ha]
    exact (canonical31594 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2290 + difference 4 0) (sourceB2290 + difference 0 4) sourceC2290) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 707) := by
    have ha : (tripleCharges (sourceA2290 + difference 4 0) (sourceB2290 + difference 0 4) sourceC2290) = raw31595 := by
      apply Matrix.ext; unfold tripleCharges sourceA2290 sourceB2290 sourceC2290 difference raw31595; decide +kernel
    rw [ha]
    exact (canonical31595 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2290 + difference 4 1) (sourceB2290 + difference 1 4) sourceC2290) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1766) := by
    have ha : (tripleCharges (sourceA2290 + difference 4 1) (sourceB2290 + difference 1 4) sourceC2290) = raw31596 := by
      apply Matrix.ext; unfold tripleCharges sourceA2290 sourceB2290 sourceC2290 difference raw31596; decide +kernel
    rw [ha]
    exact (canonical31596 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2290 + difference 4 2) (sourceB2290 + difference 2 4) sourceC2290) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1969) := by
    have ha : (tripleCharges (sourceA2290 + difference 4 2) (sourceB2290 + difference 2 4) sourceC2290) = raw31597 := by
      apply Matrix.ext; unfold tripleCharges sourceA2290 sourceB2290 sourceC2290 difference raw31597; decide +kernel
    rw [ha]
    exact (canonical31597 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2290 + difference 4 3) (sourceB2290 + difference 3 4) sourceC2290) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1860) := by
    have ha : (tripleCharges (sourceA2290 + difference 4 3) (sourceB2290 + difference 3 4) sourceC2290) = raw31598 := by
      apply Matrix.ext; unfold tripleCharges sourceA2290 sourceB2290 sourceC2290 difference raw31598; decide +kernel
    rw [ha]
    exact (canonical31598 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2290 + difference 4 5) (sourceB2290 + difference 5 4) sourceC2290) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2022) := by
    have ha : (tripleCharges (sourceA2290 + difference 4 5) (sourceB2290 + difference 5 4) sourceC2290) = raw31599 := by
      apply Matrix.ext; unfold tripleCharges sourceA2290 sourceB2290 sourceC2290 difference raw31599; decide +kernel
    rw [ha]
    exact (canonical31599 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2290 + difference 5 0) (sourceB2290 + difference 0 5) sourceC2290) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 707) := by
    have ha : (tripleCharges (sourceA2290 + difference 5 0) (sourceB2290 + difference 0 5) sourceC2290) = raw31600 := by
      apply Matrix.ext; unfold tripleCharges sourceA2290 sourceB2290 sourceC2290 difference raw31600; decide +kernel
    rw [ha]
    exact (canonical31600 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2290 + difference 5 1) (sourceB2290 + difference 1 5) sourceC2290) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1766) := by
    have ha : (tripleCharges (sourceA2290 + difference 5 1) (sourceB2290 + difference 1 5) sourceC2290) = raw31601 := by
      apply Matrix.ext; unfold tripleCharges sourceA2290 sourceB2290 sourceC2290 difference raw31601; decide +kernel
    rw [ha]
    exact (canonical31601 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2290 + difference 5 2) (sourceB2290 + difference 2 5) sourceC2290) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1969) := by
    have ha : (tripleCharges (sourceA2290 + difference 5 2) (sourceB2290 + difference 2 5) sourceC2290) = raw31602 := by
      apply Matrix.ext; unfold tripleCharges sourceA2290 sourceB2290 sourceC2290 difference raw31602; decide +kernel
    rw [ha]
    exact (canonical31602 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2290 + difference 5 3) (sourceB2290 + difference 3 5) sourceC2290) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1860) := by
    have ha : (tripleCharges (sourceA2290 + difference 5 3) (sourceB2290 + difference 3 5) sourceC2290) = raw31603 := by
      apply Matrix.ext; unfold tripleCharges sourceA2290 sourceB2290 sourceC2290 difference raw31603; decide +kernel
    rw [ha]
    exact (canonical31603 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2290 + difference 5 4) (sourceB2290 + difference 4 5) sourceC2290) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2022) := by
    have ha : (tripleCharges (sourceA2290 + difference 5 4) (sourceB2290 + difference 4 5) sourceC2290) = raw11371 := by
      apply Matrix.ext; unfold tripleCharges sourceA2290 sourceB2290 sourceC2290 difference raw11371; decide +kernel
    rw [ha]
    exact (canonical11371 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2290 sourceB2290 sourceC2290
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2290, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2291 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceB2291 : Charge := ![3, 0, -1, 0, -1, -1]
def sourceC2291 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceForm2291 : Integer.Sparse Master := [(Sum.inr 4415, 1), (Sum.inr 4419, 2), (Sum.inr 4427, 1), (Sum.inr 4487, 1), (Sum.inr 4732, 1), (Sum.inr 4745, 2), (Sum.inr 4750, 1), (Sum.inr 4782, 2), (Sum.inr 4785, 1), (Sum.inr 4795, 2), (Sum.inr 4810, 2), (Sum.inr 4811, 1), (Sum.inr 4821, 2), (Sum.inr 4825, 1), (Sum.inr 4846, 2), (Sum.inr 4856, 2), (Sum.inr 4875, 1), (Sum.inr 5081, 1), (Sum.inr 5130, 1), (Sum.inr 5152, 2), (Sum.inr 5177, 1)]

theorem sourceEq2291 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2291 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2291 + difference 0 1) (sourceB2291 + difference 1 0) sourceC2291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5081) := by
    have ha : (tripleCharges (sourceA2291 + difference 0 1) (sourceB2291 + difference 1 0) sourceC2291) = raw29683 := by
      apply Matrix.ext; unfold tripleCharges sourceA2291 sourceB2291 sourceC2291 difference raw29683; decide +kernel
    rw [ha]
    exact (canonical29683 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2291 + difference 0 2) (sourceB2291 + difference 2 0) sourceC2291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5177) := by
    have ha : (tripleCharges (sourceA2291 + difference 0 2) (sourceB2291 + difference 2 0) sourceC2291) = raw29586 := by
      apply Matrix.ext; unfold tripleCharges sourceA2291 sourceB2291 sourceC2291 difference raw29586; decide +kernel
    rw [ha]
    exact (canonical29586 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2291 + difference 0 3) (sourceB2291 + difference 3 0) sourceC2291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5130) := by
    have ha : (tripleCharges (sourceA2291 + difference 0 3) (sourceB2291 + difference 3 0) sourceC2291) = raw29684 := by
      apply Matrix.ext; unfold tripleCharges sourceA2291 sourceB2291 sourceC2291 difference raw29684; decide +kernel
    rw [ha]
    exact (canonical29684 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2291 + difference 0 4) (sourceB2291 + difference 4 0) sourceC2291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5152) := by
    have ha : (tripleCharges (sourceA2291 + difference 0 4) (sourceB2291 + difference 4 0) sourceC2291) = raw29576 := by
      apply Matrix.ext; unfold tripleCharges sourceA2291 sourceB2291 sourceC2291 difference raw29576; decide +kernel
    rw [ha]
    exact (canonical29576 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2291 + difference 0 5) (sourceB2291 + difference 5 0) sourceC2291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5152) := by
    have ha : (tripleCharges (sourceA2291 + difference 0 5) (sourceB2291 + difference 5 0) sourceC2291) = raw29685 := by
      apply Matrix.ext; unfold tripleCharges sourceA2291 sourceB2291 sourceC2291 difference raw29685; decide +kernel
    rw [ha]
    exact (canonical29685 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2291 + difference 1 0) (sourceB2291 + difference 0 1) sourceC2291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4487) := by
    have ha : (tripleCharges (sourceA2291 + difference 1 0) (sourceB2291 + difference 0 1) sourceC2291) = raw31237 := by
      apply Matrix.ext; unfold tripleCharges sourceA2291 sourceB2291 sourceC2291 difference raw31237; decide +kernel
    rw [ha]
    exact (canonical31237 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2291 + difference 1 2) (sourceB2291 + difference 2 1) sourceC2291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4875) := by
    have ha : (tripleCharges (sourceA2291 + difference 1 2) (sourceB2291 + difference 2 1) sourceC2291) = raw29678 := by
      apply Matrix.ext; unfold tripleCharges sourceA2291 sourceB2291 sourceC2291 difference raw29678; decide +kernel
    rw [ha]
    exact (canonical29678 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2291 + difference 1 3) (sourceB2291 + difference 3 1) sourceC2291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4825) := by
    have ha : (tripleCharges (sourceA2291 + difference 1 3) (sourceB2291 + difference 3 1) sourceC2291) = raw31238 := by
      apply Matrix.ext; unfold tripleCharges sourceA2291 sourceB2291 sourceC2291 difference raw31238; decide +kernel
    rw [ha]
    exact (canonical31238 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2291 + difference 1 4) (sourceB2291 + difference 4 1) sourceC2291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4856) := by
    have ha : (tripleCharges (sourceA2291 + difference 1 4) (sourceB2291 + difference 4 1) sourceC2291) = raw30037 := by
      apply Matrix.ext; unfold tripleCharges sourceA2291 sourceB2291 sourceC2291 difference raw30037; decide +kernel
    rw [ha]
    exact (canonical30037 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2291 + difference 1 5) (sourceB2291 + difference 5 1) sourceC2291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4856) := by
    have ha : (tripleCharges (sourceA2291 + difference 1 5) (sourceB2291 + difference 5 1) sourceC2291) = raw31068 := by
      apply Matrix.ext; unfold tripleCharges sourceA2291 sourceB2291 sourceC2291 difference raw31068; decide +kernel
    rw [ha]
    exact (canonical31068 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2291 + difference 2 0) (sourceB2291 + difference 0 2) sourceC2291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4427) := by
    have ha : (tripleCharges (sourceA2291 + difference 2 0) (sourceB2291 + difference 0 2) sourceC2291) = raw31604 := by
      apply Matrix.ext; unfold tripleCharges sourceA2291 sourceB2291 sourceC2291 difference raw31604; decide +kernel
    rw [ha]
    exact (canonical31604 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2291 + difference 2 1) (sourceB2291 + difference 1 2) sourceC2291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4750) := by
    have ha : (tripleCharges (sourceA2291 + difference 2 1) (sourceB2291 + difference 1 2) sourceC2291) = raw30541 := by
      apply Matrix.ext; unfold tripleCharges sourceA2291 sourceB2291 sourceC2291 difference raw30541; decide +kernel
    rw [ha]
    exact (canonical30541 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2291 + difference 2 3) (sourceB2291 + difference 3 2) sourceC2291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4785) := by
    have ha : (tripleCharges (sourceA2291 + difference 2 3) (sourceB2291 + difference 3 2) sourceC2291) = raw31605 := by
      apply Matrix.ext; unfold tripleCharges sourceA2291 sourceB2291 sourceC2291 difference raw31605; decide +kernel
    rw [ha]
    exact (canonical31605 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2291 + difference 2 4) (sourceB2291 + difference 4 2) sourceC2291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4821) := by
    have ha : (tripleCharges (sourceA2291 + difference 2 4) (sourceB2291 + difference 4 2) sourceC2291) = raw31606 := by
      apply Matrix.ext; unfold tripleCharges sourceA2291 sourceB2291 sourceC2291 difference raw31606; decide +kernel
    rw [ha]
    exact (canonical31606 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2291 + difference 2 5) (sourceB2291 + difference 5 2) sourceC2291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4821) := by
    have ha : (tripleCharges (sourceA2291 + difference 2 5) (sourceB2291 + difference 5 2) sourceC2291) = raw31426 := by
      apply Matrix.ext; unfold tripleCharges sourceA2291 sourceB2291 sourceC2291 difference raw31426; decide +kernel
    rw [ha]
    exact (canonical31426 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2291 + difference 3 0) (sourceB2291 + difference 0 3) sourceC2291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4415) := by
    have ha : (tripleCharges (sourceA2291 + difference 3 0) (sourceB2291 + difference 0 3) sourceC2291) = raw31607 := by
      apply Matrix.ext; unfold tripleCharges sourceA2291 sourceB2291 sourceC2291 difference raw31607; decide +kernel
    rw [ha]
    exact (canonical31607 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2291 + difference 3 1) (sourceB2291 + difference 1 3) sourceC2291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4732) := by
    have ha : (tripleCharges (sourceA2291 + difference 3 1) (sourceB2291 + difference 1 3) sourceC2291) = raw30545 := by
      apply Matrix.ext; unfold tripleCharges sourceA2291 sourceB2291 sourceC2291 difference raw30545; decide +kernel
    rw [ha]
    exact (canonical30545 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2291 + difference 3 2) (sourceB2291 + difference 2 3) sourceC2291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4811) := by
    have ha : (tripleCharges (sourceA2291 + difference 3 2) (sourceB2291 + difference 2 3) sourceC2291) = raw29686 := by
      apply Matrix.ext; unfold tripleCharges sourceA2291 sourceB2291 sourceC2291 difference raw29686; decide +kernel
    rw [ha]
    exact (canonical29686 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2291 + difference 3 4) (sourceB2291 + difference 4 3) sourceC2291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4795) := by
    have ha : (tripleCharges (sourceA2291 + difference 3 4) (sourceB2291 + difference 4 3) sourceC2291) = raw29829 := by
      apply Matrix.ext; unfold tripleCharges sourceA2291 sourceB2291 sourceC2291 difference raw29829; decide +kernel
    rw [ha]
    exact (canonical29829 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2291 + difference 3 5) (sourceB2291 + difference 5 3) sourceC2291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4795) := by
    have ha : (tripleCharges (sourceA2291 + difference 3 5) (sourceB2291 + difference 5 3) sourceC2291) = raw31429 := by
      apply Matrix.ext; unfold tripleCharges sourceA2291 sourceB2291 sourceC2291 difference raw31429; decide +kernel
    rw [ha]
    exact (canonical31429 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2291 + difference 4 0) (sourceB2291 + difference 0 4) sourceC2291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4419) := by
    have ha : (tripleCharges (sourceA2291 + difference 4 0) (sourceB2291 + difference 0 4) sourceC2291) = raw31434 := by
      apply Matrix.ext; unfold tripleCharges sourceA2291 sourceB2291 sourceC2291 difference raw31434; decide +kernel
    rw [ha]
    exact (canonical31434 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2291 + difference 4 1) (sourceB2291 + difference 1 4) sourceC2291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4745) := by
    have ha : (tripleCharges (sourceA2291 + difference 4 1) (sourceB2291 + difference 1 4) sourceC2291) = raw30380 := by
      apply Matrix.ext; unfold tripleCharges sourceA2291 sourceB2291 sourceC2291 difference raw30380; decide +kernel
    rw [ha]
    exact (canonical30380 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2291 + difference 4 2) (sourceB2291 + difference 2 4) sourceC2291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4846) := by
    have ha : (tripleCharges (sourceA2291 + difference 4 2) (sourceB2291 + difference 2 4) sourceC2291) = raw29690 := by
      apply Matrix.ext; unfold tripleCharges sourceA2291 sourceB2291 sourceC2291 difference raw29690; decide +kernel
    rw [ha]
    exact (canonical29690 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2291 + difference 4 3) (sourceB2291 + difference 3 4) sourceC2291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4782) := by
    have ha : (tripleCharges (sourceA2291 + difference 4 3) (sourceB2291 + difference 3 4) sourceC2291) = raw30173 := by
      apply Matrix.ext; unfold tripleCharges sourceA2291 sourceB2291 sourceC2291 difference raw30173; decide +kernel
    rw [ha]
    exact (canonical30173 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2291 + difference 4 5) (sourceB2291 + difference 5 4) sourceC2291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4810) := by
    have ha : (tripleCharges (sourceA2291 + difference 4 5) (sourceB2291 + difference 5 4) sourceC2291) = raw30363 := by
      apply Matrix.ext; unfold tripleCharges sourceA2291 sourceB2291 sourceC2291 difference raw30363; decide +kernel
    rw [ha]
    exact (canonical30363 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2291 + difference 5 0) (sourceB2291 + difference 0 5) sourceC2291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4419) := by
    have ha : (tripleCharges (sourceA2291 + difference 5 0) (sourceB2291 + difference 0 5) sourceC2291) = raw31608 := by
      apply Matrix.ext; unfold tripleCharges sourceA2291 sourceB2291 sourceC2291 difference raw31608; decide +kernel
    rw [ha]
    exact (canonical31608 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2291 + difference 5 1) (sourceB2291 + difference 1 5) sourceC2291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4745) := by
    have ha : (tripleCharges (sourceA2291 + difference 5 1) (sourceB2291 + difference 1 5) sourceC2291) = raw30548 := by
      apply Matrix.ext; unfold tripleCharges sourceA2291 sourceB2291 sourceC2291 difference raw30548; decide +kernel
    rw [ha]
    exact (canonical30548 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2291 + difference 5 2) (sourceB2291 + difference 2 5) sourceC2291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4846) := by
    have ha : (tripleCharges (sourceA2291 + difference 5 2) (sourceB2291 + difference 2 5) sourceC2291) = raw29582 := by
      apply Matrix.ext; unfold tripleCharges sourceA2291 sourceB2291 sourceC2291 difference raw29582; decide +kernel
    rw [ha]
    exact (canonical29582 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2291 + difference 5 3) (sourceB2291 + difference 3 5) sourceC2291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4782) := by
    have ha : (tripleCharges (sourceA2291 + difference 5 3) (sourceB2291 + difference 3 5) sourceC2291) = raw31609 := by
      apply Matrix.ext; unfold tripleCharges sourceA2291 sourceB2291 sourceC2291 difference raw31609; decide +kernel
    rw [ha]
    exact (canonical31609 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2291 + difference 5 4) (sourceB2291 + difference 4 5) sourceC2291) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4810) := by
    have ha : (tripleCharges (sourceA2291 + difference 5 4) (sourceB2291 + difference 4 5) sourceC2291) = raw29572 := by
      apply Matrix.ext; unfold tripleCharges sourceA2291 sourceB2291 sourceC2291 difference raw29572; decide +kernel
    rw [ha]
    exact (canonical29572 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2291 sourceB2291 sourceC2291
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2291, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2292 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2292 : Charge := ![0, 1, 1, -1, 0, -1]
def sourceC2292 : Charge := ![3, 0, -1, 1, -2, -1]
def sourceForm2292 : Integer.Sparse Master := [(Sum.inr 1990, 1), (Sum.inr 3367, 1), (Sum.inr 3429, 1), (Sum.inr 3499, 1), (Sum.inr 3514, 1), (Sum.inr 3515, 1), (Sum.inr 4080, -1)]

theorem sourceEq2292 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2292 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2292 + difference 0 0) (sourceB2292 + difference 0 0) sourceC2292) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1990) := by
    have ha : (tripleCharges (sourceA2292 + difference 0 0) (sourceB2292 + difference 0 0) sourceC2292) = raw31610 := by
      apply Matrix.ext; unfold tripleCharges sourceA2292 sourceB2292 sourceC2292 difference raw31610; decide +kernel
    rw [ha]
    exact (canonical31610 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2292 + difference 0 1) (sourceB2292 + difference 1 0) sourceC2292) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3367) := by
    have ha : (tripleCharges (sourceA2292 + difference 0 1) (sourceB2292 + difference 1 0) sourceC2292) = raw31611 := by
      apply Matrix.ext; unfold tripleCharges sourceA2292 sourceB2292 sourceC2292 difference raw31611; decide +kernel
    rw [ha]
    exact (canonical31611 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2292 + difference 0 2) (sourceB2292 + difference 2 0) sourceC2292) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3499) := by
    have ha : (tripleCharges (sourceA2292 + difference 0 2) (sourceB2292 + difference 2 0) sourceC2292) = raw31612 := by
      apply Matrix.ext; unfold tripleCharges sourceA2292 sourceB2292 sourceC2292 difference raw31612; decide +kernel
    rw [ha]
    exact (canonical31612 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2292 + difference 0 3) (sourceB2292 + difference 3 0) sourceC2292) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3429) := by
    have ha : (tripleCharges (sourceA2292 + difference 0 3) (sourceB2292 + difference 3 0) sourceC2292) = raw31613 := by
      apply Matrix.ext; unfold tripleCharges sourceA2292 sourceB2292 sourceC2292 difference raw31613; decide +kernel
    rw [ha]
    exact (canonical31613 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2292 + difference 0 4) (sourceB2292 + difference 4 0) sourceC2292) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3515) := by
    have ha : (tripleCharges (sourceA2292 + difference 0 4) (sourceB2292 + difference 4 0) sourceC2292) = raw31614 := by
      apply Matrix.ext; unfold tripleCharges sourceA2292 sourceB2292 sourceC2292 difference raw31614; decide +kernel
    rw [ha]
    exact (canonical31614 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2292 + difference 0 5) (sourceB2292 + difference 5 0) sourceC2292) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3514) := by
    have ha : (tripleCharges (sourceA2292 + difference 0 5) (sourceB2292 + difference 5 0) sourceC2292) = raw31615 := by
      apply Matrix.ext; unfold tripleCharges sourceA2292 sourceB2292 sourceC2292 difference raw31615; decide +kernel
    rw [ha]
    exact (canonical31615 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2292 + sourceB2292) sourceC2292) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA2292 + sourceB2292) sourceC2292) = raw31616 := by
      apply Matrix.ext; unfold doubleCharges sourceA2292 sourceB2292 sourceC2292 raw31616; decide +kernel
    rw [ha]
    exact (canonical31616 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2292 sourceB2292 sourceC2292
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2292, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2293 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2293 : Charge := ![0, 1, 1, -1, 0, -1]
def sourceC2293 : Charge := ![3, 0, -1, 1, -2, -1]
def sourceForm2293 : Integer.Sparse Master := [(Sum.inr 901, 1), (Sum.inr 1787, 1), (Sum.inr 1869, 1), (Sum.inr 1990, 1), (Sum.inr 1999, 1), (Sum.inr 2000, 1), (Sum.inr 4080, -1)]

theorem sourceEq2293 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2293 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2293 + difference 2 0) (sourceB2293 + difference 0 2) sourceC2293) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 901) := by
    have ha : (tripleCharges (sourceA2293 + difference 2 0) (sourceB2293 + difference 0 2) sourceC2293) = raw31617 := by
      apply Matrix.ext; unfold tripleCharges sourceA2293 sourceB2293 sourceC2293 difference raw31617; decide +kernel
    rw [ha]
    exact (canonical31617 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2293 + difference 2 1) (sourceB2293 + difference 1 2) sourceC2293) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1787) := by
    have ha : (tripleCharges (sourceA2293 + difference 2 1) (sourceB2293 + difference 1 2) sourceC2293) = raw31618 := by
      apply Matrix.ext; unfold tripleCharges sourceA2293 sourceB2293 sourceC2293 difference raw31618; decide +kernel
    rw [ha]
    exact (canonical31618 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2293 + difference 2 2) (sourceB2293 + difference 2 2) sourceC2293) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1990) := by
    have ha : (tripleCharges (sourceA2293 + difference 2 2) (sourceB2293 + difference 2 2) sourceC2293) = raw31610 := by
      apply Matrix.ext; unfold tripleCharges sourceA2293 sourceB2293 sourceC2293 difference raw31610; decide +kernel
    rw [ha]
    exact (canonical31610 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2293 + difference 2 3) (sourceB2293 + difference 3 2) sourceC2293) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1869) := by
    have ha : (tripleCharges (sourceA2293 + difference 2 3) (sourceB2293 + difference 3 2) sourceC2293) = raw31619 := by
      apply Matrix.ext; unfold tripleCharges sourceA2293 sourceB2293 sourceC2293 difference raw31619; decide +kernel
    rw [ha]
    exact (canonical31619 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2293 + difference 2 4) (sourceB2293 + difference 4 2) sourceC2293) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2000) := by
    have ha : (tripleCharges (sourceA2293 + difference 2 4) (sourceB2293 + difference 4 2) sourceC2293) = raw31620 := by
      apply Matrix.ext; unfold tripleCharges sourceA2293 sourceB2293 sourceC2293 difference raw31620; decide +kernel
    rw [ha]
    exact (canonical31620 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2293 + difference 2 5) (sourceB2293 + difference 5 2) sourceC2293) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1999) := by
    have ha : (tripleCharges (sourceA2293 + difference 2 5) (sourceB2293 + difference 5 2) sourceC2293) = raw31621 := by
      apply Matrix.ext; unfold tripleCharges sourceA2293 sourceB2293 sourceC2293 difference raw31621; decide +kernel
    rw [ha]
    exact (canonical31621 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2293 + sourceB2293) sourceC2293) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA2293 + sourceB2293) sourceC2293) = raw31616 := by
      apply Matrix.ext; unfold doubleCharges sourceA2293 sourceB2293 sourceC2293 raw31616; decide +kernel
    rw [ha]
    exact (canonical31616 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2293 sourceB2293 sourceC2293
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2293, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2294 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2294 : Charge := ![0, 1, 1, -1, 0, -1]
def sourceC2294 : Charge := ![3, 0, -1, 1, -2, -1]
def sourceForm2294 : Integer.Sparse Master := [(Sum.inr 1860, 1), (Sum.inr 1861, 1), (Sum.inr 1869, 1), (Sum.inr 1918, 1), (Sum.inr 1990, 1), (Sum.inr 3429, 1), (Sum.inr 4080, -1)]

theorem sourceEq2294 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2294 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2294 + difference 0 3) (sourceB2294 + difference 3 0) sourceC2294) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3429) := by
    have ha : (tripleCharges (sourceA2294 + difference 0 3) (sourceB2294 + difference 3 0) sourceC2294) = raw31613 := by
      apply Matrix.ext; unfold tripleCharges sourceA2294 sourceB2294 sourceC2294 difference raw31613; decide +kernel
    rw [ha]
    exact (canonical31613 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2294 + difference 1 3) (sourceB2294 + difference 3 1) sourceC2294) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1918) := by
    have ha : (tripleCharges (sourceA2294 + difference 1 3) (sourceB2294 + difference 3 1) sourceC2294) = raw31622 := by
      apply Matrix.ext; unfold tripleCharges sourceA2294 sourceB2294 sourceC2294 difference raw31622; decide +kernel
    rw [ha]
    exact (canonical31622 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2294 + difference 2 3) (sourceB2294 + difference 3 2) sourceC2294) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1869) := by
    have ha : (tripleCharges (sourceA2294 + difference 2 3) (sourceB2294 + difference 3 2) sourceC2294) = raw31619 := by
      apply Matrix.ext; unfold tripleCharges sourceA2294 sourceB2294 sourceC2294 difference raw31619; decide +kernel
    rw [ha]
    exact (canonical31619 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2294 + difference 3 3) (sourceB2294 + difference 3 3) sourceC2294) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1990) := by
    have ha : (tripleCharges (sourceA2294 + difference 3 3) (sourceB2294 + difference 3 3) sourceC2294) = raw31610 := by
      apply Matrix.ext; unfold tripleCharges sourceA2294 sourceB2294 sourceC2294 difference raw31610; decide +kernel
    rw [ha]
    exact (canonical31610 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2294 + difference 4 3) (sourceB2294 + difference 3 4) sourceC2294) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1860) := by
    have ha : (tripleCharges (sourceA2294 + difference 4 3) (sourceB2294 + difference 3 4) sourceC2294) = raw31623 := by
      apply Matrix.ext; unfold tripleCharges sourceA2294 sourceB2294 sourceC2294 difference raw31623; decide +kernel
    rw [ha]
    exact (canonical31623 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2294 + difference 5 3) (sourceB2294 + difference 3 5) sourceC2294) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1861) := by
    have ha : (tripleCharges (sourceA2294 + difference 5 3) (sourceB2294 + difference 3 5) sourceC2294) = raw31624 := by
      apply Matrix.ext; unfold tripleCharges sourceA2294 sourceB2294 sourceC2294 difference raw31624; decide +kernel
    rw [ha]
    exact (canonical31624 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2294 + sourceB2294) sourceC2294) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA2294 + sourceB2294) sourceC2294) = raw31616 := by
      apply Matrix.ext; unfold doubleCharges sourceA2294 sourceB2294 sourceC2294 raw31616; decide +kernel
    rw [ha]
    exact (canonical31616 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2294 sourceB2294 sourceC2294
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2294, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2295 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2295 : Charge := ![0, 1, 0, 0, 1, -2]
def sourceC2295 : Charge := ![3, 0, 0, 0, -3, 0]
def sourceForm2295 : Integer.Sparse Master := [(Sum.inr 4348, 2), (Sum.inr 4359, 1), (Sum.inr 4362, 1), (Sum.inr 4510, 1), (Sum.inr 4678, 2), (Sum.inr 4683, 2), (Sum.inr 4691, 1), (Sum.inr 4694, 1), (Sum.inr 4702, 2), (Sum.inr 4762, 2), (Sum.inr 4832, 2), (Sum.inr 4836, 2), (Sum.inr 4837, 1), (Sum.inr 4844, 1), (Sum.inr 4845, 2), (Sum.inr 4897, 1), (Sum.inr 4899, 1), (Sum.inr 5222, 2), (Sum.inr 5235, 1), (Sum.inr 5261, 1), (Sum.inr 5268, 1)]

theorem sourceEq2295 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2295 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2295 + difference 0 1) (sourceB2295 + difference 1 0) sourceC2295) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5235) := by
    have ha : (tripleCharges (sourceA2295 + difference 0 1) (sourceB2295 + difference 1 0) sourceC2295) = raw31625 := by
      apply Matrix.ext; unfold tripleCharges sourceA2295 sourceB2295 sourceC2295 difference raw31625; decide +kernel
    rw [ha]
    exact (canonical31625 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2295 + difference 0 2) (sourceB2295 + difference 2 0) sourceC2295) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5222) := by
    have ha : (tripleCharges (sourceA2295 + difference 0 2) (sourceB2295 + difference 2 0) sourceC2295) = raw31626 := by
      apply Matrix.ext; unfold tripleCharges sourceA2295 sourceB2295 sourceC2295 difference raw31626; decide +kernel
    rw [ha]
    exact (canonical31626 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2295 + difference 0 3) (sourceB2295 + difference 3 0) sourceC2295) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5222) := by
    have ha : (tripleCharges (sourceA2295 + difference 0 3) (sourceB2295 + difference 3 0) sourceC2295) = raw31627 := by
      apply Matrix.ext; unfold tripleCharges sourceA2295 sourceB2295 sourceC2295 difference raw31627; decide +kernel
    rw [ha]
    exact (canonical31627 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2295 + difference 0 4) (sourceB2295 + difference 4 0) sourceC2295) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5268) := by
    have ha : (tripleCharges (sourceA2295 + difference 0 4) (sourceB2295 + difference 4 0) sourceC2295) = raw31628 := by
      apply Matrix.ext; unfold tripleCharges sourceA2295 sourceB2295 sourceC2295 difference raw31628; decide +kernel
    rw [ha]
    exact (canonical31628 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2295 + difference 0 5) (sourceB2295 + difference 5 0) sourceC2295) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5261) := by
    have ha : (tripleCharges (sourceA2295 + difference 0 5) (sourceB2295 + difference 5 0) sourceC2295) = raw31629 := by
      apply Matrix.ext; unfold tripleCharges sourceA2295 sourceB2295 sourceC2295 difference raw31629; decide +kernel
    rw [ha]
    exact (canonical31629 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2295 + difference 1 0) (sourceB2295 + difference 0 1) sourceC2295) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4510) := by
    have ha : (tripleCharges (sourceA2295 + difference 1 0) (sourceB2295 + difference 0 1) sourceC2295) = raw31630 := by
      apply Matrix.ext; unfold tripleCharges sourceA2295 sourceB2295 sourceC2295 difference raw31630; decide +kernel
    rw [ha]
    exact (canonical31630 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2295 + difference 1 2) (sourceB2295 + difference 2 1) sourceC2295) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4845) := by
    have ha : (tripleCharges (sourceA2295 + difference 1 2) (sourceB2295 + difference 2 1) sourceC2295) = raw23334 := by
      apply Matrix.ext; unfold tripleCharges sourceA2295 sourceB2295 sourceC2295 difference raw23334; decide +kernel
    rw [ha]
    exact (canonical23334 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2295 + difference 1 3) (sourceB2295 + difference 3 1) sourceC2295) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4845) := by
    have ha : (tripleCharges (sourceA2295 + difference 1 3) (sourceB2295 + difference 3 1) sourceC2295) = raw23335 := by
      apply Matrix.ext; unfold tripleCharges sourceA2295 sourceB2295 sourceC2295 difference raw23335; decide +kernel
    rw [ha]
    exact (canonical23335 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2295 + difference 1 4) (sourceB2295 + difference 4 1) sourceC2295) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4899) := by
    have ha : (tripleCharges (sourceA2295 + difference 1 4) (sourceB2295 + difference 4 1) sourceC2295) = raw3475 := by
      apply Matrix.ext; unfold tripleCharges sourceA2295 sourceB2295 sourceC2295 difference raw3475; decide +kernel
    rw [ha]
    exact (canonical3475 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2295 + difference 1 5) (sourceB2295 + difference 5 1) sourceC2295) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4897) := by
    have ha : (tripleCharges (sourceA2295 + difference 1 5) (sourceB2295 + difference 5 1) sourceC2295) = raw23336 := by
      apply Matrix.ext; unfold tripleCharges sourceA2295 sourceB2295 sourceC2295 difference raw23336; decide +kernel
    rw [ha]
    exact (canonical23336 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2295 + difference 2 0) (sourceB2295 + difference 0 2) sourceC2295) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4348) := by
    have ha : (tripleCharges (sourceA2295 + difference 2 0) (sourceB2295 + difference 0 2) sourceC2295) = raw23343 := by
      apply Matrix.ext; unfold tripleCharges sourceA2295 sourceB2295 sourceC2295 difference raw23343; decide +kernel
    rw [ha]
    exact (canonical23343 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2295 + difference 2 1) (sourceB2295 + difference 1 2) sourceC2295) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4683) := by
    have ha : (tripleCharges (sourceA2295 + difference 2 1) (sourceB2295 + difference 1 2) sourceC2295) = raw31631 := by
      apply Matrix.ext; unfold tripleCharges sourceA2295 sourceB2295 sourceC2295 difference raw31631; decide +kernel
    rw [ha]
    exact (canonical31631 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2295 + difference 2 3) (sourceB2295 + difference 3 2) sourceC2295) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4762) := by
    have ha : (tripleCharges (sourceA2295 + difference 2 3) (sourceB2295 + difference 3 2) sourceC2295) = raw31632 := by
      apply Matrix.ext; unfold tripleCharges sourceA2295 sourceB2295 sourceC2295 difference raw31632; decide +kernel
    rw [ha]
    exact (canonical31632 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2295 + difference 2 4) (sourceB2295 + difference 4 2) sourceC2295) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4836) := by
    have ha : (tripleCharges (sourceA2295 + difference 2 4) (sourceB2295 + difference 4 2) sourceC2295) = raw31633 := by
      apply Matrix.ext; unfold tripleCharges sourceA2295 sourceB2295 sourceC2295 difference raw31633; decide +kernel
    rw [ha]
    exact (canonical31633 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2295 + difference 2 5) (sourceB2295 + difference 5 2) sourceC2295) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4832) := by
    have ha : (tripleCharges (sourceA2295 + difference 2 5) (sourceB2295 + difference 5 2) sourceC2295) = raw31634 := by
      apply Matrix.ext; unfold tripleCharges sourceA2295 sourceB2295 sourceC2295 difference raw31634; decide +kernel
    rw [ha]
    exact (canonical31634 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2295 + difference 3 0) (sourceB2295 + difference 0 3) sourceC2295) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4348) := by
    have ha : (tripleCharges (sourceA2295 + difference 3 0) (sourceB2295 + difference 0 3) sourceC2295) = raw23348 := by
      apply Matrix.ext; unfold tripleCharges sourceA2295 sourceB2295 sourceC2295 difference raw23348; decide +kernel
    rw [ha]
    exact (canonical23348 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2295 + difference 3 1) (sourceB2295 + difference 1 3) sourceC2295) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4683) := by
    have ha : (tripleCharges (sourceA2295 + difference 3 1) (sourceB2295 + difference 1 3) sourceC2295) = raw31635 := by
      apply Matrix.ext; unfold tripleCharges sourceA2295 sourceB2295 sourceC2295 difference raw31635; decide +kernel
    rw [ha]
    exact (canonical31635 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2295 + difference 3 2) (sourceB2295 + difference 2 3) sourceC2295) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4762) := by
    have ha : (tripleCharges (sourceA2295 + difference 3 2) (sourceB2295 + difference 2 3) sourceC2295) = raw31636 := by
      apply Matrix.ext; unfold tripleCharges sourceA2295 sourceB2295 sourceC2295 difference raw31636; decide +kernel
    rw [ha]
    exact (canonical31636 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2295 + difference 3 4) (sourceB2295 + difference 4 3) sourceC2295) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4836) := by
    have ha : (tripleCharges (sourceA2295 + difference 3 4) (sourceB2295 + difference 4 3) sourceC2295) = raw31637 := by
      apply Matrix.ext; unfold tripleCharges sourceA2295 sourceB2295 sourceC2295 difference raw31637; decide +kernel
    rw [ha]
    exact (canonical31637 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2295 + difference 3 5) (sourceB2295 + difference 5 3) sourceC2295) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4832) := by
    have ha : (tripleCharges (sourceA2295 + difference 3 5) (sourceB2295 + difference 5 3) sourceC2295) = raw31638 := by
      apply Matrix.ext; unfold tripleCharges sourceA2295 sourceB2295 sourceC2295 difference raw31638; decide +kernel
    rw [ha]
    exact (canonical31638 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2295 + difference 4 0) (sourceB2295 + difference 0 4) sourceC2295) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4359) := by
    have ha : (tripleCharges (sourceA2295 + difference 4 0) (sourceB2295 + difference 0 4) sourceC2295) = raw23353 := by
      apply Matrix.ext; unfold tripleCharges sourceA2295 sourceB2295 sourceC2295 difference raw23353; decide +kernel
    rw [ha]
    exact (canonical23353 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2295 + difference 4 1) (sourceB2295 + difference 1 4) sourceC2295) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4691) := by
    have ha : (tripleCharges (sourceA2295 + difference 4 1) (sourceB2295 + difference 1 4) sourceC2295) = raw31639 := by
      apply Matrix.ext; unfold tripleCharges sourceA2295 sourceB2295 sourceC2295 difference raw31639; decide +kernel
    rw [ha]
    exact (canonical31639 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2295 + difference 4 2) (sourceB2295 + difference 2 4) sourceC2295) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4678) := by
    have ha : (tripleCharges (sourceA2295 + difference 4 2) (sourceB2295 + difference 2 4) sourceC2295) = raw31640 := by
      apply Matrix.ext; unfold tripleCharges sourceA2295 sourceB2295 sourceC2295 difference raw31640; decide +kernel
    rw [ha]
    exact (canonical31640 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2295 + difference 4 3) (sourceB2295 + difference 3 4) sourceC2295) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4678) := by
    have ha : (tripleCharges (sourceA2295 + difference 4 3) (sourceB2295 + difference 3 4) sourceC2295) = raw31641 := by
      apply Matrix.ext; unfold tripleCharges sourceA2295 sourceB2295 sourceC2295 difference raw31641; decide +kernel
    rw [ha]
    exact (canonical31641 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2295 + difference 4 5) (sourceB2295 + difference 5 4) sourceC2295) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4837) := by
    have ha : (tripleCharges (sourceA2295 + difference 4 5) (sourceB2295 + difference 5 4) sourceC2295) = raw31642 := by
      apply Matrix.ext; unfold tripleCharges sourceA2295 sourceB2295 sourceC2295 difference raw31642; decide +kernel
    rw [ha]
    exact (canonical31642 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2295 + difference 5 0) (sourceB2295 + difference 0 5) sourceC2295) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4362) := by
    have ha : (tripleCharges (sourceA2295 + difference 5 0) (sourceB2295 + difference 0 5) sourceC2295) = raw23358 := by
      apply Matrix.ext; unfold tripleCharges sourceA2295 sourceB2295 sourceC2295 difference raw23358; decide +kernel
    rw [ha]
    exact (canonical23358 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2295 + difference 5 1) (sourceB2295 + difference 1 5) sourceC2295) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4694) := by
    have ha : (tripleCharges (sourceA2295 + difference 5 1) (sourceB2295 + difference 1 5) sourceC2295) = raw31643 := by
      apply Matrix.ext; unfold tripleCharges sourceA2295 sourceB2295 sourceC2295 difference raw31643; decide +kernel
    rw [ha]
    exact (canonical31643 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2295 + difference 5 2) (sourceB2295 + difference 2 5) sourceC2295) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4702) := by
    have ha : (tripleCharges (sourceA2295 + difference 5 2) (sourceB2295 + difference 2 5) sourceC2295) = raw31644 := by
      apply Matrix.ext; unfold tripleCharges sourceA2295 sourceB2295 sourceC2295 difference raw31644; decide +kernel
    rw [ha]
    exact (canonical31644 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2295 + difference 5 3) (sourceB2295 + difference 3 5) sourceC2295) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4702) := by
    have ha : (tripleCharges (sourceA2295 + difference 5 3) (sourceB2295 + difference 3 5) sourceC2295) = raw31645 := by
      apply Matrix.ext; unfold tripleCharges sourceA2295 sourceB2295 sourceC2295 difference raw31645; decide +kernel
    rw [ha]
    exact (canonical31645 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2295 + difference 5 4) (sourceB2295 + difference 4 5) sourceC2295) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4844) := by
    have ha : (tripleCharges (sourceA2295 + difference 5 4) (sourceB2295 + difference 4 5) sourceC2295) = raw3472 := by
      apply Matrix.ext; unfold tripleCharges sourceA2295 sourceB2295 sourceC2295 difference raw3472; decide +kernel
    rw [ha]
    exact (canonical3472 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2295 sourceB2295 sourceC2295
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2295, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2296 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2296 : Charge := ![0, 1, 0, 0, 1, -2]
def sourceC2296 : Charge := ![3, 0, 0, 0, -3, 0]
def sourceForm2296 : Integer.Sparse Master := [(Sum.inr 1347, 2), (Sum.inr 1348, 1), (Sum.inr 1349, 1), (Sum.inr 1454, 1), (Sum.inr 1828, 2), (Sum.inr 1832, 1), (Sum.inr 2136, 1), (Sum.inr 2716, 2), (Sum.inr 2734, 1), (Sum.inr 2778, 1), (Sum.inr 3031, 2), (Sum.inr 3033, 2), (Sum.inr 3046, 1), (Sum.inr 3062, 2), (Sum.inr 3082, 2), (Sum.inr 3090, 1), (Sum.inr 3095, 2), (Sum.inr 3114, 1), (Sum.inr 3143, 2), (Sum.inr 3145, 1), (Sum.inr 3215, 1)]

theorem sourceEq2296 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2296 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2296 + difference 0 1) (sourceB2296 + difference 1 0) sourceC2296) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3046) := by
    have ha : (tripleCharges (sourceA2296 + difference 0 1) (sourceB2296 + difference 1 0) sourceC2296) = raw31646 := by
      apply Matrix.ext; unfold tripleCharges sourceA2296 sourceB2296 sourceC2296 difference raw31646; decide +kernel
    rw [ha]
    exact (canonical31646 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2296 + difference 0 2) (sourceB2296 + difference 2 0) sourceC2296) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3031) := by
    have ha : (tripleCharges (sourceA2296 + difference 0 2) (sourceB2296 + difference 2 0) sourceC2296) = raw31647 := by
      apply Matrix.ext; unfold tripleCharges sourceA2296 sourceB2296 sourceC2296 difference raw31647; decide +kernel
    rw [ha]
    exact (canonical31647 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2296 + difference 0 3) (sourceB2296 + difference 3 0) sourceC2296) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3031) := by
    have ha : (tripleCharges (sourceA2296 + difference 0 3) (sourceB2296 + difference 3 0) sourceC2296) = raw31648 := by
      apply Matrix.ext; unfold tripleCharges sourceA2296 sourceB2296 sourceC2296 difference raw31648; decide +kernel
    rw [ha]
    exact (canonical31648 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2296 + difference 0 4) (sourceB2296 + difference 4 0) sourceC2296) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2734) := by
    have ha : (tripleCharges (sourceA2296 + difference 0 4) (sourceB2296 + difference 4 0) sourceC2296) = raw31649 := by
      apply Matrix.ext; unfold tripleCharges sourceA2296 sourceB2296 sourceC2296 difference raw31649; decide +kernel
    rw [ha]
    exact (canonical31649 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2296 + difference 0 5) (sourceB2296 + difference 5 0) sourceC2296) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3090) := by
    have ha : (tripleCharges (sourceA2296 + difference 0 5) (sourceB2296 + difference 5 0) sourceC2296) = raw31650 := by
      apply Matrix.ext; unfold tripleCharges sourceA2296 sourceB2296 sourceC2296 difference raw31650; decide +kernel
    rw [ha]
    exact (canonical31650 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2296 + difference 1 0) (sourceB2296 + difference 0 1) sourceC2296) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1454) := by
    have ha : (tripleCharges (sourceA2296 + difference 1 0) (sourceB2296 + difference 0 1) sourceC2296) = raw31651 := by
      apply Matrix.ext; unfold tripleCharges sourceA2296 sourceB2296 sourceC2296 difference raw31651; decide +kernel
    rw [ha]
    exact (canonical31651 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2296 + difference 1 2) (sourceB2296 + difference 2 1) sourceC2296) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3095) := by
    have ha : (tripleCharges (sourceA2296 + difference 1 2) (sourceB2296 + difference 2 1) sourceC2296) = raw23362 := by
      apply Matrix.ext; unfold tripleCharges sourceA2296 sourceB2296 sourceC2296 difference raw23362; decide +kernel
    rw [ha]
    exact (canonical23362 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2296 + difference 1 3) (sourceB2296 + difference 3 1) sourceC2296) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3095) := by
    have ha : (tripleCharges (sourceA2296 + difference 1 3) (sourceB2296 + difference 3 1) sourceC2296) = raw23363 := by
      apply Matrix.ext; unfold tripleCharges sourceA2296 sourceB2296 sourceC2296 difference raw23363; decide +kernel
    rw [ha]
    exact (canonical23363 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2296 + difference 1 4) (sourceB2296 + difference 4 1) sourceC2296) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2778) := by
    have ha : (tripleCharges (sourceA2296 + difference 1 4) (sourceB2296 + difference 4 1) sourceC2296) = raw3505 := by
      apply Matrix.ext; unfold tripleCharges sourceA2296 sourceB2296 sourceC2296 difference raw3505; decide +kernel
    rw [ha]
    exact (canonical3505 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2296 + difference 1 5) (sourceB2296 + difference 5 1) sourceC2296) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3114) := by
    have ha : (tripleCharges (sourceA2296 + difference 1 5) (sourceB2296 + difference 5 1) sourceC2296) = raw23364 := by
      apply Matrix.ext; unfold tripleCharges sourceA2296 sourceB2296 sourceC2296 difference raw23364; decide +kernel
    rw [ha]
    exact (canonical23364 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2296 + difference 2 0) (sourceB2296 + difference 0 2) sourceC2296) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1347) := by
    have ha : (tripleCharges (sourceA2296 + difference 2 0) (sourceB2296 + difference 0 2) sourceC2296) = raw23371 := by
      apply Matrix.ext; unfold tripleCharges sourceA2296 sourceB2296 sourceC2296 difference raw23371; decide +kernel
    rw [ha]
    exact (canonical23371 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2296 + difference 2 1) (sourceB2296 + difference 1 2) sourceC2296) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3033) := by
    have ha : (tripleCharges (sourceA2296 + difference 2 1) (sourceB2296 + difference 1 2) sourceC2296) = raw31652 := by
      apply Matrix.ext; unfold tripleCharges sourceA2296 sourceB2296 sourceC2296 difference raw31652; decide +kernel
    rw [ha]
    exact (canonical31652 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2296 + difference 2 3) (sourceB2296 + difference 3 2) sourceC2296) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3062) := by
    have ha : (tripleCharges (sourceA2296 + difference 2 3) (sourceB2296 + difference 3 2) sourceC2296) = raw31653 := by
      apply Matrix.ext; unfold tripleCharges sourceA2296 sourceB2296 sourceC2296 difference raw31653; decide +kernel
    rw [ha]
    exact (canonical31653 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2296 + difference 2 4) (sourceB2296 + difference 4 2) sourceC2296) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2716) := by
    have ha : (tripleCharges (sourceA2296 + difference 2 4) (sourceB2296 + difference 4 2) sourceC2296) = raw31654 := by
      apply Matrix.ext; unfold tripleCharges sourceA2296 sourceB2296 sourceC2296 difference raw31654; decide +kernel
    rw [ha]
    exact (canonical31654 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2296 + difference 2 5) (sourceB2296 + difference 5 2) sourceC2296) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3082) := by
    have ha : (tripleCharges (sourceA2296 + difference 2 5) (sourceB2296 + difference 5 2) sourceC2296) = raw31655 := by
      apply Matrix.ext; unfold tripleCharges sourceA2296 sourceB2296 sourceC2296 difference raw31655; decide +kernel
    rw [ha]
    exact (canonical31655 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2296 + difference 3 0) (sourceB2296 + difference 0 3) sourceC2296) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1347) := by
    have ha : (tripleCharges (sourceA2296 + difference 3 0) (sourceB2296 + difference 0 3) sourceC2296) = raw23376 := by
      apply Matrix.ext; unfold tripleCharges sourceA2296 sourceB2296 sourceC2296 difference raw23376; decide +kernel
    rw [ha]
    exact (canonical23376 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2296 + difference 3 1) (sourceB2296 + difference 1 3) sourceC2296) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3033) := by
    have ha : (tripleCharges (sourceA2296 + difference 3 1) (sourceB2296 + difference 1 3) sourceC2296) = raw31656 := by
      apply Matrix.ext; unfold tripleCharges sourceA2296 sourceB2296 sourceC2296 difference raw31656; decide +kernel
    rw [ha]
    exact (canonical31656 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2296 + difference 3 2) (sourceB2296 + difference 2 3) sourceC2296) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3062) := by
    have ha : (tripleCharges (sourceA2296 + difference 3 2) (sourceB2296 + difference 2 3) sourceC2296) = raw31657 := by
      apply Matrix.ext; unfold tripleCharges sourceA2296 sourceB2296 sourceC2296 difference raw31657; decide +kernel
    rw [ha]
    exact (canonical31657 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2296 + difference 3 4) (sourceB2296 + difference 4 3) sourceC2296) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2716) := by
    have ha : (tripleCharges (sourceA2296 + difference 3 4) (sourceB2296 + difference 4 3) sourceC2296) = raw31658 := by
      apply Matrix.ext; unfold tripleCharges sourceA2296 sourceB2296 sourceC2296 difference raw31658; decide +kernel
    rw [ha]
    exact (canonical31658 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2296 + difference 3 5) (sourceB2296 + difference 5 3) sourceC2296) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3082) := by
    have ha : (tripleCharges (sourceA2296 + difference 3 5) (sourceB2296 + difference 5 3) sourceC2296) = raw31659 := by
      apply Matrix.ext; unfold tripleCharges sourceA2296 sourceB2296 sourceC2296 difference raw31659; decide +kernel
    rw [ha]
    exact (canonical31659 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2296 + difference 4 0) (sourceB2296 + difference 0 4) sourceC2296) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1349) := by
    have ha : (tripleCharges (sourceA2296 + difference 4 0) (sourceB2296 + difference 0 4) sourceC2296) = raw23381 := by
      apply Matrix.ext; unfold tripleCharges sourceA2296 sourceB2296 sourceC2296 difference raw23381; decide +kernel
    rw [ha]
    exact (canonical23381 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2296 + difference 4 1) (sourceB2296 + difference 1 4) sourceC2296) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3145) := by
    have ha : (tripleCharges (sourceA2296 + difference 4 1) (sourceB2296 + difference 1 4) sourceC2296) = raw31660 := by
      apply Matrix.ext; unfold tripleCharges sourceA2296 sourceB2296 sourceC2296 difference raw31660; decide +kernel
    rw [ha]
    exact (canonical31660 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2296 + difference 4 2) (sourceB2296 + difference 2 4) sourceC2296) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3143) := by
    have ha : (tripleCharges (sourceA2296 + difference 4 2) (sourceB2296 + difference 2 4) sourceC2296) = raw31661 := by
      apply Matrix.ext; unfold tripleCharges sourceA2296 sourceB2296 sourceC2296 difference raw31661; decide +kernel
    rw [ha]
    exact (canonical31661 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2296 + difference 4 3) (sourceB2296 + difference 3 4) sourceC2296) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3143) := by
    have ha : (tripleCharges (sourceA2296 + difference 4 3) (sourceB2296 + difference 3 4) sourceC2296) = raw31662 := by
      apply Matrix.ext; unfold tripleCharges sourceA2296 sourceB2296 sourceC2296 difference raw31662; decide +kernel
    rw [ha]
    exact (canonical31662 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2296 + difference 4 5) (sourceB2296 + difference 5 4) sourceC2296) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3215) := by
    have ha : (tripleCharges (sourceA2296 + difference 4 5) (sourceB2296 + difference 5 4) sourceC2296) = raw31663 := by
      apply Matrix.ext; unfold tripleCharges sourceA2296 sourceB2296 sourceC2296 difference raw31663; decide +kernel
    rw [ha]
    exact (canonical31663 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2296 + difference 5 0) (sourceB2296 + difference 0 5) sourceC2296) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1348) := by
    have ha : (tripleCharges (sourceA2296 + difference 5 0) (sourceB2296 + difference 0 5) sourceC2296) = raw23386 := by
      apply Matrix.ext; unfold tripleCharges sourceA2296 sourceB2296 sourceC2296 difference raw23386; decide +kernel
    rw [ha]
    exact (canonical23386 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2296 + difference 5 1) (sourceB2296 + difference 1 5) sourceC2296) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1832) := by
    have ha : (tripleCharges (sourceA2296 + difference 5 1) (sourceB2296 + difference 1 5) sourceC2296) = raw31664 := by
      apply Matrix.ext; unfold tripleCharges sourceA2296 sourceB2296 sourceC2296 difference raw31664; decide +kernel
    rw [ha]
    exact (canonical31664 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2296 + difference 5 2) (sourceB2296 + difference 2 5) sourceC2296) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1828) := by
    have ha : (tripleCharges (sourceA2296 + difference 5 2) (sourceB2296 + difference 2 5) sourceC2296) = raw31665 := by
      apply Matrix.ext; unfold tripleCharges sourceA2296 sourceB2296 sourceC2296 difference raw31665; decide +kernel
    rw [ha]
    exact (canonical31665 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2296 + difference 5 3) (sourceB2296 + difference 3 5) sourceC2296) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1828) := by
    have ha : (tripleCharges (sourceA2296 + difference 5 3) (sourceB2296 + difference 3 5) sourceC2296) = raw31666 := by
      apply Matrix.ext; unfold tripleCharges sourceA2296 sourceB2296 sourceC2296 difference raw31666; decide +kernel
    rw [ha]
    exact (canonical31666 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2296 + difference 5 4) (sourceB2296 + difference 4 5) sourceC2296) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2136) := by
    have ha : (tripleCharges (sourceA2296 + difference 5 4) (sourceB2296 + difference 4 5) sourceC2296) = raw3502 := by
      apply Matrix.ext; unfold tripleCharges sourceA2296 sourceB2296 sourceC2296 difference raw3502; decide +kernel
    rw [ha]
    exact (canonical3502 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2296 sourceB2296 sourceC2296
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2296, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2297 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2297 : Charge := ![0, 1, 0, 0, 1, -2]
def sourceC2297 : Charge := ![3, 0, 0, 0, -3, 0]
def sourceForm2297 : Integer.Sparse Master := [(Sum.inr 1669, 2), (Sum.inr 1683, 1), (Sum.inr 1687, 1), (Sum.inr 1741, 1), (Sum.inr 2143, 2), (Sum.inr 2146, 2), (Sum.inr 2159, 1), (Sum.inr 2163, 1), (Sum.inr 2171, 2), (Sum.inr 2180, 2), (Sum.inr 2193, 2), (Sum.inr 2197, 2), (Sum.inr 2208, 1), (Sum.inr 2218, 2), (Sum.inr 2222, 1), (Sum.inr 2268, 1), (Sum.inr 2281, 1), (Sum.inr 2664, 2), (Sum.inr 2680, 1), (Sum.inr 2726, 1), (Sum.inr 2734, 1)]

theorem sourceEq2297 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2297 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2297 + difference 0 1) (sourceB2297 + difference 1 0) sourceC2297) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2680) := by
    have ha : (tripleCharges (sourceA2297 + difference 0 1) (sourceB2297 + difference 1 0) sourceC2297) = raw31667 := by
      apply Matrix.ext; unfold tripleCharges sourceA2297 sourceB2297 sourceC2297 difference raw31667; decide +kernel
    rw [ha]
    exact (canonical31667 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2297 + difference 0 2) (sourceB2297 + difference 2 0) sourceC2297) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2664) := by
    have ha : (tripleCharges (sourceA2297 + difference 0 2) (sourceB2297 + difference 2 0) sourceC2297) = raw31668 := by
      apply Matrix.ext; unfold tripleCharges sourceA2297 sourceB2297 sourceC2297 difference raw31668; decide +kernel
    rw [ha]
    exact (canonical31668 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2297 + difference 0 3) (sourceB2297 + difference 3 0) sourceC2297) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2664) := by
    have ha : (tripleCharges (sourceA2297 + difference 0 3) (sourceB2297 + difference 3 0) sourceC2297) = raw31669 := by
      apply Matrix.ext; unfold tripleCharges sourceA2297 sourceB2297 sourceC2297 difference raw31669; decide +kernel
    rw [ha]
    exact (canonical31669 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2297 + difference 0 4) (sourceB2297 + difference 4 0) sourceC2297) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2734) := by
    have ha : (tripleCharges (sourceA2297 + difference 0 4) (sourceB2297 + difference 4 0) sourceC2297) = raw31670 := by
      apply Matrix.ext; unfold tripleCharges sourceA2297 sourceB2297 sourceC2297 difference raw31670; decide +kernel
    rw [ha]
    exact (canonical31670 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2297 + difference 0 5) (sourceB2297 + difference 5 0) sourceC2297) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2726) := by
    have ha : (tripleCharges (sourceA2297 + difference 0 5) (sourceB2297 + difference 5 0) sourceC2297) = raw31671 := by
      apply Matrix.ext; unfold tripleCharges sourceA2297 sourceB2297 sourceC2297 difference raw31671; decide +kernel
    rw [ha]
    exact (canonical31671 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2297 + difference 1 0) (sourceB2297 + difference 0 1) sourceC2297) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1741) := by
    have ha : (tripleCharges (sourceA2297 + difference 1 0) (sourceB2297 + difference 0 1) sourceC2297) = raw31672 := by
      apply Matrix.ext; unfold tripleCharges sourceA2297 sourceB2297 sourceC2297 difference raw31672; decide +kernel
    rw [ha]
    exact (canonical31672 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2297 + difference 1 2) (sourceB2297 + difference 2 1) sourceC2297) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2218) := by
    have ha : (tripleCharges (sourceA2297 + difference 1 2) (sourceB2297 + difference 2 1) sourceC2297) = raw23390 := by
      apply Matrix.ext; unfold tripleCharges sourceA2297 sourceB2297 sourceC2297 difference raw23390; decide +kernel
    rw [ha]
    exact (canonical23390 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2297 + difference 1 3) (sourceB2297 + difference 3 1) sourceC2297) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2218) := by
    have ha : (tripleCharges (sourceA2297 + difference 1 3) (sourceB2297 + difference 3 1) sourceC2297) = raw23391 := by
      apply Matrix.ext; unfold tripleCharges sourceA2297 sourceB2297 sourceC2297 difference raw23391; decide +kernel
    rw [ha]
    exact (canonical23391 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2297 + difference 1 4) (sourceB2297 + difference 4 1) sourceC2297) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2281) := by
    have ha : (tripleCharges (sourceA2297 + difference 1 4) (sourceB2297 + difference 4 1) sourceC2297) = raw23392 := by
      apply Matrix.ext; unfold tripleCharges sourceA2297 sourceB2297 sourceC2297 difference raw23392; decide +kernel
    rw [ha]
    exact (canonical23392 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2297 + difference 1 5) (sourceB2297 + difference 5 1) sourceC2297) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2268) := by
    have ha : (tripleCharges (sourceA2297 + difference 1 5) (sourceB2297 + difference 5 1) sourceC2297) = raw23393 := by
      apply Matrix.ext; unfold tripleCharges sourceA2297 sourceB2297 sourceC2297 difference raw23393; decide +kernel
    rw [ha]
    exact (canonical23393 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2297 + difference 2 0) (sourceB2297 + difference 0 2) sourceC2297) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1669) := by
    have ha : (tripleCharges (sourceA2297 + difference 2 0) (sourceB2297 + difference 0 2) sourceC2297) = raw23400 := by
      apply Matrix.ext; unfold tripleCharges sourceA2297 sourceB2297 sourceC2297 difference raw23400; decide +kernel
    rw [ha]
    exact (canonical23400 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2297 + difference 2 1) (sourceB2297 + difference 1 2) sourceC2297) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2146) := by
    have ha : (tripleCharges (sourceA2297 + difference 2 1) (sourceB2297 + difference 1 2) sourceC2297) = raw31673 := by
      apply Matrix.ext; unfold tripleCharges sourceA2297 sourceB2297 sourceC2297 difference raw31673; decide +kernel
    rw [ha]
    exact (canonical31673 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2297 + difference 2 3) (sourceB2297 + difference 3 2) sourceC2297) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2171) := by
    have ha : (tripleCharges (sourceA2297 + difference 2 3) (sourceB2297 + difference 3 2) sourceC2297) = raw31674 := by
      apply Matrix.ext; unfold tripleCharges sourceA2297 sourceB2297 sourceC2297 difference raw31674; decide +kernel
    rw [ha]
    exact (canonical31674 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2297 + difference 2 4) (sourceB2297 + difference 4 2) sourceC2297) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2197) := by
    have ha : (tripleCharges (sourceA2297 + difference 2 4) (sourceB2297 + difference 4 2) sourceC2297) = raw31675 := by
      apply Matrix.ext; unfold tripleCharges sourceA2297 sourceB2297 sourceC2297 difference raw31675; decide +kernel
    rw [ha]
    exact (canonical31675 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2297 + difference 2 5) (sourceB2297 + difference 5 2) sourceC2297) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2193) := by
    have ha : (tripleCharges (sourceA2297 + difference 2 5) (sourceB2297 + difference 5 2) sourceC2297) = raw31676 := by
      apply Matrix.ext; unfold tripleCharges sourceA2297 sourceB2297 sourceC2297 difference raw31676; decide +kernel
    rw [ha]
    exact (canonical31676 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2297 + difference 3 0) (sourceB2297 + difference 0 3) sourceC2297) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1669) := by
    have ha : (tripleCharges (sourceA2297 + difference 3 0) (sourceB2297 + difference 0 3) sourceC2297) = raw23405 := by
      apply Matrix.ext; unfold tripleCharges sourceA2297 sourceB2297 sourceC2297 difference raw23405; decide +kernel
    rw [ha]
    exact (canonical23405 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2297 + difference 3 1) (sourceB2297 + difference 1 3) sourceC2297) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2146) := by
    have ha : (tripleCharges (sourceA2297 + difference 3 1) (sourceB2297 + difference 1 3) sourceC2297) = raw31677 := by
      apply Matrix.ext; unfold tripleCharges sourceA2297 sourceB2297 sourceC2297 difference raw31677; decide +kernel
    rw [ha]
    exact (canonical31677 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2297 + difference 3 2) (sourceB2297 + difference 2 3) sourceC2297) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2171) := by
    have ha : (tripleCharges (sourceA2297 + difference 3 2) (sourceB2297 + difference 2 3) sourceC2297) = raw31678 := by
      apply Matrix.ext; unfold tripleCharges sourceA2297 sourceB2297 sourceC2297 difference raw31678; decide +kernel
    rw [ha]
    exact (canonical31678 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2297 + difference 3 4) (sourceB2297 + difference 4 3) sourceC2297) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2197) := by
    have ha : (tripleCharges (sourceA2297 + difference 3 4) (sourceB2297 + difference 4 3) sourceC2297) = raw31679 := by
      apply Matrix.ext; unfold tripleCharges sourceA2297 sourceB2297 sourceC2297 difference raw31679; decide +kernel
    rw [ha]
    exact (canonical31679 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2297 + difference 3 5) (sourceB2297 + difference 5 3) sourceC2297) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2193) := by
    have ha : (tripleCharges (sourceA2297 + difference 3 5) (sourceB2297 + difference 5 3) sourceC2297) = raw31680 := by
      apply Matrix.ext; unfold tripleCharges sourceA2297 sourceB2297 sourceC2297 difference raw31680; decide +kernel
    rw [ha]
    exact (canonical31680 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2297 + difference 4 0) (sourceB2297 + difference 0 4) sourceC2297) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1683) := by
    have ha : (tripleCharges (sourceA2297 + difference 4 0) (sourceB2297 + difference 0 4) sourceC2297) = raw23410 := by
      apply Matrix.ext; unfold tripleCharges sourceA2297 sourceB2297 sourceC2297 difference raw23410; decide +kernel
    rw [ha]
    exact (canonical23410 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2297 + difference 4 1) (sourceB2297 + difference 1 4) sourceC2297) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2159) := by
    have ha : (tripleCharges (sourceA2297 + difference 4 1) (sourceB2297 + difference 1 4) sourceC2297) = raw31681 := by
      apply Matrix.ext; unfold tripleCharges sourceA2297 sourceB2297 sourceC2297 difference raw31681; decide +kernel
    rw [ha]
    exact (canonical31681 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2297 + difference 4 2) (sourceB2297 + difference 2 4) sourceC2297) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2143) := by
    have ha : (tripleCharges (sourceA2297 + difference 4 2) (sourceB2297 + difference 2 4) sourceC2297) = raw31682 := by
      apply Matrix.ext; unfold tripleCharges sourceA2297 sourceB2297 sourceC2297 difference raw31682; decide +kernel
    rw [ha]
    exact (canonical31682 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2297 + difference 4 3) (sourceB2297 + difference 3 4) sourceC2297) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2143) := by
    have ha : (tripleCharges (sourceA2297 + difference 4 3) (sourceB2297 + difference 3 4) sourceC2297) = raw31683 := by
      apply Matrix.ext; unfold tripleCharges sourceA2297 sourceB2297 sourceC2297 difference raw31683; decide +kernel
    rw [ha]
    exact (canonical31683 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2297 + difference 4 5) (sourceB2297 + difference 5 4) sourceC2297) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2208) := by
    have ha : (tripleCharges (sourceA2297 + difference 4 5) (sourceB2297 + difference 5 4) sourceC2297) = raw31684 := by
      apply Matrix.ext; unfold tripleCharges sourceA2297 sourceB2297 sourceC2297 difference raw31684; decide +kernel
    rw [ha]
    exact (canonical31684 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2297 + difference 5 0) (sourceB2297 + difference 0 5) sourceC2297) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1687) := by
    have ha : (tripleCharges (sourceA2297 + difference 5 0) (sourceB2297 + difference 0 5) sourceC2297) = raw23415 := by
      apply Matrix.ext; unfold tripleCharges sourceA2297 sourceB2297 sourceC2297 difference raw23415; decide +kernel
    rw [ha]
    exact (canonical23415 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2297 + difference 5 1) (sourceB2297 + difference 1 5) sourceC2297) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2163) := by
    have ha : (tripleCharges (sourceA2297 + difference 5 1) (sourceB2297 + difference 1 5) sourceC2297) = raw31685 := by
      apply Matrix.ext; unfold tripleCharges sourceA2297 sourceB2297 sourceC2297 difference raw31685; decide +kernel
    rw [ha]
    exact (canonical31685 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2297 + difference 5 2) (sourceB2297 + difference 2 5) sourceC2297) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2180) := by
    have ha : (tripleCharges (sourceA2297 + difference 5 2) (sourceB2297 + difference 2 5) sourceC2297) = raw31686 := by
      apply Matrix.ext; unfold tripleCharges sourceA2297 sourceB2297 sourceC2297 difference raw31686; decide +kernel
    rw [ha]
    exact (canonical31686 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2297 + difference 5 3) (sourceB2297 + difference 3 5) sourceC2297) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2180) := by
    have ha : (tripleCharges (sourceA2297 + difference 5 3) (sourceB2297 + difference 3 5) sourceC2297) = raw31687 := by
      apply Matrix.ext; unfold tripleCharges sourceA2297 sourceB2297 sourceC2297 difference raw31687; decide +kernel
    rw [ha]
    exact (canonical31687 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2297 + difference 5 4) (sourceB2297 + difference 4 5) sourceC2297) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2222) := by
    have ha : (tripleCharges (sourceA2297 + difference 5 4) (sourceB2297 + difference 4 5) sourceC2297) = raw31688 := by
      apply Matrix.ext; unfold tripleCharges sourceA2297 sourceB2297 sourceC2297 difference raw31688; decide +kernel
    rw [ha]
    exact (canonical31688 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2297 sourceB2297 sourceC2297
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2297, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2298 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2298 : Charge := ![0, 1, 0, 0, 1, -2]
def sourceC2298 : Charge := ![3, 0, 0, 0, -3, 0]
def sourceForm2298 : Integer.Sparse Master := [(Sum.inr 1809, 2), (Sum.inr 1817, 1), (Sum.inr 1820, 1), (Sum.inr 2065, 1), (Sum.inr 3396, 1), (Sum.inr 4085, -1)]

theorem sourceEq2298 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2298 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2298 + difference 0 1) (sourceB2298 + difference 1 0) sourceC2298) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3396) := by
    have ha : (tripleCharges (sourceA2298 + difference 0 1) (sourceB2298 + difference 1 0) sourceC2298) = raw31689 := by
      apply Matrix.ext; unfold tripleCharges sourceA2298 sourceB2298 sourceC2298 difference raw31689; decide +kernel
    rw [ha]
    exact (canonical31689 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2298 + difference 1 1) (sourceB2298 + difference 1 1) sourceC2298) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2065) := by
    have ha : (tripleCharges (sourceA2298 + difference 1 1) (sourceB2298 + difference 1 1) sourceC2298) = raw27312 := by
      apply Matrix.ext; unfold tripleCharges sourceA2298 sourceB2298 sourceC2298 difference raw27312; decide +kernel
    rw [ha]
    exact (canonical27312 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2298 + difference 2 1) (sourceB2298 + difference 1 2) sourceC2298) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1809) := by
    have ha : (tripleCharges (sourceA2298 + difference 2 1) (sourceB2298 + difference 1 2) sourceC2298) = raw31690 := by
      apply Matrix.ext; unfold tripleCharges sourceA2298 sourceB2298 sourceC2298 difference raw31690; decide +kernel
    rw [ha]
    exact (canonical31690 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2298 + difference 3 1) (sourceB2298 + difference 1 3) sourceC2298) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1809) := by
    have ha : (tripleCharges (sourceA2298 + difference 3 1) (sourceB2298 + difference 1 3) sourceC2298) = raw31691 := by
      apply Matrix.ext; unfold tripleCharges sourceA2298 sourceB2298 sourceC2298 difference raw31691; decide +kernel
    rw [ha]
    exact (canonical31691 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2298 + difference 4 1) (sourceB2298 + difference 1 4) sourceC2298) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1817) := by
    have ha : (tripleCharges (sourceA2298 + difference 4 1) (sourceB2298 + difference 1 4) sourceC2298) = raw31692 := by
      apply Matrix.ext; unfold tripleCharges sourceA2298 sourceB2298 sourceC2298 difference raw31692; decide +kernel
    rw [ha]
    exact (canonical31692 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2298 + difference 5 1) (sourceB2298 + difference 1 5) sourceC2298) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1820) := by
    have ha : (tripleCharges (sourceA2298 + difference 5 1) (sourceB2298 + difference 1 5) sourceC2298) = raw27309 := by
      apply Matrix.ext; unfold tripleCharges sourceA2298 sourceB2298 sourceC2298 difference raw27309; decide +kernel
    rw [ha]
    exact (canonical27309 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2298 + sourceB2298) sourceC2298) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA2298 + sourceB2298) sourceC2298) = raw3517 := by
      apply Matrix.ext; unfold doubleCharges sourceA2298 sourceB2298 sourceC2298 raw3517; decide +kernel
    rw [ha]
    exact (canonical3517 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2298 sourceB2298 sourceC2298
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2298, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2299 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2299 : Charge := ![0, 1, 0, 0, 1, -2]
def sourceC2299 : Charge := ![3, 0, 0, 0, -3, 0]
def sourceForm2299 : Integer.Sparse Master := [(Sum.inr 926, 1), (Sum.inr 1809, 1), (Sum.inr 1962, 1), (Sum.inr 2052, 1), (Sum.inr 2055, 1), (Sum.inr 2065, 1), (Sum.inr 4085, -1)]

theorem sourceEq2299 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2299 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2299 + difference 2 0) (sourceB2299 + difference 0 2) sourceC2299) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 926) := by
    have ha : (tripleCharges (sourceA2299 + difference 2 0) (sourceB2299 + difference 0 2) sourceC2299) = raw31693 := by
      apply Matrix.ext; unfold tripleCharges sourceA2299 sourceB2299 sourceC2299 difference raw31693; decide +kernel
    rw [ha]
    exact (canonical31693 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2299 + difference 2 1) (sourceB2299 + difference 1 2) sourceC2299) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1809) := by
    have ha : (tripleCharges (sourceA2299 + difference 2 1) (sourceB2299 + difference 1 2) sourceC2299) = raw31690 := by
      apply Matrix.ext; unfold tripleCharges sourceA2299 sourceB2299 sourceC2299 difference raw31690; decide +kernel
    rw [ha]
    exact (canonical31690 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2299 + difference 2 2) (sourceB2299 + difference 2 2) sourceC2299) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2065) := by
    have ha : (tripleCharges (sourceA2299 + difference 2 2) (sourceB2299 + difference 2 2) sourceC2299) = raw27312 := by
      apply Matrix.ext; unfold tripleCharges sourceA2299 sourceB2299 sourceC2299 difference raw27312; decide +kernel
    rw [ha]
    exact (canonical27312 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2299 + difference 2 3) (sourceB2299 + difference 3 2) sourceC2299) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1962) := by
    have ha : (tripleCharges (sourceA2299 + difference 2 3) (sourceB2299 + difference 3 2) sourceC2299) = raw31694 := by
      apply Matrix.ext; unfold tripleCharges sourceA2299 sourceB2299 sourceC2299 difference raw31694; decide +kernel
    rw [ha]
    exact (canonical31694 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2299 + difference 2 4) (sourceB2299 + difference 4 2) sourceC2299) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2055) := by
    have ha : (tripleCharges (sourceA2299 + difference 2 4) (sourceB2299 + difference 4 2) sourceC2299) = raw31695 := by
      apply Matrix.ext; unfold tripleCharges sourceA2299 sourceB2299 sourceC2299 difference raw31695; decide +kernel
    rw [ha]
    exact (canonical31695 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2299 + difference 2 5) (sourceB2299 + difference 5 2) sourceC2299) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2052) := by
    have ha : (tripleCharges (sourceA2299 + difference 2 5) (sourceB2299 + difference 5 2) sourceC2299) = raw31696 := by
      apply Matrix.ext; unfold tripleCharges sourceA2299 sourceB2299 sourceC2299 difference raw31696; decide +kernel
    rw [ha]
    exact (canonical31696 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2299 + sourceB2299) sourceC2299) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA2299 + sourceB2299) sourceC2299) = raw3517 := by
      apply Matrix.ext; unfold doubleCharges sourceA2299 sourceB2299 sourceC2299 raw3517; decide +kernel
    rw [ha]
    exact (canonical3517 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2299 sourceB2299 sourceC2299
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2299, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2300 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2300 : Charge := ![3, 0, 0, 0, -3, 0]
def sourceC2300 : Charge := ![0, 1, 0, 0, 1, -2]
def sourceForm2300 : Integer.Sparse Master := [(Sum.inr 4220, 2), (Sum.inr 4226, 1), (Sum.inr 4229, 1), (Sum.inr 4272, 1), (Sum.inr 4377, 2), (Sum.inr 4382, 1), (Sum.inr 4454, 1), (Sum.inr 4651, 2), (Sum.inr 4657, 1), (Sum.inr 4714, 2), (Sum.inr 4719, 2), (Sum.inr 4744, 2), (Sum.inr 4827, 2), (Sum.inr 4839, 2), (Sum.inr 4843, 1), (Sum.inr 4868, 1), (Sum.inr 4896, 1), (Sum.inr 5228, 2), (Sum.inr 5238, 1), (Sum.inr 5291, 1), (Sum.inr 5443, 1)]

theorem sourceEq2300 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2300 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2300 + difference 0 1) (sourceB2300 + difference 1 0) sourceC2300) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5238) := by
    have ha : (tripleCharges (sourceA2300 + difference 0 1) (sourceB2300 + difference 1 0) sourceC2300) = raw14934 := by
      apply Matrix.ext; unfold tripleCharges sourceA2300 sourceB2300 sourceC2300 difference raw14934; decide +kernel
    rw [ha]
    exact (canonical14934 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2300 + difference 0 2) (sourceB2300 + difference 2 0) sourceC2300) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5228) := by
    have ha : (tripleCharges (sourceA2300 + difference 0 2) (sourceB2300 + difference 2 0) sourceC2300) = raw14935 := by
      apply Matrix.ext; unfold tripleCharges sourceA2300 sourceB2300 sourceC2300 difference raw14935; decide +kernel
    rw [ha]
    exact (canonical14935 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2300 + difference 0 3) (sourceB2300 + difference 3 0) sourceC2300) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5228) := by
    have ha : (tripleCharges (sourceA2300 + difference 0 3) (sourceB2300 + difference 3 0) sourceC2300) = raw14936 := by
      apply Matrix.ext; unfold tripleCharges sourceA2300 sourceB2300 sourceC2300 difference raw14936; decide +kernel
    rw [ha]
    exact (canonical14936 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2300 + difference 0 4) (sourceB2300 + difference 4 0) sourceC2300) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA2300 + difference 0 4) (sourceB2300 + difference 4 0) sourceC2300) = raw31697 := by
      apply Matrix.ext; unfold tripleCharges sourceA2300 sourceB2300 sourceC2300 difference raw31697; decide +kernel
    rw [ha]
    exact (canonical31697 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2300 + difference 0 5) (sourceB2300 + difference 5 0) sourceC2300) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5291) := by
    have ha : (tripleCharges (sourceA2300 + difference 0 5) (sourceB2300 + difference 5 0) sourceC2300) = raw14937 := by
      apply Matrix.ext; unfold tripleCharges sourceA2300 sourceB2300 sourceC2300 difference raw14937; decide +kernel
    rw [ha]
    exact (canonical14937 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2300 + difference 1 0) (sourceB2300 + difference 0 1) sourceC2300) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4272) := by
    have ha : (tripleCharges (sourceA2300 + difference 1 0) (sourceB2300 + difference 0 1) sourceC2300) = raw31698 := by
      apply Matrix.ext; unfold tripleCharges sourceA2300 sourceB2300 sourceC2300 difference raw31698; decide +kernel
    rw [ha]
    exact (canonical31698 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2300 + difference 1 2) (sourceB2300 + difference 2 1) sourceC2300) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4744) := by
    have ha : (tripleCharges (sourceA2300 + difference 1 2) (sourceB2300 + difference 2 1) sourceC2300) = raw31699 := by
      apply Matrix.ext; unfold tripleCharges sourceA2300 sourceB2300 sourceC2300 difference raw31699; decide +kernel
    rw [ha]
    exact (canonical31699 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2300 + difference 1 3) (sourceB2300 + difference 3 1) sourceC2300) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4744) := by
    have ha : (tripleCharges (sourceA2300 + difference 1 3) (sourceB2300 + difference 3 1) sourceC2300) = raw31700 := by
      apply Matrix.ext; unfold tripleCharges sourceA2300 sourceB2300 sourceC2300 difference raw31700; decide +kernel
    rw [ha]
    exact (canonical31700 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2300 + difference 1 4) (sourceB2300 + difference 4 1) sourceC2300) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4896) := by
    have ha : (tripleCharges (sourceA2300 + difference 1 4) (sourceB2300 + difference 4 1) sourceC2300) = raw14918 := by
      apply Matrix.ext; unfold tripleCharges sourceA2300 sourceB2300 sourceC2300 difference raw14918; decide +kernel
    rw [ha]
    exact (canonical14918 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2300 + difference 1 5) (sourceB2300 + difference 5 1) sourceC2300) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4868) := by
    have ha : (tripleCharges (sourceA2300 + difference 1 5) (sourceB2300 + difference 5 1) sourceC2300) = raw31701 := by
      apply Matrix.ext; unfold tripleCharges sourceA2300 sourceB2300 sourceC2300 difference raw31701; decide +kernel
    rw [ha]
    exact (canonical31701 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2300 + difference 2 0) (sourceB2300 + difference 0 2) sourceC2300) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4220) := by
    have ha : (tripleCharges (sourceA2300 + difference 2 0) (sourceB2300 + difference 0 2) sourceC2300) = raw31702 := by
      apply Matrix.ext; unfold tripleCharges sourceA2300 sourceB2300 sourceC2300 difference raw31702; decide +kernel
    rw [ha]
    exact (canonical31702 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2300 + difference 2 1) (sourceB2300 + difference 1 2) sourceC2300) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4651) := by
    have ha : (tripleCharges (sourceA2300 + difference 2 1) (sourceB2300 + difference 1 2) sourceC2300) = raw31703 := by
      apply Matrix.ext; unfold tripleCharges sourceA2300 sourceB2300 sourceC2300 difference raw31703; decide +kernel
    rw [ha]
    exact (canonical31703 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2300 + difference 2 3) (sourceB2300 + difference 3 2) sourceC2300) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4714) := by
    have ha : (tripleCharges (sourceA2300 + difference 2 3) (sourceB2300 + difference 3 2) sourceC2300) = raw31704 := by
      apply Matrix.ext; unfold tripleCharges sourceA2300 sourceB2300 sourceC2300 difference raw31704; decide +kernel
    rw [ha]
    exact (canonical31704 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2300 + difference 2 4) (sourceB2300 + difference 4 2) sourceC2300) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4839) := by
    have ha : (tripleCharges (sourceA2300 + difference 2 4) (sourceB2300 + difference 4 2) sourceC2300) = raw14923 := by
      apply Matrix.ext; unfold tripleCharges sourceA2300 sourceB2300 sourceC2300 difference raw14923; decide +kernel
    rw [ha]
    exact (canonical14923 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2300 + difference 2 5) (sourceB2300 + difference 5 2) sourceC2300) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4827) := by
    have ha : (tripleCharges (sourceA2300 + difference 2 5) (sourceB2300 + difference 5 2) sourceC2300) = raw31705 := by
      apply Matrix.ext; unfold tripleCharges sourceA2300 sourceB2300 sourceC2300 difference raw31705; decide +kernel
    rw [ha]
    exact (canonical31705 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2300 + difference 3 0) (sourceB2300 + difference 0 3) sourceC2300) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4220) := by
    have ha : (tripleCharges (sourceA2300 + difference 3 0) (sourceB2300 + difference 0 3) sourceC2300) = raw31706 := by
      apply Matrix.ext; unfold tripleCharges sourceA2300 sourceB2300 sourceC2300 difference raw31706; decide +kernel
    rw [ha]
    exact (canonical31706 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2300 + difference 3 1) (sourceB2300 + difference 1 3) sourceC2300) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4651) := by
    have ha : (tripleCharges (sourceA2300 + difference 3 1) (sourceB2300 + difference 1 3) sourceC2300) = raw31707 := by
      apply Matrix.ext; unfold tripleCharges sourceA2300 sourceB2300 sourceC2300 difference raw31707; decide +kernel
    rw [ha]
    exact (canonical31707 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2300 + difference 3 2) (sourceB2300 + difference 2 3) sourceC2300) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4714) := by
    have ha : (tripleCharges (sourceA2300 + difference 3 2) (sourceB2300 + difference 2 3) sourceC2300) = raw31708 := by
      apply Matrix.ext; unfold tripleCharges sourceA2300 sourceB2300 sourceC2300 difference raw31708; decide +kernel
    rw [ha]
    exact (canonical31708 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2300 + difference 3 4) (sourceB2300 + difference 4 3) sourceC2300) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4839) := by
    have ha : (tripleCharges (sourceA2300 + difference 3 4) (sourceB2300 + difference 4 3) sourceC2300) = raw14928 := by
      apply Matrix.ext; unfold tripleCharges sourceA2300 sourceB2300 sourceC2300 difference raw14928; decide +kernel
    rw [ha]
    exact (canonical14928 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2300 + difference 3 5) (sourceB2300 + difference 5 3) sourceC2300) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4827) := by
    have ha : (tripleCharges (sourceA2300 + difference 3 5) (sourceB2300 + difference 5 3) sourceC2300) = raw31709 := by
      apply Matrix.ext; unfold tripleCharges sourceA2300 sourceB2300 sourceC2300 difference raw31709; decide +kernel
    rw [ha]
    exact (canonical31709 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2300 + difference 4 0) (sourceB2300 + difference 0 4) sourceC2300) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4226) := by
    have ha : (tripleCharges (sourceA2300 + difference 4 0) (sourceB2300 + difference 0 4) sourceC2300) = raw31710 := by
      apply Matrix.ext; unfold tripleCharges sourceA2300 sourceB2300 sourceC2300 difference raw31710; decide +kernel
    rw [ha]
    exact (canonical31710 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2300 + difference 4 1) (sourceB2300 + difference 1 4) sourceC2300) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4382) := by
    have ha : (tripleCharges (sourceA2300 + difference 4 1) (sourceB2300 + difference 1 4) sourceC2300) = raw31711 := by
      apply Matrix.ext; unfold tripleCharges sourceA2300 sourceB2300 sourceC2300 difference raw31711; decide +kernel
    rw [ha]
    exact (canonical31711 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2300 + difference 4 2) (sourceB2300 + difference 2 4) sourceC2300) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4377) := by
    have ha : (tripleCharges (sourceA2300 + difference 4 2) (sourceB2300 + difference 2 4) sourceC2300) = raw31712 := by
      apply Matrix.ext; unfold tripleCharges sourceA2300 sourceB2300 sourceC2300 difference raw31712; decide +kernel
    rw [ha]
    exact (canonical31712 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2300 + difference 4 3) (sourceB2300 + difference 3 4) sourceC2300) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4377) := by
    have ha : (tripleCharges (sourceA2300 + difference 4 3) (sourceB2300 + difference 3 4) sourceC2300) = raw31713 := by
      apply Matrix.ext; unfold tripleCharges sourceA2300 sourceB2300 sourceC2300 difference raw31713; decide +kernel
    rw [ha]
    exact (canonical31713 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2300 + difference 4 5) (sourceB2300 + difference 5 4) sourceC2300) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4454) := by
    have ha : (tripleCharges (sourceA2300 + difference 4 5) (sourceB2300 + difference 5 4) sourceC2300) = raw31714 := by
      apply Matrix.ext; unfold tripleCharges sourceA2300 sourceB2300 sourceC2300 difference raw31714; decide +kernel
    rw [ha]
    exact (canonical31714 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2300 + difference 5 0) (sourceB2300 + difference 0 5) sourceC2300) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4229) := by
    have ha : (tripleCharges (sourceA2300 + difference 5 0) (sourceB2300 + difference 0 5) sourceC2300) = raw31715 := by
      apply Matrix.ext; unfold tripleCharges sourceA2300 sourceB2300 sourceC2300 difference raw31715; decide +kernel
    rw [ha]
    exact (canonical31715 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2300 + difference 5 1) (sourceB2300 + difference 1 5) sourceC2300) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4657) := by
    have ha : (tripleCharges (sourceA2300 + difference 5 1) (sourceB2300 + difference 1 5) sourceC2300) = raw31716 := by
      apply Matrix.ext; unfold tripleCharges sourceA2300 sourceB2300 sourceC2300 difference raw31716; decide +kernel
    rw [ha]
    exact (canonical31716 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2300 + difference 5 2) (sourceB2300 + difference 2 5) sourceC2300) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4719) := by
    have ha : (tripleCharges (sourceA2300 + difference 5 2) (sourceB2300 + difference 2 5) sourceC2300) = raw31717 := by
      apply Matrix.ext; unfold tripleCharges sourceA2300 sourceB2300 sourceC2300 difference raw31717; decide +kernel
    rw [ha]
    exact (canonical31717 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2300 + difference 5 3) (sourceB2300 + difference 3 5) sourceC2300) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4719) := by
    have ha : (tripleCharges (sourceA2300 + difference 5 3) (sourceB2300 + difference 3 5) sourceC2300) = raw31718 := by
      apply Matrix.ext; unfold tripleCharges sourceA2300 sourceB2300 sourceC2300 difference raw31718; decide +kernel
    rw [ha]
    exact (canonical31718 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2300 + difference 5 4) (sourceB2300 + difference 4 5) sourceC2300) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4843) := by
    have ha : (tripleCharges (sourceA2300 + difference 5 4) (sourceB2300 + difference 4 5) sourceC2300) = raw14938 := by
      apply Matrix.ext; unfold tripleCharges sourceA2300 sourceB2300 sourceC2300 difference raw14938; decide +kernel
    rw [ha]
    exact (canonical14938 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2300 sourceB2300 sourceC2300
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2300, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2301 : Charge := ![0, 1, 0, 0, 1, -2]
def sourceB2301 : Charge := ![3, 0, 0, 0, -3, 0]
def sourceC2301 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceForm2301 : Integer.Sparse Master := [(Sum.inr 4408, 2), (Sum.inr 4413, 1), (Sum.inr 4428, 1), (Sum.inr 4472, 1), (Sum.inr 4562, 2), (Sum.inr 4572, 1), (Sum.inr 4610, 1), (Sum.inr 4744, 2), (Sum.inr 4753, 1), (Sum.inr 4781, 2), (Sum.inr 4788, 2), (Sum.inr 4809, 2), (Sum.inr 4810, 2), (Sum.inr 4814, 2), (Sum.inr 4846, 1), (Sum.inr 4873, 1), (Sum.inr 4874, 1), (Sum.inr 5110, 1), (Sum.inr 5140, 2), (Sum.inr 5175, 1), (Sum.inr 5176, 1)]

theorem sourceEq2301 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2301 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2301 + difference 0 1) (sourceB2301 + difference 1 0) sourceC2301) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5110) := by
    have ha : (tripleCharges (sourceA2301 + difference 0 1) (sourceB2301 + difference 1 0) sourceC2301) = raw30377 := by
      apply Matrix.ext; unfold tripleCharges sourceA2301 sourceB2301 sourceC2301 difference raw30377; decide +kernel
    rw [ha]
    exact (canonical30377 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2301 + difference 0 2) (sourceB2301 + difference 2 0) sourceC2301) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5140) := by
    have ha : (tripleCharges (sourceA2301 + difference 0 2) (sourceB2301 + difference 2 0) sourceC2301) = raw30688 := by
      apply Matrix.ext; unfold tripleCharges sourceA2301 sourceB2301 sourceC2301 difference raw30688; decide +kernel
    rw [ha]
    exact (canonical30688 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2301 + difference 0 3) (sourceB2301 + difference 3 0) sourceC2301) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5140) := by
    have ha : (tripleCharges (sourceA2301 + difference 0 3) (sourceB2301 + difference 3 0) sourceC2301) = raw30181 := by
      apply Matrix.ext; unfold tripleCharges sourceA2301 sourceB2301 sourceC2301 difference raw30181; decide +kernel
    rw [ha]
    exact (canonical30181 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2301 + difference 0 4) (sourceB2301 + difference 4 0) sourceC2301) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5176) := by
    have ha : (tripleCharges (sourceA2301 + difference 0 4) (sourceB2301 + difference 4 0) sourceC2301) = raw29694 := by
      apply Matrix.ext; unfold tripleCharges sourceA2301 sourceB2301 sourceC2301 difference raw29694; decide +kernel
    rw [ha]
    exact (canonical29694 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2301 + difference 0 5) (sourceB2301 + difference 5 0) sourceC2301) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5175) := by
    have ha : (tripleCharges (sourceA2301 + difference 0 5) (sourceB2301 + difference 5 0) sourceC2301) = raw30689 := by
      apply Matrix.ext; unfold tripleCharges sourceA2301 sourceB2301 sourceC2301 difference raw30689; decide +kernel
    rw [ha]
    exact (canonical30689 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2301 + difference 1 0) (sourceB2301 + difference 0 1) sourceC2301) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4472) := by
    have ha : (tripleCharges (sourceA2301 + difference 1 0) (sourceB2301 + difference 0 1) sourceC2301) = raw31075 := by
      apply Matrix.ext; unfold tripleCharges sourceA2301 sourceB2301 sourceC2301 difference raw31075; decide +kernel
    rw [ha]
    exact (canonical31075 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2301 + difference 1 2) (sourceB2301 + difference 2 1) sourceC2301) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4814) := by
    have ha : (tripleCharges (sourceA2301 + difference 1 2) (sourceB2301 + difference 2 1) sourceC2301) = raw31076 := by
      apply Matrix.ext; unfold tripleCharges sourceA2301 sourceB2301 sourceC2301 difference raw31076; decide +kernel
    rw [ha]
    exact (canonical31076 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2301 + difference 1 3) (sourceB2301 + difference 3 1) sourceC2301) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4814) := by
    have ha : (tripleCharges (sourceA2301 + difference 1 3) (sourceB2301 + difference 3 1) sourceC2301) = raw31077 := by
      apply Matrix.ext; unfold tripleCharges sourceA2301 sourceB2301 sourceC2301 difference raw31077; decide +kernel
    rw [ha]
    exact (canonical31077 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2301 + difference 1 4) (sourceB2301 + difference 4 1) sourceC2301) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4874) := by
    have ha : (tripleCharges (sourceA2301 + difference 1 4) (sourceB2301 + difference 4 1) sourceC2301) = raw31241 := by
      apply Matrix.ext; unfold tripleCharges sourceA2301 sourceB2301 sourceC2301 difference raw31241; decide +kernel
    rw [ha]
    exact (canonical31241 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2301 + difference 1 5) (sourceB2301 + difference 5 1) sourceC2301) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4873) := by
    have ha : (tripleCharges (sourceA2301 + difference 1 5) (sourceB2301 + difference 5 1) sourceC2301) = raw31078 := by
      apply Matrix.ext; unfold tripleCharges sourceA2301 sourceB2301 sourceC2301 difference raw31078; decide +kernel
    rw [ha]
    exact (canonical31078 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2301 + difference 2 0) (sourceB2301 + difference 0 2) sourceC2301) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4408) := by
    have ha : (tripleCharges (sourceA2301 + difference 2 0) (sourceB2301 + difference 0 2) sourceC2301) = raw31431 := by
      apply Matrix.ext; unfold tripleCharges sourceA2301 sourceB2301 sourceC2301 difference raw31431; decide +kernel
    rw [ha]
    exact (canonical31431 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2301 + difference 2 1) (sourceB2301 + difference 1 2) sourceC2301) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4744) := by
    have ha : (tripleCharges (sourceA2301 + difference 2 1) (sourceB2301 + difference 1 2) sourceC2301) = raw30375 := by
      apply Matrix.ext; unfold tripleCharges sourceA2301 sourceB2301 sourceC2301 difference raw30375; decide +kernel
    rw [ha]
    exact (canonical30375 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2301 + difference 2 3) (sourceB2301 + difference 3 2) sourceC2301) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4781) := by
    have ha : (tripleCharges (sourceA2301 + difference 2 3) (sourceB2301 + difference 3 2) sourceC2301) = raw31432 := by
      apply Matrix.ext; unfold tripleCharges sourceA2301 sourceB2301 sourceC2301 difference raw31432; decide +kernel
    rw [ha]
    exact (canonical31432 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2301 + difference 2 4) (sourceB2301 + difference 4 2) sourceC2301) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4810) := by
    have ha : (tripleCharges (sourceA2301 + difference 2 4) (sourceB2301 + difference 4 2) sourceC2301) = raw30363 := by
      apply Matrix.ext; unfold tripleCharges sourceA2301 sourceB2301 sourceC2301 difference raw30363; decide +kernel
    rw [ha]
    exact (canonical30363 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2301 + difference 2 5) (sourceB2301 + difference 5 2) sourceC2301) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4809) := by
    have ha : (tripleCharges (sourceA2301 + difference 2 5) (sourceB2301 + difference 5 2) sourceC2301) = raw31433 := by
      apply Matrix.ext; unfold tripleCharges sourceA2301 sourceB2301 sourceC2301 difference raw31433; decide +kernel
    rw [ha]
    exact (canonical31433 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2301 + difference 3 0) (sourceB2301 + difference 0 3) sourceC2301) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4408) := by
    have ha : (tripleCharges (sourceA2301 + difference 3 0) (sourceB2301 + difference 0 3) sourceC2301) = raw31719 := by
      apply Matrix.ext; unfold tripleCharges sourceA2301 sourceB2301 sourceC2301 difference raw31719; decide +kernel
    rw [ha]
    exact (canonical31719 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2301 + difference 3 1) (sourceB2301 + difference 1 3) sourceC2301) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4744) := by
    have ha : (tripleCharges (sourceA2301 + difference 3 1) (sourceB2301 + difference 1 3) sourceC2301) = raw30690 := by
      apply Matrix.ext; unfold tripleCharges sourceA2301 sourceB2301 sourceC2301 difference raw30690; decide +kernel
    rw [ha]
    exact (canonical30690 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2301 + difference 3 2) (sourceB2301 + difference 2 3) sourceC2301) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4781) := by
    have ha : (tripleCharges (sourceA2301 + difference 3 2) (sourceB2301 + difference 2 3) sourceC2301) = raw31720 := by
      apply Matrix.ext; unfold tripleCharges sourceA2301 sourceB2301 sourceC2301 difference raw31720; decide +kernel
    rw [ha]
    exact (canonical31720 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2301 + difference 3 4) (sourceB2301 + difference 4 3) sourceC2301) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4810) := by
    have ha : (tripleCharges (sourceA2301 + difference 3 4) (sourceB2301 + difference 4 3) sourceC2301) = raw31071 := by
      apply Matrix.ext; unfold tripleCharges sourceA2301 sourceB2301 sourceC2301 difference raw31071; decide +kernel
    rw [ha]
    exact (canonical31071 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2301 + difference 3 5) (sourceB2301 + difference 5 3) sourceC2301) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4809) := by
    have ha : (tripleCharges (sourceA2301 + difference 3 5) (sourceB2301 + difference 5 3) sourceC2301) = raw31721 := by
      apply Matrix.ext; unfold tripleCharges sourceA2301 sourceB2301 sourceC2301 difference raw31721; decide +kernel
    rw [ha]
    exact (canonical31721 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2301 + difference 4 0) (sourceB2301 + difference 0 4) sourceC2301) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4413) := by
    have ha : (tripleCharges (sourceA2301 + difference 4 0) (sourceB2301 + difference 0 4) sourceC2301) = raw31722 := by
      apply Matrix.ext; unfold tripleCharges sourceA2301 sourceB2301 sourceC2301 difference raw31722; decide +kernel
    rw [ha]
    exact (canonical31722 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2301 + difference 4 1) (sourceB2301 + difference 1 4) sourceC2301) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4572) := by
    have ha : (tripleCharges (sourceA2301 + difference 4 1) (sourceB2301 + difference 1 4) sourceC2301) = raw30694 := by
      apply Matrix.ext; unfold tripleCharges sourceA2301 sourceB2301 sourceC2301 difference raw30694; decide +kernel
    rw [ha]
    exact (canonical30694 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2301 + difference 4 2) (sourceB2301 + difference 2 4) sourceC2301) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4562) := by
    have ha : (tripleCharges (sourceA2301 + difference 4 2) (sourceB2301 + difference 2 4) sourceC2301) = raw31723 := by
      apply Matrix.ext; unfold tripleCharges sourceA2301 sourceB2301 sourceC2301 difference raw31723; decide +kernel
    rw [ha]
    exact (canonical31723 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2301 + difference 4 3) (sourceB2301 + difference 3 4) sourceC2301) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4562) := by
    have ha : (tripleCharges (sourceA2301 + difference 4 3) (sourceB2301 + difference 3 4) sourceC2301) = raw31724 := by
      apply Matrix.ext; unfold tripleCharges sourceA2301 sourceB2301 sourceC2301 difference raw31724; decide +kernel
    rw [ha]
    exact (canonical31724 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2301 + difference 4 5) (sourceB2301 + difference 5 4) sourceC2301) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4610) := by
    have ha : (tripleCharges (sourceA2301 + difference 4 5) (sourceB2301 + difference 5 4) sourceC2301) = raw31725 := by
      apply Matrix.ext; unfold tripleCharges sourceA2301 sourceB2301 sourceC2301 difference raw31725; decide +kernel
    rw [ha]
    exact (canonical31725 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2301 + difference 5 0) (sourceB2301 + difference 0 5) sourceC2301) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4428) := by
    have ha : (tripleCharges (sourceA2301 + difference 5 0) (sourceB2301 + difference 0 5) sourceC2301) = raw31726 := by
      apply Matrix.ext; unfold tripleCharges sourceA2301 sourceB2301 sourceC2301 difference raw31726; decide +kernel
    rw [ha]
    exact (canonical31726 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2301 + difference 5 1) (sourceB2301 + difference 1 5) sourceC2301) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4753) := by
    have ha : (tripleCharges (sourceA2301 + difference 5 1) (sourceB2301 + difference 1 5) sourceC2301) = raw30699 := by
      apply Matrix.ext; unfold tripleCharges sourceA2301 sourceB2301 sourceC2301 difference raw30699; decide +kernel
    rw [ha]
    exact (canonical30699 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2301 + difference 5 2) (sourceB2301 + difference 2 5) sourceC2301) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4788) := by
    have ha : (tripleCharges (sourceA2301 + difference 5 2) (sourceB2301 + difference 2 5) sourceC2301) = raw31727 := by
      apply Matrix.ext; unfold tripleCharges sourceA2301 sourceB2301 sourceC2301 difference raw31727; decide +kernel
    rw [ha]
    exact (canonical31727 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2301 + difference 5 3) (sourceB2301 + difference 3 5) sourceC2301) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4788) := by
    have ha : (tripleCharges (sourceA2301 + difference 5 3) (sourceB2301 + difference 3 5) sourceC2301) = raw30177 := by
      apply Matrix.ext; unfold tripleCharges sourceA2301 sourceB2301 sourceC2301 difference raw30177; decide +kernel
    rw [ha]
    exact (canonical30177 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2301 + difference 5 4) (sourceB2301 + difference 4 5) sourceC2301) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4846) := by
    have ha : (tripleCharges (sourceA2301 + difference 5 4) (sourceB2301 + difference 4 5) sourceC2301) = raw29690 := by
      apply Matrix.ext; unfold tripleCharges sourceA2301 sourceB2301 sourceC2301 difference raw29690; decide +kernel
    rw [ha]
    exact (canonical29690 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2301 sourceB2301 sourceC2301
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2301, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2302 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2302 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC2302 : Charge := ![3, 0, 0, 0, -2, -1]
def sourceForm2302 : Integer.Sparse Master := [(Sum.inr 4084, 1), (Sum.inr 4349, 2), (Sum.inr 4360, 1), (Sum.inr 4361, 1), (Sum.inr 4511, 1), (Sum.inr 4684, 2), (Sum.inr 4692, 1), (Sum.inr 4693, 1), (Sum.inr 4763, 2), (Sum.inr 4769, 2), (Sum.inr 4770, 2), (Sum.inr 4834, 2), (Sum.inr 4835, 2), (Sum.inr 4841, 1), (Sum.inr 4843, 1), (Sum.inr 4846, 2), (Sum.inr 4901, 1), (Sum.inr 5238, 1), (Sum.inr 5248, 2), (Sum.inr 5274, 1), (Sum.inr 5275, 1)]

theorem sourceEq2302 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2302 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2302 + difference 0 1) (sourceB2302 + difference 1 0) sourceC2302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5238) := by
    have ha : (tripleCharges (sourceA2302 + difference 0 1) (sourceB2302 + difference 1 0) sourceC2302) = raw31728 := by
      apply Matrix.ext; unfold tripleCharges sourceA2302 sourceB2302 sourceC2302 difference raw31728; decide +kernel
    rw [ha]
    exact (canonical31728 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2302 + difference 0 2) (sourceB2302 + difference 2 0) sourceC2302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5248) := by
    have ha : (tripleCharges (sourceA2302 + difference 0 2) (sourceB2302 + difference 2 0) sourceC2302) = raw31729 := by
      apply Matrix.ext; unfold tripleCharges sourceA2302 sourceB2302 sourceC2302 difference raw31729; decide +kernel
    rw [ha]
    exact (canonical31729 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2302 + difference 0 3) (sourceB2302 + difference 3 0) sourceC2302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5248) := by
    have ha : (tripleCharges (sourceA2302 + difference 0 3) (sourceB2302 + difference 3 0) sourceC2302) = raw31730 := by
      apply Matrix.ext; unfold tripleCharges sourceA2302 sourceB2302 sourceC2302 difference raw31730; decide +kernel
    rw [ha]
    exact (canonical31730 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2302 + difference 0 4) (sourceB2302 + difference 4 0) sourceC2302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5275) := by
    have ha : (tripleCharges (sourceA2302 + difference 0 4) (sourceB2302 + difference 4 0) sourceC2302) = raw11501 := by
      apply Matrix.ext; unfold tripleCharges sourceA2302 sourceB2302 sourceC2302 difference raw11501; decide +kernel
    rw [ha]
    exact (canonical11501 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2302 + difference 0 5) (sourceB2302 + difference 5 0) sourceC2302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5274) := by
    have ha : (tripleCharges (sourceA2302 + difference 0 5) (sourceB2302 + difference 5 0) sourceC2302) = raw31731 := by
      apply Matrix.ext; unfold tripleCharges sourceA2302 sourceB2302 sourceC2302 difference raw31731; decide +kernel
    rw [ha]
    exact (canonical31731 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2302 + difference 1 0) (sourceB2302 + difference 0 1) sourceC2302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4511) := by
    have ha : (tripleCharges (sourceA2302 + difference 1 0) (sourceB2302 + difference 0 1) sourceC2302) = raw11521 := by
      apply Matrix.ext; unfold tripleCharges sourceA2302 sourceB2302 sourceC2302 difference raw11521; decide +kernel
    rw [ha]
    exact (canonical11521 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2302 + difference 1 2) (sourceB2302 + difference 2 1) sourceC2302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4846) := by
    have ha : (tripleCharges (sourceA2302 + difference 1 2) (sourceB2302 + difference 2 1) sourceC2302) = raw11523 := by
      apply Matrix.ext; unfold tripleCharges sourceA2302 sourceB2302 sourceC2302 difference raw11523; decide +kernel
    rw [ha]
    exact (canonical11523 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2302 + difference 1 3) (sourceB2302 + difference 3 1) sourceC2302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4846) := by
    have ha : (tripleCharges (sourceA2302 + difference 1 3) (sourceB2302 + difference 3 1) sourceC2302) = raw11524 := by
      apply Matrix.ext; unfold tripleCharges sourceA2302 sourceB2302 sourceC2302 difference raw11524; decide +kernel
    rw [ha]
    exact (canonical11524 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2302 + difference 1 4) (sourceB2302 + difference 4 1) sourceC2302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4901) := by
    have ha : (tripleCharges (sourceA2302 + difference 1 4) (sourceB2302 + difference 4 1) sourceC2302) = raw21634 := by
      apply Matrix.ext; unfold tripleCharges sourceA2302 sourceB2302 sourceC2302 difference raw21634; decide +kernel
    rw [ha]
    exact (canonical21634 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2302 + difference 1 5) (sourceB2302 + difference 5 1) sourceC2302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA2302 + difference 1 5) (sourceB2302 + difference 5 1) sourceC2302) = raw11525 := by
      apply Matrix.ext; unfold tripleCharges sourceA2302 sourceB2302 sourceC2302 difference raw11525; decide +kernel
    rw [ha]
    exact (canonical11525 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2302 + difference 2 0) (sourceB2302 + difference 0 2) sourceC2302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4349) := by
    have ha : (tripleCharges (sourceA2302 + difference 2 0) (sourceB2302 + difference 0 2) sourceC2302) = raw23523 := by
      apply Matrix.ext; unfold tripleCharges sourceA2302 sourceB2302 sourceC2302 difference raw23523; decide +kernel
    rw [ha]
    exact (canonical23523 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2302 + difference 2 1) (sourceB2302 + difference 1 2) sourceC2302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4684) := by
    have ha : (tripleCharges (sourceA2302 + difference 2 1) (sourceB2302 + difference 1 2) sourceC2302) = raw31732 := by
      apply Matrix.ext; unfold tripleCharges sourceA2302 sourceB2302 sourceC2302 difference raw31732; decide +kernel
    rw [ha]
    exact (canonical31732 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2302 + difference 2 3) (sourceB2302 + difference 3 2) sourceC2302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4763) := by
    have ha : (tripleCharges (sourceA2302 + difference 2 3) (sourceB2302 + difference 3 2) sourceC2302) = raw31733 := by
      apply Matrix.ext; unfold tripleCharges sourceA2302 sourceB2302 sourceC2302 difference raw31733; decide +kernel
    rw [ha]
    exact (canonical31733 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2302 + difference 2 4) (sourceB2302 + difference 4 2) sourceC2302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4835) := by
    have ha : (tripleCharges (sourceA2302 + difference 2 4) (sourceB2302 + difference 4 2) sourceC2302) = raw11512 := by
      apply Matrix.ext; unfold tripleCharges sourceA2302 sourceB2302 sourceC2302 difference raw11512; decide +kernel
    rw [ha]
    exact (canonical11512 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2302 + difference 2 5) (sourceB2302 + difference 5 2) sourceC2302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4834) := by
    have ha : (tripleCharges (sourceA2302 + difference 2 5) (sourceB2302 + difference 5 2) sourceC2302) = raw31734 := by
      apply Matrix.ext; unfold tripleCharges sourceA2302 sourceB2302 sourceC2302 difference raw31734; decide +kernel
    rw [ha]
    exact (canonical31734 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2302 + difference 3 0) (sourceB2302 + difference 0 3) sourceC2302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4349) := by
    have ha : (tripleCharges (sourceA2302 + difference 3 0) (sourceB2302 + difference 0 3) sourceC2302) = raw23527 := by
      apply Matrix.ext; unfold tripleCharges sourceA2302 sourceB2302 sourceC2302 difference raw23527; decide +kernel
    rw [ha]
    exact (canonical23527 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2302 + difference 3 1) (sourceB2302 + difference 1 3) sourceC2302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4684) := by
    have ha : (tripleCharges (sourceA2302 + difference 3 1) (sourceB2302 + difference 1 3) sourceC2302) = raw31735 := by
      apply Matrix.ext; unfold tripleCharges sourceA2302 sourceB2302 sourceC2302 difference raw31735; decide +kernel
    rw [ha]
    exact (canonical31735 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2302 + difference 3 2) (sourceB2302 + difference 2 3) sourceC2302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4763) := by
    have ha : (tripleCharges (sourceA2302 + difference 3 2) (sourceB2302 + difference 2 3) sourceC2302) = raw31736 := by
      apply Matrix.ext; unfold tripleCharges sourceA2302 sourceB2302 sourceC2302 difference raw31736; decide +kernel
    rw [ha]
    exact (canonical31736 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2302 + difference 3 4) (sourceB2302 + difference 4 3) sourceC2302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4835) := by
    have ha : (tripleCharges (sourceA2302 + difference 3 4) (sourceB2302 + difference 4 3) sourceC2302) = raw11517 := by
      apply Matrix.ext; unfold tripleCharges sourceA2302 sourceB2302 sourceC2302 difference raw11517; decide +kernel
    rw [ha]
    exact (canonical11517 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2302 + difference 3 5) (sourceB2302 + difference 5 3) sourceC2302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4834) := by
    have ha : (tripleCharges (sourceA2302 + difference 3 5) (sourceB2302 + difference 5 3) sourceC2302) = raw31737 := by
      apply Matrix.ext; unfold tripleCharges sourceA2302 sourceB2302 sourceC2302 difference raw31737; decide +kernel
    rw [ha]
    exact (canonical31737 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2302 + difference 4 0) (sourceB2302 + difference 0 4) sourceC2302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4360) := by
    have ha : (tripleCharges (sourceA2302 + difference 4 0) (sourceB2302 + difference 0 4) sourceC2302) = raw23531 := by
      apply Matrix.ext; unfold tripleCharges sourceA2302 sourceB2302 sourceC2302 difference raw23531; decide +kernel
    rw [ha]
    exact (canonical23531 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2302 + difference 4 1) (sourceB2302 + difference 1 4) sourceC2302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4692) := by
    have ha : (tripleCharges (sourceA2302 + difference 4 1) (sourceB2302 + difference 1 4) sourceC2302) = raw31738 := by
      apply Matrix.ext; unfold tripleCharges sourceA2302 sourceB2302 sourceC2302 difference raw31738; decide +kernel
    rw [ha]
    exact (canonical31738 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2302 + difference 4 2) (sourceB2302 + difference 2 4) sourceC2302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4769) := by
    have ha : (tripleCharges (sourceA2302 + difference 4 2) (sourceB2302 + difference 2 4) sourceC2302) = raw31739 := by
      apply Matrix.ext; unfold tripleCharges sourceA2302 sourceB2302 sourceC2302 difference raw31739; decide +kernel
    rw [ha]
    exact (canonical31739 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2302 + difference 4 3) (sourceB2302 + difference 3 4) sourceC2302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4769) := by
    have ha : (tripleCharges (sourceA2302 + difference 4 3) (sourceB2302 + difference 3 4) sourceC2302) = raw31740 := by
      apply Matrix.ext; unfold tripleCharges sourceA2302 sourceB2302 sourceC2302 difference raw31740; decide +kernel
    rw [ha]
    exact (canonical31740 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2302 + difference 4 5) (sourceB2302 + difference 5 4) sourceC2302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4841) := by
    have ha : (tripleCharges (sourceA2302 + difference 4 5) (sourceB2302 + difference 5 4) sourceC2302) = raw31741 := by
      apply Matrix.ext; unfold tripleCharges sourceA2302 sourceB2302 sourceC2302 difference raw31741; decide +kernel
    rw [ha]
    exact (canonical31741 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2302 + difference 5 0) (sourceB2302 + difference 0 5) sourceC2302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4361) := by
    have ha : (tripleCharges (sourceA2302 + difference 5 0) (sourceB2302 + difference 0 5) sourceC2302) = raw21648 := by
      apply Matrix.ext; unfold tripleCharges sourceA2302 sourceB2302 sourceC2302 difference raw21648; decide +kernel
    rw [ha]
    exact (canonical21648 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2302 + difference 5 1) (sourceB2302 + difference 1 5) sourceC2302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4693) := by
    have ha : (tripleCharges (sourceA2302 + difference 5 1) (sourceB2302 + difference 1 5) sourceC2302) = raw31742 := by
      apply Matrix.ext; unfold tripleCharges sourceA2302 sourceB2302 sourceC2302 difference raw31742; decide +kernel
    rw [ha]
    exact (canonical31742 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2302 + difference 5 2) (sourceB2302 + difference 2 5) sourceC2302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4770) := by
    have ha : (tripleCharges (sourceA2302 + difference 5 2) (sourceB2302 + difference 2 5) sourceC2302) = raw31743 := by
      apply Matrix.ext; unfold tripleCharges sourceA2302 sourceB2302 sourceC2302 difference raw31743; decide +kernel
    rw [ha]
    exact (canonical31743 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2302 + difference 5 3) (sourceB2302 + difference 3 5) sourceC2302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4770) := by
    have ha : (tripleCharges (sourceA2302 + difference 5 3) (sourceB2302 + difference 3 5) sourceC2302) = raw31744 := by
      apply Matrix.ext; unfold tripleCharges sourceA2302 sourceB2302 sourceC2302 difference raw31744; decide +kernel
    rw [ha]
    exact (canonical31744 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2302 + difference 5 4) (sourceB2302 + difference 4 5) sourceC2302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4843) := by
    have ha : (tripleCharges (sourceA2302 + difference 5 4) (sourceB2302 + difference 4 5) sourceC2302) = raw11527 := by
      apply Matrix.ext; unfold tripleCharges sourceA2302 sourceB2302 sourceC2302 difference raw11527; decide +kernel
    rw [ha]
    exact (canonical11527 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2302 sourceB2302 sourceC2302
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2302, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2303 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2303 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC2303 : Charge := ![3, 0, 0, 0, -2, -1]
def sourceForm2303 : Integer.Sparse Master := [(Sum.inr 1675, 2), (Sum.inr 1693, 1), (Sum.inr 1694, 1), (Sum.inr 1755, 1), (Sum.inr 2152, 2), (Sum.inr 2168, 1), (Sum.inr 2169, 1), (Sum.inr 2174, 2), (Sum.inr 2185, 2), (Sum.inr 2186, 2), (Sum.inr 2205, 2), (Sum.inr 2206, 2), (Sum.inr 2228, 1), (Sum.inr 2229, 2), (Sum.inr 2230, 1), (Sum.inr 2293, 1), (Sum.inr 2686, 1), (Sum.inr 2705, 2), (Sum.inr 2742, 1), (Sum.inr 2743, 1), (Sum.inr 4084, 1)]

theorem sourceEq2303 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2303 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2303 + difference 0 1) (sourceB2303 + difference 1 0) sourceC2303) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2686) := by
    have ha : (tripleCharges (sourceA2303 + difference 0 1) (sourceB2303 + difference 1 0) sourceC2303) = raw31745 := by
      apply Matrix.ext; unfold tripleCharges sourceA2303 sourceB2303 sourceC2303 difference raw31745; decide +kernel
    rw [ha]
    exact (canonical31745 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2303 + difference 0 2) (sourceB2303 + difference 2 0) sourceC2303) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2705) := by
    have ha : (tripleCharges (sourceA2303 + difference 0 2) (sourceB2303 + difference 2 0) sourceC2303) = raw31746 := by
      apply Matrix.ext; unfold tripleCharges sourceA2303 sourceB2303 sourceC2303 difference raw31746; decide +kernel
    rw [ha]
    exact (canonical31746 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2303 + difference 0 3) (sourceB2303 + difference 3 0) sourceC2303) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2705) := by
    have ha : (tripleCharges (sourceA2303 + difference 0 3) (sourceB2303 + difference 3 0) sourceC2303) = raw31747 := by
      apply Matrix.ext; unfold tripleCharges sourceA2303 sourceB2303 sourceC2303 difference raw31747; decide +kernel
    rw [ha]
    exact (canonical31747 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2303 + difference 0 4) (sourceB2303 + difference 4 0) sourceC2303) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2743) := by
    have ha : (tripleCharges (sourceA2303 + difference 0 4) (sourceB2303 + difference 4 0) sourceC2303) = raw31748 := by
      apply Matrix.ext; unfold tripleCharges sourceA2303 sourceB2303 sourceC2303 difference raw31748; decide +kernel
    rw [ha]
    exact (canonical31748 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2303 + difference 0 5) (sourceB2303 + difference 5 0) sourceC2303) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2742) := by
    have ha : (tripleCharges (sourceA2303 + difference 0 5) (sourceB2303 + difference 5 0) sourceC2303) = raw31749 := by
      apply Matrix.ext; unfold tripleCharges sourceA2303 sourceB2303 sourceC2303 difference raw31749; decide +kernel
    rw [ha]
    exact (canonical31749 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2303 + difference 1 0) (sourceB2303 + difference 0 1) sourceC2303) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1755) := by
    have ha : (tripleCharges (sourceA2303 + difference 1 0) (sourceB2303 + difference 0 1) sourceC2303) = raw21680 := by
      apply Matrix.ext; unfold tripleCharges sourceA2303 sourceB2303 sourceC2303 difference raw21680; decide +kernel
    rw [ha]
    exact (canonical21680 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2303 + difference 1 2) (sourceB2303 + difference 2 1) sourceC2303) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2229) := by
    have ha : (tripleCharges (sourceA2303 + difference 1 2) (sourceB2303 + difference 2 1) sourceC2303) = raw23536 := by
      apply Matrix.ext; unfold tripleCharges sourceA2303 sourceB2303 sourceC2303 difference raw23536; decide +kernel
    rw [ha]
    exact (canonical23536 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2303 + difference 1 3) (sourceB2303 + difference 3 1) sourceC2303) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2229) := by
    have ha : (tripleCharges (sourceA2303 + difference 1 3) (sourceB2303 + difference 3 1) sourceC2303) = raw23537 := by
      apply Matrix.ext; unfold tripleCharges sourceA2303 sourceB2303 sourceC2303 difference raw23537; decide +kernel
    rw [ha]
    exact (canonical23537 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2303 + difference 1 4) (sourceB2303 + difference 4 1) sourceC2303) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2293) := by
    have ha : (tripleCharges (sourceA2303 + difference 1 4) (sourceB2303 + difference 4 1) sourceC2303) = raw21660 := by
      apply Matrix.ext; unfold tripleCharges sourceA2303 sourceB2303 sourceC2303 difference raw21660; decide +kernel
    rw [ha]
    exact (canonical21660 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2303 + difference 1 5) (sourceB2303 + difference 5 1) sourceC2303) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA2303 + difference 1 5) (sourceB2303 + difference 5 1) sourceC2303) = raw23538 := by
      apply Matrix.ext; unfold tripleCharges sourceA2303 sourceB2303 sourceC2303 difference raw23538; decide +kernel
    rw [ha]
    exact (canonical23538 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2303 + difference 2 0) (sourceB2303 + difference 0 2) sourceC2303) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1675) := by
    have ha : (tripleCharges (sourceA2303 + difference 2 0) (sourceB2303 + difference 0 2) sourceC2303) = raw23544 := by
      apply Matrix.ext; unfold tripleCharges sourceA2303 sourceB2303 sourceC2303 difference raw23544; decide +kernel
    rw [ha]
    exact (canonical23544 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2303 + difference 2 1) (sourceB2303 + difference 1 2) sourceC2303) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2152) := by
    have ha : (tripleCharges (sourceA2303 + difference 2 1) (sourceB2303 + difference 1 2) sourceC2303) = raw31750 := by
      apply Matrix.ext; unfold tripleCharges sourceA2303 sourceB2303 sourceC2303 difference raw31750; decide +kernel
    rw [ha]
    exact (canonical31750 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2303 + difference 2 3) (sourceB2303 + difference 3 2) sourceC2303) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2174) := by
    have ha : (tripleCharges (sourceA2303 + difference 2 3) (sourceB2303 + difference 3 2) sourceC2303) = raw31751 := by
      apply Matrix.ext; unfold tripleCharges sourceA2303 sourceB2303 sourceC2303 difference raw31751; decide +kernel
    rw [ha]
    exact (canonical31751 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2303 + difference 2 4) (sourceB2303 + difference 4 2) sourceC2303) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2206) := by
    have ha : (tripleCharges (sourceA2303 + difference 2 4) (sourceB2303 + difference 4 2) sourceC2303) = raw31752 := by
      apply Matrix.ext; unfold tripleCharges sourceA2303 sourceB2303 sourceC2303 difference raw31752; decide +kernel
    rw [ha]
    exact (canonical31752 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2303 + difference 2 5) (sourceB2303 + difference 5 2) sourceC2303) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2205) := by
    have ha : (tripleCharges (sourceA2303 + difference 2 5) (sourceB2303 + difference 5 2) sourceC2303) = raw31753 := by
      apply Matrix.ext; unfold tripleCharges sourceA2303 sourceB2303 sourceC2303 difference raw31753; decide +kernel
    rw [ha]
    exact (canonical31753 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2303 + difference 3 0) (sourceB2303 + difference 0 3) sourceC2303) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1675) := by
    have ha : (tripleCharges (sourceA2303 + difference 3 0) (sourceB2303 + difference 0 3) sourceC2303) = raw23548 := by
      apply Matrix.ext; unfold tripleCharges sourceA2303 sourceB2303 sourceC2303 difference raw23548; decide +kernel
    rw [ha]
    exact (canonical23548 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2303 + difference 3 1) (sourceB2303 + difference 1 3) sourceC2303) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2152) := by
    have ha : (tripleCharges (sourceA2303 + difference 3 1) (sourceB2303 + difference 1 3) sourceC2303) = raw31754 := by
      apply Matrix.ext; unfold tripleCharges sourceA2303 sourceB2303 sourceC2303 difference raw31754; decide +kernel
    rw [ha]
    exact (canonical31754 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2303 + difference 3 2) (sourceB2303 + difference 2 3) sourceC2303) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2174) := by
    have ha : (tripleCharges (sourceA2303 + difference 3 2) (sourceB2303 + difference 2 3) sourceC2303) = raw31755 := by
      apply Matrix.ext; unfold tripleCharges sourceA2303 sourceB2303 sourceC2303 difference raw31755; decide +kernel
    rw [ha]
    exact (canonical31755 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2303 + difference 3 4) (sourceB2303 + difference 4 3) sourceC2303) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2206) := by
    have ha : (tripleCharges (sourceA2303 + difference 3 4) (sourceB2303 + difference 4 3) sourceC2303) = raw31756 := by
      apply Matrix.ext; unfold tripleCharges sourceA2303 sourceB2303 sourceC2303 difference raw31756; decide +kernel
    rw [ha]
    exact (canonical31756 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2303 + difference 3 5) (sourceB2303 + difference 5 3) sourceC2303) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2205) := by
    have ha : (tripleCharges (sourceA2303 + difference 3 5) (sourceB2303 + difference 5 3) sourceC2303) = raw31757 := by
      apply Matrix.ext; unfold tripleCharges sourceA2303 sourceB2303 sourceC2303 difference raw31757; decide +kernel
    rw [ha]
    exact (canonical31757 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2303 + difference 4 0) (sourceB2303 + difference 0 4) sourceC2303) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1693) := by
    have ha : (tripleCharges (sourceA2303 + difference 4 0) (sourceB2303 + difference 0 4) sourceC2303) = raw23552 := by
      apply Matrix.ext; unfold tripleCharges sourceA2303 sourceB2303 sourceC2303 difference raw23552; decide +kernel
    rw [ha]
    exact (canonical23552 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2303 + difference 4 1) (sourceB2303 + difference 1 4) sourceC2303) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2168) := by
    have ha : (tripleCharges (sourceA2303 + difference 4 1) (sourceB2303 + difference 1 4) sourceC2303) = raw31758 := by
      apply Matrix.ext; unfold tripleCharges sourceA2303 sourceB2303 sourceC2303 difference raw31758; decide +kernel
    rw [ha]
    exact (canonical31758 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2303 + difference 4 2) (sourceB2303 + difference 2 4) sourceC2303) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2185) := by
    have ha : (tripleCharges (sourceA2303 + difference 4 2) (sourceB2303 + difference 2 4) sourceC2303) = raw31759 := by
      apply Matrix.ext; unfold tripleCharges sourceA2303 sourceB2303 sourceC2303 difference raw31759; decide +kernel
    rw [ha]
    exact (canonical31759 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2303 + difference 4 3) (sourceB2303 + difference 3 4) sourceC2303) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2185) := by
    have ha : (tripleCharges (sourceA2303 + difference 4 3) (sourceB2303 + difference 3 4) sourceC2303) = raw31760 := by
      apply Matrix.ext; unfold tripleCharges sourceA2303 sourceB2303 sourceC2303 difference raw31760; decide +kernel
    rw [ha]
    exact (canonical31760 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2303 + difference 4 5) (sourceB2303 + difference 5 4) sourceC2303) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2228) := by
    have ha : (tripleCharges (sourceA2303 + difference 4 5) (sourceB2303 + difference 5 4) sourceC2303) = raw31761 := by
      apply Matrix.ext; unfold tripleCharges sourceA2303 sourceB2303 sourceC2303 difference raw31761; decide +kernel
    rw [ha]
    exact (canonical31761 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2303 + difference 5 0) (sourceB2303 + difference 0 5) sourceC2303) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1694) := by
    have ha : (tripleCharges (sourceA2303 + difference 5 0) (sourceB2303 + difference 0 5) sourceC2303) = raw21677 := by
      apply Matrix.ext; unfold tripleCharges sourceA2303 sourceB2303 sourceC2303 difference raw21677; decide +kernel
    rw [ha]
    exact (canonical21677 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2303 + difference 5 1) (sourceB2303 + difference 1 5) sourceC2303) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2169) := by
    have ha : (tripleCharges (sourceA2303 + difference 5 1) (sourceB2303 + difference 1 5) sourceC2303) = raw31762 := by
      apply Matrix.ext; unfold tripleCharges sourceA2303 sourceB2303 sourceC2303 difference raw31762; decide +kernel
    rw [ha]
    exact (canonical31762 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2303 + difference 5 2) (sourceB2303 + difference 2 5) sourceC2303) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2186) := by
    have ha : (tripleCharges (sourceA2303 + difference 5 2) (sourceB2303 + difference 2 5) sourceC2303) = raw31763 := by
      apply Matrix.ext; unfold tripleCharges sourceA2303 sourceB2303 sourceC2303 difference raw31763; decide +kernel
    rw [ha]
    exact (canonical31763 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2303 + difference 5 3) (sourceB2303 + difference 3 5) sourceC2303) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2186) := by
    have ha : (tripleCharges (sourceA2303 + difference 5 3) (sourceB2303 + difference 3 5) sourceC2303) = raw31764 := by
      apply Matrix.ext; unfold tripleCharges sourceA2303 sourceB2303 sourceC2303 difference raw31764; decide +kernel
    rw [ha]
    exact (canonical31764 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2303 + difference 5 4) (sourceB2303 + difference 4 5) sourceC2303) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2230) := by
    have ha : (tripleCharges (sourceA2303 + difference 5 4) (sourceB2303 + difference 4 5) sourceC2303) = raw21656 := by
      apply Matrix.ext; unfold tripleCharges sourceA2303 sourceB2303 sourceC2303 difference raw21656; decide +kernel
    rw [ha]
    exact (canonical21656 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2303 sourceB2303 sourceC2303
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2303, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
