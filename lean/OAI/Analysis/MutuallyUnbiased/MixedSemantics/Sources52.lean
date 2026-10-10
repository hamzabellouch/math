import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical97
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical98
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical111
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical143
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical151
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical185
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical188
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical189
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical190
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical191
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical192
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical193
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical194

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA1664 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1664 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC1664 : Charge := ![2, 0, 0, -1, 1, -2]
def sourceForm1664 : Integer.Sparse Master := [(Sum.inr 638, 2), (Sum.inr 641, 1), (Sum.inr 642, 1), (Sum.inr 653, 1), (Sum.inr 1294, 1), (Sum.inr 4092, -1)]

theorem sourceEq1664 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1664 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1664 + difference 0 0) (sourceB1664 + difference 0 0) sourceC1664) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1294) := by
    have ha : (tripleCharges (sourceA1664 + difference 0 0) (sourceB1664 + difference 0 0) sourceC1664) = raw24394 := by
      apply Matrix.ext; unfold tripleCharges sourceA1664 sourceB1664 sourceC1664 difference raw24394; decide +kernel
    rw [ha]
    exact (canonical24394 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1664 + difference 1 0) (sourceB1664 + difference 0 1) sourceC1664) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 638) := by
    have ha : (tripleCharges (sourceA1664 + difference 1 0) (sourceB1664 + difference 0 1) sourceC1664) = raw24395 := by
      apply Matrix.ext; unfold tripleCharges sourceA1664 sourceB1664 sourceC1664 difference raw24395; decide +kernel
    rw [ha]
    exact (canonical24395 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1664 + difference 2 0) (sourceB1664 + difference 0 2) sourceC1664) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 638) := by
    have ha : (tripleCharges (sourceA1664 + difference 2 0) (sourceB1664 + difference 0 2) sourceC1664) = raw24396 := by
      apply Matrix.ext; unfold tripleCharges sourceA1664 sourceB1664 sourceC1664 difference raw24396; decide +kernel
    rw [ha]
    exact (canonical24396 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1664 + difference 3 0) (sourceB1664 + difference 0 3) sourceC1664) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 642) := by
    have ha : (tripleCharges (sourceA1664 + difference 3 0) (sourceB1664 + difference 0 3) sourceC1664) = raw24397 := by
      apply Matrix.ext; unfold tripleCharges sourceA1664 sourceB1664 sourceC1664 difference raw24397; decide +kernel
    rw [ha]
    exact (canonical24397 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1664 + difference 4 0) (sourceB1664 + difference 0 4) sourceC1664) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 653) := by
    have ha : (tripleCharges (sourceA1664 + difference 4 0) (sourceB1664 + difference 0 4) sourceC1664) = raw24398 := by
      apply Matrix.ext; unfold tripleCharges sourceA1664 sourceB1664 sourceC1664 difference raw24398; decide +kernel
    rw [ha]
    exact (canonical24398 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1664 + difference 5 0) (sourceB1664 + difference 0 5) sourceC1664) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 641) := by
    have ha : (tripleCharges (sourceA1664 + difference 5 0) (sourceB1664 + difference 0 5) sourceC1664) = raw24399 := by
      apply Matrix.ext; unfold tripleCharges sourceA1664 sourceB1664 sourceC1664 difference raw24399; decide +kernel
    rw [ha]
    exact (canonical24399 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1664 + sourceB1664) sourceC1664) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1664 + sourceB1664) sourceC1664) = raw24400 := by
      apply Matrix.ext; unfold doubleCharges sourceA1664 sourceB1664 sourceC1664 raw24400; decide +kernel
    rw [ha]
    exact (canonical24400 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1664 sourceB1664 sourceC1664
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1664, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1665 : Charge := ![2, 0, 0, -1, 1, -2]
def sourceB1665 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC1665 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1665 : Integer.Sparse Master := [(Sum.inr 4452, 2), (Sum.inr 4459, 2), (Sum.inr 4490, 1), (Sum.inr 4491, 1), (Sum.inr 4498, 1), (Sum.inr 4499, 1), (Sum.inr 4500, 1), (Sum.inr 4503, 1), (Sum.inr 4587, 2), (Sum.inr 4596, 2), (Sum.inr 4597, 2), (Sum.inr 4602, 2), (Sum.inr 4603, 2), (Sum.inr 4604, 2), (Sum.inr 4607, 2), (Sum.inr 4614, 1), (Sum.inr 4615, 1), (Sum.inr 4617, 1), (Sum.inr 4620, 1), (Sum.inr 4623, 1), (Sum.inr 4624, 1)]

theorem sourceEq1665 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1665 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1665 + difference 0 1) (sourceB1665 + difference 1 0) sourceC1665) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4452) := by
    have ha : (tripleCharges (sourceA1665 + difference 0 1) (sourceB1665 + difference 1 0) sourceC1665) = raw24401 := by
      apply Matrix.ext; unfold tripleCharges sourceA1665 sourceB1665 sourceC1665 difference raw24401; decide +kernel
    rw [ha]
    exact (canonical24401 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1665 + difference 0 2) (sourceB1665 + difference 2 0) sourceC1665) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4452) := by
    have ha : (tripleCharges (sourceA1665 + difference 0 2) (sourceB1665 + difference 2 0) sourceC1665) = raw24402 := by
      apply Matrix.ext; unfold tripleCharges sourceA1665 sourceB1665 sourceC1665 difference raw24402; decide +kernel
    rw [ha]
    exact (canonical24402 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1665 + difference 0 3) (sourceB1665 + difference 3 0) sourceC1665) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4491) := by
    have ha : (tripleCharges (sourceA1665 + difference 0 3) (sourceB1665 + difference 3 0) sourceC1665) = raw24403 := by
      apply Matrix.ext; unfold tripleCharges sourceA1665 sourceB1665 sourceC1665 difference raw24403; decide +kernel
    rw [ha]
    exact (canonical24403 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1665 + difference 0 4) (sourceB1665 + difference 4 0) sourceC1665) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4498) := by
    have ha : (tripleCharges (sourceA1665 + difference 0 4) (sourceB1665 + difference 4 0) sourceC1665) = raw24251 := by
      apply Matrix.ext; unfold tripleCharges sourceA1665 sourceB1665 sourceC1665 difference raw24251; decide +kernel
    rw [ha]
    exact (canonical24251 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1665 + difference 0 5) (sourceB1665 + difference 5 0) sourceC1665) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4490) := by
    have ha : (tripleCharges (sourceA1665 + difference 0 5) (sourceB1665 + difference 5 0) sourceC1665) = raw24404 := by
      apply Matrix.ext; unfold tripleCharges sourceA1665 sourceB1665 sourceC1665 difference raw24404; decide +kernel
    rw [ha]
    exact (canonical24404 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1665 + difference 1 0) (sourceB1665 + difference 0 1) sourceC1665) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4459) := by
    have ha : (tripleCharges (sourceA1665 + difference 1 0) (sourceB1665 + difference 0 1) sourceC1665) = raw24405 := by
      apply Matrix.ext; unfold tripleCharges sourceA1665 sourceB1665 sourceC1665 difference raw24405; decide +kernel
    rw [ha]
    exact (canonical24405 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1665 + difference 1 2) (sourceB1665 + difference 2 1) sourceC1665) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4587) := by
    have ha : (tripleCharges (sourceA1665 + difference 1 2) (sourceB1665 + difference 2 1) sourceC1665) = raw24406 := by
      apply Matrix.ext; unfold tripleCharges sourceA1665 sourceB1665 sourceC1665 difference raw24406; decide +kernel
    rw [ha]
    exact (canonical24406 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1665 + difference 1 3) (sourceB1665 + difference 3 1) sourceC1665) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4597) := by
    have ha : (tripleCharges (sourceA1665 + difference 1 3) (sourceB1665 + difference 3 1) sourceC1665) = raw24407 := by
      apply Matrix.ext; unfold tripleCharges sourceA1665 sourceB1665 sourceC1665 difference raw24407; decide +kernel
    rw [ha]
    exact (canonical24407 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1665 + difference 1 4) (sourceB1665 + difference 4 1) sourceC1665) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1665 + difference 1 4) (sourceB1665 + difference 4 1) sourceC1665) = raw24255 := by
      apply Matrix.ext; unfold tripleCharges sourceA1665 sourceB1665 sourceC1665 difference raw24255; decide +kernel
    rw [ha]
    exact (canonical24255 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1665 + difference 1 5) (sourceB1665 + difference 5 1) sourceC1665) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4596) := by
    have ha : (tripleCharges (sourceA1665 + difference 1 5) (sourceB1665 + difference 5 1) sourceC1665) = raw24408 := by
      apply Matrix.ext; unfold tripleCharges sourceA1665 sourceB1665 sourceC1665 difference raw24408; decide +kernel
    rw [ha]
    exact (canonical24408 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1665 + difference 2 0) (sourceB1665 + difference 0 2) sourceC1665) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4459) := by
    have ha : (tripleCharges (sourceA1665 + difference 2 0) (sourceB1665 + difference 0 2) sourceC1665) = raw24409 := by
      apply Matrix.ext; unfold tripleCharges sourceA1665 sourceB1665 sourceC1665 difference raw24409; decide +kernel
    rw [ha]
    exact (canonical24409 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1665 + difference 2 1) (sourceB1665 + difference 1 2) sourceC1665) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4587) := by
    have ha : (tripleCharges (sourceA1665 + difference 2 1) (sourceB1665 + difference 1 2) sourceC1665) = raw24410 := by
      apply Matrix.ext; unfold tripleCharges sourceA1665 sourceB1665 sourceC1665 difference raw24410; decide +kernel
    rw [ha]
    exact (canonical24410 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1665 + difference 2 3) (sourceB1665 + difference 3 2) sourceC1665) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4597) := by
    have ha : (tripleCharges (sourceA1665 + difference 2 3) (sourceB1665 + difference 3 2) sourceC1665) = raw24411 := by
      apply Matrix.ext; unfold tripleCharges sourceA1665 sourceB1665 sourceC1665 difference raw24411; decide +kernel
    rw [ha]
    exact (canonical24411 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1665 + difference 2 4) (sourceB1665 + difference 4 2) sourceC1665) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1665 + difference 2 4) (sourceB1665 + difference 4 2) sourceC1665) = raw24259 := by
      apply Matrix.ext; unfold tripleCharges sourceA1665 sourceB1665 sourceC1665 difference raw24259; decide +kernel
    rw [ha]
    exact (canonical24259 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1665 + difference 2 5) (sourceB1665 + difference 5 2) sourceC1665) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4596) := by
    have ha : (tripleCharges (sourceA1665 + difference 2 5) (sourceB1665 + difference 5 2) sourceC1665) = raw24412 := by
      apply Matrix.ext; unfold tripleCharges sourceA1665 sourceB1665 sourceC1665 difference raw24412; decide +kernel
    rw [ha]
    exact (canonical24412 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1665 + difference 3 0) (sourceB1665 + difference 0 3) sourceC1665) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4503) := by
    have ha : (tripleCharges (sourceA1665 + difference 3 0) (sourceB1665 + difference 0 3) sourceC1665) = raw24413 := by
      apply Matrix.ext; unfold tripleCharges sourceA1665 sourceB1665 sourceC1665 difference raw24413; decide +kernel
    rw [ha]
    exact (canonical24413 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1665 + difference 3 1) (sourceB1665 + difference 1 3) sourceC1665) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4607) := by
    have ha : (tripleCharges (sourceA1665 + difference 3 1) (sourceB1665 + difference 1 3) sourceC1665) = raw24414 := by
      apply Matrix.ext; unfold tripleCharges sourceA1665 sourceB1665 sourceC1665 difference raw24414; decide +kernel
    rw [ha]
    exact (canonical24414 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1665 + difference 3 2) (sourceB1665 + difference 2 3) sourceC1665) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4607) := by
    have ha : (tripleCharges (sourceA1665 + difference 3 2) (sourceB1665 + difference 2 3) sourceC1665) = raw24415 := by
      apply Matrix.ext; unfold tripleCharges sourceA1665 sourceB1665 sourceC1665 difference raw24415; decide +kernel
    rw [ha]
    exact (canonical24415 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1665 + difference 3 4) (sourceB1665 + difference 4 3) sourceC1665) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4623) := by
    have ha : (tripleCharges (sourceA1665 + difference 3 4) (sourceB1665 + difference 4 3) sourceC1665) = raw24263 := by
      apply Matrix.ext; unfold tripleCharges sourceA1665 sourceB1665 sourceC1665 difference raw24263; decide +kernel
    rw [ha]
    exact (canonical24263 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1665 + difference 3 5) (sourceB1665 + difference 5 3) sourceC1665) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4617) := by
    have ha : (tripleCharges (sourceA1665 + difference 3 5) (sourceB1665 + difference 5 3) sourceC1665) = raw24416 := by
      apply Matrix.ext; unfold tripleCharges sourceA1665 sourceB1665 sourceC1665 difference raw24416; decide +kernel
    rw [ha]
    exact (canonical24416 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1665 + difference 4 0) (sourceB1665 + difference 0 4) sourceC1665) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4500) := by
    have ha : (tripleCharges (sourceA1665 + difference 4 0) (sourceB1665 + difference 0 4) sourceC1665) = raw24417 := by
      apply Matrix.ext; unfold tripleCharges sourceA1665 sourceB1665 sourceC1665 difference raw24417; decide +kernel
    rw [ha]
    exact (canonical24417 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1665 + difference 4 1) (sourceB1665 + difference 1 4) sourceC1665) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4604) := by
    have ha : (tripleCharges (sourceA1665 + difference 4 1) (sourceB1665 + difference 1 4) sourceC1665) = raw24418 := by
      apply Matrix.ext; unfold tripleCharges sourceA1665 sourceB1665 sourceC1665 difference raw24418; decide +kernel
    rw [ha]
    exact (canonical24418 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1665 + difference 4 2) (sourceB1665 + difference 2 4) sourceC1665) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4604) := by
    have ha : (tripleCharges (sourceA1665 + difference 4 2) (sourceB1665 + difference 2 4) sourceC1665) = raw24419 := by
      apply Matrix.ext; unfold tripleCharges sourceA1665 sourceB1665 sourceC1665 difference raw24419; decide +kernel
    rw [ha]
    exact (canonical24419 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1665 + difference 4 3) (sourceB1665 + difference 3 4) sourceC1665) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4615) := by
    have ha : (tripleCharges (sourceA1665 + difference 4 3) (sourceB1665 + difference 3 4) sourceC1665) = raw24420 := by
      apply Matrix.ext; unfold tripleCharges sourceA1665 sourceB1665 sourceC1665 difference raw24420; decide +kernel
    rw [ha]
    exact (canonical24420 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1665 + difference 4 5) (sourceB1665 + difference 5 4) sourceC1665) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4614) := by
    have ha : (tripleCharges (sourceA1665 + difference 4 5) (sourceB1665 + difference 5 4) sourceC1665) = raw24421 := by
      apply Matrix.ext; unfold tripleCharges sourceA1665 sourceB1665 sourceC1665 difference raw24421; decide +kernel
    rw [ha]
    exact (canonical24421 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1665 + difference 5 0) (sourceB1665 + difference 0 5) sourceC1665) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4499) := by
    have ha : (tripleCharges (sourceA1665 + difference 5 0) (sourceB1665 + difference 0 5) sourceC1665) = raw24264 := by
      apply Matrix.ext; unfold tripleCharges sourceA1665 sourceB1665 sourceC1665 difference raw24264; decide +kernel
    rw [ha]
    exact (canonical24264 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1665 + difference 5 1) (sourceB1665 + difference 1 5) sourceC1665) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4603) := by
    have ha : (tripleCharges (sourceA1665 + difference 5 1) (sourceB1665 + difference 1 5) sourceC1665) = raw24265 := by
      apply Matrix.ext; unfold tripleCharges sourceA1665 sourceB1665 sourceC1665 difference raw24265; decide +kernel
    rw [ha]
    exact (canonical24265 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1665 + difference 5 2) (sourceB1665 + difference 2 5) sourceC1665) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4603) := by
    have ha : (tripleCharges (sourceA1665 + difference 5 2) (sourceB1665 + difference 2 5) sourceC1665) = raw24266 := by
      apply Matrix.ext; unfold tripleCharges sourceA1665 sourceB1665 sourceC1665 difference raw24266; decide +kernel
    rw [ha]
    exact (canonical24266 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1665 + difference 5 3) (sourceB1665 + difference 3 5) sourceC1665) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4620) := by
    have ha : (tripleCharges (sourceA1665 + difference 5 3) (sourceB1665 + difference 3 5) sourceC1665) = raw24267 := by
      apply Matrix.ext; unfold tripleCharges sourceA1665 sourceB1665 sourceC1665 difference raw24267; decide +kernel
    rw [ha]
    exact (canonical24267 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1665 + difference 5 4) (sourceB1665 + difference 4 5) sourceC1665) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4624) := by
    have ha : (tripleCharges (sourceA1665 + difference 5 4) (sourceB1665 + difference 4 5) sourceC1665) = raw24176 := by
      apply Matrix.ext; unfold tripleCharges sourceA1665 sourceB1665 sourceC1665 difference raw24176; decide +kernel
    rw [ha]
    exact (canonical24176 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1665 sourceB1665 sourceC1665
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1665, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1666 : Charge := ![2, 0, 0, -1, 1, -2]
def sourceB1666 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC1666 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1666 : Integer.Sparse Master := [(Sum.inr 1035, 2), (Sum.inr 1074, 1), (Sum.inr 1075, 1), (Sum.inr 1082, 1), (Sum.inr 1210, 2), (Sum.inr 1229, 2), (Sum.inr 1230, 2), (Sum.inr 1236, 2), (Sum.inr 1257, 2), (Sum.inr 1261, 2), (Sum.inr 1262, 2), (Sum.inr 1287, 1), (Sum.inr 1288, 1), (Sum.inr 1292, 1), (Sum.inr 1295, 1), (Sum.inr 1300, 1), (Sum.inr 1301, 1), (Sum.inr 1406, 2), (Sum.inr 1436, 1), (Sum.inr 1442, 1), (Sum.inr 1443, 1)]

theorem sourceEq1666 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1666 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1666 + difference 0 1) (sourceB1666 + difference 1 0) sourceC1666) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1035) := by
    have ha : (tripleCharges (sourceA1666 + difference 0 1) (sourceB1666 + difference 1 0) sourceC1666) = raw24422 := by
      apply Matrix.ext; unfold tripleCharges sourceA1666 sourceB1666 sourceC1666 difference raw24422; decide +kernel
    rw [ha]
    exact (canonical24422 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1666 + difference 0 2) (sourceB1666 + difference 2 0) sourceC1666) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1035) := by
    have ha : (tripleCharges (sourceA1666 + difference 0 2) (sourceB1666 + difference 2 0) sourceC1666) = raw24423 := by
      apply Matrix.ext; unfold tripleCharges sourceA1666 sourceB1666 sourceC1666 difference raw24423; decide +kernel
    rw [ha]
    exact (canonical24423 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1666 + difference 0 3) (sourceB1666 + difference 3 0) sourceC1666) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1075) := by
    have ha : (tripleCharges (sourceA1666 + difference 0 3) (sourceB1666 + difference 3 0) sourceC1666) = raw24424 := by
      apply Matrix.ext; unfold tripleCharges sourceA1666 sourceB1666 sourceC1666 difference raw24424; decide +kernel
    rw [ha]
    exact (canonical24424 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1666 + difference 0 4) (sourceB1666 + difference 4 0) sourceC1666) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1082) := by
    have ha : (tripleCharges (sourceA1666 + difference 0 4) (sourceB1666 + difference 4 0) sourceC1666) = raw24425 := by
      apply Matrix.ext; unfold tripleCharges sourceA1666 sourceB1666 sourceC1666 difference raw24425; decide +kernel
    rw [ha]
    exact (canonical24425 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1666 + difference 0 5) (sourceB1666 + difference 5 0) sourceC1666) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1074) := by
    have ha : (tripleCharges (sourceA1666 + difference 0 5) (sourceB1666 + difference 5 0) sourceC1666) = raw24426 := by
      apply Matrix.ext; unfold tripleCharges sourceA1666 sourceB1666 sourceC1666 difference raw24426; decide +kernel
    rw [ha]
    exact (canonical24426 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1666 + difference 1 0) (sourceB1666 + difference 0 1) sourceC1666) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1406) := by
    have ha : (tripleCharges (sourceA1666 + difference 1 0) (sourceB1666 + difference 0 1) sourceC1666) = raw24427 := by
      apply Matrix.ext; unfold tripleCharges sourceA1666 sourceB1666 sourceC1666 difference raw24427; decide +kernel
    rw [ha]
    exact (canonical24427 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1666 + difference 1 2) (sourceB1666 + difference 2 1) sourceC1666) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1210) := by
    have ha : (tripleCharges (sourceA1666 + difference 1 2) (sourceB1666 + difference 2 1) sourceC1666) = raw24428 := by
      apply Matrix.ext; unfold tripleCharges sourceA1666 sourceB1666 sourceC1666 difference raw24428; decide +kernel
    rw [ha]
    exact (canonical24428 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1666 + difference 1 3) (sourceB1666 + difference 3 1) sourceC1666) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1230) := by
    have ha : (tripleCharges (sourceA1666 + difference 1 3) (sourceB1666 + difference 3 1) sourceC1666) = raw24429 := by
      apply Matrix.ext; unfold tripleCharges sourceA1666 sourceB1666 sourceC1666 difference raw24429; decide +kernel
    rw [ha]
    exact (canonical24429 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1666 + difference 1 4) (sourceB1666 + difference 4 1) sourceC1666) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1236) := by
    have ha : (tripleCharges (sourceA1666 + difference 1 4) (sourceB1666 + difference 4 1) sourceC1666) = raw24430 := by
      apply Matrix.ext; unfold tripleCharges sourceA1666 sourceB1666 sourceC1666 difference raw24430; decide +kernel
    rw [ha]
    exact (canonical24430 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1666 + difference 1 5) (sourceB1666 + difference 5 1) sourceC1666) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1229) := by
    have ha : (tripleCharges (sourceA1666 + difference 1 5) (sourceB1666 + difference 5 1) sourceC1666) = raw24431 := by
      apply Matrix.ext; unfold tripleCharges sourceA1666 sourceB1666 sourceC1666 difference raw24431; decide +kernel
    rw [ha]
    exact (canonical24431 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1666 + difference 2 0) (sourceB1666 + difference 0 2) sourceC1666) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1406) := by
    have ha : (tripleCharges (sourceA1666 + difference 2 0) (sourceB1666 + difference 0 2) sourceC1666) = raw24432 := by
      apply Matrix.ext; unfold tripleCharges sourceA1666 sourceB1666 sourceC1666 difference raw24432; decide +kernel
    rw [ha]
    exact (canonical24432 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1666 + difference 2 1) (sourceB1666 + difference 1 2) sourceC1666) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1210) := by
    have ha : (tripleCharges (sourceA1666 + difference 2 1) (sourceB1666 + difference 1 2) sourceC1666) = raw24433 := by
      apply Matrix.ext; unfold tripleCharges sourceA1666 sourceB1666 sourceC1666 difference raw24433; decide +kernel
    rw [ha]
    exact (canonical24433 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1666 + difference 2 3) (sourceB1666 + difference 3 2) sourceC1666) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1230) := by
    have ha : (tripleCharges (sourceA1666 + difference 2 3) (sourceB1666 + difference 3 2) sourceC1666) = raw24434 := by
      apply Matrix.ext; unfold tripleCharges sourceA1666 sourceB1666 sourceC1666 difference raw24434; decide +kernel
    rw [ha]
    exact (canonical24434 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1666 + difference 2 4) (sourceB1666 + difference 4 2) sourceC1666) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1236) := by
    have ha : (tripleCharges (sourceA1666 + difference 2 4) (sourceB1666 + difference 4 2) sourceC1666) = raw24435 := by
      apply Matrix.ext; unfold tripleCharges sourceA1666 sourceB1666 sourceC1666 difference raw24435; decide +kernel
    rw [ha]
    exact (canonical24435 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1666 + difference 2 5) (sourceB1666 + difference 5 2) sourceC1666) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1229) := by
    have ha : (tripleCharges (sourceA1666 + difference 2 5) (sourceB1666 + difference 5 2) sourceC1666) = raw24436 := by
      apply Matrix.ext; unfold tripleCharges sourceA1666 sourceB1666 sourceC1666 difference raw24436; decide +kernel
    rw [ha]
    exact (canonical24436 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1666 + difference 3 0) (sourceB1666 + difference 0 3) sourceC1666) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1442) := by
    have ha : (tripleCharges (sourceA1666 + difference 3 0) (sourceB1666 + difference 0 3) sourceC1666) = raw24437 := by
      apply Matrix.ext; unfold tripleCharges sourceA1666 sourceB1666 sourceC1666 difference raw24437; decide +kernel
    rw [ha]
    exact (canonical24437 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1666 + difference 3 1) (sourceB1666 + difference 1 3) sourceC1666) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1261) := by
    have ha : (tripleCharges (sourceA1666 + difference 3 1) (sourceB1666 + difference 1 3) sourceC1666) = raw24438 := by
      apply Matrix.ext; unfold tripleCharges sourceA1666 sourceB1666 sourceC1666 difference raw24438; decide +kernel
    rw [ha]
    exact (canonical24438 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1666 + difference 3 2) (sourceB1666 + difference 2 3) sourceC1666) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1261) := by
    have ha : (tripleCharges (sourceA1666 + difference 3 2) (sourceB1666 + difference 2 3) sourceC1666) = raw24439 := by
      apply Matrix.ext; unfold tripleCharges sourceA1666 sourceB1666 sourceC1666 difference raw24439; decide +kernel
    rw [ha]
    exact (canonical24439 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1666 + difference 3 4) (sourceB1666 + difference 4 3) sourceC1666) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1300) := by
    have ha : (tripleCharges (sourceA1666 + difference 3 4) (sourceB1666 + difference 4 3) sourceC1666) = raw24440 := by
      apply Matrix.ext; unfold tripleCharges sourceA1666 sourceB1666 sourceC1666 difference raw24440; decide +kernel
    rw [ha]
    exact (canonical24440 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1666 + difference 3 5) (sourceB1666 + difference 5 3) sourceC1666) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1292) := by
    have ha : (tripleCharges (sourceA1666 + difference 3 5) (sourceB1666 + difference 5 3) sourceC1666) = raw24441 := by
      apply Matrix.ext; unfold tripleCharges sourceA1666 sourceB1666 sourceC1666 difference raw24441; decide +kernel
    rw [ha]
    exact (canonical24441 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1666 + difference 4 0) (sourceB1666 + difference 0 4) sourceC1666) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1436) := by
    have ha : (tripleCharges (sourceA1666 + difference 4 0) (sourceB1666 + difference 0 4) sourceC1666) = raw24442 := by
      apply Matrix.ext; unfold tripleCharges sourceA1666 sourceB1666 sourceC1666 difference raw24442; decide +kernel
    rw [ha]
    exact (canonical24442 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1666 + difference 4 1) (sourceB1666 + difference 1 4) sourceC1666) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1257) := by
    have ha : (tripleCharges (sourceA1666 + difference 4 1) (sourceB1666 + difference 1 4) sourceC1666) = raw24443 := by
      apply Matrix.ext; unfold tripleCharges sourceA1666 sourceB1666 sourceC1666 difference raw24443; decide +kernel
    rw [ha]
    exact (canonical24443 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1666 + difference 4 2) (sourceB1666 + difference 2 4) sourceC1666) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1257) := by
    have ha : (tripleCharges (sourceA1666 + difference 4 2) (sourceB1666 + difference 2 4) sourceC1666) = raw24444 := by
      apply Matrix.ext; unfold tripleCharges sourceA1666 sourceB1666 sourceC1666 difference raw24444; decide +kernel
    rw [ha]
    exact (canonical24444 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1666 + difference 4 3) (sourceB1666 + difference 3 4) sourceC1666) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1288) := by
    have ha : (tripleCharges (sourceA1666 + difference 4 3) (sourceB1666 + difference 3 4) sourceC1666) = raw24445 := by
      apply Matrix.ext; unfold tripleCharges sourceA1666 sourceB1666 sourceC1666 difference raw24445; decide +kernel
    rw [ha]
    exact (canonical24445 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1666 + difference 4 5) (sourceB1666 + difference 5 4) sourceC1666) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1287) := by
    have ha : (tripleCharges (sourceA1666 + difference 4 5) (sourceB1666 + difference 5 4) sourceC1666) = raw24446 := by
      apply Matrix.ext; unfold tripleCharges sourceA1666 sourceB1666 sourceC1666 difference raw24446; decide +kernel
    rw [ha]
    exact (canonical24446 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1666 + difference 5 0) (sourceB1666 + difference 0 5) sourceC1666) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1443) := by
    have ha : (tripleCharges (sourceA1666 + difference 5 0) (sourceB1666 + difference 0 5) sourceC1666) = raw24447 := by
      apply Matrix.ext; unfold tripleCharges sourceA1666 sourceB1666 sourceC1666 difference raw24447; decide +kernel
    rw [ha]
    exact (canonical24447 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1666 + difference 5 1) (sourceB1666 + difference 1 5) sourceC1666) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1262) := by
    have ha : (tripleCharges (sourceA1666 + difference 5 1) (sourceB1666 + difference 1 5) sourceC1666) = raw24448 := by
      apply Matrix.ext; unfold tripleCharges sourceA1666 sourceB1666 sourceC1666 difference raw24448; decide +kernel
    rw [ha]
    exact (canonical24448 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1666 + difference 5 2) (sourceB1666 + difference 2 5) sourceC1666) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1262) := by
    have ha : (tripleCharges (sourceA1666 + difference 5 2) (sourceB1666 + difference 2 5) sourceC1666) = raw24449 := by
      apply Matrix.ext; unfold tripleCharges sourceA1666 sourceB1666 sourceC1666 difference raw24449; decide +kernel
    rw [ha]
    exact (canonical24449 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1666 + difference 5 3) (sourceB1666 + difference 3 5) sourceC1666) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1295) := by
    have ha : (tripleCharges (sourceA1666 + difference 5 3) (sourceB1666 + difference 3 5) sourceC1666) = raw24450 := by
      apply Matrix.ext; unfold tripleCharges sourceA1666 sourceB1666 sourceC1666 difference raw24450; decide +kernel
    rw [ha]
    exact (canonical24450 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1666 + difference 5 4) (sourceB1666 + difference 4 5) sourceC1666) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1301) := by
    have ha : (tripleCharges (sourceA1666 + difference 5 4) (sourceB1666 + difference 4 5) sourceC1666) = raw24206 := by
      apply Matrix.ext; unfold tripleCharges sourceA1666 sourceB1666 sourceC1666 difference raw24206; decide +kernel
    rw [ha]
    exact (canonical24206 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1666 sourceB1666 sourceC1666
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1666, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1667 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1667 : Charge := ![2, 0, 0, 0, -3, 1]
def sourceC1667 : Charge := ![2, 0, 0, -1, 2, -3]
def sourceForm1667 : Integer.Sparse Master := [(Sum.inr 1287, 1), (Sum.inr 2584, 2), (Sum.inr 2685, 1), (Sum.inr 2761, 2), (Sum.inr 4082, -1)]

theorem sourceEq1667 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1667 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1667 + difference 0 0) (sourceB1667 + difference 0 0) sourceC1667) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1287) := by
    have ha : (tripleCharges (sourceA1667 + difference 0 0) (sourceB1667 + difference 0 0) sourceC1667) = raw24451 := by
      apply Matrix.ext; unfold tripleCharges sourceA1667 sourceB1667 sourceC1667 difference raw24451; decide +kernel
    rw [ha]
    exact (canonical24451 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1667 + difference 0 1) (sourceB1667 + difference 1 0) sourceC1667) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2584) := by
    have ha : (tripleCharges (sourceA1667 + difference 0 1) (sourceB1667 + difference 1 0) sourceC1667) = raw24452 := by
      apply Matrix.ext; unfold tripleCharges sourceA1667 sourceB1667 sourceC1667 difference raw24452; decide +kernel
    rw [ha]
    exact (canonical24452 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1667 + difference 0 2) (sourceB1667 + difference 2 0) sourceC1667) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2584) := by
    have ha : (tripleCharges (sourceA1667 + difference 0 2) (sourceB1667 + difference 2 0) sourceC1667) = raw24453 := by
      apply Matrix.ext; unfold tripleCharges sourceA1667 sourceB1667 sourceC1667 difference raw24453; decide +kernel
    rw [ha]
    exact (canonical24453 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1667 + difference 0 3) (sourceB1667 + difference 3 0) sourceC1667) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2761) := by
    have ha : (tripleCharges (sourceA1667 + difference 0 3) (sourceB1667 + difference 3 0) sourceC1667) = raw24454 := by
      apply Matrix.ext; unfold tripleCharges sourceA1667 sourceB1667 sourceC1667 difference raw24454; decide +kernel
    rw [ha]
    exact (canonical24454 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1667 + difference 0 4) (sourceB1667 + difference 4 0) sourceC1667) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2685) := by
    have ha : (tripleCharges (sourceA1667 + difference 0 4) (sourceB1667 + difference 4 0) sourceC1667) = raw24455 := by
      apply Matrix.ext; unfold tripleCharges sourceA1667 sourceB1667 sourceC1667 difference raw24455; decide +kernel
    rw [ha]
    exact (canonical24455 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1667 + difference 0 5) (sourceB1667 + difference 5 0) sourceC1667) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2761) := by
    have ha : (tripleCharges (sourceA1667 + difference 0 5) (sourceB1667 + difference 5 0) sourceC1667) = raw24456 := by
      apply Matrix.ext; unfold tripleCharges sourceA1667 sourceB1667 sourceC1667 difference raw24456; decide +kernel
    rw [ha]
    exact (canonical24456 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1667 + sourceB1667) sourceC1667) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA1667 + sourceB1667) sourceC1667) = raw24457 := by
      apply Matrix.ext; unfold doubleCharges sourceA1667 sourceB1667 sourceC1667 raw24457; decide +kernel
    rw [ha]
    exact (canonical24457 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1667 sourceB1667 sourceC1667
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1667, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1668 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1668 : Charge := ![2, 0, -1, 1, -2, 0]
def sourceC1668 : Charge := ![2, 0, 1, -2, 1, -2]
def sourceForm1668 : Integer.Sparse Master := [(Sum.inr 1230, 1), (Sum.inr 2505, 1), (Sum.inr 2551, 1), (Sum.inr 2705, 1), (Sum.inr 2729, 1), (Sum.inr 2736, 1), (Sum.inr 4088, -1)]

theorem sourceEq1668 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1668 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1668 + difference 0 0) (sourceB1668 + difference 0 0) sourceC1668) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1230) := by
    have ha : (tripleCharges (sourceA1668 + difference 0 0) (sourceB1668 + difference 0 0) sourceC1668) = raw24458 := by
      apply Matrix.ext; unfold tripleCharges sourceA1668 sourceB1668 sourceC1668 difference raw24458; decide +kernel
    rw [ha]
    exact (canonical24458 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1668 + difference 0 1) (sourceB1668 + difference 1 0) sourceC1668) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2551) := by
    have ha : (tripleCharges (sourceA1668 + difference 0 1) (sourceB1668 + difference 1 0) sourceC1668) = raw24459 := by
      apply Matrix.ext; unfold tripleCharges sourceA1668 sourceB1668 sourceC1668 difference raw24459; decide +kernel
    rw [ha]
    exact (canonical24459 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1668 + difference 0 2) (sourceB1668 + difference 2 0) sourceC1668) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2505) := by
    have ha : (tripleCharges (sourceA1668 + difference 0 2) (sourceB1668 + difference 2 0) sourceC1668) = raw24460 := by
      apply Matrix.ext; unfold tripleCharges sourceA1668 sourceB1668 sourceC1668 difference raw24460; decide +kernel
    rw [ha]
    exact (canonical24460 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1668 + difference 0 3) (sourceB1668 + difference 3 0) sourceC1668) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2729) := by
    have ha : (tripleCharges (sourceA1668 + difference 0 3) (sourceB1668 + difference 3 0) sourceC1668) = raw24461 := by
      apply Matrix.ext; unfold tripleCharges sourceA1668 sourceB1668 sourceC1668 difference raw24461; decide +kernel
    rw [ha]
    exact (canonical24461 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1668 + difference 0 4) (sourceB1668 + difference 4 0) sourceC1668) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2705) := by
    have ha : (tripleCharges (sourceA1668 + difference 0 4) (sourceB1668 + difference 4 0) sourceC1668) = raw24462 := by
      apply Matrix.ext; unfold tripleCharges sourceA1668 sourceB1668 sourceC1668 difference raw24462; decide +kernel
    rw [ha]
    exact (canonical24462 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1668 + difference 0 5) (sourceB1668 + difference 5 0) sourceC1668) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2736) := by
    have ha : (tripleCharges (sourceA1668 + difference 0 5) (sourceB1668 + difference 5 0) sourceC1668) = raw24463 := by
      apply Matrix.ext; unfold tripleCharges sourceA1668 sourceB1668 sourceC1668 difference raw24463; decide +kernel
    rw [ha]
    exact (canonical24463 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1668 + sourceB1668) sourceC1668) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA1668 + sourceB1668) sourceC1668) = raw24464 := by
      apply Matrix.ext; unfold doubleCharges sourceA1668 sourceB1668 sourceC1668 raw24464; decide +kernel
    rw [ha]
    exact (canonical24464 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1668 sourceB1668 sourceC1668
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1668, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1669 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1669 : Charge := ![2, 0, -1, 0, 0, -1]
def sourceC1669 : Charge := ![2, 0, 1, -1, -1, -1]
def sourceForm1669 : Integer.Sparse Master := [(Sum.inr 4150, 1), (Sum.inr 4151, 1), (Sum.inr 4155, 2), (Sum.inr 4173, 1), (Sum.inr 4527, 1), (Sum.inr 4530, 2), (Sum.inr 4542, 1), (Sum.inr 4544, 1), (Sum.inr 4551, 1), (Sum.inr 4554, 2), (Sum.inr 4590, 2), (Sum.inr 4591, 2), (Sum.inr 4593, 2), (Sum.inr 4601, 1), (Sum.inr 4603, 2), (Sum.inr 4606, 2), (Sum.inr 4618, 1), (Sum.inr 5104, 1), (Sum.inr 5137, 1), (Sum.inr 5259, 2), (Sum.inr 5273, 1)]

theorem sourceEq1669 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1669 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1669 + difference 0 1) (sourceB1669 + difference 1 0) sourceC1669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5137) := by
    have ha : (tripleCharges (sourceA1669 + difference 0 1) (sourceB1669 + difference 1 0) sourceC1669) = raw14247 := by
      apply Matrix.ext; unfold tripleCharges sourceA1669 sourceB1669 sourceC1669 difference raw14247; decide +kernel
    rw [ha]
    exact (canonical14247 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1669 + difference 0 2) (sourceB1669 + difference 2 0) sourceC1669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5104) := by
    have ha : (tripleCharges (sourceA1669 + difference 0 2) (sourceB1669 + difference 2 0) sourceC1669) = raw14248 := by
      apply Matrix.ext; unfold tripleCharges sourceA1669 sourceB1669 sourceC1669 difference raw14248; decide +kernel
    rw [ha]
    exact (canonical14248 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1669 + difference 0 3) (sourceB1669 + difference 3 0) sourceC1669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA1669 + difference 0 3) (sourceB1669 + difference 3 0) sourceC1669) = raw14249 := by
      apply Matrix.ext; unfold tripleCharges sourceA1669 sourceB1669 sourceC1669 difference raw14249; decide +kernel
    rw [ha]
    exact (canonical14249 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1669 + difference 0 4) (sourceB1669 + difference 4 0) sourceC1669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA1669 + difference 0 4) (sourceB1669 + difference 4 0) sourceC1669) = raw14250 := by
      apply Matrix.ext; unfold tripleCharges sourceA1669 sourceB1669 sourceC1669 difference raw14250; decide +kernel
    rw [ha]
    exact (canonical14250 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1669 + difference 0 5) (sourceB1669 + difference 5 0) sourceC1669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5273) := by
    have ha : (tripleCharges (sourceA1669 + difference 0 5) (sourceB1669 + difference 5 0) sourceC1669) = raw19343 := by
      apply Matrix.ext; unfold tripleCharges sourceA1669 sourceB1669 sourceC1669 difference raw19343; decide +kernel
    rw [ha]
    exact (canonical19343 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1669 + difference 1 0) (sourceB1669 + difference 0 1) sourceC1669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4150) := by
    have ha : (tripleCharges (sourceA1669 + difference 1 0) (sourceB1669 + difference 0 1) sourceC1669) = raw24465 := by
      apply Matrix.ext; unfold tripleCharges sourceA1669 sourceB1669 sourceC1669 difference raw24465; decide +kernel
    rw [ha]
    exact (canonical24465 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1669 + difference 1 2) (sourceB1669 + difference 2 1) sourceC1669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4544) := by
    have ha : (tripleCharges (sourceA1669 + difference 1 2) (sourceB1669 + difference 2 1) sourceC1669) = raw24466 := by
      apply Matrix.ext; unfold tripleCharges sourceA1669 sourceB1669 sourceC1669 difference raw24466; decide +kernel
    rw [ha]
    exact (canonical24466 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1669 + difference 1 3) (sourceB1669 + difference 3 1) sourceC1669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4590) := by
    have ha : (tripleCharges (sourceA1669 + difference 1 3) (sourceB1669 + difference 3 1) sourceC1669) = raw24467 := by
      apply Matrix.ext; unfold tripleCharges sourceA1669 sourceB1669 sourceC1669 difference raw24467; decide +kernel
    rw [ha]
    exact (canonical24467 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1669 + difference 1 4) (sourceB1669 + difference 4 1) sourceC1669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4590) := by
    have ha : (tripleCharges (sourceA1669 + difference 1 4) (sourceB1669 + difference 4 1) sourceC1669) = raw24468 := by
      apply Matrix.ext; unfold tripleCharges sourceA1669 sourceB1669 sourceC1669 difference raw24468; decide +kernel
    rw [ha]
    exact (canonical24468 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1669 + difference 1 5) (sourceB1669 + difference 5 1) sourceC1669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4601) := by
    have ha : (tripleCharges (sourceA1669 + difference 1 5) (sourceB1669 + difference 5 1) sourceC1669) = raw14226 := by
      apply Matrix.ext; unfold tripleCharges sourceA1669 sourceB1669 sourceC1669 difference raw14226; decide +kernel
    rw [ha]
    exact (canonical14226 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1669 + difference 2 0) (sourceB1669 + difference 0 2) sourceC1669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4173) := by
    have ha : (tripleCharges (sourceA1669 + difference 2 0) (sourceB1669 + difference 0 2) sourceC1669) = raw24469 := by
      apply Matrix.ext; unfold tripleCharges sourceA1669 sourceB1669 sourceC1669 difference raw24469; decide +kernel
    rw [ha]
    exact (canonical24469 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1669 + difference 2 1) (sourceB1669 + difference 1 2) sourceC1669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4542) := by
    have ha : (tripleCharges (sourceA1669 + difference 2 1) (sourceB1669 + difference 1 2) sourceC1669) = raw24470 := by
      apply Matrix.ext; unfold tripleCharges sourceA1669 sourceB1669 sourceC1669 difference raw24470; decide +kernel
    rw [ha]
    exact (canonical24470 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1669 + difference 2 3) (sourceB1669 + difference 3 2) sourceC1669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4603) := by
    have ha : (tripleCharges (sourceA1669 + difference 2 3) (sourceB1669 + difference 3 2) sourceC1669) = raw24471 := by
      apply Matrix.ext; unfold tripleCharges sourceA1669 sourceB1669 sourceC1669 difference raw24471; decide +kernel
    rw [ha]
    exact (canonical24471 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1669 + difference 2 4) (sourceB1669 + difference 4 2) sourceC1669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4603) := by
    have ha : (tripleCharges (sourceA1669 + difference 2 4) (sourceB1669 + difference 4 2) sourceC1669) = raw24472 := by
      apply Matrix.ext; unfold tripleCharges sourceA1669 sourceB1669 sourceC1669 difference raw24472; decide +kernel
    rw [ha]
    exact (canonical24472 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1669 + difference 2 5) (sourceB1669 + difference 5 2) sourceC1669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4618) := by
    have ha : (tripleCharges (sourceA1669 + difference 2 5) (sourceB1669 + difference 5 2) sourceC1669) = raw14231 := by
      apply Matrix.ext; unfold tripleCharges sourceA1669 sourceB1669 sourceC1669 difference raw14231; decide +kernel
    rw [ha]
    exact (canonical14231 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1669 + difference 3 0) (sourceB1669 + difference 0 3) sourceC1669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4155) := by
    have ha : (tripleCharges (sourceA1669 + difference 3 0) (sourceB1669 + difference 0 3) sourceC1669) = raw24473 := by
      apply Matrix.ext; unfold tripleCharges sourceA1669 sourceB1669 sourceC1669 difference raw24473; decide +kernel
    rw [ha]
    exact (canonical24473 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1669 + difference 3 1) (sourceB1669 + difference 1 3) sourceC1669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4530) := by
    have ha : (tripleCharges (sourceA1669 + difference 3 1) (sourceB1669 + difference 1 3) sourceC1669) = raw24474 := by
      apply Matrix.ext; unfold tripleCharges sourceA1669 sourceB1669 sourceC1669 difference raw24474; decide +kernel
    rw [ha]
    exact (canonical24474 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1669 + difference 3 2) (sourceB1669 + difference 2 3) sourceC1669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4554) := by
    have ha : (tripleCharges (sourceA1669 + difference 3 2) (sourceB1669 + difference 2 3) sourceC1669) = raw24475 := by
      apply Matrix.ext; unfold tripleCharges sourceA1669 sourceB1669 sourceC1669 difference raw24475; decide +kernel
    rw [ha]
    exact (canonical24475 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1669 + difference 3 4) (sourceB1669 + difference 4 3) sourceC1669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4593) := by
    have ha : (tripleCharges (sourceA1669 + difference 3 4) (sourceB1669 + difference 4 3) sourceC1669) = raw24476 := by
      apply Matrix.ext; unfold tripleCharges sourceA1669 sourceB1669 sourceC1669 difference raw24476; decide +kernel
    rw [ha]
    exact (canonical24476 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1669 + difference 3 5) (sourceB1669 + difference 5 3) sourceC1669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4606) := by
    have ha : (tripleCharges (sourceA1669 + difference 3 5) (sourceB1669 + difference 5 3) sourceC1669) = raw14236 := by
      apply Matrix.ext; unfold tripleCharges sourceA1669 sourceB1669 sourceC1669 difference raw14236; decide +kernel
    rw [ha]
    exact (canonical14236 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1669 + difference 4 0) (sourceB1669 + difference 0 4) sourceC1669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4155) := by
    have ha : (tripleCharges (sourceA1669 + difference 4 0) (sourceB1669 + difference 0 4) sourceC1669) = raw24477 := by
      apply Matrix.ext; unfold tripleCharges sourceA1669 sourceB1669 sourceC1669 difference raw24477; decide +kernel
    rw [ha]
    exact (canonical24477 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1669 + difference 4 1) (sourceB1669 + difference 1 4) sourceC1669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4530) := by
    have ha : (tripleCharges (sourceA1669 + difference 4 1) (sourceB1669 + difference 1 4) sourceC1669) = raw24478 := by
      apply Matrix.ext; unfold tripleCharges sourceA1669 sourceB1669 sourceC1669 difference raw24478; decide +kernel
    rw [ha]
    exact (canonical24478 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1669 + difference 4 2) (sourceB1669 + difference 2 4) sourceC1669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4554) := by
    have ha : (tripleCharges (sourceA1669 + difference 4 2) (sourceB1669 + difference 2 4) sourceC1669) = raw24479 := by
      apply Matrix.ext; unfold tripleCharges sourceA1669 sourceB1669 sourceC1669 difference raw24479; decide +kernel
    rw [ha]
    exact (canonical24479 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1669 + difference 4 3) (sourceB1669 + difference 3 4) sourceC1669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4593) := by
    have ha : (tripleCharges (sourceA1669 + difference 4 3) (sourceB1669 + difference 3 4) sourceC1669) = raw24480 := by
      apply Matrix.ext; unfold tripleCharges sourceA1669 sourceB1669 sourceC1669 difference raw24480; decide +kernel
    rw [ha]
    exact (canonical24480 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1669 + difference 4 5) (sourceB1669 + difference 5 4) sourceC1669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4606) := by
    have ha : (tripleCharges (sourceA1669 + difference 4 5) (sourceB1669 + difference 5 4) sourceC1669) = raw14241 := by
      apply Matrix.ext; unfold tripleCharges sourceA1669 sourceB1669 sourceC1669 difference raw14241; decide +kernel
    rw [ha]
    exact (canonical14241 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1669 + difference 5 0) (sourceB1669 + difference 0 5) sourceC1669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4151) := by
    have ha : (tripleCharges (sourceA1669 + difference 5 0) (sourceB1669 + difference 0 5) sourceC1669) = raw24481 := by
      apply Matrix.ext; unfold tripleCharges sourceA1669 sourceB1669 sourceC1669 difference raw24481; decide +kernel
    rw [ha]
    exact (canonical24481 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1669 + difference 5 1) (sourceB1669 + difference 1 5) sourceC1669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4527) := by
    have ha : (tripleCharges (sourceA1669 + difference 5 1) (sourceB1669 + difference 1 5) sourceC1669) = raw24482 := by
      apply Matrix.ext; unfold tripleCharges sourceA1669 sourceB1669 sourceC1669 difference raw24482; decide +kernel
    rw [ha]
    exact (canonical24482 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1669 + difference 5 2) (sourceB1669 + difference 2 5) sourceC1669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4551) := by
    have ha : (tripleCharges (sourceA1669 + difference 5 2) (sourceB1669 + difference 2 5) sourceC1669) = raw24483 := by
      apply Matrix.ext; unfold tripleCharges sourceA1669 sourceB1669 sourceC1669 difference raw24483; decide +kernel
    rw [ha]
    exact (canonical24483 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1669 + difference 5 3) (sourceB1669 + difference 3 5) sourceC1669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4591) := by
    have ha : (tripleCharges (sourceA1669 + difference 5 3) (sourceB1669 + difference 3 5) sourceC1669) = raw24484 := by
      apply Matrix.ext; unfold tripleCharges sourceA1669 sourceB1669 sourceC1669 difference raw24484; decide +kernel
    rw [ha]
    exact (canonical24484 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1669 + difference 5 4) (sourceB1669 + difference 4 5) sourceC1669) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4591) := by
    have ha : (tripleCharges (sourceA1669 + difference 5 4) (sourceB1669 + difference 4 5) sourceC1669) = raw24485 := by
      apply Matrix.ext; unfold tripleCharges sourceA1669 sourceB1669 sourceC1669 difference raw24485; decide +kernel
    rw [ha]
    exact (canonical24485 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1669 sourceB1669 sourceC1669
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1669, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1670 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1670 : Charge := ![2, 0, -1, 0, 0, -1]
def sourceC1670 : Charge := ![2, 0, 1, -1, -1, -1]
def sourceForm1670 : Integer.Sparse Master := [(Sum.inr 578, 1), (Sum.inr 579, 1), (Sum.inr 583, 2), (Sum.inr 601, 1), (Sum.inr 1111, 1), (Sum.inr 1114, 2), (Sum.inr 1127, 1), (Sum.inr 1162, 1), (Sum.inr 1163, 1), (Sum.inr 1167, 2), (Sum.inr 1213, 2), (Sum.inr 1215, 2), (Sum.inr 1220, 2), (Sum.inr 1237, 2), (Sum.inr 1265, 1), (Sum.inr 1266, 2), (Sum.inr 1298, 1), (Sum.inr 2936, 1), (Sum.inr 3000, 1), (Sum.inr 3088, 2), (Sum.inr 3111, 1)]

theorem sourceEq1670 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1670 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1670 + difference 0 1) (sourceB1670 + difference 1 0) sourceC1670) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2936) := by
    have ha : (tripleCharges (sourceA1670 + difference 0 1) (sourceB1670 + difference 1 0) sourceC1670) = raw24486 := by
      apply Matrix.ext; unfold tripleCharges sourceA1670 sourceB1670 sourceC1670 difference raw24486; decide +kernel
    rw [ha]
    exact (canonical24486 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1670 + difference 0 2) (sourceB1670 + difference 2 0) sourceC1670) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3000) := by
    have ha : (tripleCharges (sourceA1670 + difference 0 2) (sourceB1670 + difference 2 0) sourceC1670) = raw24487 := by
      apply Matrix.ext; unfold tripleCharges sourceA1670 sourceB1670 sourceC1670 difference raw24487; decide +kernel
    rw [ha]
    exact (canonical24487 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1670 + difference 0 3) (sourceB1670 + difference 3 0) sourceC1670) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3088) := by
    have ha : (tripleCharges (sourceA1670 + difference 0 3) (sourceB1670 + difference 3 0) sourceC1670) = raw24488 := by
      apply Matrix.ext; unfold tripleCharges sourceA1670 sourceB1670 sourceC1670 difference raw24488; decide +kernel
    rw [ha]
    exact (canonical24488 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1670 + difference 0 4) (sourceB1670 + difference 4 0) sourceC1670) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3088) := by
    have ha : (tripleCharges (sourceA1670 + difference 0 4) (sourceB1670 + difference 4 0) sourceC1670) = raw24489 := by
      apply Matrix.ext; unfold tripleCharges sourceA1670 sourceB1670 sourceC1670 difference raw24489; decide +kernel
    rw [ha]
    exact (canonical24489 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1670 + difference 0 5) (sourceB1670 + difference 5 0) sourceC1670) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3111) := by
    have ha : (tripleCharges (sourceA1670 + difference 0 5) (sourceB1670 + difference 5 0) sourceC1670) = raw24490 := by
      apply Matrix.ext; unfold tripleCharges sourceA1670 sourceB1670 sourceC1670 difference raw24490; decide +kernel
    rw [ha]
    exact (canonical24490 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1670 + difference 1 0) (sourceB1670 + difference 0 1) sourceC1670) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 578) := by
    have ha : (tripleCharges (sourceA1670 + difference 1 0) (sourceB1670 + difference 0 1) sourceC1670) = raw24491 := by
      apply Matrix.ext; unfold tripleCharges sourceA1670 sourceB1670 sourceC1670 difference raw24491; decide +kernel
    rw [ha]
    exact (canonical24491 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1670 + difference 1 2) (sourceB1670 + difference 2 1) sourceC1670) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1162) := by
    have ha : (tripleCharges (sourceA1670 + difference 1 2) (sourceB1670 + difference 2 1) sourceC1670) = raw24492 := by
      apply Matrix.ext; unfold tripleCharges sourceA1670 sourceB1670 sourceC1670 difference raw24492; decide +kernel
    rw [ha]
    exact (canonical24492 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1670 + difference 1 3) (sourceB1670 + difference 3 1) sourceC1670) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1213) := by
    have ha : (tripleCharges (sourceA1670 + difference 1 3) (sourceB1670 + difference 3 1) sourceC1670) = raw24493 := by
      apply Matrix.ext; unfold tripleCharges sourceA1670 sourceB1670 sourceC1670 difference raw24493; decide +kernel
    rw [ha]
    exact (canonical24493 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1670 + difference 1 4) (sourceB1670 + difference 4 1) sourceC1670) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1213) := by
    have ha : (tripleCharges (sourceA1670 + difference 1 4) (sourceB1670 + difference 4 1) sourceC1670) = raw24494 := by
      apply Matrix.ext; unfold tripleCharges sourceA1670 sourceB1670 sourceC1670 difference raw24494; decide +kernel
    rw [ha]
    exact (canonical24494 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1670 + difference 1 5) (sourceB1670 + difference 5 1) sourceC1670) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1265) := by
    have ha : (tripleCharges (sourceA1670 + difference 1 5) (sourceB1670 + difference 5 1) sourceC1670) = raw24495 := by
      apply Matrix.ext; unfold tripleCharges sourceA1670 sourceB1670 sourceC1670 difference raw24495; decide +kernel
    rw [ha]
    exact (canonical24495 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1670 + difference 2 0) (sourceB1670 + difference 0 2) sourceC1670) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 601) := by
    have ha : (tripleCharges (sourceA1670 + difference 2 0) (sourceB1670 + difference 0 2) sourceC1670) = raw24496 := by
      apply Matrix.ext; unfold tripleCharges sourceA1670 sourceB1670 sourceC1670 difference raw24496; decide +kernel
    rw [ha]
    exact (canonical24496 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1670 + difference 2 1) (sourceB1670 + difference 1 2) sourceC1670) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1127) := by
    have ha : (tripleCharges (sourceA1670 + difference 2 1) (sourceB1670 + difference 1 2) sourceC1670) = raw24497 := by
      apply Matrix.ext; unfold tripleCharges sourceA1670 sourceB1670 sourceC1670 difference raw24497; decide +kernel
    rw [ha]
    exact (canonical24497 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1670 + difference 2 3) (sourceB1670 + difference 3 2) sourceC1670) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1237) := by
    have ha : (tripleCharges (sourceA1670 + difference 2 3) (sourceB1670 + difference 3 2) sourceC1670) = raw24498 := by
      apply Matrix.ext; unfold tripleCharges sourceA1670 sourceB1670 sourceC1670 difference raw24498; decide +kernel
    rw [ha]
    exact (canonical24498 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1670 + difference 2 4) (sourceB1670 + difference 4 2) sourceC1670) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1237) := by
    have ha : (tripleCharges (sourceA1670 + difference 2 4) (sourceB1670 + difference 4 2) sourceC1670) = raw24499 := by
      apply Matrix.ext; unfold tripleCharges sourceA1670 sourceB1670 sourceC1670 difference raw24499; decide +kernel
    rw [ha]
    exact (canonical24499 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1670 + difference 2 5) (sourceB1670 + difference 5 2) sourceC1670) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1298) := by
    have ha : (tripleCharges (sourceA1670 + difference 2 5) (sourceB1670 + difference 5 2) sourceC1670) = raw24500 := by
      apply Matrix.ext; unfold tripleCharges sourceA1670 sourceB1670 sourceC1670 difference raw24500; decide +kernel
    rw [ha]
    exact (canonical24500 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1670 + difference 3 0) (sourceB1670 + difference 0 3) sourceC1670) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 583) := by
    have ha : (tripleCharges (sourceA1670 + difference 3 0) (sourceB1670 + difference 0 3) sourceC1670) = raw24501 := by
      apply Matrix.ext; unfold tripleCharges sourceA1670 sourceB1670 sourceC1670 difference raw24501; decide +kernel
    rw [ha]
    exact (canonical24501 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1670 + difference 3 1) (sourceB1670 + difference 1 3) sourceC1670) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1114) := by
    have ha : (tripleCharges (sourceA1670 + difference 3 1) (sourceB1670 + difference 1 3) sourceC1670) = raw24502 := by
      apply Matrix.ext; unfold tripleCharges sourceA1670 sourceB1670 sourceC1670 difference raw24502; decide +kernel
    rw [ha]
    exact (canonical24502 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1670 + difference 3 2) (sourceB1670 + difference 2 3) sourceC1670) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1167) := by
    have ha : (tripleCharges (sourceA1670 + difference 3 2) (sourceB1670 + difference 2 3) sourceC1670) = raw24503 := by
      apply Matrix.ext; unfold tripleCharges sourceA1670 sourceB1670 sourceC1670 difference raw24503; decide +kernel
    rw [ha]
    exact (canonical24503 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1670 + difference 3 4) (sourceB1670 + difference 4 3) sourceC1670) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1220) := by
    have ha : (tripleCharges (sourceA1670 + difference 3 4) (sourceB1670 + difference 4 3) sourceC1670) = raw24504 := by
      apply Matrix.ext; unfold tripleCharges sourceA1670 sourceB1670 sourceC1670 difference raw24504; decide +kernel
    rw [ha]
    exact (canonical24504 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1670 + difference 3 5) (sourceB1670 + difference 5 3) sourceC1670) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1266) := by
    have ha : (tripleCharges (sourceA1670 + difference 3 5) (sourceB1670 + difference 5 3) sourceC1670) = raw24505 := by
      apply Matrix.ext; unfold tripleCharges sourceA1670 sourceB1670 sourceC1670 difference raw24505; decide +kernel
    rw [ha]
    exact (canonical24505 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1670 + difference 4 0) (sourceB1670 + difference 0 4) sourceC1670) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 583) := by
    have ha : (tripleCharges (sourceA1670 + difference 4 0) (sourceB1670 + difference 0 4) sourceC1670) = raw24506 := by
      apply Matrix.ext; unfold tripleCharges sourceA1670 sourceB1670 sourceC1670 difference raw24506; decide +kernel
    rw [ha]
    exact (canonical24506 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1670 + difference 4 1) (sourceB1670 + difference 1 4) sourceC1670) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1114) := by
    have ha : (tripleCharges (sourceA1670 + difference 4 1) (sourceB1670 + difference 1 4) sourceC1670) = raw24507 := by
      apply Matrix.ext; unfold tripleCharges sourceA1670 sourceB1670 sourceC1670 difference raw24507; decide +kernel
    rw [ha]
    exact (canonical24507 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1670 + difference 4 2) (sourceB1670 + difference 2 4) sourceC1670) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1167) := by
    have ha : (tripleCharges (sourceA1670 + difference 4 2) (sourceB1670 + difference 2 4) sourceC1670) = raw24508 := by
      apply Matrix.ext; unfold tripleCharges sourceA1670 sourceB1670 sourceC1670 difference raw24508; decide +kernel
    rw [ha]
    exact (canonical24508 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1670 + difference 4 3) (sourceB1670 + difference 3 4) sourceC1670) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1220) := by
    have ha : (tripleCharges (sourceA1670 + difference 4 3) (sourceB1670 + difference 3 4) sourceC1670) = raw24509 := by
      apply Matrix.ext; unfold tripleCharges sourceA1670 sourceB1670 sourceC1670 difference raw24509; decide +kernel
    rw [ha]
    exact (canonical24509 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1670 + difference 4 5) (sourceB1670 + difference 5 4) sourceC1670) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1266) := by
    have ha : (tripleCharges (sourceA1670 + difference 4 5) (sourceB1670 + difference 5 4) sourceC1670) = raw24510 := by
      apply Matrix.ext; unfold tripleCharges sourceA1670 sourceB1670 sourceC1670 difference raw24510; decide +kernel
    rw [ha]
    exact (canonical24510 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1670 + difference 5 0) (sourceB1670 + difference 0 5) sourceC1670) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 579) := by
    have ha : (tripleCharges (sourceA1670 + difference 5 0) (sourceB1670 + difference 0 5) sourceC1670) = raw24511 := by
      apply Matrix.ext; unfold tripleCharges sourceA1670 sourceB1670 sourceC1670 difference raw24511; decide +kernel
    rw [ha]
    exact (canonical24511 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1670 + difference 5 1) (sourceB1670 + difference 1 5) sourceC1670) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1111) := by
    have ha : (tripleCharges (sourceA1670 + difference 5 1) (sourceB1670 + difference 1 5) sourceC1670) = raw24512 := by
      apply Matrix.ext; unfold tripleCharges sourceA1670 sourceB1670 sourceC1670 difference raw24512; decide +kernel
    rw [ha]
    exact (canonical24512 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1670 + difference 5 2) (sourceB1670 + difference 2 5) sourceC1670) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1163) := by
    have ha : (tripleCharges (sourceA1670 + difference 5 2) (sourceB1670 + difference 2 5) sourceC1670) = raw24513 := by
      apply Matrix.ext; unfold tripleCharges sourceA1670 sourceB1670 sourceC1670 difference raw24513; decide +kernel
    rw [ha]
    exact (canonical24513 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1670 + difference 5 3) (sourceB1670 + difference 3 5) sourceC1670) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1215) := by
    have ha : (tripleCharges (sourceA1670 + difference 5 3) (sourceB1670 + difference 3 5) sourceC1670) = raw24514 := by
      apply Matrix.ext; unfold tripleCharges sourceA1670 sourceB1670 sourceC1670 difference raw24514; decide +kernel
    rw [ha]
    exact (canonical24514 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1670 + difference 5 4) (sourceB1670 + difference 4 5) sourceC1670) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1215) := by
    have ha : (tripleCharges (sourceA1670 + difference 5 4) (sourceB1670 + difference 4 5) sourceC1670) = raw24515 := by
      apply Matrix.ext; unfold tripleCharges sourceA1670 sourceB1670 sourceC1670 difference raw24515; decide +kernel
    rw [ha]
    exact (canonical24515 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1670 sourceB1670 sourceC1670
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1670, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1671 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1671 : Charge := ![2, 0, -1, 0, 0, -1]
def sourceC1671 : Charge := ![2, 0, 1, -1, -1, -1]
def sourceForm1671 : Integer.Sparse Master := [(Sum.inr 1504, 1), (Sum.inr 1505, 1), (Sum.inr 1508, 1), (Sum.inr 1515, 2), (Sum.inr 3255, 1), (Sum.inr 3257, 1), (Sum.inr 3261, 2), (Sum.inr 3263, 1), (Sum.inr 3273, 1), (Sum.inr 3274, 2), (Sum.inr 3290, 2), (Sum.inr 3291, 2), (Sum.inr 3292, 1), (Sum.inr 3294, 2), (Sum.inr 3297, 2), (Sum.inr 3299, 2), (Sum.inr 3304, 1), (Sum.inr 3483, 1), (Sum.inr 3521, 1), (Sum.inr 3544, 2), (Sum.inr 3546, 1)]

theorem sourceEq1671 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1671 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1671 + difference 0 1) (sourceB1671 + difference 1 0) sourceC1671) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3521) := by
    have ha : (tripleCharges (sourceA1671 + difference 0 1) (sourceB1671 + difference 1 0) sourceC1671) = raw24516 := by
      apply Matrix.ext; unfold tripleCharges sourceA1671 sourceB1671 sourceC1671 difference raw24516; decide +kernel
    rw [ha]
    exact (canonical24516 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1671 + difference 0 2) (sourceB1671 + difference 2 0) sourceC1671) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3483) := by
    have ha : (tripleCharges (sourceA1671 + difference 0 2) (sourceB1671 + difference 2 0) sourceC1671) = raw24517 := by
      apply Matrix.ext; unfold tripleCharges sourceA1671 sourceB1671 sourceC1671 difference raw24517; decide +kernel
    rw [ha]
    exact (canonical24517 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1671 + difference 0 3) (sourceB1671 + difference 3 0) sourceC1671) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3544) := by
    have ha : (tripleCharges (sourceA1671 + difference 0 3) (sourceB1671 + difference 3 0) sourceC1671) = raw24518 := by
      apply Matrix.ext; unfold tripleCharges sourceA1671 sourceB1671 sourceC1671 difference raw24518; decide +kernel
    rw [ha]
    exact (canonical24518 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1671 + difference 0 4) (sourceB1671 + difference 4 0) sourceC1671) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3544) := by
    have ha : (tripleCharges (sourceA1671 + difference 0 4) (sourceB1671 + difference 4 0) sourceC1671) = raw24519 := by
      apply Matrix.ext; unfold tripleCharges sourceA1671 sourceB1671 sourceC1671 difference raw24519; decide +kernel
    rw [ha]
    exact (canonical24519 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1671 + difference 0 5) (sourceB1671 + difference 5 0) sourceC1671) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3546) := by
    have ha : (tripleCharges (sourceA1671 + difference 0 5) (sourceB1671 + difference 5 0) sourceC1671) = raw24520 := by
      apply Matrix.ext; unfold tripleCharges sourceA1671 sourceB1671 sourceC1671 difference raw24520; decide +kernel
    rw [ha]
    exact (canonical24520 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1671 + difference 1 0) (sourceB1671 + difference 0 1) sourceC1671) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1504) := by
    have ha : (tripleCharges (sourceA1671 + difference 1 0) (sourceB1671 + difference 0 1) sourceC1671) = raw24521 := by
      apply Matrix.ext; unfold tripleCharges sourceA1671 sourceB1671 sourceC1671 difference raw24521; decide +kernel
    rw [ha]
    exact (canonical24521 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1671 + difference 1 2) (sourceB1671 + difference 2 1) sourceC1671) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3263) := by
    have ha : (tripleCharges (sourceA1671 + difference 1 2) (sourceB1671 + difference 2 1) sourceC1671) = raw24522 := by
      apply Matrix.ext; unfold tripleCharges sourceA1671 sourceB1671 sourceC1671 difference raw24522; decide +kernel
    rw [ha]
    exact (canonical24522 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1671 + difference 1 3) (sourceB1671 + difference 3 1) sourceC1671) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3290) := by
    have ha : (tripleCharges (sourceA1671 + difference 1 3) (sourceB1671 + difference 3 1) sourceC1671) = raw24523 := by
      apply Matrix.ext; unfold tripleCharges sourceA1671 sourceB1671 sourceC1671 difference raw24523; decide +kernel
    rw [ha]
    exact (canonical24523 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1671 + difference 1 4) (sourceB1671 + difference 4 1) sourceC1671) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3290) := by
    have ha : (tripleCharges (sourceA1671 + difference 1 4) (sourceB1671 + difference 4 1) sourceC1671) = raw24524 := by
      apply Matrix.ext; unfold tripleCharges sourceA1671 sourceB1671 sourceC1671 difference raw24524; decide +kernel
    rw [ha]
    exact (canonical24524 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1671 + difference 1 5) (sourceB1671 + difference 5 1) sourceC1671) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3292) := by
    have ha : (tripleCharges (sourceA1671 + difference 1 5) (sourceB1671 + difference 5 1) sourceC1671) = raw24525 := by
      apply Matrix.ext; unfold tripleCharges sourceA1671 sourceB1671 sourceC1671 difference raw24525; decide +kernel
    rw [ha]
    exact (canonical24525 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1671 + difference 2 0) (sourceB1671 + difference 0 2) sourceC1671) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1508) := by
    have ha : (tripleCharges (sourceA1671 + difference 2 0) (sourceB1671 + difference 0 2) sourceC1671) = raw24526 := by
      apply Matrix.ext; unfold tripleCharges sourceA1671 sourceB1671 sourceC1671 difference raw24526; decide +kernel
    rw [ha]
    exact (canonical24526 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1671 + difference 2 1) (sourceB1671 + difference 1 2) sourceC1671) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3257) := by
    have ha : (tripleCharges (sourceA1671 + difference 2 1) (sourceB1671 + difference 1 2) sourceC1671) = raw24527 := by
      apply Matrix.ext; unfold tripleCharges sourceA1671 sourceB1671 sourceC1671 difference raw24527; decide +kernel
    rw [ha]
    exact (canonical24527 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1671 + difference 2 3) (sourceB1671 + difference 3 2) sourceC1671) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3294) := by
    have ha : (tripleCharges (sourceA1671 + difference 2 3) (sourceB1671 + difference 3 2) sourceC1671) = raw24528 := by
      apply Matrix.ext; unfold tripleCharges sourceA1671 sourceB1671 sourceC1671 difference raw24528; decide +kernel
    rw [ha]
    exact (canonical24528 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1671 + difference 2 4) (sourceB1671 + difference 4 2) sourceC1671) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3294) := by
    have ha : (tripleCharges (sourceA1671 + difference 2 4) (sourceB1671 + difference 4 2) sourceC1671) = raw24529 := by
      apply Matrix.ext; unfold tripleCharges sourceA1671 sourceB1671 sourceC1671 difference raw24529; decide +kernel
    rw [ha]
    exact (canonical24529 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1671 + difference 2 5) (sourceB1671 + difference 5 2) sourceC1671) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3304) := by
    have ha : (tripleCharges (sourceA1671 + difference 2 5) (sourceB1671 + difference 5 2) sourceC1671) = raw24530 := by
      apply Matrix.ext; unfold tripleCharges sourceA1671 sourceB1671 sourceC1671 difference raw24530; decide +kernel
    rw [ha]
    exact (canonical24530 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1671 + difference 3 0) (sourceB1671 + difference 0 3) sourceC1671) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1515) := by
    have ha : (tripleCharges (sourceA1671 + difference 3 0) (sourceB1671 + difference 0 3) sourceC1671) = raw24531 := by
      apply Matrix.ext; unfold tripleCharges sourceA1671 sourceB1671 sourceC1671 difference raw24531; decide +kernel
    rw [ha]
    exact (canonical24531 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1671 + difference 3 1) (sourceB1671 + difference 1 3) sourceC1671) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3261) := by
    have ha : (tripleCharges (sourceA1671 + difference 3 1) (sourceB1671 + difference 1 3) sourceC1671) = raw24532 := by
      apply Matrix.ext; unfold tripleCharges sourceA1671 sourceB1671 sourceC1671 difference raw24532; decide +kernel
    rw [ha]
    exact (canonical24532 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1671 + difference 3 2) (sourceB1671 + difference 2 3) sourceC1671) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3274) := by
    have ha : (tripleCharges (sourceA1671 + difference 3 2) (sourceB1671 + difference 2 3) sourceC1671) = raw24533 := by
      apply Matrix.ext; unfold tripleCharges sourceA1671 sourceB1671 sourceC1671 difference raw24533; decide +kernel
    rw [ha]
    exact (canonical24533 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1671 + difference 3 4) (sourceB1671 + difference 4 3) sourceC1671) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3297) := by
    have ha : (tripleCharges (sourceA1671 + difference 3 4) (sourceB1671 + difference 4 3) sourceC1671) = raw24534 := by
      apply Matrix.ext; unfold tripleCharges sourceA1671 sourceB1671 sourceC1671 difference raw24534; decide +kernel
    rw [ha]
    exact (canonical24534 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1671 + difference 3 5) (sourceB1671 + difference 5 3) sourceC1671) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3299) := by
    have ha : (tripleCharges (sourceA1671 + difference 3 5) (sourceB1671 + difference 5 3) sourceC1671) = raw24535 := by
      apply Matrix.ext; unfold tripleCharges sourceA1671 sourceB1671 sourceC1671 difference raw24535; decide +kernel
    rw [ha]
    exact (canonical24535 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1671 + difference 4 0) (sourceB1671 + difference 0 4) sourceC1671) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1515) := by
    have ha : (tripleCharges (sourceA1671 + difference 4 0) (sourceB1671 + difference 0 4) sourceC1671) = raw24536 := by
      apply Matrix.ext; unfold tripleCharges sourceA1671 sourceB1671 sourceC1671 difference raw24536; decide +kernel
    rw [ha]
    exact (canonical24536 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1671 + difference 4 1) (sourceB1671 + difference 1 4) sourceC1671) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3261) := by
    have ha : (tripleCharges (sourceA1671 + difference 4 1) (sourceB1671 + difference 1 4) sourceC1671) = raw24537 := by
      apply Matrix.ext; unfold tripleCharges sourceA1671 sourceB1671 sourceC1671 difference raw24537; decide +kernel
    rw [ha]
    exact (canonical24537 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1671 + difference 4 2) (sourceB1671 + difference 2 4) sourceC1671) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3274) := by
    have ha : (tripleCharges (sourceA1671 + difference 4 2) (sourceB1671 + difference 2 4) sourceC1671) = raw24538 := by
      apply Matrix.ext; unfold tripleCharges sourceA1671 sourceB1671 sourceC1671 difference raw24538; decide +kernel
    rw [ha]
    exact (canonical24538 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1671 + difference 4 3) (sourceB1671 + difference 3 4) sourceC1671) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3297) := by
    have ha : (tripleCharges (sourceA1671 + difference 4 3) (sourceB1671 + difference 3 4) sourceC1671) = raw24539 := by
      apply Matrix.ext; unfold tripleCharges sourceA1671 sourceB1671 sourceC1671 difference raw24539; decide +kernel
    rw [ha]
    exact (canonical24539 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1671 + difference 4 5) (sourceB1671 + difference 5 4) sourceC1671) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3299) := by
    have ha : (tripleCharges (sourceA1671 + difference 4 5) (sourceB1671 + difference 5 4) sourceC1671) = raw24540 := by
      apply Matrix.ext; unfold tripleCharges sourceA1671 sourceB1671 sourceC1671 difference raw24540; decide +kernel
    rw [ha]
    exact (canonical24540 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1671 + difference 5 0) (sourceB1671 + difference 0 5) sourceC1671) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1505) := by
    have ha : (tripleCharges (sourceA1671 + difference 5 0) (sourceB1671 + difference 0 5) sourceC1671) = raw24541 := by
      apply Matrix.ext; unfold tripleCharges sourceA1671 sourceB1671 sourceC1671 difference raw24541; decide +kernel
    rw [ha]
    exact (canonical24541 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1671 + difference 5 1) (sourceB1671 + difference 1 5) sourceC1671) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3255) := by
    have ha : (tripleCharges (sourceA1671 + difference 5 1) (sourceB1671 + difference 1 5) sourceC1671) = raw24542 := by
      apply Matrix.ext; unfold tripleCharges sourceA1671 sourceB1671 sourceC1671 difference raw24542; decide +kernel
    rw [ha]
    exact (canonical24542 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1671 + difference 5 2) (sourceB1671 + difference 2 5) sourceC1671) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3273) := by
    have ha : (tripleCharges (sourceA1671 + difference 5 2) (sourceB1671 + difference 2 5) sourceC1671) = raw24543 := by
      apply Matrix.ext; unfold tripleCharges sourceA1671 sourceB1671 sourceC1671 difference raw24543; decide +kernel
    rw [ha]
    exact (canonical24543 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1671 + difference 5 3) (sourceB1671 + difference 3 5) sourceC1671) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3291) := by
    have ha : (tripleCharges (sourceA1671 + difference 5 3) (sourceB1671 + difference 3 5) sourceC1671) = raw24544 := by
      apply Matrix.ext; unfold tripleCharges sourceA1671 sourceB1671 sourceC1671 difference raw24544; decide +kernel
    rw [ha]
    exact (canonical24544 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1671 + difference 5 4) (sourceB1671 + difference 4 5) sourceC1671) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3291) := by
    have ha : (tripleCharges (sourceA1671 + difference 5 4) (sourceB1671 + difference 4 5) sourceC1671) = raw24545 := by
      apply Matrix.ext; unfold tripleCharges sourceA1671 sourceB1671 sourceC1671 difference raw24545; decide +kernel
    rw [ha]
    exact (canonical24545 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1671 sourceB1671 sourceC1671
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1671, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1672 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1672 : Charge := ![2, 0, -1, 0, 0, -1]
def sourceC1672 : Charge := ![2, 0, 1, -1, -1, -1]
def sourceForm1672 : Integer.Sparse Master := [(Sum.inr 625, 1), (Sum.inr 630, 1), (Sum.inr 632, 2), (Sum.inr 640, 1), (Sum.inr 1240, 1), (Sum.inr 4091, -1)]

theorem sourceEq1672 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1672 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1672 + difference 0 0) (sourceB1672 + difference 0 0) sourceC1672) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1240) := by
    have ha : (tripleCharges (sourceA1672 + difference 0 0) (sourceB1672 + difference 0 0) sourceC1672) = raw24546 := by
      apply Matrix.ext; unfold tripleCharges sourceA1672 sourceB1672 sourceC1672 difference raw24546; decide +kernel
    rw [ha]
    exact (canonical24546 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1672 + difference 1 0) (sourceB1672 + difference 0 1) sourceC1672) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 625) := by
    have ha : (tripleCharges (sourceA1672 + difference 1 0) (sourceB1672 + difference 0 1) sourceC1672) = raw24547 := by
      apply Matrix.ext; unfold tripleCharges sourceA1672 sourceB1672 sourceC1672 difference raw24547; decide +kernel
    rw [ha]
    exact (canonical24547 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1672 + difference 2 0) (sourceB1672 + difference 0 2) sourceC1672) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 640) := by
    have ha : (tripleCharges (sourceA1672 + difference 2 0) (sourceB1672 + difference 0 2) sourceC1672) = raw24548 := by
      apply Matrix.ext; unfold tripleCharges sourceA1672 sourceB1672 sourceC1672 difference raw24548; decide +kernel
    rw [ha]
    exact (canonical24548 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1672 + difference 3 0) (sourceB1672 + difference 0 3) sourceC1672) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 632) := by
    have ha : (tripleCharges (sourceA1672 + difference 3 0) (sourceB1672 + difference 0 3) sourceC1672) = raw24549 := by
      apply Matrix.ext; unfold tripleCharges sourceA1672 sourceB1672 sourceC1672 difference raw24549; decide +kernel
    rw [ha]
    exact (canonical24549 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1672 + difference 4 0) (sourceB1672 + difference 0 4) sourceC1672) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 632) := by
    have ha : (tripleCharges (sourceA1672 + difference 4 0) (sourceB1672 + difference 0 4) sourceC1672) = raw24550 := by
      apply Matrix.ext; unfold tripleCharges sourceA1672 sourceB1672 sourceC1672 difference raw24550; decide +kernel
    rw [ha]
    exact (canonical24550 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1672 + difference 5 0) (sourceB1672 + difference 0 5) sourceC1672) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 630) := by
    have ha : (tripleCharges (sourceA1672 + difference 5 0) (sourceB1672 + difference 0 5) sourceC1672) = raw24551 := by
      apply Matrix.ext; unfold tripleCharges sourceA1672 sourceB1672 sourceC1672 difference raw24551; decide +kernel
    rw [ha]
    exact (canonical24551 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1672 + sourceB1672) sourceC1672) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1672 + sourceB1672) sourceC1672) = raw24552 := by
      apply Matrix.ext; unfold doubleCharges sourceA1672 sourceB1672 sourceC1672 raw24552; decide +kernel
    rw [ha]
    exact (canonical24552 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1672 sourceB1672 sourceC1672
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1672, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1673 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1673 : Charge := ![2, 0, -1, 0, 0, -1]
def sourceC1673 : Charge := ![2, 0, 1, -1, -1, -1]
def sourceForm1673 : Integer.Sparse Master := [(Sum.inr 1150, 1), (Sum.inr 1152, 2), (Sum.inr 1158, 1), (Sum.inr 1240, 1), (Sum.inr 2556, 1), (Sum.inr 4091, -1)]

theorem sourceEq1673 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1673 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1673 + difference 0 1) (sourceB1673 + difference 1 0) sourceC1673) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2556) := by
    have ha : (tripleCharges (sourceA1673 + difference 0 1) (sourceB1673 + difference 1 0) sourceC1673) = raw24553 := by
      apply Matrix.ext; unfold tripleCharges sourceA1673 sourceB1673 sourceC1673 difference raw24553; decide +kernel
    rw [ha]
    exact (canonical24553 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1673 + difference 1 1) (sourceB1673 + difference 1 1) sourceC1673) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1240) := by
    have ha : (tripleCharges (sourceA1673 + difference 1 1) (sourceB1673 + difference 1 1) sourceC1673) = raw24546 := by
      apply Matrix.ext; unfold tripleCharges sourceA1673 sourceB1673 sourceC1673 difference raw24546; decide +kernel
    rw [ha]
    exact (canonical24546 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1673 + difference 2 1) (sourceB1673 + difference 1 2) sourceC1673) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1158) := by
    have ha : (tripleCharges (sourceA1673 + difference 2 1) (sourceB1673 + difference 1 2) sourceC1673) = raw24554 := by
      apply Matrix.ext; unfold tripleCharges sourceA1673 sourceB1673 sourceC1673 difference raw24554; decide +kernel
    rw [ha]
    exact (canonical24554 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1673 + difference 3 1) (sourceB1673 + difference 1 3) sourceC1673) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1152) := by
    have ha : (tripleCharges (sourceA1673 + difference 3 1) (sourceB1673 + difference 1 3) sourceC1673) = raw24555 := by
      apply Matrix.ext; unfold tripleCharges sourceA1673 sourceB1673 sourceC1673 difference raw24555; decide +kernel
    rw [ha]
    exact (canonical24555 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1673 + difference 4 1) (sourceB1673 + difference 1 4) sourceC1673) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1152) := by
    have ha : (tripleCharges (sourceA1673 + difference 4 1) (sourceB1673 + difference 1 4) sourceC1673) = raw24556 := by
      apply Matrix.ext; unfold tripleCharges sourceA1673 sourceB1673 sourceC1673 difference raw24556; decide +kernel
    rw [ha]
    exact (canonical24556 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1673 + difference 5 1) (sourceB1673 + difference 1 5) sourceC1673) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1150) := by
    have ha : (tripleCharges (sourceA1673 + difference 5 1) (sourceB1673 + difference 1 5) sourceC1673) = raw24557 := by
      apply Matrix.ext; unfold tripleCharges sourceA1673 sourceB1673 sourceC1673 difference raw24557; decide +kernel
    rw [ha]
    exact (canonical24557 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1673 + sourceB1673) sourceC1673) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1673 + sourceB1673) sourceC1673) = raw24552 := by
      apply Matrix.ext; unfold doubleCharges sourceA1673 sourceB1673 sourceC1673 raw24552; decide +kernel
    rw [ha]
    exact (canonical24552 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1673 sourceB1673 sourceC1673
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1673, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1674 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1674 : Charge := ![2, 0, 1, -1, -1, -1]
def sourceC1674 : Charge := ![2, 0, -1, 0, 0, -1]
def sourceForm1674 : Integer.Sparse Master := [(Sum.inr 4143, 1), (Sum.inr 4144, 1), (Sum.inr 4145, 2), (Sum.inr 4175, 1), (Sum.inr 4516, 1), (Sum.inr 4517, 1), (Sum.inr 4518, 2), (Sum.inr 4523, 1), (Sum.inr 4524, 2), (Sum.inr 4544, 1), (Sum.inr 4601, 1), (Sum.inr 4602, 2), (Sum.inr 4606, 2), (Sum.inr 4608, 2), (Sum.inr 4612, 2), (Sum.inr 4622, 1), (Sum.inr 4624, 2), (Sum.inr 5148, 1), (Sum.inr 5203, 1), (Sum.inr 5292, 1), (Sum.inr 5293, 2)]

theorem sourceEq1674 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1674 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1674 + difference 0 1) (sourceB1674 + difference 1 0) sourceC1674) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5148) := by
    have ha : (tripleCharges (sourceA1674 + difference 0 1) (sourceB1674 + difference 1 0) sourceC1674) = raw12557 := by
      apply Matrix.ext; unfold tripleCharges sourceA1674 sourceB1674 sourceC1674 difference raw12557; decide +kernel
    rw [ha]
    exact (canonical12557 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1674 + difference 0 2) (sourceB1674 + difference 2 0) sourceC1674) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5203) := by
    have ha : (tripleCharges (sourceA1674 + difference 0 2) (sourceB1674 + difference 2 0) sourceC1674) = raw12558 := by
      apply Matrix.ext; unfold tripleCharges sourceA1674 sourceB1674 sourceC1674 difference raw12558; decide +kernel
    rw [ha]
    exact (canonical12558 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1674 + difference 0 3) (sourceB1674 + difference 3 0) sourceC1674) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA1674 + difference 0 3) (sourceB1674 + difference 3 0) sourceC1674) = raw12559 := by
      apply Matrix.ext; unfold tripleCharges sourceA1674 sourceB1674 sourceC1674 difference raw12559; decide +kernel
    rw [ha]
    exact (canonical12559 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1674 + difference 0 4) (sourceB1674 + difference 4 0) sourceC1674) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA1674 + difference 0 4) (sourceB1674 + difference 4 0) sourceC1674) = raw12560 := by
      apply Matrix.ext; unfold tripleCharges sourceA1674 sourceB1674 sourceC1674 difference raw12560; decide +kernel
    rw [ha]
    exact (canonical12560 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1674 + difference 0 5) (sourceB1674 + difference 5 0) sourceC1674) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA1674 + difference 0 5) (sourceB1674 + difference 5 0) sourceC1674) = raw18364 := by
      apply Matrix.ext; unfold tripleCharges sourceA1674 sourceB1674 sourceC1674 difference raw18364; decide +kernel
    rw [ha]
    exact (canonical18364 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1674 + difference 1 0) (sourceB1674 + difference 0 1) sourceC1674) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4143) := by
    have ha : (tripleCharges (sourceA1674 + difference 1 0) (sourceB1674 + difference 0 1) sourceC1674) = raw24558 := by
      apply Matrix.ext; unfold tripleCharges sourceA1674 sourceB1674 sourceC1674 difference raw24558; decide +kernel
    rw [ha]
    exact (canonical24558 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1674 + difference 1 2) (sourceB1674 + difference 2 1) sourceC1674) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4516) := by
    have ha : (tripleCharges (sourceA1674 + difference 1 2) (sourceB1674 + difference 2 1) sourceC1674) = raw24559 := by
      apply Matrix.ext; unfold tripleCharges sourceA1674 sourceB1674 sourceC1674 difference raw24559; decide +kernel
    rw [ha]
    exact (canonical24559 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1674 + difference 1 3) (sourceB1674 + difference 3 1) sourceC1674) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4606) := by
    have ha : (tripleCharges (sourceA1674 + difference 1 3) (sourceB1674 + difference 3 1) sourceC1674) = raw24560 := by
      apply Matrix.ext; unfold tripleCharges sourceA1674 sourceB1674 sourceC1674 difference raw24560; decide +kernel
    rw [ha]
    exact (canonical24560 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1674 + difference 1 4) (sourceB1674 + difference 4 1) sourceC1674) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4606) := by
    have ha : (tripleCharges (sourceA1674 + difference 1 4) (sourceB1674 + difference 4 1) sourceC1674) = raw24561 := by
      apply Matrix.ext; unfold tripleCharges sourceA1674 sourceB1674 sourceC1674 difference raw24561; decide +kernel
    rw [ha]
    exact (canonical24561 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1674 + difference 1 5) (sourceB1674 + difference 5 1) sourceC1674) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4601) := by
    have ha : (tripleCharges (sourceA1674 + difference 1 5) (sourceB1674 + difference 5 1) sourceC1674) = raw12536 := by
      apply Matrix.ext; unfold tripleCharges sourceA1674 sourceB1674 sourceC1674 difference raw12536; decide +kernel
    rw [ha]
    exact (canonical12536 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1674 + difference 2 0) (sourceB1674 + difference 0 2) sourceC1674) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4175) := by
    have ha : (tripleCharges (sourceA1674 + difference 2 0) (sourceB1674 + difference 0 2) sourceC1674) = raw24562 := by
      apply Matrix.ext; unfold tripleCharges sourceA1674 sourceB1674 sourceC1674 difference raw24562; decide +kernel
    rw [ha]
    exact (canonical24562 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1674 + difference 2 1) (sourceB1674 + difference 1 2) sourceC1674) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4544) := by
    have ha : (tripleCharges (sourceA1674 + difference 2 1) (sourceB1674 + difference 1 2) sourceC1674) = raw24563 := by
      apply Matrix.ext; unfold tripleCharges sourceA1674 sourceB1674 sourceC1674 difference raw24563; decide +kernel
    rw [ha]
    exact (canonical24563 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1674 + difference 2 3) (sourceB1674 + difference 3 2) sourceC1674) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4624) := by
    have ha : (tripleCharges (sourceA1674 + difference 2 3) (sourceB1674 + difference 3 2) sourceC1674) = raw24564 := by
      apply Matrix.ext; unfold tripleCharges sourceA1674 sourceB1674 sourceC1674 difference raw24564; decide +kernel
    rw [ha]
    exact (canonical24564 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1674 + difference 2 4) (sourceB1674 + difference 4 2) sourceC1674) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4624) := by
    have ha : (tripleCharges (sourceA1674 + difference 2 4) (sourceB1674 + difference 4 2) sourceC1674) = raw24565 := by
      apply Matrix.ext; unfold tripleCharges sourceA1674 sourceB1674 sourceC1674 difference raw24565; decide +kernel
    rw [ha]
    exact (canonical24565 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1674 + difference 2 5) (sourceB1674 + difference 5 2) sourceC1674) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4622) := by
    have ha : (tripleCharges (sourceA1674 + difference 2 5) (sourceB1674 + difference 5 2) sourceC1674) = raw12541 := by
      apply Matrix.ext; unfold tripleCharges sourceA1674 sourceB1674 sourceC1674 difference raw12541; decide +kernel
    rw [ha]
    exact (canonical12541 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1674 + difference 3 0) (sourceB1674 + difference 0 3) sourceC1674) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4145) := by
    have ha : (tripleCharges (sourceA1674 + difference 3 0) (sourceB1674 + difference 0 3) sourceC1674) = raw24566 := by
      apply Matrix.ext; unfold tripleCharges sourceA1674 sourceB1674 sourceC1674 difference raw24566; decide +kernel
    rw [ha]
    exact (canonical24566 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1674 + difference 3 1) (sourceB1674 + difference 1 3) sourceC1674) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4524) := by
    have ha : (tripleCharges (sourceA1674 + difference 3 1) (sourceB1674 + difference 1 3) sourceC1674) = raw24567 := by
      apply Matrix.ext; unfold tripleCharges sourceA1674 sourceB1674 sourceC1674 difference raw24567; decide +kernel
    rw [ha]
    exact (canonical24567 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1674 + difference 3 2) (sourceB1674 + difference 2 3) sourceC1674) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4518) := by
    have ha : (tripleCharges (sourceA1674 + difference 3 2) (sourceB1674 + difference 2 3) sourceC1674) = raw24568 := by
      apply Matrix.ext; unfold tripleCharges sourceA1674 sourceB1674 sourceC1674 difference raw24568; decide +kernel
    rw [ha]
    exact (canonical24568 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1674 + difference 3 4) (sourceB1674 + difference 4 3) sourceC1674) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA1674 + difference 3 4) (sourceB1674 + difference 4 3) sourceC1674) = raw24569 := by
      apply Matrix.ext; unfold tripleCharges sourceA1674 sourceB1674 sourceC1674 difference raw24569; decide +kernel
    rw [ha]
    exact (canonical24569 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1674 + difference 3 5) (sourceB1674 + difference 5 3) sourceC1674) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1674 + difference 3 5) (sourceB1674 + difference 5 3) sourceC1674) = raw12546 := by
      apply Matrix.ext; unfold tripleCharges sourceA1674 sourceB1674 sourceC1674 difference raw12546; decide +kernel
    rw [ha]
    exact (canonical12546 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1674 + difference 4 0) (sourceB1674 + difference 0 4) sourceC1674) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4145) := by
    have ha : (tripleCharges (sourceA1674 + difference 4 0) (sourceB1674 + difference 0 4) sourceC1674) = raw24570 := by
      apply Matrix.ext; unfold tripleCharges sourceA1674 sourceB1674 sourceC1674 difference raw24570; decide +kernel
    rw [ha]
    exact (canonical24570 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1674 + difference 4 1) (sourceB1674 + difference 1 4) sourceC1674) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4524) := by
    have ha : (tripleCharges (sourceA1674 + difference 4 1) (sourceB1674 + difference 1 4) sourceC1674) = raw24571 := by
      apply Matrix.ext; unfold tripleCharges sourceA1674 sourceB1674 sourceC1674 difference raw24571; decide +kernel
    rw [ha]
    exact (canonical24571 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1674 + difference 4 2) (sourceB1674 + difference 2 4) sourceC1674) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4518) := by
    have ha : (tripleCharges (sourceA1674 + difference 4 2) (sourceB1674 + difference 2 4) sourceC1674) = raw24572 := by
      apply Matrix.ext; unfold tripleCharges sourceA1674 sourceB1674 sourceC1674 difference raw24572; decide +kernel
    rw [ha]
    exact (canonical24572 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1674 + difference 4 3) (sourceB1674 + difference 3 4) sourceC1674) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA1674 + difference 4 3) (sourceB1674 + difference 3 4) sourceC1674) = raw24573 := by
      apply Matrix.ext; unfold tripleCharges sourceA1674 sourceB1674 sourceC1674 difference raw24573; decide +kernel
    rw [ha]
    exact (canonical24573 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1674 + difference 4 5) (sourceB1674 + difference 5 4) sourceC1674) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1674 + difference 4 5) (sourceB1674 + difference 5 4) sourceC1674) = raw12551 := by
      apply Matrix.ext; unfold tripleCharges sourceA1674 sourceB1674 sourceC1674 difference raw12551; decide +kernel
    rw [ha]
    exact (canonical12551 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1674 + difference 5 0) (sourceB1674 + difference 0 5) sourceC1674) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4144) := by
    have ha : (tripleCharges (sourceA1674 + difference 5 0) (sourceB1674 + difference 0 5) sourceC1674) = raw24574 := by
      apply Matrix.ext; unfold tripleCharges sourceA1674 sourceB1674 sourceC1674 difference raw24574; decide +kernel
    rw [ha]
    exact (canonical24574 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1674 + difference 5 1) (sourceB1674 + difference 1 5) sourceC1674) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4523) := by
    have ha : (tripleCharges (sourceA1674 + difference 5 1) (sourceB1674 + difference 1 5) sourceC1674) = raw24575 := by
      apply Matrix.ext; unfold tripleCharges sourceA1674 sourceB1674 sourceC1674 difference raw24575; decide +kernel
    rw [ha]
    exact (canonical24575 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1674 + difference 5 2) (sourceB1674 + difference 2 5) sourceC1674) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4517) := by
    have ha : (tripleCharges (sourceA1674 + difference 5 2) (sourceB1674 + difference 2 5) sourceC1674) = raw24576 := by
      apply Matrix.ext; unfold tripleCharges sourceA1674 sourceB1674 sourceC1674 difference raw24576; decide +kernel
    rw [ha]
    exact (canonical24576 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1674 + difference 5 3) (sourceB1674 + difference 3 5) sourceC1674) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4608) := by
    have ha : (tripleCharges (sourceA1674 + difference 5 3) (sourceB1674 + difference 3 5) sourceC1674) = raw24577 := by
      apply Matrix.ext; unfold tripleCharges sourceA1674 sourceB1674 sourceC1674 difference raw24577; decide +kernel
    rw [ha]
    exact (canonical24577 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1674 + difference 5 4) (sourceB1674 + difference 4 5) sourceC1674) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4608) := by
    have ha : (tripleCharges (sourceA1674 + difference 5 4) (sourceB1674 + difference 4 5) sourceC1674) = raw24578 := by
      apply Matrix.ext; unfold tripleCharges sourceA1674 sourceB1674 sourceC1674 difference raw24578; decide +kernel
    rw [ha]
    exact (canonical24578 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1674 sourceB1674 sourceC1674
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1674, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1675 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1675 : Charge := ![2, 0, 1, -1, -1, -1]
def sourceC1675 : Charge := ![2, 0, -1, 0, 0, -1]
def sourceForm1675 : Integer.Sparse Master := [(Sum.inr 571, 1), (Sum.inr 572, 1), (Sum.inr 573, 2), (Sum.inr 603, 1), (Sum.inr 1100, 1), (Sum.inr 1101, 1), (Sum.inr 1102, 2), (Sum.inr 1107, 1), (Sum.inr 1108, 2), (Sum.inr 1129, 1), (Sum.inr 1235, 1), (Sum.inr 1236, 2), (Sum.inr 1240, 2), (Sum.inr 1242, 2), (Sum.inr 1246, 2), (Sum.inr 1299, 1), (Sum.inr 1301, 2), (Sum.inr 2884, 1), (Sum.inr 2927, 1), (Sum.inr 3100, 1), (Sum.inr 3102, 2)]

theorem sourceEq1675 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1675 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1675 + difference 0 1) (sourceB1675 + difference 1 0) sourceC1675) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2927) := by
    have ha : (tripleCharges (sourceA1675 + difference 0 1) (sourceB1675 + difference 1 0) sourceC1675) = raw12587 := by
      apply Matrix.ext; unfold tripleCharges sourceA1675 sourceB1675 sourceC1675 difference raw12587; decide +kernel
    rw [ha]
    exact (canonical12587 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1675 + difference 0 2) (sourceB1675 + difference 2 0) sourceC1675) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2884) := by
    have ha : (tripleCharges (sourceA1675 + difference 0 2) (sourceB1675 + difference 2 0) sourceC1675) = raw12588 := by
      apply Matrix.ext; unfold tripleCharges sourceA1675 sourceB1675 sourceC1675 difference raw12588; decide +kernel
    rw [ha]
    exact (canonical12588 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1675 + difference 0 3) (sourceB1675 + difference 3 0) sourceC1675) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3102) := by
    have ha : (tripleCharges (sourceA1675 + difference 0 3) (sourceB1675 + difference 3 0) sourceC1675) = raw12589 := by
      apply Matrix.ext; unfold tripleCharges sourceA1675 sourceB1675 sourceC1675 difference raw12589; decide +kernel
    rw [ha]
    exact (canonical12589 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1675 + difference 0 4) (sourceB1675 + difference 4 0) sourceC1675) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3102) := by
    have ha : (tripleCharges (sourceA1675 + difference 0 4) (sourceB1675 + difference 4 0) sourceC1675) = raw12590 := by
      apply Matrix.ext; unfold tripleCharges sourceA1675 sourceB1675 sourceC1675 difference raw12590; decide +kernel
    rw [ha]
    exact (canonical12590 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1675 + difference 0 5) (sourceB1675 + difference 5 0) sourceC1675) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3100) := by
    have ha : (tripleCharges (sourceA1675 + difference 0 5) (sourceB1675 + difference 5 0) sourceC1675) = raw24579 := by
      apply Matrix.ext; unfold tripleCharges sourceA1675 sourceB1675 sourceC1675 difference raw24579; decide +kernel
    rw [ha]
    exact (canonical24579 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1675 + difference 1 0) (sourceB1675 + difference 0 1) sourceC1675) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 571) := by
    have ha : (tripleCharges (sourceA1675 + difference 1 0) (sourceB1675 + difference 0 1) sourceC1675) = raw24580 := by
      apply Matrix.ext; unfold tripleCharges sourceA1675 sourceB1675 sourceC1675 difference raw24580; decide +kernel
    rw [ha]
    exact (canonical24580 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1675 + difference 1 2) (sourceB1675 + difference 2 1) sourceC1675) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1100) := by
    have ha : (tripleCharges (sourceA1675 + difference 1 2) (sourceB1675 + difference 2 1) sourceC1675) = raw24581 := by
      apply Matrix.ext; unfold tripleCharges sourceA1675 sourceB1675 sourceC1675 difference raw24581; decide +kernel
    rw [ha]
    exact (canonical24581 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1675 + difference 1 3) (sourceB1675 + difference 3 1) sourceC1675) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1240) := by
    have ha : (tripleCharges (sourceA1675 + difference 1 3) (sourceB1675 + difference 3 1) sourceC1675) = raw24582 := by
      apply Matrix.ext; unfold tripleCharges sourceA1675 sourceB1675 sourceC1675 difference raw24582; decide +kernel
    rw [ha]
    exact (canonical24582 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1675 + difference 1 4) (sourceB1675 + difference 4 1) sourceC1675) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1240) := by
    have ha : (tripleCharges (sourceA1675 + difference 1 4) (sourceB1675 + difference 4 1) sourceC1675) = raw24583 := by
      apply Matrix.ext; unfold tripleCharges sourceA1675 sourceB1675 sourceC1675 difference raw24583; decide +kernel
    rw [ha]
    exact (canonical24583 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1675 + difference 1 5) (sourceB1675 + difference 5 1) sourceC1675) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1235) := by
    have ha : (tripleCharges (sourceA1675 + difference 1 5) (sourceB1675 + difference 5 1) sourceC1675) = raw12566 := by
      apply Matrix.ext; unfold tripleCharges sourceA1675 sourceB1675 sourceC1675 difference raw12566; decide +kernel
    rw [ha]
    exact (canonical12566 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1675 + difference 2 0) (sourceB1675 + difference 0 2) sourceC1675) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 603) := by
    have ha : (tripleCharges (sourceA1675 + difference 2 0) (sourceB1675 + difference 0 2) sourceC1675) = raw24584 := by
      apply Matrix.ext; unfold tripleCharges sourceA1675 sourceB1675 sourceC1675 difference raw24584; decide +kernel
    rw [ha]
    exact (canonical24584 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1675 + difference 2 1) (sourceB1675 + difference 1 2) sourceC1675) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1129) := by
    have ha : (tripleCharges (sourceA1675 + difference 2 1) (sourceB1675 + difference 1 2) sourceC1675) = raw24585 := by
      apply Matrix.ext; unfold tripleCharges sourceA1675 sourceB1675 sourceC1675 difference raw24585; decide +kernel
    rw [ha]
    exact (canonical24585 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1675 + difference 2 3) (sourceB1675 + difference 3 2) sourceC1675) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1301) := by
    have ha : (tripleCharges (sourceA1675 + difference 2 3) (sourceB1675 + difference 3 2) sourceC1675) = raw24586 := by
      apply Matrix.ext; unfold tripleCharges sourceA1675 sourceB1675 sourceC1675 difference raw24586; decide +kernel
    rw [ha]
    exact (canonical24586 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1675 + difference 2 4) (sourceB1675 + difference 4 2) sourceC1675) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1301) := by
    have ha : (tripleCharges (sourceA1675 + difference 2 4) (sourceB1675 + difference 4 2) sourceC1675) = raw24587 := by
      apply Matrix.ext; unfold tripleCharges sourceA1675 sourceB1675 sourceC1675 difference raw24587; decide +kernel
    rw [ha]
    exact (canonical24587 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1675 + difference 2 5) (sourceB1675 + difference 5 2) sourceC1675) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1299) := by
    have ha : (tripleCharges (sourceA1675 + difference 2 5) (sourceB1675 + difference 5 2) sourceC1675) = raw12571 := by
      apply Matrix.ext; unfold tripleCharges sourceA1675 sourceB1675 sourceC1675 difference raw12571; decide +kernel
    rw [ha]
    exact (canonical12571 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1675 + difference 3 0) (sourceB1675 + difference 0 3) sourceC1675) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 573) := by
    have ha : (tripleCharges (sourceA1675 + difference 3 0) (sourceB1675 + difference 0 3) sourceC1675) = raw24588 := by
      apply Matrix.ext; unfold tripleCharges sourceA1675 sourceB1675 sourceC1675 difference raw24588; decide +kernel
    rw [ha]
    exact (canonical24588 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1675 + difference 3 1) (sourceB1675 + difference 1 3) sourceC1675) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1108) := by
    have ha : (tripleCharges (sourceA1675 + difference 3 1) (sourceB1675 + difference 1 3) sourceC1675) = raw24589 := by
      apply Matrix.ext; unfold tripleCharges sourceA1675 sourceB1675 sourceC1675 difference raw24589; decide +kernel
    rw [ha]
    exact (canonical24589 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1675 + difference 3 2) (sourceB1675 + difference 2 3) sourceC1675) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1102) := by
    have ha : (tripleCharges (sourceA1675 + difference 3 2) (sourceB1675 + difference 2 3) sourceC1675) = raw24590 := by
      apply Matrix.ext; unfold tripleCharges sourceA1675 sourceB1675 sourceC1675 difference raw24590; decide +kernel
    rw [ha]
    exact (canonical24590 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1675 + difference 3 4) (sourceB1675 + difference 4 3) sourceC1675) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1246) := by
    have ha : (tripleCharges (sourceA1675 + difference 3 4) (sourceB1675 + difference 4 3) sourceC1675) = raw24591 := by
      apply Matrix.ext; unfold tripleCharges sourceA1675 sourceB1675 sourceC1675 difference raw24591; decide +kernel
    rw [ha]
    exact (canonical24591 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1675 + difference 3 5) (sourceB1675 + difference 5 3) sourceC1675) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1236) := by
    have ha : (tripleCharges (sourceA1675 + difference 3 5) (sourceB1675 + difference 5 3) sourceC1675) = raw12576 := by
      apply Matrix.ext; unfold tripleCharges sourceA1675 sourceB1675 sourceC1675 difference raw12576; decide +kernel
    rw [ha]
    exact (canonical12576 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1675 + difference 4 0) (sourceB1675 + difference 0 4) sourceC1675) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 573) := by
    have ha : (tripleCharges (sourceA1675 + difference 4 0) (sourceB1675 + difference 0 4) sourceC1675) = raw24592 := by
      apply Matrix.ext; unfold tripleCharges sourceA1675 sourceB1675 sourceC1675 difference raw24592; decide +kernel
    rw [ha]
    exact (canonical24592 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1675 + difference 4 1) (sourceB1675 + difference 1 4) sourceC1675) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1108) := by
    have ha : (tripleCharges (sourceA1675 + difference 4 1) (sourceB1675 + difference 1 4) sourceC1675) = raw24593 := by
      apply Matrix.ext; unfold tripleCharges sourceA1675 sourceB1675 sourceC1675 difference raw24593; decide +kernel
    rw [ha]
    exact (canonical24593 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1675 + difference 4 2) (sourceB1675 + difference 2 4) sourceC1675) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1102) := by
    have ha : (tripleCharges (sourceA1675 + difference 4 2) (sourceB1675 + difference 2 4) sourceC1675) = raw24594 := by
      apply Matrix.ext; unfold tripleCharges sourceA1675 sourceB1675 sourceC1675 difference raw24594; decide +kernel
    rw [ha]
    exact (canonical24594 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1675 + difference 4 3) (sourceB1675 + difference 3 4) sourceC1675) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1246) := by
    have ha : (tripleCharges (sourceA1675 + difference 4 3) (sourceB1675 + difference 3 4) sourceC1675) = raw24595 := by
      apply Matrix.ext; unfold tripleCharges sourceA1675 sourceB1675 sourceC1675 difference raw24595; decide +kernel
    rw [ha]
    exact (canonical24595 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1675 + difference 4 5) (sourceB1675 + difference 5 4) sourceC1675) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1236) := by
    have ha : (tripleCharges (sourceA1675 + difference 4 5) (sourceB1675 + difference 5 4) sourceC1675) = raw12581 := by
      apply Matrix.ext; unfold tripleCharges sourceA1675 sourceB1675 sourceC1675 difference raw12581; decide +kernel
    rw [ha]
    exact (canonical12581 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1675 + difference 5 0) (sourceB1675 + difference 0 5) sourceC1675) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 572) := by
    have ha : (tripleCharges (sourceA1675 + difference 5 0) (sourceB1675 + difference 0 5) sourceC1675) = raw24596 := by
      apply Matrix.ext; unfold tripleCharges sourceA1675 sourceB1675 sourceC1675 difference raw24596; decide +kernel
    rw [ha]
    exact (canonical24596 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1675 + difference 5 1) (sourceB1675 + difference 1 5) sourceC1675) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1107) := by
    have ha : (tripleCharges (sourceA1675 + difference 5 1) (sourceB1675 + difference 1 5) sourceC1675) = raw24597 := by
      apply Matrix.ext; unfold tripleCharges sourceA1675 sourceB1675 sourceC1675 difference raw24597; decide +kernel
    rw [ha]
    exact (canonical24597 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1675 + difference 5 2) (sourceB1675 + difference 2 5) sourceC1675) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1101) := by
    have ha : (tripleCharges (sourceA1675 + difference 5 2) (sourceB1675 + difference 2 5) sourceC1675) = raw24598 := by
      apply Matrix.ext; unfold tripleCharges sourceA1675 sourceB1675 sourceC1675 difference raw24598; decide +kernel
    rw [ha]
    exact (canonical24598 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1675 + difference 5 3) (sourceB1675 + difference 3 5) sourceC1675) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1242) := by
    have ha : (tripleCharges (sourceA1675 + difference 5 3) (sourceB1675 + difference 3 5) sourceC1675) = raw24599 := by
      apply Matrix.ext; unfold tripleCharges sourceA1675 sourceB1675 sourceC1675 difference raw24599; decide +kernel
    rw [ha]
    exact (canonical24599 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1675 + difference 5 4) (sourceB1675 + difference 4 5) sourceC1675) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1242) := by
    have ha : (tripleCharges (sourceA1675 + difference 5 4) (sourceB1675 + difference 4 5) sourceC1675) = raw24600 := by
      apply Matrix.ext; unfold tripleCharges sourceA1675 sourceB1675 sourceC1675 difference raw24600; decide +kernel
    rw [ha]
    exact (canonical24600 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1675 sourceB1675 sourceC1675
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1675, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1676 : Charge := ![2, 0, -1, 0, 0, -1]
def sourceB1676 : Charge := ![2, 0, 1, -1, -1, -1]
def sourceC1676 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1676 : Integer.Sparse Master := [(Sum.inr 4399, 1), (Sum.inr 4423, 1), (Sum.inr 4424, 2), (Sum.inr 4438, 1), (Sum.inr 4457, 1), (Sum.inr 4458, 2), (Sum.inr 4474, 1), (Sum.inr 4502, 1), (Sum.inr 4563, 1), (Sum.inr 4570, 1), (Sum.inr 4571, 2), (Sum.inr 4581, 1), (Sum.inr 4582, 2), (Sum.inr 4589, 1), (Sum.inr 4590, 2), (Sum.inr 4602, 2), (Sum.inr 4603, 2), (Sum.inr 4606, 1), (Sum.inr 4607, 2), (Sum.inr 4623, 1), (Sum.inr 4624, 2)]

theorem sourceEq1676 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1676 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1676 + difference 0 1) (sourceB1676 + difference 1 0) sourceC1676) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4438) := by
    have ha : (tripleCharges (sourceA1676 + difference 0 1) (sourceB1676 + difference 1 0) sourceC1676) = raw24601 := by
      apply Matrix.ext; unfold tripleCharges sourceA1676 sourceB1676 sourceC1676 difference raw24601; decide +kernel
    rw [ha]
    exact (canonical24601 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1676 + difference 0 2) (sourceB1676 + difference 2 0) sourceC1676) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4474) := by
    have ha : (tripleCharges (sourceA1676 + difference 0 2) (sourceB1676 + difference 2 0) sourceC1676) = raw24602 := by
      apply Matrix.ext; unfold tripleCharges sourceA1676 sourceB1676 sourceC1676 difference raw24602; decide +kernel
    rw [ha]
    exact (canonical24602 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1676 + difference 0 3) (sourceB1676 + difference 3 0) sourceC1676) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1676 + difference 0 3) (sourceB1676 + difference 3 0) sourceC1676) = raw24249 := by
      apply Matrix.ext; unfold tripleCharges sourceA1676 sourceB1676 sourceC1676 difference raw24249; decide +kernel
    rw [ha]
    exact (canonical24249 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1676 + difference 0 4) (sourceB1676 + difference 4 0) sourceC1676) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1676 + difference 0 4) (sourceB1676 + difference 4 0) sourceC1676) = raw24603 := by
      apply Matrix.ext; unfold tripleCharges sourceA1676 sourceB1676 sourceC1676 difference raw24603; decide +kernel
    rw [ha]
    exact (canonical24603 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1676 + difference 0 5) (sourceB1676 + difference 5 0) sourceC1676) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4457) := by
    have ha : (tripleCharges (sourceA1676 + difference 0 5) (sourceB1676 + difference 5 0) sourceC1676) = raw24604 := by
      apply Matrix.ext; unfold tripleCharges sourceA1676 sourceB1676 sourceC1676 difference raw24604; decide +kernel
    rw [ha]
    exact (canonical24604 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1676 + difference 1 0) (sourceB1676 + difference 0 1) sourceC1676) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4399) := by
    have ha : (tripleCharges (sourceA1676 + difference 1 0) (sourceB1676 + difference 0 1) sourceC1676) = raw24605 := by
      apply Matrix.ext; unfold tripleCharges sourceA1676 sourceB1676 sourceC1676 difference raw24605; decide +kernel
    rw [ha]
    exact (canonical24605 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1676 + difference 1 2) (sourceB1676 + difference 2 1) sourceC1676) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4563) := by
    have ha : (tripleCharges (sourceA1676 + difference 1 2) (sourceB1676 + difference 2 1) sourceC1676) = raw24606 := by
      apply Matrix.ext; unfold tripleCharges sourceA1676 sourceB1676 sourceC1676 difference raw24606; decide +kernel
    rw [ha]
    exact (canonical24606 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1676 + difference 1 3) (sourceB1676 + difference 3 1) sourceC1676) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4590) := by
    have ha : (tripleCharges (sourceA1676 + difference 1 3) (sourceB1676 + difference 3 1) sourceC1676) = raw24253 := by
      apply Matrix.ext; unfold tripleCharges sourceA1676 sourceB1676 sourceC1676 difference raw24253; decide +kernel
    rw [ha]
    exact (canonical24253 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1676 + difference 1 4) (sourceB1676 + difference 4 1) sourceC1676) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4590) := by
    have ha : (tripleCharges (sourceA1676 + difference 1 4) (sourceB1676 + difference 4 1) sourceC1676) = raw24607 := by
      apply Matrix.ext; unfold tripleCharges sourceA1676 sourceB1676 sourceC1676 difference raw24607; decide +kernel
    rw [ha]
    exact (canonical24607 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1676 + difference 1 5) (sourceB1676 + difference 5 1) sourceC1676) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4589) := by
    have ha : (tripleCharges (sourceA1676 + difference 1 5) (sourceB1676 + difference 5 1) sourceC1676) = raw24608 := by
      apply Matrix.ext; unfold tripleCharges sourceA1676 sourceB1676 sourceC1676 difference raw24608; decide +kernel
    rw [ha]
    exact (canonical24608 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1676 + difference 2 0) (sourceB1676 + difference 0 2) sourceC1676) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4502) := by
    have ha : (tripleCharges (sourceA1676 + difference 2 0) (sourceB1676 + difference 0 2) sourceC1676) = raw24260 := by
      apply Matrix.ext; unfold tripleCharges sourceA1676 sourceB1676 sourceC1676 difference raw24260; decide +kernel
    rw [ha]
    exact (canonical24260 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1676 + difference 2 1) (sourceB1676 + difference 1 2) sourceC1676) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4606) := by
    have ha : (tripleCharges (sourceA1676 + difference 2 1) (sourceB1676 + difference 1 2) sourceC1676) = raw24261 := by
      apply Matrix.ext; unfold tripleCharges sourceA1676 sourceB1676 sourceC1676 difference raw24261; decide +kernel
    rw [ha]
    exact (canonical24261 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1676 + difference 2 3) (sourceB1676 + difference 3 2) sourceC1676) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4624) := by
    have ha : (tripleCharges (sourceA1676 + difference 2 3) (sourceB1676 + difference 3 2) sourceC1676) = raw24176 := by
      apply Matrix.ext; unfold tripleCharges sourceA1676 sourceB1676 sourceC1676 difference raw24176; decide +kernel
    rw [ha]
    exact (canonical24176 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1676 + difference 2 4) (sourceB1676 + difference 4 2) sourceC1676) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4624) := by
    have ha : (tripleCharges (sourceA1676 + difference 2 4) (sourceB1676 + difference 4 2) sourceC1676) = raw24171 := by
      apply Matrix.ext; unfold tripleCharges sourceA1676 sourceB1676 sourceC1676 difference raw24171; decide +kernel
    rw [ha]
    exact (canonical24171 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1676 + difference 2 5) (sourceB1676 + difference 5 2) sourceC1676) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4623) := by
    have ha : (tripleCharges (sourceA1676 + difference 2 5) (sourceB1676 + difference 5 2) sourceC1676) = raw24263 := by
      apply Matrix.ext; unfold tripleCharges sourceA1676 sourceB1676 sourceC1676 difference raw24263; decide +kernel
    rw [ha]
    exact (canonical24263 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1676 + difference 3 0) (sourceB1676 + difference 0 3) sourceC1676) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4424) := by
    have ha : (tripleCharges (sourceA1676 + difference 3 0) (sourceB1676 + difference 0 3) sourceC1676) = raw24609 := by
      apply Matrix.ext; unfold tripleCharges sourceA1676 sourceB1676 sourceC1676 difference raw24609; decide +kernel
    rw [ha]
    exact (canonical24609 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1676 + difference 3 1) (sourceB1676 + difference 1 3) sourceC1676) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4582) := by
    have ha : (tripleCharges (sourceA1676 + difference 3 1) (sourceB1676 + difference 1 3) sourceC1676) = raw24610 := by
      apply Matrix.ext; unfold tripleCharges sourceA1676 sourceB1676 sourceC1676 difference raw24610; decide +kernel
    rw [ha]
    exact (canonical24610 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1676 + difference 3 2) (sourceB1676 + difference 2 3) sourceC1676) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4571) := by
    have ha : (tripleCharges (sourceA1676 + difference 3 2) (sourceB1676 + difference 2 3) sourceC1676) = raw24611 := by
      apply Matrix.ext; unfold tripleCharges sourceA1676 sourceB1676 sourceC1676 difference raw24611; decide +kernel
    rw [ha]
    exact (canonical24611 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1676 + difference 3 4) (sourceB1676 + difference 4 3) sourceC1676) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4603) := by
    have ha : (tripleCharges (sourceA1676 + difference 3 4) (sourceB1676 + difference 4 3) sourceC1676) = raw24612 := by
      apply Matrix.ext; unfold tripleCharges sourceA1676 sourceB1676 sourceC1676 difference raw24612; decide +kernel
    rw [ha]
    exact (canonical24612 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1676 + difference 3 5) (sourceB1676 + difference 5 3) sourceC1676) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4607) := by
    have ha : (tripleCharges (sourceA1676 + difference 3 5) (sourceB1676 + difference 5 3) sourceC1676) = raw24613 := by
      apply Matrix.ext; unfold tripleCharges sourceA1676 sourceB1676 sourceC1676 difference raw24613; decide +kernel
    rw [ha]
    exact (canonical24613 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1676 + difference 4 0) (sourceB1676 + difference 0 4) sourceC1676) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4424) := by
    have ha : (tripleCharges (sourceA1676 + difference 4 0) (sourceB1676 + difference 0 4) sourceC1676) = raw24614 := by
      apply Matrix.ext; unfold tripleCharges sourceA1676 sourceB1676 sourceC1676 difference raw24614; decide +kernel
    rw [ha]
    exact (canonical24614 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1676 + difference 4 1) (sourceB1676 + difference 1 4) sourceC1676) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4582) := by
    have ha : (tripleCharges (sourceA1676 + difference 4 1) (sourceB1676 + difference 1 4) sourceC1676) = raw24615 := by
      apply Matrix.ext; unfold tripleCharges sourceA1676 sourceB1676 sourceC1676 difference raw24615; decide +kernel
    rw [ha]
    exact (canonical24615 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1676 + difference 4 2) (sourceB1676 + difference 2 4) sourceC1676) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4571) := by
    have ha : (tripleCharges (sourceA1676 + difference 4 2) (sourceB1676 + difference 2 4) sourceC1676) = raw24616 := by
      apply Matrix.ext; unfold tripleCharges sourceA1676 sourceB1676 sourceC1676 difference raw24616; decide +kernel
    rw [ha]
    exact (canonical24616 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1676 + difference 4 3) (sourceB1676 + difference 3 4) sourceC1676) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4603) := by
    have ha : (tripleCharges (sourceA1676 + difference 4 3) (sourceB1676 + difference 3 4) sourceC1676) = raw24266 := by
      apply Matrix.ext; unfold tripleCharges sourceA1676 sourceB1676 sourceC1676 difference raw24266; decide +kernel
    rw [ha]
    exact (canonical24266 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1676 + difference 4 5) (sourceB1676 + difference 5 4) sourceC1676) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4607) := by
    have ha : (tripleCharges (sourceA1676 + difference 4 5) (sourceB1676 + difference 5 4) sourceC1676) = raw24415 := by
      apply Matrix.ext; unfold tripleCharges sourceA1676 sourceB1676 sourceC1676 difference raw24415; decide +kernel
    rw [ha]
    exact (canonical24415 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1676 + difference 5 0) (sourceB1676 + difference 0 5) sourceC1676) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4423) := by
    have ha : (tripleCharges (sourceA1676 + difference 5 0) (sourceB1676 + difference 0 5) sourceC1676) = raw24617 := by
      apply Matrix.ext; unfold tripleCharges sourceA1676 sourceB1676 sourceC1676 difference raw24617; decide +kernel
    rw [ha]
    exact (canonical24617 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1676 + difference 5 1) (sourceB1676 + difference 1 5) sourceC1676) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4581) := by
    have ha : (tripleCharges (sourceA1676 + difference 5 1) (sourceB1676 + difference 1 5) sourceC1676) = raw24618 := by
      apply Matrix.ext; unfold tripleCharges sourceA1676 sourceB1676 sourceC1676 difference raw24618; decide +kernel
    rw [ha]
    exact (canonical24618 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1676 + difference 5 2) (sourceB1676 + difference 2 5) sourceC1676) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4570) := by
    have ha : (tripleCharges (sourceA1676 + difference 5 2) (sourceB1676 + difference 2 5) sourceC1676) = raw24619 := by
      apply Matrix.ext; unfold tripleCharges sourceA1676 sourceB1676 sourceC1676 difference raw24619; decide +kernel
    rw [ha]
    exact (canonical24619 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1676 + difference 5 3) (sourceB1676 + difference 3 5) sourceC1676) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1676 + difference 5 3) (sourceB1676 + difference 3 5) sourceC1676) = raw24174 := by
      apply Matrix.ext; unfold tripleCharges sourceA1676 sourceB1676 sourceC1676 difference raw24174; decide +kernel
    rw [ha]
    exact (canonical24174 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1676 + difference 5 4) (sourceB1676 + difference 4 5) sourceC1676) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1676 + difference 5 4) (sourceB1676 + difference 4 5) sourceC1676) = raw24169 := by
      apply Matrix.ext; unfold tripleCharges sourceA1676 sourceB1676 sourceC1676 difference raw24169; decide +kernel
    rw [ha]
    exact (canonical24169 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1676 sourceB1676 sourceC1676
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1676, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1677 : Charge := ![2, 0, -1, 0, 0, -1]
def sourceB1677 : Charge := ![2, 0, 1, -1, -1, -1]
def sourceC1677 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1677 : Integer.Sparse Master := [(Sum.inr 980, 1), (Sum.inr 1004, 1), (Sum.inr 1005, 2), (Sum.inr 1086, 1), (Sum.inr 1180, 1), (Sum.inr 1188, 1), (Sum.inr 1189, 2), (Sum.inr 1200, 1), (Sum.inr 1201, 2), (Sum.inr 1213, 2), (Sum.inr 1216, 1), (Sum.inr 1236, 2), (Sum.inr 1237, 2), (Sum.inr 1240, 1), (Sum.inr 1241, 2), (Sum.inr 1301, 2), (Sum.inr 1305, 1), (Sum.inr 1370, 1), (Sum.inr 1386, 1), (Sum.inr 1411, 2), (Sum.inr 1414, 1)]

theorem sourceEq1677 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1677 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1677 + difference 0 1) (sourceB1677 + difference 1 0) sourceC1677) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1386) := by
    have ha : (tripleCharges (sourceA1677 + difference 0 1) (sourceB1677 + difference 1 0) sourceC1677) = raw24620 := by
      apply Matrix.ext; unfold tripleCharges sourceA1677 sourceB1677 sourceC1677 difference raw24620; decide +kernel
    rw [ha]
    exact (canonical24620 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1677 + difference 0 2) (sourceB1677 + difference 2 0) sourceC1677) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1370) := by
    have ha : (tripleCharges (sourceA1677 + difference 0 2) (sourceB1677 + difference 2 0) sourceC1677) = raw24621 := by
      apply Matrix.ext; unfold tripleCharges sourceA1677 sourceB1677 sourceC1677 difference raw24621; decide +kernel
    rw [ha]
    exact (canonical24621 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1677 + difference 0 3) (sourceB1677 + difference 3 0) sourceC1677) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1411) := by
    have ha : (tripleCharges (sourceA1677 + difference 0 3) (sourceB1677 + difference 3 0) sourceC1677) = raw24622 := by
      apply Matrix.ext; unfold tripleCharges sourceA1677 sourceB1677 sourceC1677 difference raw24622; decide +kernel
    rw [ha]
    exact (canonical24622 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1677 + difference 0 4) (sourceB1677 + difference 4 0) sourceC1677) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1411) := by
    have ha : (tripleCharges (sourceA1677 + difference 0 4) (sourceB1677 + difference 4 0) sourceC1677) = raw24623 := by
      apply Matrix.ext; unfold tripleCharges sourceA1677 sourceB1677 sourceC1677 difference raw24623; decide +kernel
    rw [ha]
    exact (canonical24623 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1677 + difference 0 5) (sourceB1677 + difference 5 0) sourceC1677) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1414) := by
    have ha : (tripleCharges (sourceA1677 + difference 0 5) (sourceB1677 + difference 5 0) sourceC1677) = raw24624 := by
      apply Matrix.ext; unfold tripleCharges sourceA1677 sourceB1677 sourceC1677 difference raw24624; decide +kernel
    rw [ha]
    exact (canonical24624 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1677 + difference 1 0) (sourceB1677 + difference 0 1) sourceC1677) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 980) := by
    have ha : (tripleCharges (sourceA1677 + difference 1 0) (sourceB1677 + difference 0 1) sourceC1677) = raw24625 := by
      apply Matrix.ext; unfold tripleCharges sourceA1677 sourceB1677 sourceC1677 difference raw24625; decide +kernel
    rw [ha]
    exact (canonical24625 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1677 + difference 1 2) (sourceB1677 + difference 2 1) sourceC1677) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1180) := by
    have ha : (tripleCharges (sourceA1677 + difference 1 2) (sourceB1677 + difference 2 1) sourceC1677) = raw24626 := by
      apply Matrix.ext; unfold tripleCharges sourceA1677 sourceB1677 sourceC1677 difference raw24626; decide +kernel
    rw [ha]
    exact (canonical24626 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1677 + difference 1 3) (sourceB1677 + difference 3 1) sourceC1677) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1213) := by
    have ha : (tripleCharges (sourceA1677 + difference 1 3) (sourceB1677 + difference 3 1) sourceC1677) = raw24627 := by
      apply Matrix.ext; unfold tripleCharges sourceA1677 sourceB1677 sourceC1677 difference raw24627; decide +kernel
    rw [ha]
    exact (canonical24627 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1677 + difference 1 4) (sourceB1677 + difference 4 1) sourceC1677) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1213) := by
    have ha : (tripleCharges (sourceA1677 + difference 1 4) (sourceB1677 + difference 4 1) sourceC1677) = raw24628 := by
      apply Matrix.ext; unfold tripleCharges sourceA1677 sourceB1677 sourceC1677 difference raw24628; decide +kernel
    rw [ha]
    exact (canonical24628 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1677 + difference 1 5) (sourceB1677 + difference 5 1) sourceC1677) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1216) := by
    have ha : (tripleCharges (sourceA1677 + difference 1 5) (sourceB1677 + difference 5 1) sourceC1677) = raw24629 := by
      apply Matrix.ext; unfold tripleCharges sourceA1677 sourceB1677 sourceC1677 difference raw24629; decide +kernel
    rw [ha]
    exact (canonical24629 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1677 + difference 2 0) (sourceB1677 + difference 0 2) sourceC1677) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1086) := by
    have ha : (tripleCharges (sourceA1677 + difference 2 0) (sourceB1677 + difference 0 2) sourceC1677) = raw24630 := by
      apply Matrix.ext; unfold tripleCharges sourceA1677 sourceB1677 sourceC1677 difference raw24630; decide +kernel
    rw [ha]
    exact (canonical24630 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1677 + difference 2 1) (sourceB1677 + difference 1 2) sourceC1677) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1240) := by
    have ha : (tripleCharges (sourceA1677 + difference 2 1) (sourceB1677 + difference 1 2) sourceC1677) = raw24631 := by
      apply Matrix.ext; unfold tripleCharges sourceA1677 sourceB1677 sourceC1677 difference raw24631; decide +kernel
    rw [ha]
    exact (canonical24631 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1677 + difference 2 3) (sourceB1677 + difference 3 2) sourceC1677) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1301) := by
    have ha : (tripleCharges (sourceA1677 + difference 2 3) (sourceB1677 + difference 3 2) sourceC1677) = raw24632 := by
      apply Matrix.ext; unfold tripleCharges sourceA1677 sourceB1677 sourceC1677 difference raw24632; decide +kernel
    rw [ha]
    exact (canonical24632 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1677 + difference 2 4) (sourceB1677 + difference 4 2) sourceC1677) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1301) := by
    have ha : (tripleCharges (sourceA1677 + difference 2 4) (sourceB1677 + difference 4 2) sourceC1677) = raw24633 := by
      apply Matrix.ext; unfold tripleCharges sourceA1677 sourceB1677 sourceC1677 difference raw24633; decide +kernel
    rw [ha]
    exact (canonical24633 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1677 + difference 2 5) (sourceB1677 + difference 5 2) sourceC1677) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1305) := by
    have ha : (tripleCharges (sourceA1677 + difference 2 5) (sourceB1677 + difference 5 2) sourceC1677) = raw24634 := by
      apply Matrix.ext; unfold tripleCharges sourceA1677 sourceB1677 sourceC1677 difference raw24634; decide +kernel
    rw [ha]
    exact (canonical24634 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1677 + difference 3 0) (sourceB1677 + difference 0 3) sourceC1677) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1005) := by
    have ha : (tripleCharges (sourceA1677 + difference 3 0) (sourceB1677 + difference 0 3) sourceC1677) = raw24635 := by
      apply Matrix.ext; unfold tripleCharges sourceA1677 sourceB1677 sourceC1677 difference raw24635; decide +kernel
    rw [ha]
    exact (canonical24635 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1677 + difference 3 1) (sourceB1677 + difference 1 3) sourceC1677) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1201) := by
    have ha : (tripleCharges (sourceA1677 + difference 3 1) (sourceB1677 + difference 1 3) sourceC1677) = raw24636 := by
      apply Matrix.ext; unfold tripleCharges sourceA1677 sourceB1677 sourceC1677 difference raw24636; decide +kernel
    rw [ha]
    exact (canonical24636 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1677 + difference 3 2) (sourceB1677 + difference 2 3) sourceC1677) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1189) := by
    have ha : (tripleCharges (sourceA1677 + difference 3 2) (sourceB1677 + difference 2 3) sourceC1677) = raw24637 := by
      apply Matrix.ext; unfold tripleCharges sourceA1677 sourceB1677 sourceC1677 difference raw24637; decide +kernel
    rw [ha]
    exact (canonical24637 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1677 + difference 3 4) (sourceB1677 + difference 4 3) sourceC1677) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1237) := by
    have ha : (tripleCharges (sourceA1677 + difference 3 4) (sourceB1677 + difference 4 3) sourceC1677) = raw24638 := by
      apply Matrix.ext; unfold tripleCharges sourceA1677 sourceB1677 sourceC1677 difference raw24638; decide +kernel
    rw [ha]
    exact (canonical24638 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1677 + difference 3 5) (sourceB1677 + difference 5 3) sourceC1677) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1241) := by
    have ha : (tripleCharges (sourceA1677 + difference 3 5) (sourceB1677 + difference 5 3) sourceC1677) = raw24639 := by
      apply Matrix.ext; unfold tripleCharges sourceA1677 sourceB1677 sourceC1677 difference raw24639; decide +kernel
    rw [ha]
    exact (canonical24639 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1677 + difference 4 0) (sourceB1677 + difference 0 4) sourceC1677) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1005) := by
    have ha : (tripleCharges (sourceA1677 + difference 4 0) (sourceB1677 + difference 0 4) sourceC1677) = raw24640 := by
      apply Matrix.ext; unfold tripleCharges sourceA1677 sourceB1677 sourceC1677 difference raw24640; decide +kernel
    rw [ha]
    exact (canonical24640 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1677 + difference 4 1) (sourceB1677 + difference 1 4) sourceC1677) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1201) := by
    have ha : (tripleCharges (sourceA1677 + difference 4 1) (sourceB1677 + difference 1 4) sourceC1677) = raw24641 := by
      apply Matrix.ext; unfold tripleCharges sourceA1677 sourceB1677 sourceC1677 difference raw24641; decide +kernel
    rw [ha]
    exact (canonical24641 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1677 + difference 4 2) (sourceB1677 + difference 2 4) sourceC1677) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1189) := by
    have ha : (tripleCharges (sourceA1677 + difference 4 2) (sourceB1677 + difference 2 4) sourceC1677) = raw24642 := by
      apply Matrix.ext; unfold tripleCharges sourceA1677 sourceB1677 sourceC1677 difference raw24642; decide +kernel
    rw [ha]
    exact (canonical24642 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1677 + difference 4 3) (sourceB1677 + difference 3 4) sourceC1677) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1237) := by
    have ha : (tripleCharges (sourceA1677 + difference 4 3) (sourceB1677 + difference 3 4) sourceC1677) = raw24643 := by
      apply Matrix.ext; unfold tripleCharges sourceA1677 sourceB1677 sourceC1677 difference raw24643; decide +kernel
    rw [ha]
    exact (canonical24643 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1677 + difference 4 5) (sourceB1677 + difference 5 4) sourceC1677) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1241) := by
    have ha : (tripleCharges (sourceA1677 + difference 4 5) (sourceB1677 + difference 5 4) sourceC1677) = raw24644 := by
      apply Matrix.ext; unfold tripleCharges sourceA1677 sourceB1677 sourceC1677 difference raw24644; decide +kernel
    rw [ha]
    exact (canonical24644 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1677 + difference 5 0) (sourceB1677 + difference 0 5) sourceC1677) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1004) := by
    have ha : (tripleCharges (sourceA1677 + difference 5 0) (sourceB1677 + difference 0 5) sourceC1677) = raw24645 := by
      apply Matrix.ext; unfold tripleCharges sourceA1677 sourceB1677 sourceC1677 difference raw24645; decide +kernel
    rw [ha]
    exact (canonical24645 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1677 + difference 5 1) (sourceB1677 + difference 1 5) sourceC1677) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1200) := by
    have ha : (tripleCharges (sourceA1677 + difference 5 1) (sourceB1677 + difference 1 5) sourceC1677) = raw24646 := by
      apply Matrix.ext; unfold tripleCharges sourceA1677 sourceB1677 sourceC1677 difference raw24646; decide +kernel
    rw [ha]
    exact (canonical24646 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1677 + difference 5 2) (sourceB1677 + difference 2 5) sourceC1677) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1188) := by
    have ha : (tripleCharges (sourceA1677 + difference 5 2) (sourceB1677 + difference 2 5) sourceC1677) = raw24647 := by
      apply Matrix.ext; unfold tripleCharges sourceA1677 sourceB1677 sourceC1677 difference raw24647; decide +kernel
    rw [ha]
    exact (canonical24647 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1677 + difference 5 3) (sourceB1677 + difference 3 5) sourceC1677) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1236) := by
    have ha : (tripleCharges (sourceA1677 + difference 5 3) (sourceB1677 + difference 3 5) sourceC1677) = raw24648 := by
      apply Matrix.ext; unfold tripleCharges sourceA1677 sourceB1677 sourceC1677 difference raw24648; decide +kernel
    rw [ha]
    exact (canonical24648 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1677 + difference 5 4) (sourceB1677 + difference 4 5) sourceC1677) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1236) := by
    have ha : (tripleCharges (sourceA1677 + difference 5 4) (sourceB1677 + difference 4 5) sourceC1677) = raw24649 := by
      apply Matrix.ext; unfold tripleCharges sourceA1677 sourceB1677 sourceC1677 difference raw24649; decide +kernel
    rw [ha]
    exact (canonical24649 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1677 sourceB1677 sourceC1677
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1677, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1678 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1678 : Charge := ![2, 0, -1, 0, -1, 0]
def sourceC1678 : Charge := ![2, 0, 1, -1, 0, -2]
def sourceForm1678 : Integer.Sparse Master := [(Sum.inr 4152, 1), (Sum.inr 4153, 1), (Sum.inr 4154, 1), (Sum.inr 4158, 1), (Sum.inr 4176, 1), (Sum.inr 4528, 1), (Sum.inr 4529, 1), (Sum.inr 4533, 1), (Sum.inr 4541, 1), (Sum.inr 4545, 1), (Sum.inr 4546, 1), (Sum.inr 4549, 1), (Sum.inr 4553, 1), (Sum.inr 4589, 1), (Sum.inr 4591, 1), (Sum.inr 4592, 1), (Sum.inr 4599, 1), (Sum.inr 4602, 1), (Sum.inr 4603, 1), (Sum.inr 4607, 2), (Sum.inr 4608, 1), (Sum.inr 4612, 1), (Sum.inr 4616, 1), (Sum.inr 4619, 1), (Sum.inr 5101, 1), (Sum.inr 5134, 1), (Sum.inr 5258, 1), (Sum.inr 5271, 1), (Sum.inr 5274, 1)]

theorem sourceEq1678 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1678 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1678 + difference 0 1) (sourceB1678 + difference 1 0) sourceC1678) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5134) := by
    have ha : (tripleCharges (sourceA1678 + difference 0 1) (sourceB1678 + difference 1 0) sourceC1678) = raw24650 := by
      apply Matrix.ext; unfold tripleCharges sourceA1678 sourceB1678 sourceC1678 difference raw24650; decide +kernel
    rw [ha]
    exact (canonical24650 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1678 + difference 0 2) (sourceB1678 + difference 2 0) sourceC1678) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5101) := by
    have ha : (tripleCharges (sourceA1678 + difference 0 2) (sourceB1678 + difference 2 0) sourceC1678) = raw24651 := by
      apply Matrix.ext; unfold tripleCharges sourceA1678 sourceB1678 sourceC1678 difference raw24651; decide +kernel
    rw [ha]
    exact (canonical24651 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1678 + difference 0 3) (sourceB1678 + difference 3 0) sourceC1678) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA1678 + difference 0 3) (sourceB1678 + difference 3 0) sourceC1678) = raw24652 := by
      apply Matrix.ext; unfold tripleCharges sourceA1678 sourceB1678 sourceC1678 difference raw24652; decide +kernel
    rw [ha]
    exact (canonical24652 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1678 + difference 0 4) (sourceB1678 + difference 4 0) sourceC1678) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5274) := by
    have ha : (tripleCharges (sourceA1678 + difference 0 4) (sourceB1678 + difference 4 0) sourceC1678) = raw24653 := by
      apply Matrix.ext; unfold tripleCharges sourceA1678 sourceB1678 sourceC1678 difference raw24653; decide +kernel
    rw [ha]
    exact (canonical24653 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1678 + difference 0 5) (sourceB1678 + difference 5 0) sourceC1678) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA1678 + difference 0 5) (sourceB1678 + difference 5 0) sourceC1678) = raw24654 := by
      apply Matrix.ext; unfold tripleCharges sourceA1678 sourceB1678 sourceC1678 difference raw24654; decide +kernel
    rw [ha]
    exact (canonical24654 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1678 + difference 1 0) (sourceB1678 + difference 0 1) sourceC1678) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4152) := by
    have ha : (tripleCharges (sourceA1678 + difference 1 0) (sourceB1678 + difference 0 1) sourceC1678) = raw24655 := by
      apply Matrix.ext; unfold tripleCharges sourceA1678 sourceB1678 sourceC1678 difference raw24655; decide +kernel
    rw [ha]
    exact (canonical24655 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1678 + difference 1 2) (sourceB1678 + difference 2 1) sourceC1678) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4541) := by
    have ha : (tripleCharges (sourceA1678 + difference 1 2) (sourceB1678 + difference 2 1) sourceC1678) = raw24656 := by
      apply Matrix.ext; unfold tripleCharges sourceA1678 sourceB1678 sourceC1678 difference raw24656; decide +kernel
    rw [ha]
    exact (canonical24656 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1678 + difference 1 3) (sourceB1678 + difference 3 1) sourceC1678) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4589) := by
    have ha : (tripleCharges (sourceA1678 + difference 1 3) (sourceB1678 + difference 3 1) sourceC1678) = raw24657 := by
      apply Matrix.ext; unfold tripleCharges sourceA1678 sourceB1678 sourceC1678 difference raw24657; decide +kernel
    rw [ha]
    exact (canonical24657 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1678 + difference 1 4) (sourceB1678 + difference 4 1) sourceC1678) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1678 + difference 1 4) (sourceB1678 + difference 4 1) sourceC1678) = raw24658 := by
      apply Matrix.ext; unfold tripleCharges sourceA1678 sourceB1678 sourceC1678 difference raw24658; decide +kernel
    rw [ha]
    exact (canonical24658 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1678 + difference 1 5) (sourceB1678 + difference 5 1) sourceC1678) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4599) := by
    have ha : (tripleCharges (sourceA1678 + difference 1 5) (sourceB1678 + difference 5 1) sourceC1678) = raw24659 := by
      apply Matrix.ext; unfold tripleCharges sourceA1678 sourceB1678 sourceC1678 difference raw24659; decide +kernel
    rw [ha]
    exact (canonical24659 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1678 + difference 2 0) (sourceB1678 + difference 0 2) sourceC1678) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4176) := by
    have ha : (tripleCharges (sourceA1678 + difference 2 0) (sourceB1678 + difference 0 2) sourceC1678) = raw24660 := by
      apply Matrix.ext; unfold tripleCharges sourceA1678 sourceB1678 sourceC1678 difference raw24660; decide +kernel
    rw [ha]
    exact (canonical24660 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1678 + difference 2 1) (sourceB1678 + difference 1 2) sourceC1678) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4545) := by
    have ha : (tripleCharges (sourceA1678 + difference 2 1) (sourceB1678 + difference 1 2) sourceC1678) = raw24661 := by
      apply Matrix.ext; unfold tripleCharges sourceA1678 sourceB1678 sourceC1678 difference raw24661; decide +kernel
    rw [ha]
    exact (canonical24661 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1678 + difference 2 3) (sourceB1678 + difference 3 2) sourceC1678) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4607) := by
    have ha : (tripleCharges (sourceA1678 + difference 2 3) (sourceB1678 + difference 3 2) sourceC1678) = raw24662 := by
      apply Matrix.ext; unfold tripleCharges sourceA1678 sourceB1678 sourceC1678 difference raw24662; decide +kernel
    rw [ha]
    exact (canonical24662 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1678 + difference 2 4) (sourceB1678 + difference 4 2) sourceC1678) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4619) := by
    have ha : (tripleCharges (sourceA1678 + difference 2 4) (sourceB1678 + difference 4 2) sourceC1678) = raw24663 := by
      apply Matrix.ext; unfold tripleCharges sourceA1678 sourceB1678 sourceC1678 difference raw24663; decide +kernel
    rw [ha]
    exact (canonical24663 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1678 + difference 2 5) (sourceB1678 + difference 5 2) sourceC1678) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4616) := by
    have ha : (tripleCharges (sourceA1678 + difference 2 5) (sourceB1678 + difference 5 2) sourceC1678) = raw24664 := by
      apply Matrix.ext; unfold tripleCharges sourceA1678 sourceB1678 sourceC1678 difference raw24664; decide +kernel
    rw [ha]
    exact (canonical24664 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1678 + difference 3 0) (sourceB1678 + difference 0 3) sourceC1678) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4158) := by
    have ha : (tripleCharges (sourceA1678 + difference 3 0) (sourceB1678 + difference 0 3) sourceC1678) = raw24665 := by
      apply Matrix.ext; unfold tripleCharges sourceA1678 sourceB1678 sourceC1678 difference raw24665; decide +kernel
    rw [ha]
    exact (canonical24665 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1678 + difference 3 1) (sourceB1678 + difference 1 3) sourceC1678) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4533) := by
    have ha : (tripleCharges (sourceA1678 + difference 3 1) (sourceB1678 + difference 1 3) sourceC1678) = raw24666 := by
      apply Matrix.ext; unfold tripleCharges sourceA1678 sourceB1678 sourceC1678 difference raw24666; decide +kernel
    rw [ha]
    exact (canonical24666 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1678 + difference 3 2) (sourceB1678 + difference 2 3) sourceC1678) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4549) := by
    have ha : (tripleCharges (sourceA1678 + difference 3 2) (sourceB1678 + difference 2 3) sourceC1678) = raw24667 := by
      apply Matrix.ext; unfold tripleCharges sourceA1678 sourceB1678 sourceC1678 difference raw24667; decide +kernel
    rw [ha]
    exact (canonical24667 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1678 + difference 3 4) (sourceB1678 + difference 4 3) sourceC1678) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA1678 + difference 3 4) (sourceB1678 + difference 4 3) sourceC1678) = raw24668 := by
      apply Matrix.ext; unfold tripleCharges sourceA1678 sourceB1678 sourceC1678 difference raw24668; decide +kernel
    rw [ha]
    exact (canonical24668 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1678 + difference 3 5) (sourceB1678 + difference 5 3) sourceC1678) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4603) := by
    have ha : (tripleCharges (sourceA1678 + difference 3 5) (sourceB1678 + difference 5 3) sourceC1678) = raw24669 := by
      apply Matrix.ext; unfold tripleCharges sourceA1678 sourceB1678 sourceC1678 difference raw24669; decide +kernel
    rw [ha]
    exact (canonical24669 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1678 + difference 4 0) (sourceB1678 + difference 0 4) sourceC1678) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4154) := by
    have ha : (tripleCharges (sourceA1678 + difference 4 0) (sourceB1678 + difference 0 4) sourceC1678) = raw24670 := by
      apply Matrix.ext; unfold tripleCharges sourceA1678 sourceB1678 sourceC1678 difference raw24670; decide +kernel
    rw [ha]
    exact (canonical24670 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1678 + difference 4 1) (sourceB1678 + difference 1 4) sourceC1678) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4529) := by
    have ha : (tripleCharges (sourceA1678 + difference 4 1) (sourceB1678 + difference 1 4) sourceC1678) = raw24671 := by
      apply Matrix.ext; unfold tripleCharges sourceA1678 sourceB1678 sourceC1678 difference raw24671; decide +kernel
    rw [ha]
    exact (canonical24671 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1678 + difference 4 2) (sourceB1678 + difference 2 4) sourceC1678) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4553) := by
    have ha : (tripleCharges (sourceA1678 + difference 4 2) (sourceB1678 + difference 2 4) sourceC1678) = raw24672 := by
      apply Matrix.ext; unfold tripleCharges sourceA1678 sourceB1678 sourceC1678 difference raw24672; decide +kernel
    rw [ha]
    exact (canonical24672 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1678 + difference 4 3) (sourceB1678 + difference 3 4) sourceC1678) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4592) := by
    have ha : (tripleCharges (sourceA1678 + difference 4 3) (sourceB1678 + difference 3 4) sourceC1678) = raw24673 := by
      apply Matrix.ext; unfold tripleCharges sourceA1678 sourceB1678 sourceC1678 difference raw24673; decide +kernel
    rw [ha]
    exact (canonical24673 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1678 + difference 4 5) (sourceB1678 + difference 5 4) sourceC1678) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4607) := by
    have ha : (tripleCharges (sourceA1678 + difference 4 5) (sourceB1678 + difference 5 4) sourceC1678) = raw24674 := by
      apply Matrix.ext; unfold tripleCharges sourceA1678 sourceB1678 sourceC1678 difference raw24674; decide +kernel
    rw [ha]
    exact (canonical24674 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1678 + difference 5 0) (sourceB1678 + difference 0 5) sourceC1678) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4153) := by
    have ha : (tripleCharges (sourceA1678 + difference 5 0) (sourceB1678 + difference 0 5) sourceC1678) = raw24675 := by
      apply Matrix.ext; unfold tripleCharges sourceA1678 sourceB1678 sourceC1678 difference raw24675; decide +kernel
    rw [ha]
    exact (canonical24675 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1678 + difference 5 1) (sourceB1678 + difference 1 5) sourceC1678) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4528) := by
    have ha : (tripleCharges (sourceA1678 + difference 5 1) (sourceB1678 + difference 1 5) sourceC1678) = raw24676 := by
      apply Matrix.ext; unfold tripleCharges sourceA1678 sourceB1678 sourceC1678 difference raw24676; decide +kernel
    rw [ha]
    exact (canonical24676 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1678 + difference 5 2) (sourceB1678 + difference 2 5) sourceC1678) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4546) := by
    have ha : (tripleCharges (sourceA1678 + difference 5 2) (sourceB1678 + difference 2 5) sourceC1678) = raw24677 := by
      apply Matrix.ext; unfold tripleCharges sourceA1678 sourceB1678 sourceC1678 difference raw24677; decide +kernel
    rw [ha]
    exact (canonical24677 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1678 + difference 5 3) (sourceB1678 + difference 3 5) sourceC1678) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4591) := by
    have ha : (tripleCharges (sourceA1678 + difference 5 3) (sourceB1678 + difference 3 5) sourceC1678) = raw24678 := by
      apply Matrix.ext; unfold tripleCharges sourceA1678 sourceB1678 sourceC1678 difference raw24678; decide +kernel
    rw [ha]
    exact (canonical24678 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1678 + difference 5 4) (sourceB1678 + difference 4 5) sourceC1678) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4608) := by
    have ha : (tripleCharges (sourceA1678 + difference 5 4) (sourceB1678 + difference 4 5) sourceC1678) = raw24679 := by
      apply Matrix.ext; unfold tripleCharges sourceA1678 sourceB1678 sourceC1678 difference raw24679; decide +kernel
    rw [ha]
    exact (canonical24679 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1678 sourceB1678 sourceC1678
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1678, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1679 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1679 : Charge := ![2, 0, -1, 0, -1, 0]
def sourceC1679 : Charge := ![2, 0, 1, -1, 0, -2]
def sourceForm1679 : Integer.Sparse Master := [(Sum.inr 580, 1), (Sum.inr 581, 1), (Sum.inr 582, 1), (Sum.inr 586, 1), (Sum.inr 604, 1), (Sum.inr 1112, 1), (Sum.inr 1113, 1), (Sum.inr 1117, 1), (Sum.inr 1130, 1), (Sum.inr 1164, 1), (Sum.inr 1165, 1), (Sum.inr 1166, 1), (Sum.inr 1172, 1), (Sum.inr 1216, 1), (Sum.inr 1217, 1), (Sum.inr 1219, 1), (Sum.inr 1241, 1), (Sum.inr 1260, 1), (Sum.inr 1261, 1), (Sum.inr 1262, 1), (Sum.inr 1267, 1), (Sum.inr 1269, 1), (Sum.inr 1274, 1), (Sum.inr 1291, 1), (Sum.inr 1302, 1), (Sum.inr 2937, 1), (Sum.inr 3001, 1), (Sum.inr 3089, 1), (Sum.inr 3109, 1), (Sum.inr 3112, 1)]

theorem sourceEq1679 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1679 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1679 + difference 0 1) (sourceB1679 + difference 1 0) sourceC1679) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2937) := by
    have ha : (tripleCharges (sourceA1679 + difference 0 1) (sourceB1679 + difference 1 0) sourceC1679) = raw24680 := by
      apply Matrix.ext; unfold tripleCharges sourceA1679 sourceB1679 sourceC1679 difference raw24680; decide +kernel
    rw [ha]
    exact (canonical24680 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1679 + difference 0 2) (sourceB1679 + difference 2 0) sourceC1679) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3001) := by
    have ha : (tripleCharges (sourceA1679 + difference 0 2) (sourceB1679 + difference 2 0) sourceC1679) = raw24681 := by
      apply Matrix.ext; unfold tripleCharges sourceA1679 sourceB1679 sourceC1679 difference raw24681; decide +kernel
    rw [ha]
    exact (canonical24681 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1679 + difference 0 3) (sourceB1679 + difference 3 0) sourceC1679) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3089) := by
    have ha : (tripleCharges (sourceA1679 + difference 0 3) (sourceB1679 + difference 3 0) sourceC1679) = raw24682 := by
      apply Matrix.ext; unfold tripleCharges sourceA1679 sourceB1679 sourceC1679 difference raw24682; decide +kernel
    rw [ha]
    exact (canonical24682 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1679 + difference 0 4) (sourceB1679 + difference 4 0) sourceC1679) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3112) := by
    have ha : (tripleCharges (sourceA1679 + difference 0 4) (sourceB1679 + difference 4 0) sourceC1679) = raw24683 := by
      apply Matrix.ext; unfold tripleCharges sourceA1679 sourceB1679 sourceC1679 difference raw24683; decide +kernel
    rw [ha]
    exact (canonical24683 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1679 + difference 0 5) (sourceB1679 + difference 5 0) sourceC1679) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3109) := by
    have ha : (tripleCharges (sourceA1679 + difference 0 5) (sourceB1679 + difference 5 0) sourceC1679) = raw24684 := by
      apply Matrix.ext; unfold tripleCharges sourceA1679 sourceB1679 sourceC1679 difference raw24684; decide +kernel
    rw [ha]
    exact (canonical24684 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1679 + difference 1 0) (sourceB1679 + difference 0 1) sourceC1679) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 580) := by
    have ha : (tripleCharges (sourceA1679 + difference 1 0) (sourceB1679 + difference 0 1) sourceC1679) = raw24685 := by
      apply Matrix.ext; unfold tripleCharges sourceA1679 sourceB1679 sourceC1679 difference raw24685; decide +kernel
    rw [ha]
    exact (canonical24685 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1679 + difference 1 2) (sourceB1679 + difference 2 1) sourceC1679) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1164) := by
    have ha : (tripleCharges (sourceA1679 + difference 1 2) (sourceB1679 + difference 2 1) sourceC1679) = raw24686 := by
      apply Matrix.ext; unfold tripleCharges sourceA1679 sourceB1679 sourceC1679 difference raw24686; decide +kernel
    rw [ha]
    exact (canonical24686 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1679 + difference 1 3) (sourceB1679 + difference 3 1) sourceC1679) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1216) := by
    have ha : (tripleCharges (sourceA1679 + difference 1 3) (sourceB1679 + difference 3 1) sourceC1679) = raw24687 := by
      apply Matrix.ext; unfold tripleCharges sourceA1679 sourceB1679 sourceC1679 difference raw24687; decide +kernel
    rw [ha]
    exact (canonical24687 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1679 + difference 1 4) (sourceB1679 + difference 4 1) sourceC1679) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1267) := by
    have ha : (tripleCharges (sourceA1679 + difference 1 4) (sourceB1679 + difference 4 1) sourceC1679) = raw24688 := by
      apply Matrix.ext; unfold tripleCharges sourceA1679 sourceB1679 sourceC1679 difference raw24688; decide +kernel
    rw [ha]
    exact (canonical24688 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1679 + difference 1 5) (sourceB1679 + difference 5 1) sourceC1679) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1260) := by
    have ha : (tripleCharges (sourceA1679 + difference 1 5) (sourceB1679 + difference 5 1) sourceC1679) = raw24689 := by
      apply Matrix.ext; unfold tripleCharges sourceA1679 sourceB1679 sourceC1679 difference raw24689; decide +kernel
    rw [ha]
    exact (canonical24689 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1679 + difference 2 0) (sourceB1679 + difference 0 2) sourceC1679) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 604) := by
    have ha : (tripleCharges (sourceA1679 + difference 2 0) (sourceB1679 + difference 0 2) sourceC1679) = raw24690 := by
      apply Matrix.ext; unfold tripleCharges sourceA1679 sourceB1679 sourceC1679 difference raw24690; decide +kernel
    rw [ha]
    exact (canonical24690 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1679 + difference 2 1) (sourceB1679 + difference 1 2) sourceC1679) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1130) := by
    have ha : (tripleCharges (sourceA1679 + difference 2 1) (sourceB1679 + difference 1 2) sourceC1679) = raw24691 := by
      apply Matrix.ext; unfold tripleCharges sourceA1679 sourceB1679 sourceC1679 difference raw24691; decide +kernel
    rw [ha]
    exact (canonical24691 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1679 + difference 2 3) (sourceB1679 + difference 3 2) sourceC1679) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1241) := by
    have ha : (tripleCharges (sourceA1679 + difference 2 3) (sourceB1679 + difference 3 2) sourceC1679) = raw24692 := by
      apply Matrix.ext; unfold tripleCharges sourceA1679 sourceB1679 sourceC1679 difference raw24692; decide +kernel
    rw [ha]
    exact (canonical24692 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1679 + difference 2 4) (sourceB1679 + difference 4 2) sourceC1679) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1302) := by
    have ha : (tripleCharges (sourceA1679 + difference 2 4) (sourceB1679 + difference 4 2) sourceC1679) = raw24693 := by
      apply Matrix.ext; unfold tripleCharges sourceA1679 sourceB1679 sourceC1679 difference raw24693; decide +kernel
    rw [ha]
    exact (canonical24693 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1679 + difference 2 5) (sourceB1679 + difference 5 2) sourceC1679) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1291) := by
    have ha : (tripleCharges (sourceA1679 + difference 2 5) (sourceB1679 + difference 5 2) sourceC1679) = raw24694 := by
      apply Matrix.ext; unfold tripleCharges sourceA1679 sourceB1679 sourceC1679 difference raw24694; decide +kernel
    rw [ha]
    exact (canonical24694 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1679 + difference 3 0) (sourceB1679 + difference 0 3) sourceC1679) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 586) := by
    have ha : (tripleCharges (sourceA1679 + difference 3 0) (sourceB1679 + difference 0 3) sourceC1679) = raw24695 := by
      apply Matrix.ext; unfold tripleCharges sourceA1679 sourceB1679 sourceC1679 difference raw24695; decide +kernel
    rw [ha]
    exact (canonical24695 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1679 + difference 3 1) (sourceB1679 + difference 1 3) sourceC1679) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1117) := by
    have ha : (tripleCharges (sourceA1679 + difference 3 1) (sourceB1679 + difference 1 3) sourceC1679) = raw24696 := by
      apply Matrix.ext; unfold tripleCharges sourceA1679 sourceB1679 sourceC1679 difference raw24696; decide +kernel
    rw [ha]
    exact (canonical24696 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1679 + difference 3 2) (sourceB1679 + difference 2 3) sourceC1679) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1172) := by
    have ha : (tripleCharges (sourceA1679 + difference 3 2) (sourceB1679 + difference 2 3) sourceC1679) = raw24697 := by
      apply Matrix.ext; unfold tripleCharges sourceA1679 sourceB1679 sourceC1679 difference raw24697; decide +kernel
    rw [ha]
    exact (canonical24697 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1679 + difference 3 4) (sourceB1679 + difference 4 3) sourceC1679) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1274) := by
    have ha : (tripleCharges (sourceA1679 + difference 3 4) (sourceB1679 + difference 4 3) sourceC1679) = raw24698 := by
      apply Matrix.ext; unfold tripleCharges sourceA1679 sourceB1679 sourceC1679 difference raw24698; decide +kernel
    rw [ha]
    exact (canonical24698 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1679 + difference 3 5) (sourceB1679 + difference 5 3) sourceC1679) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1262) := by
    have ha : (tripleCharges (sourceA1679 + difference 3 5) (sourceB1679 + difference 5 3) sourceC1679) = raw24699 := by
      apply Matrix.ext; unfold tripleCharges sourceA1679 sourceB1679 sourceC1679 difference raw24699; decide +kernel
    rw [ha]
    exact (canonical24699 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1679 + difference 4 0) (sourceB1679 + difference 0 4) sourceC1679) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 582) := by
    have ha : (tripleCharges (sourceA1679 + difference 4 0) (sourceB1679 + difference 0 4) sourceC1679) = raw24700 := by
      apply Matrix.ext; unfold tripleCharges sourceA1679 sourceB1679 sourceC1679 difference raw24700; decide +kernel
    rw [ha]
    exact (canonical24700 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1679 + difference 4 1) (sourceB1679 + difference 1 4) sourceC1679) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1113) := by
    have ha : (tripleCharges (sourceA1679 + difference 4 1) (sourceB1679 + difference 1 4) sourceC1679) = raw24701 := by
      apply Matrix.ext; unfold tripleCharges sourceA1679 sourceB1679 sourceC1679 difference raw24701; decide +kernel
    rw [ha]
    exact (canonical24701 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1679 + difference 4 2) (sourceB1679 + difference 2 4) sourceC1679) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1166) := by
    have ha : (tripleCharges (sourceA1679 + difference 4 2) (sourceB1679 + difference 2 4) sourceC1679) = raw24702 := by
      apply Matrix.ext; unfold tripleCharges sourceA1679 sourceB1679 sourceC1679 difference raw24702; decide +kernel
    rw [ha]
    exact (canonical24702 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1679 + difference 4 3) (sourceB1679 + difference 3 4) sourceC1679) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1219) := by
    have ha : (tripleCharges (sourceA1679 + difference 4 3) (sourceB1679 + difference 3 4) sourceC1679) = raw24703 := by
      apply Matrix.ext; unfold tripleCharges sourceA1679 sourceB1679 sourceC1679 difference raw24703; decide +kernel
    rw [ha]
    exact (canonical24703 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1679 + difference 4 5) (sourceB1679 + difference 5 4) sourceC1679) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1261) := by
    have ha : (tripleCharges (sourceA1679 + difference 4 5) (sourceB1679 + difference 5 4) sourceC1679) = raw24704 := by
      apply Matrix.ext; unfold tripleCharges sourceA1679 sourceB1679 sourceC1679 difference raw24704; decide +kernel
    rw [ha]
    exact (canonical24704 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1679 + difference 5 0) (sourceB1679 + difference 0 5) sourceC1679) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 581) := by
    have ha : (tripleCharges (sourceA1679 + difference 5 0) (sourceB1679 + difference 0 5) sourceC1679) = raw24705 := by
      apply Matrix.ext; unfold tripleCharges sourceA1679 sourceB1679 sourceC1679 difference raw24705; decide +kernel
    rw [ha]
    exact (canonical24705 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1679 + difference 5 1) (sourceB1679 + difference 1 5) sourceC1679) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1112) := by
    have ha : (tripleCharges (sourceA1679 + difference 5 1) (sourceB1679 + difference 1 5) sourceC1679) = raw24706 := by
      apply Matrix.ext; unfold tripleCharges sourceA1679 sourceB1679 sourceC1679 difference raw24706; decide +kernel
    rw [ha]
    exact (canonical24706 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1679 + difference 5 2) (sourceB1679 + difference 2 5) sourceC1679) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1165) := by
    have ha : (tripleCharges (sourceA1679 + difference 5 2) (sourceB1679 + difference 2 5) sourceC1679) = raw24707 := by
      apply Matrix.ext; unfold tripleCharges sourceA1679 sourceB1679 sourceC1679 difference raw24707; decide +kernel
    rw [ha]
    exact (canonical24707 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1679 + difference 5 3) (sourceB1679 + difference 3 5) sourceC1679) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1217) := by
    have ha : (tripleCharges (sourceA1679 + difference 5 3) (sourceB1679 + difference 3 5) sourceC1679) = raw24708 := by
      apply Matrix.ext; unfold tripleCharges sourceA1679 sourceB1679 sourceC1679 difference raw24708; decide +kernel
    rw [ha]
    exact (canonical24708 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1679 + difference 5 4) (sourceB1679 + difference 4 5) sourceC1679) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1269) := by
    have ha : (tripleCharges (sourceA1679 + difference 5 4) (sourceB1679 + difference 4 5) sourceC1679) = raw24709 := by
      apply Matrix.ext; unfold tripleCharges sourceA1679 sourceB1679 sourceC1679 difference raw24709; decide +kernel
    rw [ha]
    exact (canonical24709 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1679 sourceB1679 sourceC1679
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1679, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1680 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1680 : Charge := ![2, 0, -1, 0, -1, 0]
def sourceC1680 : Charge := ![2, 0, 1, -1, 0, -2]
def sourceForm1680 : Integer.Sparse Master := [(Sum.inr 1510, 1), (Sum.inr 1511, 1), (Sum.inr 1512, 1), (Sum.inr 1514, 1), (Sum.inr 1522, 1), (Sum.inr 3256, 1), (Sum.inr 3258, 1), (Sum.inr 3259, 1), (Sum.inr 3260, 1), (Sum.inr 3264, 1), (Sum.inr 3265, 1), (Sum.inr 3267, 1), (Sum.inr 3270, 1), (Sum.inr 3288, 1), (Sum.inr 3289, 1), (Sum.inr 3291, 1), (Sum.inr 3293, 1), (Sum.inr 3294, 1), (Sum.inr 3295, 1), (Sum.inr 3296, 2), (Sum.inr 3300, 1), (Sum.inr 3301, 1), (Sum.inr 3303, 1), (Sum.inr 3305, 1), (Sum.inr 3470, 1), (Sum.inr 3514, 1), (Sum.inr 3533, 1), (Sum.inr 3534, 1), (Sum.inr 3547, 1)]

theorem sourceEq1680 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1680 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1680 + difference 0 1) (sourceB1680 + difference 1 0) sourceC1680) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3514) := by
    have ha : (tripleCharges (sourceA1680 + difference 0 1) (sourceB1680 + difference 1 0) sourceC1680) = raw24710 := by
      apply Matrix.ext; unfold tripleCharges sourceA1680 sourceB1680 sourceC1680 difference raw24710; decide +kernel
    rw [ha]
    exact (canonical24710 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1680 + difference 0 2) (sourceB1680 + difference 2 0) sourceC1680) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3470) := by
    have ha : (tripleCharges (sourceA1680 + difference 0 2) (sourceB1680 + difference 2 0) sourceC1680) = raw24711 := by
      apply Matrix.ext; unfold tripleCharges sourceA1680 sourceB1680 sourceC1680 difference raw24711; decide +kernel
    rw [ha]
    exact (canonical24711 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1680 + difference 0 3) (sourceB1680 + difference 3 0) sourceC1680) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3533) := by
    have ha : (tripleCharges (sourceA1680 + difference 0 3) (sourceB1680 + difference 3 0) sourceC1680) = raw24712 := by
      apply Matrix.ext; unfold tripleCharges sourceA1680 sourceB1680 sourceC1680 difference raw24712; decide +kernel
    rw [ha]
    exact (canonical24712 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1680 + difference 0 4) (sourceB1680 + difference 4 0) sourceC1680) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3547) := by
    have ha : (tripleCharges (sourceA1680 + difference 0 4) (sourceB1680 + difference 4 0) sourceC1680) = raw24713 := by
      apply Matrix.ext; unfold tripleCharges sourceA1680 sourceB1680 sourceC1680 difference raw24713; decide +kernel
    rw [ha]
    exact (canonical24713 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1680 + difference 0 5) (sourceB1680 + difference 5 0) sourceC1680) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3534) := by
    have ha : (tripleCharges (sourceA1680 + difference 0 5) (sourceB1680 + difference 5 0) sourceC1680) = raw24714 := by
      apply Matrix.ext; unfold tripleCharges sourceA1680 sourceB1680 sourceC1680 difference raw24714; decide +kernel
    rw [ha]
    exact (canonical24714 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1680 + difference 1 0) (sourceB1680 + difference 0 1) sourceC1680) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1510) := by
    have ha : (tripleCharges (sourceA1680 + difference 1 0) (sourceB1680 + difference 0 1) sourceC1680) = raw24715 := by
      apply Matrix.ext; unfold tripleCharges sourceA1680 sourceB1680 sourceC1680 difference raw24715; decide +kernel
    rw [ha]
    exact (canonical24715 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1680 + difference 1 2) (sourceB1680 + difference 2 1) sourceC1680) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3256) := by
    have ha : (tripleCharges (sourceA1680 + difference 1 2) (sourceB1680 + difference 2 1) sourceC1680) = raw24716 := by
      apply Matrix.ext; unfold tripleCharges sourceA1680 sourceB1680 sourceC1680 difference raw24716; decide +kernel
    rw [ha]
    exact (canonical24716 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1680 + difference 1 3) (sourceB1680 + difference 3 1) sourceC1680) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3288) := by
    have ha : (tripleCharges (sourceA1680 + difference 1 3) (sourceB1680 + difference 3 1) sourceC1680) = raw24717 := by
      apply Matrix.ext; unfold tripleCharges sourceA1680 sourceB1680 sourceC1680 difference raw24717; decide +kernel
    rw [ha]
    exact (canonical24717 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1680 + difference 1 4) (sourceB1680 + difference 4 1) sourceC1680) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3293) := by
    have ha : (tripleCharges (sourceA1680 + difference 1 4) (sourceB1680 + difference 4 1) sourceC1680) = raw24718 := by
      apply Matrix.ext; unfold tripleCharges sourceA1680 sourceB1680 sourceC1680 difference raw24718; decide +kernel
    rw [ha]
    exact (canonical24718 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1680 + difference 1 5) (sourceB1680 + difference 5 1) sourceC1680) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3289) := by
    have ha : (tripleCharges (sourceA1680 + difference 1 5) (sourceB1680 + difference 5 1) sourceC1680) = raw24719 := by
      apply Matrix.ext; unfold tripleCharges sourceA1680 sourceB1680 sourceC1680 difference raw24719; decide +kernel
    rw [ha]
    exact (canonical24719 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1680 + difference 2 0) (sourceB1680 + difference 0 2) sourceC1680) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1512) := by
    have ha : (tripleCharges (sourceA1680 + difference 2 0) (sourceB1680 + difference 0 2) sourceC1680) = raw24720 := by
      apply Matrix.ext; unfold tripleCharges sourceA1680 sourceB1680 sourceC1680 difference raw24720; decide +kernel
    rw [ha]
    exact (canonical24720 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1680 + difference 2 1) (sourceB1680 + difference 1 2) sourceC1680) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3259) := by
    have ha : (tripleCharges (sourceA1680 + difference 2 1) (sourceB1680 + difference 1 2) sourceC1680) = raw24721 := by
      apply Matrix.ext; unfold tripleCharges sourceA1680 sourceB1680 sourceC1680 difference raw24721; decide +kernel
    rw [ha]
    exact (canonical24721 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1680 + difference 2 3) (sourceB1680 + difference 3 2) sourceC1680) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3296) := by
    have ha : (tripleCharges (sourceA1680 + difference 2 3) (sourceB1680 + difference 3 2) sourceC1680) = raw24722 := by
      apply Matrix.ext; unfold tripleCharges sourceA1680 sourceB1680 sourceC1680 difference raw24722; decide +kernel
    rw [ha]
    exact (canonical24722 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1680 + difference 2 4) (sourceB1680 + difference 4 2) sourceC1680) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3305) := by
    have ha : (tripleCharges (sourceA1680 + difference 2 4) (sourceB1680 + difference 4 2) sourceC1680) = raw24723 := by
      apply Matrix.ext; unfold tripleCharges sourceA1680 sourceB1680 sourceC1680 difference raw24723; decide +kernel
    rw [ha]
    exact (canonical24723 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1680 + difference 2 5) (sourceB1680 + difference 5 2) sourceC1680) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3303) := by
    have ha : (tripleCharges (sourceA1680 + difference 2 5) (sourceB1680 + difference 5 2) sourceC1680) = raw24724 := by
      apply Matrix.ext; unfold tripleCharges sourceA1680 sourceB1680 sourceC1680 difference raw24724; decide +kernel
    rw [ha]
    exact (canonical24724 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1680 + difference 3 0) (sourceB1680 + difference 0 3) sourceC1680) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1522) := by
    have ha : (tripleCharges (sourceA1680 + difference 3 0) (sourceB1680 + difference 0 3) sourceC1680) = raw24725 := by
      apply Matrix.ext; unfold tripleCharges sourceA1680 sourceB1680 sourceC1680 difference raw24725; decide +kernel
    rw [ha]
    exact (canonical24725 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1680 + difference 3 1) (sourceB1680 + difference 1 3) sourceC1680) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3267) := by
    have ha : (tripleCharges (sourceA1680 + difference 3 1) (sourceB1680 + difference 1 3) sourceC1680) = raw24726 := by
      apply Matrix.ext; unfold tripleCharges sourceA1680 sourceB1680 sourceC1680 difference raw24726; decide +kernel
    rw [ha]
    exact (canonical24726 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1680 + difference 3 2) (sourceB1680 + difference 2 3) sourceC1680) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3265) := by
    have ha : (tripleCharges (sourceA1680 + difference 3 2) (sourceB1680 + difference 2 3) sourceC1680) = raw24727 := by
      apply Matrix.ext; unfold tripleCharges sourceA1680 sourceB1680 sourceC1680 difference raw24727; decide +kernel
    rw [ha]
    exact (canonical24727 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1680 + difference 3 4) (sourceB1680 + difference 4 3) sourceC1680) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3301) := by
    have ha : (tripleCharges (sourceA1680 + difference 3 4) (sourceB1680 + difference 4 3) sourceC1680) = raw24728 := by
      apply Matrix.ext; unfold tripleCharges sourceA1680 sourceB1680 sourceC1680 difference raw24728; decide +kernel
    rw [ha]
    exact (canonical24728 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1680 + difference 3 5) (sourceB1680 + difference 5 3) sourceC1680) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3294) := by
    have ha : (tripleCharges (sourceA1680 + difference 3 5) (sourceB1680 + difference 5 3) sourceC1680) = raw24729 := by
      apply Matrix.ext; unfold tripleCharges sourceA1680 sourceB1680 sourceC1680 difference raw24729; decide +kernel
    rw [ha]
    exact (canonical24729 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1680 + difference 4 0) (sourceB1680 + difference 0 4) sourceC1680) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1511) := by
    have ha : (tripleCharges (sourceA1680 + difference 4 0) (sourceB1680 + difference 0 4) sourceC1680) = raw24730 := by
      apply Matrix.ext; unfold tripleCharges sourceA1680 sourceB1680 sourceC1680 difference raw24730; decide +kernel
    rw [ha]
    exact (canonical24730 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1680 + difference 4 1) (sourceB1680 + difference 1 4) sourceC1680) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3258) := by
    have ha : (tripleCharges (sourceA1680 + difference 4 1) (sourceB1680 + difference 1 4) sourceC1680) = raw24731 := by
      apply Matrix.ext; unfold tripleCharges sourceA1680 sourceB1680 sourceC1680 difference raw24731; decide +kernel
    rw [ha]
    exact (canonical24731 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1680 + difference 4 2) (sourceB1680 + difference 2 4) sourceC1680) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3270) := by
    have ha : (tripleCharges (sourceA1680 + difference 4 2) (sourceB1680 + difference 2 4) sourceC1680) = raw24732 := by
      apply Matrix.ext; unfold tripleCharges sourceA1680 sourceB1680 sourceC1680 difference raw24732; decide +kernel
    rw [ha]
    exact (canonical24732 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1680 + difference 4 3) (sourceB1680 + difference 3 4) sourceC1680) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3295) := by
    have ha : (tripleCharges (sourceA1680 + difference 4 3) (sourceB1680 + difference 3 4) sourceC1680) = raw24733 := by
      apply Matrix.ext; unfold tripleCharges sourceA1680 sourceB1680 sourceC1680 difference raw24733; decide +kernel
    rw [ha]
    exact (canonical24733 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1680 + difference 4 5) (sourceB1680 + difference 5 4) sourceC1680) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3296) := by
    have ha : (tripleCharges (sourceA1680 + difference 4 5) (sourceB1680 + difference 5 4) sourceC1680) = raw24734 := by
      apply Matrix.ext; unfold tripleCharges sourceA1680 sourceB1680 sourceC1680 difference raw24734; decide +kernel
    rw [ha]
    exact (canonical24734 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1680 + difference 5 0) (sourceB1680 + difference 0 5) sourceC1680) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1514) := by
    have ha : (tripleCharges (sourceA1680 + difference 5 0) (sourceB1680 + difference 0 5) sourceC1680) = raw24735 := by
      apply Matrix.ext; unfold tripleCharges sourceA1680 sourceB1680 sourceC1680 difference raw24735; decide +kernel
    rw [ha]
    exact (canonical24735 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1680 + difference 5 1) (sourceB1680 + difference 1 5) sourceC1680) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3260) := by
    have ha : (tripleCharges (sourceA1680 + difference 5 1) (sourceB1680 + difference 1 5) sourceC1680) = raw24736 := by
      apply Matrix.ext; unfold tripleCharges sourceA1680 sourceB1680 sourceC1680 difference raw24736; decide +kernel
    rw [ha]
    exact (canonical24736 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1680 + difference 5 2) (sourceB1680 + difference 2 5) sourceC1680) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3264) := by
    have ha : (tripleCharges (sourceA1680 + difference 5 2) (sourceB1680 + difference 2 5) sourceC1680) = raw24737 := by
      apply Matrix.ext; unfold tripleCharges sourceA1680 sourceB1680 sourceC1680 difference raw24737; decide +kernel
    rw [ha]
    exact (canonical24737 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1680 + difference 5 3) (sourceB1680 + difference 3 5) sourceC1680) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3291) := by
    have ha : (tripleCharges (sourceA1680 + difference 5 3) (sourceB1680 + difference 3 5) sourceC1680) = raw24738 := by
      apply Matrix.ext; unfold tripleCharges sourceA1680 sourceB1680 sourceC1680 difference raw24738; decide +kernel
    rw [ha]
    exact (canonical24738 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1680 + difference 5 4) (sourceB1680 + difference 4 5) sourceC1680) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3300) := by
    have ha : (tripleCharges (sourceA1680 + difference 5 4) (sourceB1680 + difference 4 5) sourceC1680) = raw24739 := by
      apply Matrix.ext; unfold tripleCharges sourceA1680 sourceB1680 sourceC1680 difference raw24739; decide +kernel
    rw [ha]
    exact (canonical24739 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1680 sourceB1680 sourceC1680
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1680, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1681 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1681 : Charge := ![2, 0, -1, 0, -1, 0]
def sourceC1681 : Charge := ![2, 0, 1, -1, 0, -2]
def sourceForm1681 : Integer.Sparse Master := [(Sum.inr 623, 1), (Sum.inr 626, 1), (Sum.inr 627, 1), (Sum.inr 631, 1), (Sum.inr 638, 1), (Sum.inr 1236, 1), (Sum.inr 4092, -1)]

theorem sourceEq1681 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1681 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1681 + difference 0 0) (sourceB1681 + difference 0 0) sourceC1681) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1236) := by
    have ha : (tripleCharges (sourceA1681 + difference 0 0) (sourceB1681 + difference 0 0) sourceC1681) = raw24740 := by
      apply Matrix.ext; unfold tripleCharges sourceA1681 sourceB1681 sourceC1681 difference raw24740; decide +kernel
    rw [ha]
    exact (canonical24740 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1681 + difference 1 0) (sourceB1681 + difference 0 1) sourceC1681) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 623) := by
    have ha : (tripleCharges (sourceA1681 + difference 1 0) (sourceB1681 + difference 0 1) sourceC1681) = raw24741 := by
      apply Matrix.ext; unfold tripleCharges sourceA1681 sourceB1681 sourceC1681 difference raw24741; decide +kernel
    rw [ha]
    exact (canonical24741 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1681 + difference 2 0) (sourceB1681 + difference 0 2) sourceC1681) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 638) := by
    have ha : (tripleCharges (sourceA1681 + difference 2 0) (sourceB1681 + difference 0 2) sourceC1681) = raw24742 := by
      apply Matrix.ext; unfold tripleCharges sourceA1681 sourceB1681 sourceC1681 difference raw24742; decide +kernel
    rw [ha]
    exact (canonical24742 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1681 + difference 3 0) (sourceB1681 + difference 0 3) sourceC1681) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 627) := by
    have ha : (tripleCharges (sourceA1681 + difference 3 0) (sourceB1681 + difference 0 3) sourceC1681) = raw24743 := by
      apply Matrix.ext; unfold tripleCharges sourceA1681 sourceB1681 sourceC1681 difference raw24743; decide +kernel
    rw [ha]
    exact (canonical24743 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1681 + difference 4 0) (sourceB1681 + difference 0 4) sourceC1681) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 631) := by
    have ha : (tripleCharges (sourceA1681 + difference 4 0) (sourceB1681 + difference 0 4) sourceC1681) = raw24744 := by
      apply Matrix.ext; unfold tripleCharges sourceA1681 sourceB1681 sourceC1681 difference raw24744; decide +kernel
    rw [ha]
    exact (canonical24744 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1681 + difference 5 0) (sourceB1681 + difference 0 5) sourceC1681) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 626) := by
    have ha : (tripleCharges (sourceA1681 + difference 5 0) (sourceB1681 + difference 0 5) sourceC1681) = raw24745 := by
      apply Matrix.ext; unfold tripleCharges sourceA1681 sourceB1681 sourceC1681 difference raw24745; decide +kernel
    rw [ha]
    exact (canonical24745 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1681 + sourceB1681) sourceC1681) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1681 + sourceB1681) sourceC1681) = raw24746 := by
      apply Matrix.ext; unfold doubleCharges sourceA1681 sourceB1681 sourceC1681 raw24746; decide +kernel
    rw [ha]
    exact (canonical24746 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1681 sourceB1681 sourceC1681
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1681, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1682 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1682 : Charge := ![2, 0, -1, 0, -1, 0]
def sourceC1682 : Charge := ![2, 0, 1, -1, 0, -2]
def sourceForm1682 : Integer.Sparse Master := [(Sum.inr 1148, 1), (Sum.inr 1149, 1), (Sum.inr 1151, 1), (Sum.inr 1156, 1), (Sum.inr 1236, 1), (Sum.inr 2553, 1), (Sum.inr 4092, -1)]

theorem sourceEq1682 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1682 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1682 + difference 0 1) (sourceB1682 + difference 1 0) sourceC1682) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2553) := by
    have ha : (tripleCharges (sourceA1682 + difference 0 1) (sourceB1682 + difference 1 0) sourceC1682) = raw24747 := by
      apply Matrix.ext; unfold tripleCharges sourceA1682 sourceB1682 sourceC1682 difference raw24747; decide +kernel
    rw [ha]
    exact (canonical24747 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1682 + difference 1 1) (sourceB1682 + difference 1 1) sourceC1682) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1236) := by
    have ha : (tripleCharges (sourceA1682 + difference 1 1) (sourceB1682 + difference 1 1) sourceC1682) = raw24740 := by
      apply Matrix.ext; unfold tripleCharges sourceA1682 sourceB1682 sourceC1682 difference raw24740; decide +kernel
    rw [ha]
    exact (canonical24740 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1682 + difference 2 1) (sourceB1682 + difference 1 2) sourceC1682) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1156) := by
    have ha : (tripleCharges (sourceA1682 + difference 2 1) (sourceB1682 + difference 1 2) sourceC1682) = raw24748 := by
      apply Matrix.ext; unfold tripleCharges sourceA1682 sourceB1682 sourceC1682 difference raw24748; decide +kernel
    rw [ha]
    exact (canonical24748 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1682 + difference 3 1) (sourceB1682 + difference 1 3) sourceC1682) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1149) := by
    have ha : (tripleCharges (sourceA1682 + difference 3 1) (sourceB1682 + difference 1 3) sourceC1682) = raw24749 := by
      apply Matrix.ext; unfold tripleCharges sourceA1682 sourceB1682 sourceC1682 difference raw24749; decide +kernel
    rw [ha]
    exact (canonical24749 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1682 + difference 4 1) (sourceB1682 + difference 1 4) sourceC1682) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1151) := by
    have ha : (tripleCharges (sourceA1682 + difference 4 1) (sourceB1682 + difference 1 4) sourceC1682) = raw24750 := by
      apply Matrix.ext; unfold tripleCharges sourceA1682 sourceB1682 sourceC1682 difference raw24750; decide +kernel
    rw [ha]
    exact (canonical24750 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1682 + difference 5 1) (sourceB1682 + difference 1 5) sourceC1682) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1148) := by
    have ha : (tripleCharges (sourceA1682 + difference 5 1) (sourceB1682 + difference 1 5) sourceC1682) = raw24751 := by
      apply Matrix.ext; unfold tripleCharges sourceA1682 sourceB1682 sourceC1682 difference raw24751; decide +kernel
    rw [ha]
    exact (canonical24751 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1682 + sourceB1682) sourceC1682) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1682 + sourceB1682) sourceC1682) = raw24746 := by
      apply Matrix.ext; unfold doubleCharges sourceA1682 sourceB1682 sourceC1682 raw24746; decide +kernel
    rw [ha]
    exact (canonical24746 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1682 sourceB1682 sourceC1682
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1682, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1683 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1683 : Charge := ![2, 0, 1, -1, 0, -2]
def sourceC1683 : Charge := ![2, 0, -1, 0, -1, 0]
def sourceForm1683 : Integer.Sparse Master := [(Sum.inr 4139, 1), (Sum.inr 4140, 1), (Sum.inr 4141, 1), (Sum.inr 4145, 1), (Sum.inr 4172, 1), (Sum.inr 4513, 1), (Sum.inr 4514, 1), (Sum.inr 4515, 1), (Sum.inr 4518, 1), (Sum.inr 4521, 1), (Sum.inr 4522, 1), (Sum.inr 4524, 1), (Sum.inr 4541, 1), (Sum.inr 4581, 1), (Sum.inr 4583, 1), (Sum.inr 4586, 1), (Sum.inr 4601, 1), (Sum.inr 4602, 3), (Sum.inr 4605, 1), (Sum.inr 4606, 1), (Sum.inr 4612, 1), (Sum.inr 4622, 1), (Sum.inr 4623, 1), (Sum.inr 5149, 1), (Sum.inr 5204, 1), (Sum.inr 5284, 1), (Sum.inr 5292, 1), (Sum.inr 5294, 1)]

theorem sourceEq1683 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1683 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1683 + difference 0 1) (sourceB1683 + difference 1 0) sourceC1683) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5149) := by
    have ha : (tripleCharges (sourceA1683 + difference 0 1) (sourceB1683 + difference 1 0) sourceC1683) = raw24752 := by
      apply Matrix.ext; unfold tripleCharges sourceA1683 sourceB1683 sourceC1683 difference raw24752; decide +kernel
    rw [ha]
    exact (canonical24752 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1683 + difference 0 2) (sourceB1683 + difference 2 0) sourceC1683) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5204) := by
    have ha : (tripleCharges (sourceA1683 + difference 0 2) (sourceB1683 + difference 2 0) sourceC1683) = raw24753 := by
      apply Matrix.ext; unfold tripleCharges sourceA1683 sourceB1683 sourceC1683 difference raw24753; decide +kernel
    rw [ha]
    exact (canonical24753 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1683 + difference 0 3) (sourceB1683 + difference 3 0) sourceC1683) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA1683 + difference 0 3) (sourceB1683 + difference 3 0) sourceC1683) = raw24754 := by
      apply Matrix.ext; unfold tripleCharges sourceA1683 sourceB1683 sourceC1683 difference raw24754; decide +kernel
    rw [ha]
    exact (canonical24754 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1683 + difference 0 4) (sourceB1683 + difference 4 0) sourceC1683) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA1683 + difference 0 4) (sourceB1683 + difference 4 0) sourceC1683) = raw24755 := by
      apply Matrix.ext; unfold tripleCharges sourceA1683 sourceB1683 sourceC1683 difference raw24755; decide +kernel
    rw [ha]
    exact (canonical24755 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1683 + difference 0 5) (sourceB1683 + difference 5 0) sourceC1683) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA1683 + difference 0 5) (sourceB1683 + difference 5 0) sourceC1683) = raw24756 := by
      apply Matrix.ext; unfold tripleCharges sourceA1683 sourceB1683 sourceC1683 difference raw24756; decide +kernel
    rw [ha]
    exact (canonical24756 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1683 + difference 1 0) (sourceB1683 + difference 0 1) sourceC1683) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4139) := by
    have ha : (tripleCharges (sourceA1683 + difference 1 0) (sourceB1683 + difference 0 1) sourceC1683) = raw24757 := by
      apply Matrix.ext; unfold tripleCharges sourceA1683 sourceB1683 sourceC1683 difference raw24757; decide +kernel
    rw [ha]
    exact (canonical24757 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1683 + difference 1 2) (sourceB1683 + difference 2 1) sourceC1683) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4513) := by
    have ha : (tripleCharges (sourceA1683 + difference 1 2) (sourceB1683 + difference 2 1) sourceC1683) = raw24758 := by
      apply Matrix.ext; unfold tripleCharges sourceA1683 sourceB1683 sourceC1683 difference raw24758; decide +kernel
    rw [ha]
    exact (canonical24758 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1683 + difference 1 3) (sourceB1683 + difference 3 1) sourceC1683) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1683 + difference 1 3) (sourceB1683 + difference 3 1) sourceC1683) = raw24759 := by
      apply Matrix.ext; unfold tripleCharges sourceA1683 sourceB1683 sourceC1683 difference raw24759; decide +kernel
    rw [ha]
    exact (canonical24759 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1683 + difference 1 4) (sourceB1683 + difference 4 1) sourceC1683) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4581) := by
    have ha : (tripleCharges (sourceA1683 + difference 1 4) (sourceB1683 + difference 4 1) sourceC1683) = raw24760 := by
      apply Matrix.ext; unfold tripleCharges sourceA1683 sourceB1683 sourceC1683 difference raw24760; decide +kernel
    rw [ha]
    exact (canonical24760 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1683 + difference 1 5) (sourceB1683 + difference 5 1) sourceC1683) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4601) := by
    have ha : (tripleCharges (sourceA1683 + difference 1 5) (sourceB1683 + difference 5 1) sourceC1683) = raw24761 := by
      apply Matrix.ext; unfold tripleCharges sourceA1683 sourceB1683 sourceC1683 difference raw24761; decide +kernel
    rw [ha]
    exact (canonical24761 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1683 + difference 2 0) (sourceB1683 + difference 0 2) sourceC1683) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4172) := by
    have ha : (tripleCharges (sourceA1683 + difference 2 0) (sourceB1683 + difference 0 2) sourceC1683) = raw24762 := by
      apply Matrix.ext; unfold tripleCharges sourceA1683 sourceB1683 sourceC1683 difference raw24762; decide +kernel
    rw [ha]
    exact (canonical24762 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1683 + difference 2 1) (sourceB1683 + difference 1 2) sourceC1683) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4541) := by
    have ha : (tripleCharges (sourceA1683 + difference 2 1) (sourceB1683 + difference 1 2) sourceC1683) = raw24763 := by
      apply Matrix.ext; unfold tripleCharges sourceA1683 sourceB1683 sourceC1683 difference raw24763; decide +kernel
    rw [ha]
    exact (canonical24763 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1683 + difference 2 3) (sourceB1683 + difference 3 2) sourceC1683) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4623) := by
    have ha : (tripleCharges (sourceA1683 + difference 2 3) (sourceB1683 + difference 3 2) sourceC1683) = raw24764 := by
      apply Matrix.ext; unfold tripleCharges sourceA1683 sourceB1683 sourceC1683 difference raw24764; decide +kernel
    rw [ha]
    exact (canonical24764 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1683 + difference 2 4) (sourceB1683 + difference 4 2) sourceC1683) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1683 + difference 2 4) (sourceB1683 + difference 4 2) sourceC1683) = raw24765 := by
      apply Matrix.ext; unfold tripleCharges sourceA1683 sourceB1683 sourceC1683 difference raw24765; decide +kernel
    rw [ha]
    exact (canonical24765 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1683 + difference 2 5) (sourceB1683 + difference 5 2) sourceC1683) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4622) := by
    have ha : (tripleCharges (sourceA1683 + difference 2 5) (sourceB1683 + difference 5 2) sourceC1683) = raw24766 := by
      apply Matrix.ext; unfold tripleCharges sourceA1683 sourceB1683 sourceC1683 difference raw24766; decide +kernel
    rw [ha]
    exact (canonical24766 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1683 + difference 3 0) (sourceB1683 + difference 0 3) sourceC1683) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4141) := by
    have ha : (tripleCharges (sourceA1683 + difference 3 0) (sourceB1683 + difference 0 3) sourceC1683) = raw24767 := by
      apply Matrix.ext; unfold tripleCharges sourceA1683 sourceB1683 sourceC1683 difference raw24767; decide +kernel
    rw [ha]
    exact (canonical24767 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1683 + difference 3 1) (sourceB1683 + difference 1 3) sourceC1683) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4522) := by
    have ha : (tripleCharges (sourceA1683 + difference 3 1) (sourceB1683 + difference 1 3) sourceC1683) = raw24768 := by
      apply Matrix.ext; unfold tripleCharges sourceA1683 sourceB1683 sourceC1683 difference raw24768; decide +kernel
    rw [ha]
    exact (canonical24768 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1683 + difference 3 2) (sourceB1683 + difference 2 3) sourceC1683) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4515) := by
    have ha : (tripleCharges (sourceA1683 + difference 3 2) (sourceB1683 + difference 2 3) sourceC1683) = raw24769 := by
      apply Matrix.ext; unfold tripleCharges sourceA1683 sourceB1683 sourceC1683 difference raw24769; decide +kernel
    rw [ha]
    exact (canonical24769 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1683 + difference 3 4) (sourceB1683 + difference 4 3) sourceC1683) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4586) := by
    have ha : (tripleCharges (sourceA1683 + difference 3 4) (sourceB1683 + difference 4 3) sourceC1683) = raw24770 := by
      apply Matrix.ext; unfold tripleCharges sourceA1683 sourceB1683 sourceC1683 difference raw24770; decide +kernel
    rw [ha]
    exact (canonical24770 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1683 + difference 3 5) (sourceB1683 + difference 5 3) sourceC1683) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1683 + difference 3 5) (sourceB1683 + difference 5 3) sourceC1683) = raw24771 := by
      apply Matrix.ext; unfold tripleCharges sourceA1683 sourceB1683 sourceC1683 difference raw24771; decide +kernel
    rw [ha]
    exact (canonical24771 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1683 + difference 4 0) (sourceB1683 + difference 0 4) sourceC1683) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4145) := by
    have ha : (tripleCharges (sourceA1683 + difference 4 0) (sourceB1683 + difference 0 4) sourceC1683) = raw24772 := by
      apply Matrix.ext; unfold tripleCharges sourceA1683 sourceB1683 sourceC1683 difference raw24772; decide +kernel
    rw [ha]
    exact (canonical24772 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1683 + difference 4 1) (sourceB1683 + difference 1 4) sourceC1683) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4524) := by
    have ha : (tripleCharges (sourceA1683 + difference 4 1) (sourceB1683 + difference 1 4) sourceC1683) = raw24773 := by
      apply Matrix.ext; unfold tripleCharges sourceA1683 sourceB1683 sourceC1683 difference raw24773; decide +kernel
    rw [ha]
    exact (canonical24773 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1683 + difference 4 2) (sourceB1683 + difference 2 4) sourceC1683) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4518) := by
    have ha : (tripleCharges (sourceA1683 + difference 4 2) (sourceB1683 + difference 2 4) sourceC1683) = raw24774 := by
      apply Matrix.ext; unfold tripleCharges sourceA1683 sourceB1683 sourceC1683 difference raw24774; decide +kernel
    rw [ha]
    exact (canonical24774 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1683 + difference 4 3) (sourceB1683 + difference 3 4) sourceC1683) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA1683 + difference 4 3) (sourceB1683 + difference 3 4) sourceC1683) = raw24775 := by
      apply Matrix.ext; unfold tripleCharges sourceA1683 sourceB1683 sourceC1683 difference raw24775; decide +kernel
    rw [ha]
    exact (canonical24775 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1683 + difference 4 5) (sourceB1683 + difference 5 4) sourceC1683) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4606) := by
    have ha : (tripleCharges (sourceA1683 + difference 4 5) (sourceB1683 + difference 5 4) sourceC1683) = raw24776 := by
      apply Matrix.ext; unfold tripleCharges sourceA1683 sourceB1683 sourceC1683 difference raw24776; decide +kernel
    rw [ha]
    exact (canonical24776 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1683 + difference 5 0) (sourceB1683 + difference 0 5) sourceC1683) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4140) := by
    have ha : (tripleCharges (sourceA1683 + difference 5 0) (sourceB1683 + difference 0 5) sourceC1683) = raw24777 := by
      apply Matrix.ext; unfold tripleCharges sourceA1683 sourceB1683 sourceC1683 difference raw24777; decide +kernel
    rw [ha]
    exact (canonical24777 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1683 + difference 5 1) (sourceB1683 + difference 1 5) sourceC1683) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4521) := by
    have ha : (tripleCharges (sourceA1683 + difference 5 1) (sourceB1683 + difference 1 5) sourceC1683) = raw24778 := by
      apply Matrix.ext; unfold tripleCharges sourceA1683 sourceB1683 sourceC1683 difference raw24778; decide +kernel
    rw [ha]
    exact (canonical24778 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1683 + difference 5 2) (sourceB1683 + difference 2 5) sourceC1683) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4514) := by
    have ha : (tripleCharges (sourceA1683 + difference 5 2) (sourceB1683 + difference 2 5) sourceC1683) = raw24779 := by
      apply Matrix.ext; unfold tripleCharges sourceA1683 sourceB1683 sourceC1683 difference raw24779; decide +kernel
    rw [ha]
    exact (canonical24779 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1683 + difference 5 3) (sourceB1683 + difference 3 5) sourceC1683) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4605) := by
    have ha : (tripleCharges (sourceA1683 + difference 5 3) (sourceB1683 + difference 3 5) sourceC1683) = raw24780 := by
      apply Matrix.ext; unfold tripleCharges sourceA1683 sourceB1683 sourceC1683 difference raw24780; decide +kernel
    rw [ha]
    exact (canonical24780 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1683 + difference 5 4) (sourceB1683 + difference 4 5) sourceC1683) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4583) := by
    have ha : (tripleCharges (sourceA1683 + difference 5 4) (sourceB1683 + difference 4 5) sourceC1683) = raw24781 := by
      apply Matrix.ext; unfold tripleCharges sourceA1683 sourceB1683 sourceC1683 difference raw24781; decide +kernel
    rw [ha]
    exact (canonical24781 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1683 sourceB1683 sourceC1683
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1683, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1684 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1684 : Charge := ![2, 0, 1, -1, 0, -2]
def sourceC1684 : Charge := ![2, 0, -1, 0, -1, 0]
def sourceForm1684 : Integer.Sparse Master := [(Sum.inr 567, 1), (Sum.inr 568, 1), (Sum.inr 569, 1), (Sum.inr 573, 1), (Sum.inr 600, 1), (Sum.inr 1097, 1), (Sum.inr 1098, 1), (Sum.inr 1099, 1), (Sum.inr 1102, 1), (Sum.inr 1105, 1), (Sum.inr 1106, 1), (Sum.inr 1108, 1), (Sum.inr 1126, 1), (Sum.inr 1200, 1), (Sum.inr 1202, 1), (Sum.inr 1205, 1), (Sum.inr 1235, 1), (Sum.inr 1236, 3), (Sum.inr 1239, 1), (Sum.inr 1240, 1), (Sum.inr 1246, 1), (Sum.inr 1299, 1), (Sum.inr 1300, 1), (Sum.inr 2881, 1), (Sum.inr 2924, 1), (Sum.inr 3077, 1), (Sum.inr 3100, 1), (Sum.inr 3101, 1)]

theorem sourceEq1684 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1684 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1684 + difference 0 1) (sourceB1684 + difference 1 0) sourceC1684) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2924) := by
    have ha : (tripleCharges (sourceA1684 + difference 0 1) (sourceB1684 + difference 1 0) sourceC1684) = raw24782 := by
      apply Matrix.ext; unfold tripleCharges sourceA1684 sourceB1684 sourceC1684 difference raw24782; decide +kernel
    rw [ha]
    exact (canonical24782 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1684 + difference 0 2) (sourceB1684 + difference 2 0) sourceC1684) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2881) := by
    have ha : (tripleCharges (sourceA1684 + difference 0 2) (sourceB1684 + difference 2 0) sourceC1684) = raw24783 := by
      apply Matrix.ext; unfold tripleCharges sourceA1684 sourceB1684 sourceC1684 difference raw24783; decide +kernel
    rw [ha]
    exact (canonical24783 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1684 + difference 0 3) (sourceB1684 + difference 3 0) sourceC1684) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3101) := by
    have ha : (tripleCharges (sourceA1684 + difference 0 3) (sourceB1684 + difference 3 0) sourceC1684) = raw24784 := by
      apply Matrix.ext; unfold tripleCharges sourceA1684 sourceB1684 sourceC1684 difference raw24784; decide +kernel
    rw [ha]
    exact (canonical24784 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1684 + difference 0 4) (sourceB1684 + difference 4 0) sourceC1684) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3077) := by
    have ha : (tripleCharges (sourceA1684 + difference 0 4) (sourceB1684 + difference 4 0) sourceC1684) = raw24785 := by
      apply Matrix.ext; unfold tripleCharges sourceA1684 sourceB1684 sourceC1684 difference raw24785; decide +kernel
    rw [ha]
    exact (canonical24785 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1684 + difference 0 5) (sourceB1684 + difference 5 0) sourceC1684) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3100) := by
    have ha : (tripleCharges (sourceA1684 + difference 0 5) (sourceB1684 + difference 5 0) sourceC1684) = raw24786 := by
      apply Matrix.ext; unfold tripleCharges sourceA1684 sourceB1684 sourceC1684 difference raw24786; decide +kernel
    rw [ha]
    exact (canonical24786 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1684 + difference 1 0) (sourceB1684 + difference 0 1) sourceC1684) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 567) := by
    have ha : (tripleCharges (sourceA1684 + difference 1 0) (sourceB1684 + difference 0 1) sourceC1684) = raw24787 := by
      apply Matrix.ext; unfold tripleCharges sourceA1684 sourceB1684 sourceC1684 difference raw24787; decide +kernel
    rw [ha]
    exact (canonical24787 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1684 + difference 1 2) (sourceB1684 + difference 2 1) sourceC1684) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1097) := by
    have ha : (tripleCharges (sourceA1684 + difference 1 2) (sourceB1684 + difference 2 1) sourceC1684) = raw24788 := by
      apply Matrix.ext; unfold tripleCharges sourceA1684 sourceB1684 sourceC1684 difference raw24788; decide +kernel
    rw [ha]
    exact (canonical24788 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1684 + difference 1 3) (sourceB1684 + difference 3 1) sourceC1684) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1236) := by
    have ha : (tripleCharges (sourceA1684 + difference 1 3) (sourceB1684 + difference 3 1) sourceC1684) = raw24789 := by
      apply Matrix.ext; unfold tripleCharges sourceA1684 sourceB1684 sourceC1684 difference raw24789; decide +kernel
    rw [ha]
    exact (canonical24789 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1684 + difference 1 4) (sourceB1684 + difference 4 1) sourceC1684) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1200) := by
    have ha : (tripleCharges (sourceA1684 + difference 1 4) (sourceB1684 + difference 4 1) sourceC1684) = raw24790 := by
      apply Matrix.ext; unfold tripleCharges sourceA1684 sourceB1684 sourceC1684 difference raw24790; decide +kernel
    rw [ha]
    exact (canonical24790 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1684 + difference 1 5) (sourceB1684 + difference 5 1) sourceC1684) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1235) := by
    have ha : (tripleCharges (sourceA1684 + difference 1 5) (sourceB1684 + difference 5 1) sourceC1684) = raw24791 := by
      apply Matrix.ext; unfold tripleCharges sourceA1684 sourceB1684 sourceC1684 difference raw24791; decide +kernel
    rw [ha]
    exact (canonical24791 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1684 + difference 2 0) (sourceB1684 + difference 0 2) sourceC1684) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 600) := by
    have ha : (tripleCharges (sourceA1684 + difference 2 0) (sourceB1684 + difference 0 2) sourceC1684) = raw24792 := by
      apply Matrix.ext; unfold tripleCharges sourceA1684 sourceB1684 sourceC1684 difference raw24792; decide +kernel
    rw [ha]
    exact (canonical24792 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1684 + difference 2 1) (sourceB1684 + difference 1 2) sourceC1684) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1126) := by
    have ha : (tripleCharges (sourceA1684 + difference 2 1) (sourceB1684 + difference 1 2) sourceC1684) = raw24793 := by
      apply Matrix.ext; unfold tripleCharges sourceA1684 sourceB1684 sourceC1684 difference raw24793; decide +kernel
    rw [ha]
    exact (canonical24793 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1684 + difference 2 3) (sourceB1684 + difference 3 2) sourceC1684) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1300) := by
    have ha : (tripleCharges (sourceA1684 + difference 2 3) (sourceB1684 + difference 3 2) sourceC1684) = raw24794 := by
      apply Matrix.ext; unfold tripleCharges sourceA1684 sourceB1684 sourceC1684 difference raw24794; decide +kernel
    rw [ha]
    exact (canonical24794 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1684 + difference 2 4) (sourceB1684 + difference 4 2) sourceC1684) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1236) := by
    have ha : (tripleCharges (sourceA1684 + difference 2 4) (sourceB1684 + difference 4 2) sourceC1684) = raw24795 := by
      apply Matrix.ext; unfold tripleCharges sourceA1684 sourceB1684 sourceC1684 difference raw24795; decide +kernel
    rw [ha]
    exact (canonical24795 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1684 + difference 2 5) (sourceB1684 + difference 5 2) sourceC1684) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1299) := by
    have ha : (tripleCharges (sourceA1684 + difference 2 5) (sourceB1684 + difference 5 2) sourceC1684) = raw24796 := by
      apply Matrix.ext; unfold tripleCharges sourceA1684 sourceB1684 sourceC1684 difference raw24796; decide +kernel
    rw [ha]
    exact (canonical24796 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1684 + difference 3 0) (sourceB1684 + difference 0 3) sourceC1684) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 569) := by
    have ha : (tripleCharges (sourceA1684 + difference 3 0) (sourceB1684 + difference 0 3) sourceC1684) = raw24797 := by
      apply Matrix.ext; unfold tripleCharges sourceA1684 sourceB1684 sourceC1684 difference raw24797; decide +kernel
    rw [ha]
    exact (canonical24797 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1684 + difference 3 1) (sourceB1684 + difference 1 3) sourceC1684) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1106) := by
    have ha : (tripleCharges (sourceA1684 + difference 3 1) (sourceB1684 + difference 1 3) sourceC1684) = raw24798 := by
      apply Matrix.ext; unfold tripleCharges sourceA1684 sourceB1684 sourceC1684 difference raw24798; decide +kernel
    rw [ha]
    exact (canonical24798 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1684 + difference 3 2) (sourceB1684 + difference 2 3) sourceC1684) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1099) := by
    have ha : (tripleCharges (sourceA1684 + difference 3 2) (sourceB1684 + difference 2 3) sourceC1684) = raw24799 := by
      apply Matrix.ext; unfold tripleCharges sourceA1684 sourceB1684 sourceC1684 difference raw24799; decide +kernel
    rw [ha]
    exact (canonical24799 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1684 + difference 3 4) (sourceB1684 + difference 4 3) sourceC1684) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1205) := by
    have ha : (tripleCharges (sourceA1684 + difference 3 4) (sourceB1684 + difference 4 3) sourceC1684) = raw24800 := by
      apply Matrix.ext; unfold tripleCharges sourceA1684 sourceB1684 sourceC1684 difference raw24800; decide +kernel
    rw [ha]
    exact (canonical24800 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1684 + difference 3 5) (sourceB1684 + difference 5 3) sourceC1684) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1236) := by
    have ha : (tripleCharges (sourceA1684 + difference 3 5) (sourceB1684 + difference 5 3) sourceC1684) = raw24801 := by
      apply Matrix.ext; unfold tripleCharges sourceA1684 sourceB1684 sourceC1684 difference raw24801; decide +kernel
    rw [ha]
    exact (canonical24801 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1684 + difference 4 0) (sourceB1684 + difference 0 4) sourceC1684) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 573) := by
    have ha : (tripleCharges (sourceA1684 + difference 4 0) (sourceB1684 + difference 0 4) sourceC1684) = raw24802 := by
      apply Matrix.ext; unfold tripleCharges sourceA1684 sourceB1684 sourceC1684 difference raw24802; decide +kernel
    rw [ha]
    exact (canonical24802 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1684 + difference 4 1) (sourceB1684 + difference 1 4) sourceC1684) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1108) := by
    have ha : (tripleCharges (sourceA1684 + difference 4 1) (sourceB1684 + difference 1 4) sourceC1684) = raw24803 := by
      apply Matrix.ext; unfold tripleCharges sourceA1684 sourceB1684 sourceC1684 difference raw24803; decide +kernel
    rw [ha]
    exact (canonical24803 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1684 + difference 4 2) (sourceB1684 + difference 2 4) sourceC1684) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1102) := by
    have ha : (tripleCharges (sourceA1684 + difference 4 2) (sourceB1684 + difference 2 4) sourceC1684) = raw24804 := by
      apply Matrix.ext; unfold tripleCharges sourceA1684 sourceB1684 sourceC1684 difference raw24804; decide +kernel
    rw [ha]
    exact (canonical24804 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1684 + difference 4 3) (sourceB1684 + difference 3 4) sourceC1684) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1246) := by
    have ha : (tripleCharges (sourceA1684 + difference 4 3) (sourceB1684 + difference 3 4) sourceC1684) = raw24805 := by
      apply Matrix.ext; unfold tripleCharges sourceA1684 sourceB1684 sourceC1684 difference raw24805; decide +kernel
    rw [ha]
    exact (canonical24805 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1684 + difference 4 5) (sourceB1684 + difference 5 4) sourceC1684) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1240) := by
    have ha : (tripleCharges (sourceA1684 + difference 4 5) (sourceB1684 + difference 5 4) sourceC1684) = raw24806 := by
      apply Matrix.ext; unfold tripleCharges sourceA1684 sourceB1684 sourceC1684 difference raw24806; decide +kernel
    rw [ha]
    exact (canonical24806 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1684 + difference 5 0) (sourceB1684 + difference 0 5) sourceC1684) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 568) := by
    have ha : (tripleCharges (sourceA1684 + difference 5 0) (sourceB1684 + difference 0 5) sourceC1684) = raw24807 := by
      apply Matrix.ext; unfold tripleCharges sourceA1684 sourceB1684 sourceC1684 difference raw24807; decide +kernel
    rw [ha]
    exact (canonical24807 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1684 + difference 5 1) (sourceB1684 + difference 1 5) sourceC1684) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1105) := by
    have ha : (tripleCharges (sourceA1684 + difference 5 1) (sourceB1684 + difference 1 5) sourceC1684) = raw24808 := by
      apply Matrix.ext; unfold tripleCharges sourceA1684 sourceB1684 sourceC1684 difference raw24808; decide +kernel
    rw [ha]
    exact (canonical24808 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1684 + difference 5 2) (sourceB1684 + difference 2 5) sourceC1684) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1098) := by
    have ha : (tripleCharges (sourceA1684 + difference 5 2) (sourceB1684 + difference 2 5) sourceC1684) = raw24809 := by
      apply Matrix.ext; unfold tripleCharges sourceA1684 sourceB1684 sourceC1684 difference raw24809; decide +kernel
    rw [ha]
    exact (canonical24809 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1684 + difference 5 3) (sourceB1684 + difference 3 5) sourceC1684) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1239) := by
    have ha : (tripleCharges (sourceA1684 + difference 5 3) (sourceB1684 + difference 3 5) sourceC1684) = raw24810 := by
      apply Matrix.ext; unfold tripleCharges sourceA1684 sourceB1684 sourceC1684 difference raw24810; decide +kernel
    rw [ha]
    exact (canonical24810 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1684 + difference 5 4) (sourceB1684 + difference 4 5) sourceC1684) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1202) := by
    have ha : (tripleCharges (sourceA1684 + difference 5 4) (sourceB1684 + difference 4 5) sourceC1684) = raw24811 := by
      apply Matrix.ext; unfold tripleCharges sourceA1684 sourceB1684 sourceC1684 difference raw24811; decide +kernel
    rw [ha]
    exact (canonical24811 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1684 sourceB1684 sourceC1684
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1684, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1685 : Charge := ![2, 0, -1, 0, -1, 0]
def sourceB1685 : Charge := ![2, 0, 1, -1, 0, -2]
def sourceC1685 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1685 : Integer.Sparse Master := [(Sum.inr 4396, 1), (Sum.inr 4418, 1), (Sum.inr 4419, 1), (Sum.inr 4423, 1), (Sum.inr 4439, 1), (Sum.inr 4458, 1), (Sum.inr 4459, 1), (Sum.inr 4461, 1), (Sum.inr 4475, 1), (Sum.inr 4498, 1), (Sum.inr 4561, 1), (Sum.inr 4567, 1), (Sum.inr 4568, 1), (Sum.inr 4570, 1), (Sum.inr 4579, 1), (Sum.inr 4580, 1), (Sum.inr 4581, 1), (Sum.inr 4587, 1), (Sum.inr 4589, 1), (Sum.inr 4590, 1), (Sum.inr 4596, 1), (Sum.inr 4597, 1), (Sum.inr 4600, 1), (Sum.inr 4602, 2), (Sum.inr 4603, 1), (Sum.inr 4606, 1), (Sum.inr 4619, 1), (Sum.inr 4623, 1), (Sum.inr 4624, 1)]

theorem sourceEq1685 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1685 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1685 + difference 0 1) (sourceB1685 + difference 1 0) sourceC1685) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4439) := by
    have ha : (tripleCharges (sourceA1685 + difference 0 1) (sourceB1685 + difference 1 0) sourceC1685) = raw24812 := by
      apply Matrix.ext; unfold tripleCharges sourceA1685 sourceB1685 sourceC1685 difference raw24812; decide +kernel
    rw [ha]
    exact (canonical24812 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1685 + difference 0 2) (sourceB1685 + difference 2 0) sourceC1685) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4475) := by
    have ha : (tripleCharges (sourceA1685 + difference 0 2) (sourceB1685 + difference 2 0) sourceC1685) = raw24813 := by
      apply Matrix.ext; unfold tripleCharges sourceA1685 sourceB1685 sourceC1685 difference raw24813; decide +kernel
    rw [ha]
    exact (canonical24813 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1685 + difference 0 3) (sourceB1685 + difference 3 0) sourceC1685) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4461) := by
    have ha : (tripleCharges (sourceA1685 + difference 0 3) (sourceB1685 + difference 3 0) sourceC1685) = raw24153 := by
      apply Matrix.ext; unfold tripleCharges sourceA1685 sourceB1685 sourceC1685 difference raw24153; decide +kernel
    rw [ha]
    exact (canonical24153 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1685 + difference 0 4) (sourceB1685 + difference 4 0) sourceC1685) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4459) := by
    have ha : (tripleCharges (sourceA1685 + difference 0 4) (sourceB1685 + difference 4 0) sourceC1685) = raw24814 := by
      apply Matrix.ext; unfold tripleCharges sourceA1685 sourceB1685 sourceC1685 difference raw24814; decide +kernel
    rw [ha]
    exact (canonical24814 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1685 + difference 0 5) (sourceB1685 + difference 5 0) sourceC1685) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1685 + difference 0 5) (sourceB1685 + difference 5 0) sourceC1685) = raw24603 := by
      apply Matrix.ext; unfold tripleCharges sourceA1685 sourceB1685 sourceC1685 difference raw24603; decide +kernel
    rw [ha]
    exact (canonical24603 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1685 + difference 1 0) (sourceB1685 + difference 0 1) sourceC1685) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4396) := by
    have ha : (tripleCharges (sourceA1685 + difference 1 0) (sourceB1685 + difference 0 1) sourceC1685) = raw24815 := by
      apply Matrix.ext; unfold tripleCharges sourceA1685 sourceB1685 sourceC1685 difference raw24815; decide +kernel
    rw [ha]
    exact (canonical24815 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1685 + difference 1 2) (sourceB1685 + difference 2 1) sourceC1685) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4561) := by
    have ha : (tripleCharges (sourceA1685 + difference 1 2) (sourceB1685 + difference 2 1) sourceC1685) = raw24816 := by
      apply Matrix.ext; unfold tripleCharges sourceA1685 sourceB1685 sourceC1685 difference raw24816; decide +kernel
    rw [ha]
    exact (canonical24816 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1685 + difference 1 3) (sourceB1685 + difference 3 1) sourceC1685) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4589) := by
    have ha : (tripleCharges (sourceA1685 + difference 1 3) (sourceB1685 + difference 3 1) sourceC1685) = raw24158 := by
      apply Matrix.ext; unfold tripleCharges sourceA1685 sourceB1685 sourceC1685 difference raw24158; decide +kernel
    rw [ha]
    exact (canonical24158 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1685 + difference 1 4) (sourceB1685 + difference 4 1) sourceC1685) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4587) := by
    have ha : (tripleCharges (sourceA1685 + difference 1 4) (sourceB1685 + difference 4 1) sourceC1685) = raw24817 := by
      apply Matrix.ext; unfold tripleCharges sourceA1685 sourceB1685 sourceC1685 difference raw24817; decide +kernel
    rw [ha]
    exact (canonical24817 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1685 + difference 1 5) (sourceB1685 + difference 5 1) sourceC1685) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4590) := by
    have ha : (tripleCharges (sourceA1685 + difference 1 5) (sourceB1685 + difference 5 1) sourceC1685) = raw24607 := by
      apply Matrix.ext; unfold tripleCharges sourceA1685 sourceB1685 sourceC1685 difference raw24607; decide +kernel
    rw [ha]
    exact (canonical24607 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1685 + difference 2 0) (sourceB1685 + difference 0 2) sourceC1685) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4498) := by
    have ha : (tripleCharges (sourceA1685 + difference 2 0) (sourceB1685 + difference 0 2) sourceC1685) = raw24167 := by
      apply Matrix.ext; unfold tripleCharges sourceA1685 sourceB1685 sourceC1685 difference raw24167; decide +kernel
    rw [ha]
    exact (canonical24167 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1685 + difference 2 1) (sourceB1685 + difference 1 2) sourceC1685) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1685 + difference 2 1) (sourceB1685 + difference 1 2) sourceC1685) = raw24168 := by
      apply Matrix.ext; unfold tripleCharges sourceA1685 sourceB1685 sourceC1685 difference raw24168; decide +kernel
    rw [ha]
    exact (canonical24168 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1685 + difference 2 3) (sourceB1685 + difference 3 2) sourceC1685) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4623) := by
    have ha : (tripleCharges (sourceA1685 + difference 2 3) (sourceB1685 + difference 3 2) sourceC1685) = raw24269 := by
      apply Matrix.ext; unfold tripleCharges sourceA1685 sourceB1685 sourceC1685 difference raw24269; decide +kernel
    rw [ha]
    exact (canonical24269 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1685 + difference 2 4) (sourceB1685 + difference 4 2) sourceC1685) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4619) := by
    have ha : (tripleCharges (sourceA1685 + difference 2 4) (sourceB1685 + difference 4 2) sourceC1685) = raw24170 := by
      apply Matrix.ext; unfold tripleCharges sourceA1685 sourceB1685 sourceC1685 difference raw24170; decide +kernel
    rw [ha]
    exact (canonical24170 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1685 + difference 2 5) (sourceB1685 + difference 5 2) sourceC1685) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4624) := by
    have ha : (tripleCharges (sourceA1685 + difference 2 5) (sourceB1685 + difference 5 2) sourceC1685) = raw24171 := by
      apply Matrix.ext; unfold tripleCharges sourceA1685 sourceB1685 sourceC1685 difference raw24171; decide +kernel
    rw [ha]
    exact (canonical24171 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1685 + difference 3 0) (sourceB1685 + difference 0 3) sourceC1685) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4419) := by
    have ha : (tripleCharges (sourceA1685 + difference 3 0) (sourceB1685 + difference 0 3) sourceC1685) = raw24818 := by
      apply Matrix.ext; unfold tripleCharges sourceA1685 sourceB1685 sourceC1685 difference raw24818; decide +kernel
    rw [ha]
    exact (canonical24818 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1685 + difference 3 1) (sourceB1685 + difference 1 3) sourceC1685) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4580) := by
    have ha : (tripleCharges (sourceA1685 + difference 3 1) (sourceB1685 + difference 1 3) sourceC1685) = raw24819 := by
      apply Matrix.ext; unfold tripleCharges sourceA1685 sourceB1685 sourceC1685 difference raw24819; decide +kernel
    rw [ha]
    exact (canonical24819 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1685 + difference 3 2) (sourceB1685 + difference 2 3) sourceC1685) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4568) := by
    have ha : (tripleCharges (sourceA1685 + difference 3 2) (sourceB1685 + difference 2 3) sourceC1685) = raw24820 := by
      apply Matrix.ext; unfold tripleCharges sourceA1685 sourceB1685 sourceC1685 difference raw24820; decide +kernel
    rw [ha]
    exact (canonical24820 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1685 + difference 3 4) (sourceB1685 + difference 4 3) sourceC1685) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4597) := by
    have ha : (tripleCharges (sourceA1685 + difference 3 4) (sourceB1685 + difference 4 3) sourceC1685) = raw24821 := by
      apply Matrix.ext; unfold tripleCharges sourceA1685 sourceB1685 sourceC1685 difference raw24821; decide +kernel
    rw [ha]
    exact (canonical24821 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1685 + difference 3 5) (sourceB1685 + difference 5 3) sourceC1685) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4603) := by
    have ha : (tripleCharges (sourceA1685 + difference 3 5) (sourceB1685 + difference 5 3) sourceC1685) = raw24612 := by
      apply Matrix.ext; unfold tripleCharges sourceA1685 sourceB1685 sourceC1685 difference raw24612; decide +kernel
    rw [ha]
    exact (canonical24612 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1685 + difference 4 0) (sourceB1685 + difference 0 4) sourceC1685) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4423) := by
    have ha : (tripleCharges (sourceA1685 + difference 4 0) (sourceB1685 + difference 0 4) sourceC1685) = raw24617 := by
      apply Matrix.ext; unfold tripleCharges sourceA1685 sourceB1685 sourceC1685 difference raw24617; decide +kernel
    rw [ha]
    exact (canonical24617 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1685 + difference 4 1) (sourceB1685 + difference 1 4) sourceC1685) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4581) := by
    have ha : (tripleCharges (sourceA1685 + difference 4 1) (sourceB1685 + difference 1 4) sourceC1685) = raw24618 := by
      apply Matrix.ext; unfold tripleCharges sourceA1685 sourceB1685 sourceC1685 difference raw24618; decide +kernel
    rw [ha]
    exact (canonical24618 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1685 + difference 4 2) (sourceB1685 + difference 2 4) sourceC1685) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4570) := by
    have ha : (tripleCharges (sourceA1685 + difference 4 2) (sourceB1685 + difference 2 4) sourceC1685) = raw24619 := by
      apply Matrix.ext; unfold tripleCharges sourceA1685 sourceB1685 sourceC1685 difference raw24619; decide +kernel
    rw [ha]
    exact (canonical24619 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1685 + difference 4 3) (sourceB1685 + difference 3 4) sourceC1685) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1685 + difference 4 3) (sourceB1685 + difference 3 4) sourceC1685) = raw24174 := by
      apply Matrix.ext; unfold tripleCharges sourceA1685 sourceB1685 sourceC1685 difference raw24174; decide +kernel
    rw [ha]
    exact (canonical24174 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1685 + difference 4 5) (sourceB1685 + difference 5 4) sourceC1685) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4606) := by
    have ha : (tripleCharges (sourceA1685 + difference 4 5) (sourceB1685 + difference 5 4) sourceC1685) = raw24262 := by
      apply Matrix.ext; unfold tripleCharges sourceA1685 sourceB1685 sourceC1685 difference raw24262; decide +kernel
    rw [ha]
    exact (canonical24262 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1685 + difference 5 0) (sourceB1685 + difference 0 5) sourceC1685) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4418) := by
    have ha : (tripleCharges (sourceA1685 + difference 5 0) (sourceB1685 + difference 0 5) sourceC1685) = raw24822 := by
      apply Matrix.ext; unfold tripleCharges sourceA1685 sourceB1685 sourceC1685 difference raw24822; decide +kernel
    rw [ha]
    exact (canonical24822 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1685 + difference 5 1) (sourceB1685 + difference 1 5) sourceC1685) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4579) := by
    have ha : (tripleCharges (sourceA1685 + difference 5 1) (sourceB1685 + difference 1 5) sourceC1685) = raw24823 := by
      apply Matrix.ext; unfold tripleCharges sourceA1685 sourceB1685 sourceC1685 difference raw24823; decide +kernel
    rw [ha]
    exact (canonical24823 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1685 + difference 5 2) (sourceB1685 + difference 2 5) sourceC1685) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4567) := by
    have ha : (tripleCharges (sourceA1685 + difference 5 2) (sourceB1685 + difference 2 5) sourceC1685) = raw24824 := by
      apply Matrix.ext; unfold tripleCharges sourceA1685 sourceB1685 sourceC1685 difference raw24824; decide +kernel
    rw [ha]
    exact (canonical24824 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1685 + difference 5 3) (sourceB1685 + difference 3 5) sourceC1685) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4600) := by
    have ha : (tripleCharges (sourceA1685 + difference 5 3) (sourceB1685 + difference 3 5) sourceC1685) = raw24179 := by
      apply Matrix.ext; unfold tripleCharges sourceA1685 sourceB1685 sourceC1685 difference raw24179; decide +kernel
    rw [ha]
    exact (canonical24179 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1685 + difference 5 4) (sourceB1685 + difference 4 5) sourceC1685) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4596) := by
    have ha : (tripleCharges (sourceA1685 + difference 5 4) (sourceB1685 + difference 4 5) sourceC1685) = raw24825 := by
      apply Matrix.ext; unfold tripleCharges sourceA1685 sourceB1685 sourceC1685 difference raw24825; decide +kernel
    rw [ha]
    exact (canonical24825 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1685 sourceB1685 sourceC1685
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1685, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1686 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1686 : Charge := ![2, 0, -1, 0, -2, 1]
def sourceC1686 : Charge := ![2, 0, 1, -1, 1, -3]
def sourceForm1686 : Integer.Sparse Master := [(Sum.inr 1229, 1), (Sum.inr 2504, 1), (Sum.inr 2550, 1), (Sum.inr 2704, 1), (Sum.inr 2719, 1), (Sum.inr 2735, 1), (Sum.inr 4080, -1)]

theorem sourceEq1686 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1686 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1686 + difference 0 0) (sourceB1686 + difference 0 0) sourceC1686) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1229) := by
    have ha : (tripleCharges (sourceA1686 + difference 0 0) (sourceB1686 + difference 0 0) sourceC1686) = raw24826 := by
      apply Matrix.ext; unfold tripleCharges sourceA1686 sourceB1686 sourceC1686 difference raw24826; decide +kernel
    rw [ha]
    exact (canonical24826 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1686 + difference 0 1) (sourceB1686 + difference 1 0) sourceC1686) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2550) := by
    have ha : (tripleCharges (sourceA1686 + difference 0 1) (sourceB1686 + difference 1 0) sourceC1686) = raw24827 := by
      apply Matrix.ext; unfold tripleCharges sourceA1686 sourceB1686 sourceC1686 difference raw24827; decide +kernel
    rw [ha]
    exact (canonical24827 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1686 + difference 0 2) (sourceB1686 + difference 2 0) sourceC1686) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2504) := by
    have ha : (tripleCharges (sourceA1686 + difference 0 2) (sourceB1686 + difference 2 0) sourceC1686) = raw24828 := by
      apply Matrix.ext; unfold tripleCharges sourceA1686 sourceB1686 sourceC1686 difference raw24828; decide +kernel
    rw [ha]
    exact (canonical24828 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1686 + difference 0 3) (sourceB1686 + difference 3 0) sourceC1686) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2719) := by
    have ha : (tripleCharges (sourceA1686 + difference 0 3) (sourceB1686 + difference 3 0) sourceC1686) = raw24829 := by
      apply Matrix.ext; unfold tripleCharges sourceA1686 sourceB1686 sourceC1686 difference raw24829; decide +kernel
    rw [ha]
    exact (canonical24829 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1686 + difference 0 4) (sourceB1686 + difference 4 0) sourceC1686) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2704) := by
    have ha : (tripleCharges (sourceA1686 + difference 0 4) (sourceB1686 + difference 4 0) sourceC1686) = raw24830 := by
      apply Matrix.ext; unfold tripleCharges sourceA1686 sourceB1686 sourceC1686 difference raw24830; decide +kernel
    rw [ha]
    exact (canonical24830 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1686 + difference 0 5) (sourceB1686 + difference 5 0) sourceC1686) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2735) := by
    have ha : (tripleCharges (sourceA1686 + difference 0 5) (sourceB1686 + difference 5 0) sourceC1686) = raw24831 := by
      apply Matrix.ext; unfold tripleCharges sourceA1686 sourceB1686 sourceC1686 difference raw24831; decide +kernel
    rw [ha]
    exact (canonical24831 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1686 + sourceB1686) sourceC1686) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1686 + sourceB1686) sourceC1686) = raw24832 := by
      apply Matrix.ext; unfold doubleCharges sourceA1686 sourceB1686 sourceC1686 raw24832; decide +kernel
    rw [ha]
    exact (canonical24832 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1686 sourceB1686 sourceC1686
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1686, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1687 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1687 : Charge := ![2, 0, -2, 1, 0, -1]
def sourceC1687 : Charge := ![2, 0, 2, -2, -1, -1]
def sourceForm1687 : Integer.Sparse Master := [(Sum.inr 1189, 1), (Sum.inr 2404, 1), (Sum.inr 2537, 1), (Sum.inr 2673, 1), (Sum.inr 2678, 1), (Sum.inr 2684, 1), (Sum.inr 4088, -1)]

theorem sourceEq1687 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1687 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1687 + difference 0 0) (sourceB1687 + difference 0 0) sourceC1687) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1189) := by
    have ha : (tripleCharges (sourceA1687 + difference 0 0) (sourceB1687 + difference 0 0) sourceC1687) = raw24833 := by
      apply Matrix.ext; unfold tripleCharges sourceA1687 sourceB1687 sourceC1687 difference raw24833; decide +kernel
    rw [ha]
    exact (canonical24833 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1687 + difference 0 1) (sourceB1687 + difference 1 0) sourceC1687) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2537) := by
    have ha : (tripleCharges (sourceA1687 + difference 0 1) (sourceB1687 + difference 1 0) sourceC1687) = raw24834 := by
      apply Matrix.ext; unfold tripleCharges sourceA1687 sourceB1687 sourceC1687 difference raw24834; decide +kernel
    rw [ha]
    exact (canonical24834 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1687 + difference 0 2) (sourceB1687 + difference 2 0) sourceC1687) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2404) := by
    have ha : (tripleCharges (sourceA1687 + difference 0 2) (sourceB1687 + difference 2 0) sourceC1687) = raw24835 := by
      apply Matrix.ext; unfold tripleCharges sourceA1687 sourceB1687 sourceC1687 difference raw24835; decide +kernel
    rw [ha]
    exact (canonical24835 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1687 + difference 0 3) (sourceB1687 + difference 3 0) sourceC1687) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2678) := by
    have ha : (tripleCharges (sourceA1687 + difference 0 3) (sourceB1687 + difference 3 0) sourceC1687) = raw24836 := by
      apply Matrix.ext; unfold tripleCharges sourceA1687 sourceB1687 sourceC1687 difference raw24836; decide +kernel
    rw [ha]
    exact (canonical24836 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1687 + difference 0 4) (sourceB1687 + difference 4 0) sourceC1687) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2673) := by
    have ha : (tripleCharges (sourceA1687 + difference 0 4) (sourceB1687 + difference 4 0) sourceC1687) = raw24837 := by
      apply Matrix.ext; unfold tripleCharges sourceA1687 sourceB1687 sourceC1687 difference raw24837; decide +kernel
    rw [ha]
    exact (canonical24837 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1687 + difference 0 5) (sourceB1687 + difference 5 0) sourceC1687) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2684) := by
    have ha : (tripleCharges (sourceA1687 + difference 0 5) (sourceB1687 + difference 5 0) sourceC1687) = raw24838 := by
      apply Matrix.ext; unfold tripleCharges sourceA1687 sourceB1687 sourceC1687 difference raw24838; decide +kernel
    rw [ha]
    exact (canonical24838 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1687 + sourceB1687) sourceC1687) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA1687 + sourceB1687) sourceC1687) = raw24839 := by
      apply Matrix.ext; unfold doubleCharges sourceA1687 sourceB1687 sourceC1687 raw24839; decide +kernel
    rw [ha]
    exact (canonical24839 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1687 sourceB1687 sourceC1687
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1687, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1688 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1688 : Charge := ![2, 0, -2, 1, 0, -1]
def sourceC1688 : Charge := ![2, 0, 2, -2, -1, -1]
def sourceForm1688 : Integer.Sparse Master := [(Sum.inr 1183, 1), (Sum.inr 1188, 1), (Sum.inr 1189, 2), (Sum.inr 1286, 1), (Sum.inr 2684, 1), (Sum.inr 4088, -1)]

theorem sourceEq1688 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1688 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1688 + difference 0 5) (sourceB1688 + difference 5 0) sourceC1688) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2684) := by
    have ha : (tripleCharges (sourceA1688 + difference 0 5) (sourceB1688 + difference 5 0) sourceC1688) = raw24838 := by
      apply Matrix.ext; unfold tripleCharges sourceA1688 sourceB1688 sourceC1688 difference raw24838; decide +kernel
    rw [ha]
    exact (canonical24838 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1688 + difference 1 5) (sourceB1688 + difference 5 1) sourceC1688) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1183) := by
    have ha : (tripleCharges (sourceA1688 + difference 1 5) (sourceB1688 + difference 5 1) sourceC1688) = raw24840 := by
      apply Matrix.ext; unfold tripleCharges sourceA1688 sourceB1688 sourceC1688 difference raw24840; decide +kernel
    rw [ha]
    exact (canonical24840 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1688 + difference 2 5) (sourceB1688 + difference 5 2) sourceC1688) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1286) := by
    have ha : (tripleCharges (sourceA1688 + difference 2 5) (sourceB1688 + difference 5 2) sourceC1688) = raw24841 := by
      apply Matrix.ext; unfold tripleCharges sourceA1688 sourceB1688 sourceC1688 difference raw24841; decide +kernel
    rw [ha]
    exact (canonical24841 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1688 + difference 3 5) (sourceB1688 + difference 5 3) sourceC1688) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1188) := by
    have ha : (tripleCharges (sourceA1688 + difference 3 5) (sourceB1688 + difference 5 3) sourceC1688) = raw24842 := by
      apply Matrix.ext; unfold tripleCharges sourceA1688 sourceB1688 sourceC1688 difference raw24842; decide +kernel
    rw [ha]
    exact (canonical24842 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1688 + difference 4 5) (sourceB1688 + difference 5 4) sourceC1688) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1189) := by
    have ha : (tripleCharges (sourceA1688 + difference 4 5) (sourceB1688 + difference 5 4) sourceC1688) = raw24843 := by
      apply Matrix.ext; unfold tripleCharges sourceA1688 sourceB1688 sourceC1688 difference raw24843; decide +kernel
    rw [ha]
    exact (canonical24843 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1688 + difference 5 5) (sourceB1688 + difference 5 5) sourceC1688) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1189) := by
    have ha : (tripleCharges (sourceA1688 + difference 5 5) (sourceB1688 + difference 5 5) sourceC1688) = raw24833 := by
      apply Matrix.ext; unfold tripleCharges sourceA1688 sourceB1688 sourceC1688 difference raw24833; decide +kernel
    rw [ha]
    exact (canonical24833 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1688 + sourceB1688) sourceC1688) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA1688 + sourceB1688) sourceC1688) = raw24839 := by
      apply Matrix.ext; unfold doubleCharges sourceA1688 sourceB1688 sourceC1688 raw24839; decide +kernel
    rw [ha]
    exact (canonical24839 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1688 sourceB1688 sourceC1688
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1688, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1689 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1689 : Charge := ![2, 0, -2, 1, -1, 0]
def sourceC1689 : Charge := ![2, 0, 2, -2, 0, -2]
def sourceForm1689 : Integer.Sparse Master := [(Sum.inr 1185, 1), (Sum.inr 2400, 1), (Sum.inr 2535, 1), (Sum.inr 2677, 1), (Sum.inr 2682, 1), (Sum.inr 2686, 1), (Sum.inr 4089, -1)]

theorem sourceEq1689 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1689 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1689 + difference 0 0) (sourceB1689 + difference 0 0) sourceC1689) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1185) := by
    have ha : (tripleCharges (sourceA1689 + difference 0 0) (sourceB1689 + difference 0 0) sourceC1689) = raw24844 := by
      apply Matrix.ext; unfold tripleCharges sourceA1689 sourceB1689 sourceC1689 difference raw24844; decide +kernel
    rw [ha]
    exact (canonical24844 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1689 + difference 0 1) (sourceB1689 + difference 1 0) sourceC1689) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2535) := by
    have ha : (tripleCharges (sourceA1689 + difference 0 1) (sourceB1689 + difference 1 0) sourceC1689) = raw24845 := by
      apply Matrix.ext; unfold tripleCharges sourceA1689 sourceB1689 sourceC1689 difference raw24845; decide +kernel
    rw [ha]
    exact (canonical24845 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1689 + difference 0 2) (sourceB1689 + difference 2 0) sourceC1689) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2400) := by
    have ha : (tripleCharges (sourceA1689 + difference 0 2) (sourceB1689 + difference 2 0) sourceC1689) = raw24846 := by
      apply Matrix.ext; unfold tripleCharges sourceA1689 sourceB1689 sourceC1689 difference raw24846; decide +kernel
    rw [ha]
    exact (canonical24846 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1689 + difference 0 3) (sourceB1689 + difference 3 0) sourceC1689) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2677) := by
    have ha : (tripleCharges (sourceA1689 + difference 0 3) (sourceB1689 + difference 3 0) sourceC1689) = raw24847 := by
      apply Matrix.ext; unfold tripleCharges sourceA1689 sourceB1689 sourceC1689 difference raw24847; decide +kernel
    rw [ha]
    exact (canonical24847 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1689 + difference 0 4) (sourceB1689 + difference 4 0) sourceC1689) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2686) := by
    have ha : (tripleCharges (sourceA1689 + difference 0 4) (sourceB1689 + difference 4 0) sourceC1689) = raw24848 := by
      apply Matrix.ext; unfold tripleCharges sourceA1689 sourceB1689 sourceC1689 difference raw24848; decide +kernel
    rw [ha]
    exact (canonical24848 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1689 + difference 0 5) (sourceB1689 + difference 5 0) sourceC1689) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2682) := by
    have ha : (tripleCharges (sourceA1689 + difference 0 5) (sourceB1689 + difference 5 0) sourceC1689) = raw24849 := by
      apply Matrix.ext; unfold tripleCharges sourceA1689 sourceB1689 sourceC1689 difference raw24849; decide +kernel
    rw [ha]
    exact (canonical24849 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1689 + sourceB1689) sourceC1689) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4089) := by
    have ha : (doubleCharges (sourceA1689 + sourceB1689) sourceC1689) = raw24850 := by
      apply Matrix.ext; unfold doubleCharges sourceA1689 sourceB1689 sourceC1689 raw24850; decide +kernel
    rw [ha]
    exact (canonical24850 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1689 sourceB1689 sourceC1689
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1689, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1690 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1690 : Charge := ![2, 0, -2, 0, 0, 0]
def sourceC1690 : Charge := ![2, 0, 2, -1, -1, -2]
def sourceForm1690 : Integer.Sparse Master := [(Sum.inr 1188, 1), (Sum.inr 2403, 1), (Sum.inr 2536, 1), (Sum.inr 2672, 2), (Sum.inr 2684, 1), (Sum.inr 4088, -1)]

theorem sourceEq1690 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1690 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1690 + difference 0 0) (sourceB1690 + difference 0 0) sourceC1690) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1188) := by
    have ha : (tripleCharges (sourceA1690 + difference 0 0) (sourceB1690 + difference 0 0) sourceC1690) = raw24851 := by
      apply Matrix.ext; unfold tripleCharges sourceA1690 sourceB1690 sourceC1690 difference raw24851; decide +kernel
    rw [ha]
    exact (canonical24851 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1690 + difference 0 1) (sourceB1690 + difference 1 0) sourceC1690) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2536) := by
    have ha : (tripleCharges (sourceA1690 + difference 0 1) (sourceB1690 + difference 1 0) sourceC1690) = raw24852 := by
      apply Matrix.ext; unfold tripleCharges sourceA1690 sourceB1690 sourceC1690 difference raw24852; decide +kernel
    rw [ha]
    exact (canonical24852 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1690 + difference 0 2) (sourceB1690 + difference 2 0) sourceC1690) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2403) := by
    have ha : (tripleCharges (sourceA1690 + difference 0 2) (sourceB1690 + difference 2 0) sourceC1690) = raw24853 := by
      apply Matrix.ext; unfold tripleCharges sourceA1690 sourceB1690 sourceC1690 difference raw24853; decide +kernel
    rw [ha]
    exact (canonical24853 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1690 + difference 0 3) (sourceB1690 + difference 3 0) sourceC1690) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2672) := by
    have ha : (tripleCharges (sourceA1690 + difference 0 3) (sourceB1690 + difference 3 0) sourceC1690) = raw24854 := by
      apply Matrix.ext; unfold tripleCharges sourceA1690 sourceB1690 sourceC1690 difference raw24854; decide +kernel
    rw [ha]
    exact (canonical24854 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1690 + difference 0 4) (sourceB1690 + difference 4 0) sourceC1690) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2672) := by
    have ha : (tripleCharges (sourceA1690 + difference 0 4) (sourceB1690 + difference 4 0) sourceC1690) = raw24855 := by
      apply Matrix.ext; unfold tripleCharges sourceA1690 sourceB1690 sourceC1690 difference raw24855; decide +kernel
    rw [ha]
    exact (canonical24855 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1690 + difference 0 5) (sourceB1690 + difference 5 0) sourceC1690) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2684) := by
    have ha : (tripleCharges (sourceA1690 + difference 0 5) (sourceB1690 + difference 5 0) sourceC1690) = raw24856 := by
      apply Matrix.ext; unfold tripleCharges sourceA1690 sourceB1690 sourceC1690 difference raw24856; decide +kernel
    rw [ha]
    exact (canonical24856 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1690 + sourceB1690) sourceC1690) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA1690 + sourceB1690) sourceC1690) = raw24857 := by
      apply Matrix.ext; unfold doubleCharges sourceA1690 sourceB1690 sourceC1690 raw24857; decide +kernel
    rw [ha]
    exact (canonical24857 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1690 sourceB1690 sourceC1690
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1690, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1691 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1691 : Charge := ![2, 0, -2, 0, 0, 0]
def sourceC1691 : Charge := ![2, 0, 2, -1, -1, -2]
def sourceForm1691 : Integer.Sparse Master := [(Sum.inr 1097, 1), (Sum.inr 1101, 1), (Sum.inr 1102, 2), (Sum.inr 1188, 1), (Sum.inr 2403, 1), (Sum.inr 4088, -1)]

theorem sourceEq1691 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1691 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1691 + difference 0 2) (sourceB1691 + difference 2 0) sourceC1691) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2403) := by
    have ha : (tripleCharges (sourceA1691 + difference 0 2) (sourceB1691 + difference 2 0) sourceC1691) = raw24853 := by
      apply Matrix.ext; unfold tripleCharges sourceA1691 sourceB1691 sourceC1691 difference raw24853; decide +kernel
    rw [ha]
    exact (canonical24853 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1691 + difference 1 2) (sourceB1691 + difference 2 1) sourceC1691) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1097) := by
    have ha : (tripleCharges (sourceA1691 + difference 1 2) (sourceB1691 + difference 2 1) sourceC1691) = raw24858 := by
      apply Matrix.ext; unfold tripleCharges sourceA1691 sourceB1691 sourceC1691 difference raw24858; decide +kernel
    rw [ha]
    exact (canonical24858 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1691 + difference 2 2) (sourceB1691 + difference 2 2) sourceC1691) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1188) := by
    have ha : (tripleCharges (sourceA1691 + difference 2 2) (sourceB1691 + difference 2 2) sourceC1691) = raw24851 := by
      apply Matrix.ext; unfold tripleCharges sourceA1691 sourceB1691 sourceC1691 difference raw24851; decide +kernel
    rw [ha]
    exact (canonical24851 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1691 + difference 3 2) (sourceB1691 + difference 2 3) sourceC1691) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1102) := by
    have ha : (tripleCharges (sourceA1691 + difference 3 2) (sourceB1691 + difference 2 3) sourceC1691) = raw24859 := by
      apply Matrix.ext; unfold tripleCharges sourceA1691 sourceB1691 sourceC1691 difference raw24859; decide +kernel
    rw [ha]
    exact (canonical24859 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1691 + difference 4 2) (sourceB1691 + difference 2 4) sourceC1691) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1102) := by
    have ha : (tripleCharges (sourceA1691 + difference 4 2) (sourceB1691 + difference 2 4) sourceC1691) = raw24860 := by
      apply Matrix.ext; unfold tripleCharges sourceA1691 sourceB1691 sourceC1691 difference raw24860; decide +kernel
    rw [ha]
    exact (canonical24860 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1691 + difference 5 2) (sourceB1691 + difference 2 5) sourceC1691) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1101) := by
    have ha : (tripleCharges (sourceA1691 + difference 5 2) (sourceB1691 + difference 2 5) sourceC1691) = raw24861 := by
      apply Matrix.ext; unfold tripleCharges sourceA1691 sourceB1691 sourceC1691 difference raw24861; decide +kernel
    rw [ha]
    exact (canonical24861 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1691 + sourceB1691) sourceC1691) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA1691 + sourceB1691) sourceC1691) = raw24857 := by
      apply Matrix.ext; unfold doubleCharges sourceA1691 sourceB1691 sourceC1691 raw24857; decide +kernel
    rw [ha]
    exact (canonical24857 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1691 sourceB1691 sourceC1691
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1691, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1692 : Charge := ![2, 0, -2, 0, 0, 0]
def sourceB1692 : Charge := ![2, 0, 2, -1, -1, -2]
def sourceC1692 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1692 : Integer.Sparse Master := [(Sum.inr 1542, 1), (Sum.inr 1546, 1), (Sum.inr 1547, 2), (Sum.inr 1622, 1), (Sum.inr 3245, 1), (Sum.inr 4069, -1)]

theorem sourceEq1692 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1692 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1692 + difference 0 0) (sourceB1692 + difference 0 0) sourceC1692) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3245) := by
    have ha : (tripleCharges (sourceA1692 + difference 0 0) (sourceB1692 + difference 0 0) sourceC1692) = raw24862 := by
      apply Matrix.ext; unfold tripleCharges sourceA1692 sourceB1692 sourceC1692 difference raw24862; decide +kernel
    rw [ha]
    exact (canonical24862 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1692 + difference 1 0) (sourceB1692 + difference 0 1) sourceC1692) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1542) := by
    have ha : (tripleCharges (sourceA1692 + difference 1 0) (sourceB1692 + difference 0 1) sourceC1692) = raw24863 := by
      apply Matrix.ext; unfold tripleCharges sourceA1692 sourceB1692 sourceC1692 difference raw24863; decide +kernel
    rw [ha]
    exact (canonical24863 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1692 + difference 2 0) (sourceB1692 + difference 0 2) sourceC1692) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1622) := by
    have ha : (tripleCharges (sourceA1692 + difference 2 0) (sourceB1692 + difference 0 2) sourceC1692) = raw24864 := by
      apply Matrix.ext; unfold tripleCharges sourceA1692 sourceB1692 sourceC1692 difference raw24864; decide +kernel
    rw [ha]
    exact (canonical24864 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1692 + difference 3 0) (sourceB1692 + difference 0 3) sourceC1692) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1547) := by
    have ha : (tripleCharges (sourceA1692 + difference 3 0) (sourceB1692 + difference 0 3) sourceC1692) = raw24865 := by
      apply Matrix.ext; unfold tripleCharges sourceA1692 sourceB1692 sourceC1692 difference raw24865; decide +kernel
    rw [ha]
    exact (canonical24865 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1692 + difference 4 0) (sourceB1692 + difference 0 4) sourceC1692) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1547) := by
    have ha : (tripleCharges (sourceA1692 + difference 4 0) (sourceB1692 + difference 0 4) sourceC1692) = raw24866 := by
      apply Matrix.ext; unfold tripleCharges sourceA1692 sourceB1692 sourceC1692 difference raw24866; decide +kernel
    rw [ha]
    exact (canonical24866 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1692 + difference 5 0) (sourceB1692 + difference 0 5) sourceC1692) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1546) := by
    have ha : (tripleCharges (sourceA1692 + difference 5 0) (sourceB1692 + difference 0 5) sourceC1692) = raw24867 := by
      apply Matrix.ext; unfold tripleCharges sourceA1692 sourceB1692 sourceC1692 difference raw24867; decide +kernel
    rw [ha]
    exact (canonical24867 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1692 + sourceB1692) sourceC1692) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1692 + sourceB1692) sourceC1692) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1692 sourceB1692 sourceC1692 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1692 sourceB1692 sourceC1692
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1692, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1693 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1693 : Charge := ![2, 0, -2, 0, -1, 1]
def sourceC1693 : Charge := ![2, 0, 2, -1, 0, -3]
def sourceForm1693 : Integer.Sparse Master := [(Sum.inr 1184, 1), (Sum.inr 2399, 1), (Sum.inr 2534, 1), (Sum.inr 2670, 1), (Sum.inr 2681, 1), (Sum.inr 2685, 1), (Sum.inr 4082, -1)]

theorem sourceEq1693 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1693 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1693 + difference 0 0) (sourceB1693 + difference 0 0) sourceC1693) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1184) := by
    have ha : (tripleCharges (sourceA1693 + difference 0 0) (sourceB1693 + difference 0 0) sourceC1693) = raw24868 := by
      apply Matrix.ext; unfold tripleCharges sourceA1693 sourceB1693 sourceC1693 difference raw24868; decide +kernel
    rw [ha]
    exact (canonical24868 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1693 + difference 0 1) (sourceB1693 + difference 1 0) sourceC1693) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2534) := by
    have ha : (tripleCharges (sourceA1693 + difference 0 1) (sourceB1693 + difference 1 0) sourceC1693) = raw24869 := by
      apply Matrix.ext; unfold tripleCharges sourceA1693 sourceB1693 sourceC1693 difference raw24869; decide +kernel
    rw [ha]
    exact (canonical24869 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1693 + difference 0 2) (sourceB1693 + difference 2 0) sourceC1693) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2399) := by
    have ha : (tripleCharges (sourceA1693 + difference 0 2) (sourceB1693 + difference 2 0) sourceC1693) = raw24870 := by
      apply Matrix.ext; unfold tripleCharges sourceA1693 sourceB1693 sourceC1693 difference raw24870; decide +kernel
    rw [ha]
    exact (canonical24870 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1693 + difference 0 3) (sourceB1693 + difference 3 0) sourceC1693) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2670) := by
    have ha : (tripleCharges (sourceA1693 + difference 0 3) (sourceB1693 + difference 3 0) sourceC1693) = raw24871 := by
      apply Matrix.ext; unfold tripleCharges sourceA1693 sourceB1693 sourceC1693 difference raw24871; decide +kernel
    rw [ha]
    exact (canonical24871 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1693 + difference 0 4) (sourceB1693 + difference 4 0) sourceC1693) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2685) := by
    have ha : (tripleCharges (sourceA1693 + difference 0 4) (sourceB1693 + difference 4 0) sourceC1693) = raw24872 := by
      apply Matrix.ext; unfold tripleCharges sourceA1693 sourceB1693 sourceC1693 difference raw24872; decide +kernel
    rw [ha]
    exact (canonical24872 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1693 + difference 0 5) (sourceB1693 + difference 5 0) sourceC1693) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2681) := by
    have ha : (tripleCharges (sourceA1693 + difference 0 5) (sourceB1693 + difference 5 0) sourceC1693) = raw24873 := by
      apply Matrix.ext; unfold tripleCharges sourceA1693 sourceB1693 sourceC1693 difference raw24873; decide +kernel
    rw [ha]
    exact (canonical24873 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1693 + sourceB1693) sourceC1693) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA1693 + sourceB1693) sourceC1693) = raw24874 := by
      apply Matrix.ext; unfold doubleCharges sourceA1693 sourceB1693 sourceC1693 raw24874; decide +kernel
    rw [ha]
    exact (canonical24874 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1693 sourceB1693 sourceC1693
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1693, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1694 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1694 : Charge := ![2, -1, -1, 1, 0, -1]
def sourceC1694 : Charge := ![2, 1, 1, -2, -1, -1]
def sourceForm1694 : Integer.Sparse Master := [(Sum.inr 1201, 1), (Sum.inr 2462, 2), (Sum.inr 2695, 1), (Sum.inr 2698, 1), (Sum.inr 2703, 1), (Sum.inr 4090, -1)]

theorem sourceEq1694 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1694 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1694 + difference 0 0) (sourceB1694 + difference 0 0) sourceC1694) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1201) := by
    have ha : (tripleCharges (sourceA1694 + difference 0 0) (sourceB1694 + difference 0 0) sourceC1694) = raw24875 := by
      apply Matrix.ext; unfold tripleCharges sourceA1694 sourceB1694 sourceC1694 difference raw24875; decide +kernel
    rw [ha]
    exact (canonical24875 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1694 + difference 0 1) (sourceB1694 + difference 1 0) sourceC1694) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2462) := by
    have ha : (tripleCharges (sourceA1694 + difference 0 1) (sourceB1694 + difference 1 0) sourceC1694) = raw24876 := by
      apply Matrix.ext; unfold tripleCharges sourceA1694 sourceB1694 sourceC1694 difference raw24876; decide +kernel
    rw [ha]
    exact (canonical24876 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1694 + difference 0 2) (sourceB1694 + difference 2 0) sourceC1694) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2462) := by
    have ha : (tripleCharges (sourceA1694 + difference 0 2) (sourceB1694 + difference 2 0) sourceC1694) = raw24877 := by
      apply Matrix.ext; unfold tripleCharges sourceA1694 sourceB1694 sourceC1694 difference raw24877; decide +kernel
    rw [ha]
    exact (canonical24877 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1694 + difference 0 3) (sourceB1694 + difference 3 0) sourceC1694) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2698) := by
    have ha : (tripleCharges (sourceA1694 + difference 0 3) (sourceB1694 + difference 3 0) sourceC1694) = raw24878 := by
      apply Matrix.ext; unfold tripleCharges sourceA1694 sourceB1694 sourceC1694 difference raw24878; decide +kernel
    rw [ha]
    exact (canonical24878 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1694 + difference 0 4) (sourceB1694 + difference 4 0) sourceC1694) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2695) := by
    have ha : (tripleCharges (sourceA1694 + difference 0 4) (sourceB1694 + difference 4 0) sourceC1694) = raw24879 := by
      apply Matrix.ext; unfold tripleCharges sourceA1694 sourceB1694 sourceC1694 difference raw24879; decide +kernel
    rw [ha]
    exact (canonical24879 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1694 + difference 0 5) (sourceB1694 + difference 5 0) sourceC1694) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2703) := by
    have ha : (tripleCharges (sourceA1694 + difference 0 5) (sourceB1694 + difference 5 0) sourceC1694) = raw24880 := by
      apply Matrix.ext; unfold tripleCharges sourceA1694 sourceB1694 sourceC1694 difference raw24880; decide +kernel
    rw [ha]
    exact (canonical24880 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1694 + sourceB1694) sourceC1694) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (doubleCharges (sourceA1694 + sourceB1694) sourceC1694) = raw24881 := by
      apply Matrix.ext; unfold doubleCharges sourceA1694 sourceB1694 sourceC1694 raw24881; decide +kernel
    rw [ha]
    exact (canonical24881 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1694 sourceB1694 sourceC1694
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1694, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1695 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1695 : Charge := ![2, -1, -1, 1, 0, -1]
def sourceC1695 : Charge := ![2, 1, 1, -2, -1, -1]
def sourceForm1695 : Integer.Sparse Master := [(Sum.inr 1200, 1), (Sum.inr 1201, 2), (Sum.inr 1228, 2), (Sum.inr 2703, 1), (Sum.inr 4090, -1)]

theorem sourceEq1695 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1695 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1695 + difference 0 5) (sourceB1695 + difference 5 0) sourceC1695) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2703) := by
    have ha : (tripleCharges (sourceA1695 + difference 0 5) (sourceB1695 + difference 5 0) sourceC1695) = raw24880 := by
      apply Matrix.ext; unfold tripleCharges sourceA1695 sourceB1695 sourceC1695 difference raw24880; decide +kernel
    rw [ha]
    exact (canonical24880 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1695 + difference 1 5) (sourceB1695 + difference 5 1) sourceC1695) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1228) := by
    have ha : (tripleCharges (sourceA1695 + difference 1 5) (sourceB1695 + difference 5 1) sourceC1695) = raw24882 := by
      apply Matrix.ext; unfold tripleCharges sourceA1695 sourceB1695 sourceC1695 difference raw24882; decide +kernel
    rw [ha]
    exact (canonical24882 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1695 + difference 2 5) (sourceB1695 + difference 5 2) sourceC1695) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1228) := by
    have ha : (tripleCharges (sourceA1695 + difference 2 5) (sourceB1695 + difference 5 2) sourceC1695) = raw24883 := by
      apply Matrix.ext; unfold tripleCharges sourceA1695 sourceB1695 sourceC1695 difference raw24883; decide +kernel
    rw [ha]
    exact (canonical24883 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1695 + difference 3 5) (sourceB1695 + difference 5 3) sourceC1695) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1200) := by
    have ha : (tripleCharges (sourceA1695 + difference 3 5) (sourceB1695 + difference 5 3) sourceC1695) = raw24884 := by
      apply Matrix.ext; unfold tripleCharges sourceA1695 sourceB1695 sourceC1695 difference raw24884; decide +kernel
    rw [ha]
    exact (canonical24884 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1695 + difference 4 5) (sourceB1695 + difference 5 4) sourceC1695) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1201) := by
    have ha : (tripleCharges (sourceA1695 + difference 4 5) (sourceB1695 + difference 5 4) sourceC1695) = raw24885 := by
      apply Matrix.ext; unfold tripleCharges sourceA1695 sourceB1695 sourceC1695 difference raw24885; decide +kernel
    rw [ha]
    exact (canonical24885 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1695 + difference 5 5) (sourceB1695 + difference 5 5) sourceC1695) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1201) := by
    have ha : (tripleCharges (sourceA1695 + difference 5 5) (sourceB1695 + difference 5 5) sourceC1695) = raw24875 := by
      apply Matrix.ext; unfold tripleCharges sourceA1695 sourceB1695 sourceC1695 difference raw24875; decide +kernel
    rw [ha]
    exact (canonical24875 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1695 + sourceB1695) sourceC1695) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (doubleCharges (sourceA1695 + sourceB1695) sourceC1695) = raw24881 := by
      apply Matrix.ext; unfold doubleCharges sourceA1695 sourceB1695 sourceC1695 raw24881; decide +kernel
    rw [ha]
    exact (canonical24881 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1695 sourceB1695 sourceC1695
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1695, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
