import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical89
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical90
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical151
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical155
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical157
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical159
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical162
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical163
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical164
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical166
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical168
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical169
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical170
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical171
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical172

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA1376 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1376 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC1376 : Charge := ![3, -1, 0, 1, 0, -3]
def sourceForm1376 : Integer.Sparse Master := [(Sum.inr 976, 1), (Sum.inr 979, 1), (Sum.inr 984, 1), (Sum.inr 999, 1), (Sum.inr 1033, 1), (Sum.inr 2203, 1), (Sum.inr 4081, -1)]

theorem sourceEq1376 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1376 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1376 + difference 0 5) (sourceB1376 + difference 5 0) sourceC1376) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2203) := by
    have ha : (tripleCharges (sourceA1376 + difference 0 5) (sourceB1376 + difference 5 0) sourceC1376) = raw21618 := by
      apply Matrix.ext; unfold tripleCharges sourceA1376 sourceB1376 sourceC1376 difference raw21618; decide +kernel
    rw [ha]
    exact (canonical21618 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1376 + difference 1 5) (sourceB1376 + difference 5 1) sourceC1376) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 999) := by
    have ha : (tripleCharges (sourceA1376 + difference 1 5) (sourceB1376 + difference 5 1) sourceC1376) = raw21624 := by
      apply Matrix.ext; unfold tripleCharges sourceA1376 sourceB1376 sourceC1376 difference raw21624; decide +kernel
    rw [ha]
    exact (canonical21624 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1376 + difference 2 5) (sourceB1376 + difference 5 2) sourceC1376) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 976) := by
    have ha : (tripleCharges (sourceA1376 + difference 2 5) (sourceB1376 + difference 5 2) sourceC1376) = raw21628 := by
      apply Matrix.ext; unfold tripleCharges sourceA1376 sourceB1376 sourceC1376 difference raw21628; decide +kernel
    rw [ha]
    exact (canonical21628 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1376 + difference 3 5) (sourceB1376 + difference 5 3) sourceC1376) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1033) := by
    have ha : (tripleCharges (sourceA1376 + difference 3 5) (sourceB1376 + difference 5 3) sourceC1376) = raw21629 := by
      apply Matrix.ext; unfold tripleCharges sourceA1376 sourceB1376 sourceC1376 difference raw21629; decide +kernel
    rw [ha]
    exact (canonical21629 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1376 + difference 4 5) (sourceB1376 + difference 5 4) sourceC1376) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 984) := by
    have ha : (tripleCharges (sourceA1376 + difference 4 5) (sourceB1376 + difference 5 4) sourceC1376) = raw21630 := by
      apply Matrix.ext; unfold tripleCharges sourceA1376 sourceB1376 sourceC1376 difference raw21630; decide +kernel
    rw [ha]
    exact (canonical21630 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1376 + difference 5 5) (sourceB1376 + difference 5 5) sourceC1376) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 979) := by
    have ha : (tripleCharges (sourceA1376 + difference 5 5) (sourceB1376 + difference 5 5) sourceC1376) = raw21613 := by
      apply Matrix.ext; unfold tripleCharges sourceA1376 sourceB1376 sourceC1376 difference raw21613; decide +kernel
    rw [ha]
    exact (canonical21613 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1376 + sourceB1376) sourceC1376) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1376 + sourceB1376) sourceC1376) = raw21619 := by
      apply Matrix.ext; unfold doubleCharges sourceA1376 sourceB1376 sourceC1376 raw21619; decide +kernel
    rw [ha]
    exact (canonical21619 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1376 sourceB1376 sourceC1376
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1376, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1377 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceB1377 : Charge := ![3, -1, 0, 1, 0, -3]
def sourceC1377 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1377 : Integer.Sparse Master := [(Sum.inr 698, 1), (Sum.inr 701, 1), (Sum.inr 706, 1), (Sum.inr 714, 1), (Sum.inr 809, 1), (Sum.inr 1599, 1), (Sum.inr 4070, -1)]

theorem sourceEq1377 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1377 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1377 + difference 0 0) (sourceB1377 + difference 0 0) sourceC1377) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1599) := by
    have ha : (tripleCharges (sourceA1377 + difference 0 0) (sourceB1377 + difference 0 0) sourceC1377) = raw20995 := by
      apply Matrix.ext; unfold tripleCharges sourceA1377 sourceB1377 sourceC1377 difference raw20995; decide +kernel
    rw [ha]
    exact (canonical20995 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1377 + difference 1 0) (sourceB1377 + difference 0 1) sourceC1377) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 706) := by
    have ha : (tripleCharges (sourceA1377 + difference 1 0) (sourceB1377 + difference 0 1) sourceC1377) = raw21631 := by
      apply Matrix.ext; unfold tripleCharges sourceA1377 sourceB1377 sourceC1377 difference raw21631; decide +kernel
    rw [ha]
    exact (canonical21631 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1377 + difference 2 0) (sourceB1377 + difference 0 2) sourceC1377) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 698) := by
    have ha : (tripleCharges (sourceA1377 + difference 2 0) (sourceB1377 + difference 0 2) sourceC1377) = raw21632 := by
      apply Matrix.ext; unfold tripleCharges sourceA1377 sourceB1377 sourceC1377 difference raw21632; decide +kernel
    rw [ha]
    exact (canonical21632 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1377 + difference 3 0) (sourceB1377 + difference 0 3) sourceC1377) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 809) := by
    have ha : (tripleCharges (sourceA1377 + difference 3 0) (sourceB1377 + difference 0 3) sourceC1377) = raw21578 := by
      apply Matrix.ext; unfold tripleCharges sourceA1377 sourceB1377 sourceC1377 difference raw21578; decide +kernel
    rw [ha]
    exact (canonical21578 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1377 + difference 4 0) (sourceB1377 + difference 0 4) sourceC1377) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 714) := by
    have ha : (tripleCharges (sourceA1377 + difference 4 0) (sourceB1377 + difference 0 4) sourceC1377) = raw21612 := by
      apply Matrix.ext; unfold tripleCharges sourceA1377 sourceB1377 sourceC1377 difference raw21612; decide +kernel
    rw [ha]
    exact (canonical21612 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1377 + difference 5 0) (sourceB1377 + difference 0 5) sourceC1377) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 701) := by
    have ha : (tripleCharges (sourceA1377 + difference 5 0) (sourceB1377 + difference 0 5) sourceC1377) = raw21633 := by
      apply Matrix.ext; unfold tripleCharges sourceA1377 sourceB1377 sourceC1377 difference raw21633; decide +kernel
    rw [ha]
    exact (canonical21633 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1377 + sourceB1377) sourceC1377) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1377 + sourceB1377) sourceC1377) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1377 sourceB1377 sourceC1377 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1377 sourceB1377 sourceC1377
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1377, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1378 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1378 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceC1378 : Charge := ![3, 0, 0, 0, -2, -1]
def sourceForm1378 : Integer.Sparse Master := [(Sum.inr 4178, 3), (Sum.inr 4189, 1), (Sum.inr 4192, 1), (Sum.inr 4347, 6), (Sum.inr 4358, 3), (Sum.inr 4361, 3), (Sum.inr 4476, 3), (Sum.inr 4481, 1), (Sum.inr 4499, 3), (Sum.inr 4511, 1), (Sum.inr 4843, 3), (Sum.inr 4899, 1), (Sum.inr 4901, 1)]

theorem sourceEq1378 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1378 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1378 + difference 0 1) (sourceB1378 + difference 1 0) sourceC1378) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4843) := by
    have ha : (tripleCharges (sourceA1378 + difference 0 1) (sourceB1378 + difference 1 0) sourceC1378) = raw11527 := by
      apply Matrix.ext; unfold tripleCharges sourceA1378 sourceB1378 sourceC1378 difference raw11527; decide +kernel
    rw [ha]
    exact (canonical11527 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1378 + difference 0 2) (sourceB1378 + difference 2 0) sourceC1378) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4843) := by
    have ha : (tripleCharges (sourceA1378 + difference 0 2) (sourceB1378 + difference 2 0) sourceC1378) = raw11528 := by
      apply Matrix.ext; unfold tripleCharges sourceA1378 sourceB1378 sourceC1378 difference raw11528; decide +kernel
    rw [ha]
    exact (canonical11528 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1378 + difference 0 3) (sourceB1378 + difference 3 0) sourceC1378) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4843) := by
    have ha : (tripleCharges (sourceA1378 + difference 0 3) (sourceB1378 + difference 3 0) sourceC1378) = raw11529 := by
      apply Matrix.ext; unfold tripleCharges sourceA1378 sourceB1378 sourceC1378 difference raw11529; decide +kernel
    rw [ha]
    exact (canonical11529 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1378 + difference 0 4) (sourceB1378 + difference 4 0) sourceC1378) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4899) := by
    have ha : (tripleCharges (sourceA1378 + difference 0 4) (sourceB1378 + difference 4 0) sourceC1378) = raw11530 := by
      apply Matrix.ext; unfold tripleCharges sourceA1378 sourceB1378 sourceC1378 difference raw11530; decide +kernel
    rw [ha]
    exact (canonical11530 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1378 + difference 0 5) (sourceB1378 + difference 5 0) sourceC1378) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4901) := by
    have ha : (tripleCharges (sourceA1378 + difference 0 5) (sourceB1378 + difference 5 0) sourceC1378) = raw21634 := by
      apply Matrix.ext; unfold tripleCharges sourceA1378 sourceB1378 sourceC1378 difference raw21634; decide +kernel
    rw [ha]
    exact (canonical21634 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1378 + difference 1 0) (sourceB1378 + difference 0 1) sourceC1378) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4178) := by
    have ha : (tripleCharges (sourceA1378 + difference 1 0) (sourceB1378 + difference 0 1) sourceC1378) = raw21635 := by
      apply Matrix.ext; unfold tripleCharges sourceA1378 sourceB1378 sourceC1378 difference raw21635; decide +kernel
    rw [ha]
    exact (canonical21635 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1378 + difference 1 2) (sourceB1378 + difference 2 1) sourceC1378) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4347) := by
    have ha : (tripleCharges (sourceA1378 + difference 1 2) (sourceB1378 + difference 2 1) sourceC1378) = raw21636 := by
      apply Matrix.ext; unfold tripleCharges sourceA1378 sourceB1378 sourceC1378 difference raw21636; decide +kernel
    rw [ha]
    exact (canonical21636 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1378 + difference 1 3) (sourceB1378 + difference 3 1) sourceC1378) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4347) := by
    have ha : (tripleCharges (sourceA1378 + difference 1 3) (sourceB1378 + difference 3 1) sourceC1378) = raw21637 := by
      apply Matrix.ext; unfold tripleCharges sourceA1378 sourceB1378 sourceC1378 difference raw21637; decide +kernel
    rw [ha]
    exact (canonical21637 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1378 + difference 1 4) (sourceB1378 + difference 4 1) sourceC1378) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4476) := by
    have ha : (tripleCharges (sourceA1378 + difference 1 4) (sourceB1378 + difference 4 1) sourceC1378) = raw21638 := by
      apply Matrix.ext; unfold tripleCharges sourceA1378 sourceB1378 sourceC1378 difference raw21638; decide +kernel
    rw [ha]
    exact (canonical21638 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1378 + difference 1 5) (sourceB1378 + difference 5 1) sourceC1378) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4499) := by
    have ha : (tripleCharges (sourceA1378 + difference 1 5) (sourceB1378 + difference 5 1) sourceC1378) = raw11506 := by
      apply Matrix.ext; unfold tripleCharges sourceA1378 sourceB1378 sourceC1378 difference raw11506; decide +kernel
    rw [ha]
    exact (canonical11506 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1378 + difference 2 0) (sourceB1378 + difference 0 2) sourceC1378) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4178) := by
    have ha : (tripleCharges (sourceA1378 + difference 2 0) (sourceB1378 + difference 0 2) sourceC1378) = raw21639 := by
      apply Matrix.ext; unfold tripleCharges sourceA1378 sourceB1378 sourceC1378 difference raw21639; decide +kernel
    rw [ha]
    exact (canonical21639 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1378 + difference 2 1) (sourceB1378 + difference 1 2) sourceC1378) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4347) := by
    have ha : (tripleCharges (sourceA1378 + difference 2 1) (sourceB1378 + difference 1 2) sourceC1378) = raw21640 := by
      apply Matrix.ext; unfold tripleCharges sourceA1378 sourceB1378 sourceC1378 difference raw21640; decide +kernel
    rw [ha]
    exact (canonical21640 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1378 + difference 2 3) (sourceB1378 + difference 3 2) sourceC1378) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4347) := by
    have ha : (tripleCharges (sourceA1378 + difference 2 3) (sourceB1378 + difference 3 2) sourceC1378) = raw21641 := by
      apply Matrix.ext; unfold tripleCharges sourceA1378 sourceB1378 sourceC1378 difference raw21641; decide +kernel
    rw [ha]
    exact (canonical21641 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1378 + difference 2 4) (sourceB1378 + difference 4 2) sourceC1378) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4476) := by
    have ha : (tripleCharges (sourceA1378 + difference 2 4) (sourceB1378 + difference 4 2) sourceC1378) = raw21642 := by
      apply Matrix.ext; unfold tripleCharges sourceA1378 sourceB1378 sourceC1378 difference raw21642; decide +kernel
    rw [ha]
    exact (canonical21642 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1378 + difference 2 5) (sourceB1378 + difference 5 2) sourceC1378) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4499) := by
    have ha : (tripleCharges (sourceA1378 + difference 2 5) (sourceB1378 + difference 5 2) sourceC1378) = raw11511 := by
      apply Matrix.ext; unfold tripleCharges sourceA1378 sourceB1378 sourceC1378 difference raw11511; decide +kernel
    rw [ha]
    exact (canonical11511 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1378 + difference 3 0) (sourceB1378 + difference 0 3) sourceC1378) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4178) := by
    have ha : (tripleCharges (sourceA1378 + difference 3 0) (sourceB1378 + difference 0 3) sourceC1378) = raw21643 := by
      apply Matrix.ext; unfold tripleCharges sourceA1378 sourceB1378 sourceC1378 difference raw21643; decide +kernel
    rw [ha]
    exact (canonical21643 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1378 + difference 3 1) (sourceB1378 + difference 1 3) sourceC1378) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4347) := by
    have ha : (tripleCharges (sourceA1378 + difference 3 1) (sourceB1378 + difference 1 3) sourceC1378) = raw21644 := by
      apply Matrix.ext; unfold tripleCharges sourceA1378 sourceB1378 sourceC1378 difference raw21644; decide +kernel
    rw [ha]
    exact (canonical21644 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1378 + difference 3 2) (sourceB1378 + difference 2 3) sourceC1378) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4347) := by
    have ha : (tripleCharges (sourceA1378 + difference 3 2) (sourceB1378 + difference 2 3) sourceC1378) = raw21645 := by
      apply Matrix.ext; unfold tripleCharges sourceA1378 sourceB1378 sourceC1378 difference raw21645; decide +kernel
    rw [ha]
    exact (canonical21645 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1378 + difference 3 4) (sourceB1378 + difference 4 3) sourceC1378) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4476) := by
    have ha : (tripleCharges (sourceA1378 + difference 3 4) (sourceB1378 + difference 4 3) sourceC1378) = raw21646 := by
      apply Matrix.ext; unfold tripleCharges sourceA1378 sourceB1378 sourceC1378 difference raw21646; decide +kernel
    rw [ha]
    exact (canonical21646 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1378 + difference 3 5) (sourceB1378 + difference 5 3) sourceC1378) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4499) := by
    have ha : (tripleCharges (sourceA1378 + difference 3 5) (sourceB1378 + difference 5 3) sourceC1378) = raw11516 := by
      apply Matrix.ext; unfold tripleCharges sourceA1378 sourceB1378 sourceC1378 difference raw11516; decide +kernel
    rw [ha]
    exact (canonical11516 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1378 + difference 4 0) (sourceB1378 + difference 0 4) sourceC1378) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4192) := by
    have ha : (tripleCharges (sourceA1378 + difference 4 0) (sourceB1378 + difference 0 4) sourceC1378) = raw21647 := by
      apply Matrix.ext; unfold tripleCharges sourceA1378 sourceB1378 sourceC1378 difference raw21647; decide +kernel
    rw [ha]
    exact (canonical21647 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1378 + difference 4 1) (sourceB1378 + difference 1 4) sourceC1378) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4361) := by
    have ha : (tripleCharges (sourceA1378 + difference 4 1) (sourceB1378 + difference 1 4) sourceC1378) = raw21648 := by
      apply Matrix.ext; unfold tripleCharges sourceA1378 sourceB1378 sourceC1378 difference raw21648; decide +kernel
    rw [ha]
    exact (canonical21648 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1378 + difference 4 2) (sourceB1378 + difference 2 4) sourceC1378) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4361) := by
    have ha : (tripleCharges (sourceA1378 + difference 4 2) (sourceB1378 + difference 2 4) sourceC1378) = raw21649 := by
      apply Matrix.ext; unfold tripleCharges sourceA1378 sourceB1378 sourceC1378 difference raw21649; decide +kernel
    rw [ha]
    exact (canonical21649 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1378 + difference 4 3) (sourceB1378 + difference 3 4) sourceC1378) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4361) := by
    have ha : (tripleCharges (sourceA1378 + difference 4 3) (sourceB1378 + difference 3 4) sourceC1378) = raw21650 := by
      apply Matrix.ext; unfold tripleCharges sourceA1378 sourceB1378 sourceC1378 difference raw21650; decide +kernel
    rw [ha]
    exact (canonical21650 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1378 + difference 4 5) (sourceB1378 + difference 5 4) sourceC1378) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4511) := by
    have ha : (tripleCharges (sourceA1378 + difference 4 5) (sourceB1378 + difference 5 4) sourceC1378) = raw11521 := by
      apply Matrix.ext; unfold tripleCharges sourceA1378 sourceB1378 sourceC1378 difference raw11521; decide +kernel
    rw [ha]
    exact (canonical11521 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1378 + difference 5 0) (sourceB1378 + difference 0 5) sourceC1378) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4189) := by
    have ha : (tripleCharges (sourceA1378 + difference 5 0) (sourceB1378 + difference 0 5) sourceC1378) = raw21651 := by
      apply Matrix.ext; unfold tripleCharges sourceA1378 sourceB1378 sourceC1378 difference raw21651; decide +kernel
    rw [ha]
    exact (canonical21651 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1378 + difference 5 1) (sourceB1378 + difference 1 5) sourceC1378) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4358) := by
    have ha : (tripleCharges (sourceA1378 + difference 5 1) (sourceB1378 + difference 1 5) sourceC1378) = raw21652 := by
      apply Matrix.ext; unfold tripleCharges sourceA1378 sourceB1378 sourceC1378 difference raw21652; decide +kernel
    rw [ha]
    exact (canonical21652 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1378 + difference 5 2) (sourceB1378 + difference 2 5) sourceC1378) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4358) := by
    have ha : (tripleCharges (sourceA1378 + difference 5 2) (sourceB1378 + difference 2 5) sourceC1378) = raw21653 := by
      apply Matrix.ext; unfold tripleCharges sourceA1378 sourceB1378 sourceC1378 difference raw21653; decide +kernel
    rw [ha]
    exact (canonical21653 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1378 + difference 5 3) (sourceB1378 + difference 3 5) sourceC1378) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4358) := by
    have ha : (tripleCharges (sourceA1378 + difference 5 3) (sourceB1378 + difference 3 5) sourceC1378) = raw21654 := by
      apply Matrix.ext; unfold tripleCharges sourceA1378 sourceB1378 sourceC1378 difference raw21654; decide +kernel
    rw [ha]
    exact (canonical21654 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1378 + difference 5 4) (sourceB1378 + difference 4 5) sourceC1378) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4481) := by
    have ha : (tripleCharges (sourceA1378 + difference 5 4) (sourceB1378 + difference 4 5) sourceC1378) = raw21655 := by
      apply Matrix.ext; unfold tripleCharges sourceA1378 sourceB1378 sourceC1378 difference raw21655; decide +kernel
    rw [ha]
    exact (canonical21655 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1378 sourceB1378 sourceC1378
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1378, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1379 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1379 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceC1379 : Charge := ![3, 0, 0, 0, -2, -1]
def sourceForm1379 : Integer.Sparse Master := [(Sum.inr 1520, 3), (Sum.inr 1539, 1), (Sum.inr 1540, 1), (Sum.inr 1676, 6), (Sum.inr 1694, 3), (Sum.inr 1695, 3), (Sum.inr 1728, 3), (Sum.inr 1729, 3), (Sum.inr 1755, 1), (Sum.inr 1757, 1), (Sum.inr 2230, 3), (Sum.inr 2293, 1), (Sum.inr 2294, 1)]

theorem sourceEq1379 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1379 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1379 + difference 0 1) (sourceB1379 + difference 1 0) sourceC1379) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2230) := by
    have ha : (tripleCharges (sourceA1379 + difference 0 1) (sourceB1379 + difference 1 0) sourceC1379) = raw21656 := by
      apply Matrix.ext; unfold tripleCharges sourceA1379 sourceB1379 sourceC1379 difference raw21656; decide +kernel
    rw [ha]
    exact (canonical21656 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1379 + difference 0 2) (sourceB1379 + difference 2 0) sourceC1379) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2230) := by
    have ha : (tripleCharges (sourceA1379 + difference 0 2) (sourceB1379 + difference 2 0) sourceC1379) = raw21657 := by
      apply Matrix.ext; unfold tripleCharges sourceA1379 sourceB1379 sourceC1379 difference raw21657; decide +kernel
    rw [ha]
    exact (canonical21657 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1379 + difference 0 3) (sourceB1379 + difference 3 0) sourceC1379) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2230) := by
    have ha : (tripleCharges (sourceA1379 + difference 0 3) (sourceB1379 + difference 3 0) sourceC1379) = raw21658 := by
      apply Matrix.ext; unfold tripleCharges sourceA1379 sourceB1379 sourceC1379 difference raw21658; decide +kernel
    rw [ha]
    exact (canonical21658 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1379 + difference 0 4) (sourceB1379 + difference 4 0) sourceC1379) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2294) := by
    have ha : (tripleCharges (sourceA1379 + difference 0 4) (sourceB1379 + difference 4 0) sourceC1379) = raw21659 := by
      apply Matrix.ext; unfold tripleCharges sourceA1379 sourceB1379 sourceC1379 difference raw21659; decide +kernel
    rw [ha]
    exact (canonical21659 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1379 + difference 0 5) (sourceB1379 + difference 5 0) sourceC1379) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2293) := by
    have ha : (tripleCharges (sourceA1379 + difference 0 5) (sourceB1379 + difference 5 0) sourceC1379) = raw21660 := by
      apply Matrix.ext; unfold tripleCharges sourceA1379 sourceB1379 sourceC1379 difference raw21660; decide +kernel
    rw [ha]
    exact (canonical21660 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1379 + difference 1 0) (sourceB1379 + difference 0 1) sourceC1379) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1520) := by
    have ha : (tripleCharges (sourceA1379 + difference 1 0) (sourceB1379 + difference 0 1) sourceC1379) = raw21661 := by
      apply Matrix.ext; unfold tripleCharges sourceA1379 sourceB1379 sourceC1379 difference raw21661; decide +kernel
    rw [ha]
    exact (canonical21661 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1379 + difference 1 2) (sourceB1379 + difference 2 1) sourceC1379) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1676) := by
    have ha : (tripleCharges (sourceA1379 + difference 1 2) (sourceB1379 + difference 2 1) sourceC1379) = raw21662 := by
      apply Matrix.ext; unfold tripleCharges sourceA1379 sourceB1379 sourceC1379 difference raw21662; decide +kernel
    rw [ha]
    exact (canonical21662 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1379 + difference 1 3) (sourceB1379 + difference 3 1) sourceC1379) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1676) := by
    have ha : (tripleCharges (sourceA1379 + difference 1 3) (sourceB1379 + difference 3 1) sourceC1379) = raw21663 := by
      apply Matrix.ext; unfold tripleCharges sourceA1379 sourceB1379 sourceC1379 difference raw21663; decide +kernel
    rw [ha]
    exact (canonical21663 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1379 + difference 1 4) (sourceB1379 + difference 4 1) sourceC1379) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1729) := by
    have ha : (tripleCharges (sourceA1379 + difference 1 4) (sourceB1379 + difference 4 1) sourceC1379) = raw21664 := by
      apply Matrix.ext; unfold tripleCharges sourceA1379 sourceB1379 sourceC1379 difference raw21664; decide +kernel
    rw [ha]
    exact (canonical21664 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1379 + difference 1 5) (sourceB1379 + difference 5 1) sourceC1379) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1728) := by
    have ha : (tripleCharges (sourceA1379 + difference 1 5) (sourceB1379 + difference 5 1) sourceC1379) = raw21665 := by
      apply Matrix.ext; unfold tripleCharges sourceA1379 sourceB1379 sourceC1379 difference raw21665; decide +kernel
    rw [ha]
    exact (canonical21665 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1379 + difference 2 0) (sourceB1379 + difference 0 2) sourceC1379) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1520) := by
    have ha : (tripleCharges (sourceA1379 + difference 2 0) (sourceB1379 + difference 0 2) sourceC1379) = raw21666 := by
      apply Matrix.ext; unfold tripleCharges sourceA1379 sourceB1379 sourceC1379 difference raw21666; decide +kernel
    rw [ha]
    exact (canonical21666 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1379 + difference 2 1) (sourceB1379 + difference 1 2) sourceC1379) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1676) := by
    have ha : (tripleCharges (sourceA1379 + difference 2 1) (sourceB1379 + difference 1 2) sourceC1379) = raw21667 := by
      apply Matrix.ext; unfold tripleCharges sourceA1379 sourceB1379 sourceC1379 difference raw21667; decide +kernel
    rw [ha]
    exact (canonical21667 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1379 + difference 2 3) (sourceB1379 + difference 3 2) sourceC1379) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1676) := by
    have ha : (tripleCharges (sourceA1379 + difference 2 3) (sourceB1379 + difference 3 2) sourceC1379) = raw21668 := by
      apply Matrix.ext; unfold tripleCharges sourceA1379 sourceB1379 sourceC1379 difference raw21668; decide +kernel
    rw [ha]
    exact (canonical21668 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1379 + difference 2 4) (sourceB1379 + difference 4 2) sourceC1379) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1729) := by
    have ha : (tripleCharges (sourceA1379 + difference 2 4) (sourceB1379 + difference 4 2) sourceC1379) = raw21669 := by
      apply Matrix.ext; unfold tripleCharges sourceA1379 sourceB1379 sourceC1379 difference raw21669; decide +kernel
    rw [ha]
    exact (canonical21669 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1379 + difference 2 5) (sourceB1379 + difference 5 2) sourceC1379) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1728) := by
    have ha : (tripleCharges (sourceA1379 + difference 2 5) (sourceB1379 + difference 5 2) sourceC1379) = raw21670 := by
      apply Matrix.ext; unfold tripleCharges sourceA1379 sourceB1379 sourceC1379 difference raw21670; decide +kernel
    rw [ha]
    exact (canonical21670 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1379 + difference 3 0) (sourceB1379 + difference 0 3) sourceC1379) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1520) := by
    have ha : (tripleCharges (sourceA1379 + difference 3 0) (sourceB1379 + difference 0 3) sourceC1379) = raw21671 := by
      apply Matrix.ext; unfold tripleCharges sourceA1379 sourceB1379 sourceC1379 difference raw21671; decide +kernel
    rw [ha]
    exact (canonical21671 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1379 + difference 3 1) (sourceB1379 + difference 1 3) sourceC1379) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1676) := by
    have ha : (tripleCharges (sourceA1379 + difference 3 1) (sourceB1379 + difference 1 3) sourceC1379) = raw21672 := by
      apply Matrix.ext; unfold tripleCharges sourceA1379 sourceB1379 sourceC1379 difference raw21672; decide +kernel
    rw [ha]
    exact (canonical21672 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1379 + difference 3 2) (sourceB1379 + difference 2 3) sourceC1379) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1676) := by
    have ha : (tripleCharges (sourceA1379 + difference 3 2) (sourceB1379 + difference 2 3) sourceC1379) = raw21673 := by
      apply Matrix.ext; unfold tripleCharges sourceA1379 sourceB1379 sourceC1379 difference raw21673; decide +kernel
    rw [ha]
    exact (canonical21673 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1379 + difference 3 4) (sourceB1379 + difference 4 3) sourceC1379) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1729) := by
    have ha : (tripleCharges (sourceA1379 + difference 3 4) (sourceB1379 + difference 4 3) sourceC1379) = raw21674 := by
      apply Matrix.ext; unfold tripleCharges sourceA1379 sourceB1379 sourceC1379 difference raw21674; decide +kernel
    rw [ha]
    exact (canonical21674 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1379 + difference 3 5) (sourceB1379 + difference 5 3) sourceC1379) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1728) := by
    have ha : (tripleCharges (sourceA1379 + difference 3 5) (sourceB1379 + difference 5 3) sourceC1379) = raw21675 := by
      apply Matrix.ext; unfold tripleCharges sourceA1379 sourceB1379 sourceC1379 difference raw21675; decide +kernel
    rw [ha]
    exact (canonical21675 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1379 + difference 4 0) (sourceB1379 + difference 0 4) sourceC1379) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1539) := by
    have ha : (tripleCharges (sourceA1379 + difference 4 0) (sourceB1379 + difference 0 4) sourceC1379) = raw21676 := by
      apply Matrix.ext; unfold tripleCharges sourceA1379 sourceB1379 sourceC1379 difference raw21676; decide +kernel
    rw [ha]
    exact (canonical21676 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1379 + difference 4 1) (sourceB1379 + difference 1 4) sourceC1379) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1694) := by
    have ha : (tripleCharges (sourceA1379 + difference 4 1) (sourceB1379 + difference 1 4) sourceC1379) = raw21677 := by
      apply Matrix.ext; unfold tripleCharges sourceA1379 sourceB1379 sourceC1379 difference raw21677; decide +kernel
    rw [ha]
    exact (canonical21677 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1379 + difference 4 2) (sourceB1379 + difference 2 4) sourceC1379) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1694) := by
    have ha : (tripleCharges (sourceA1379 + difference 4 2) (sourceB1379 + difference 2 4) sourceC1379) = raw21678 := by
      apply Matrix.ext; unfold tripleCharges sourceA1379 sourceB1379 sourceC1379 difference raw21678; decide +kernel
    rw [ha]
    exact (canonical21678 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1379 + difference 4 3) (sourceB1379 + difference 3 4) sourceC1379) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1694) := by
    have ha : (tripleCharges (sourceA1379 + difference 4 3) (sourceB1379 + difference 3 4) sourceC1379) = raw21679 := by
      apply Matrix.ext; unfold tripleCharges sourceA1379 sourceB1379 sourceC1379 difference raw21679; decide +kernel
    rw [ha]
    exact (canonical21679 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1379 + difference 4 5) (sourceB1379 + difference 5 4) sourceC1379) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1755) := by
    have ha : (tripleCharges (sourceA1379 + difference 4 5) (sourceB1379 + difference 5 4) sourceC1379) = raw21680 := by
      apply Matrix.ext; unfold tripleCharges sourceA1379 sourceB1379 sourceC1379 difference raw21680; decide +kernel
    rw [ha]
    exact (canonical21680 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1379 + difference 5 0) (sourceB1379 + difference 0 5) sourceC1379) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1540) := by
    have ha : (tripleCharges (sourceA1379 + difference 5 0) (sourceB1379 + difference 0 5) sourceC1379) = raw21681 := by
      apply Matrix.ext; unfold tripleCharges sourceA1379 sourceB1379 sourceC1379 difference raw21681; decide +kernel
    rw [ha]
    exact (canonical21681 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1379 + difference 5 1) (sourceB1379 + difference 1 5) sourceC1379) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1695) := by
    have ha : (tripleCharges (sourceA1379 + difference 5 1) (sourceB1379 + difference 1 5) sourceC1379) = raw21682 := by
      apply Matrix.ext; unfold tripleCharges sourceA1379 sourceB1379 sourceC1379 difference raw21682; decide +kernel
    rw [ha]
    exact (canonical21682 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1379 + difference 5 2) (sourceB1379 + difference 2 5) sourceC1379) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1695) := by
    have ha : (tripleCharges (sourceA1379 + difference 5 2) (sourceB1379 + difference 2 5) sourceC1379) = raw21683 := by
      apply Matrix.ext; unfold tripleCharges sourceA1379 sourceB1379 sourceC1379 difference raw21683; decide +kernel
    rw [ha]
    exact (canonical21683 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1379 + difference 5 3) (sourceB1379 + difference 3 5) sourceC1379) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1695) := by
    have ha : (tripleCharges (sourceA1379 + difference 5 3) (sourceB1379 + difference 3 5) sourceC1379) = raw21684 := by
      apply Matrix.ext; unfold tripleCharges sourceA1379 sourceB1379 sourceC1379 difference raw21684; decide +kernel
    rw [ha]
    exact (canonical21684 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1379 + difference 5 4) (sourceB1379 + difference 4 5) sourceC1379) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1757) := by
    have ha : (tripleCharges (sourceA1379 + difference 5 4) (sourceB1379 + difference 4 5) sourceC1379) = raw21685 := by
      apply Matrix.ext; unfold tripleCharges sourceA1379 sourceB1379 sourceC1379 difference raw21685; decide +kernel
    rw [ha]
    exact (canonical21685 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1379 sourceB1379 sourceC1379
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1379, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1380 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1380 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceC1380 : Charge := ![3, 0, 0, 0, -2, -1]
def sourceForm1380 : Integer.Sparse Master := [(Sum.inr 925, 2), (Sum.inr 936, 1), (Sum.inr 939, 1), (Sum.inr 1091, 1), (Sum.inr 2062, 1), (Sum.inr 4084, -1)]

theorem sourceEq1380 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1380 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1380 + difference 0 1) (sourceB1380 + difference 1 0) sourceC1380) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2062) := by
    have ha : (tripleCharges (sourceA1380 + difference 0 1) (sourceB1380 + difference 1 0) sourceC1380) = raw21686 := by
      apply Matrix.ext; unfold tripleCharges sourceA1380 sourceB1380 sourceC1380 difference raw21686; decide +kernel
    rw [ha]
    exact (canonical21686 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1380 + difference 1 1) (sourceB1380 + difference 1 1) sourceC1380) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1091) := by
    have ha : (tripleCharges (sourceA1380 + difference 1 1) (sourceB1380 + difference 1 1) sourceC1380) = raw19412 := by
      apply Matrix.ext; unfold tripleCharges sourceA1380 sourceB1380 sourceC1380 difference raw19412; decide +kernel
    rw [ha]
    exact (canonical19412 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1380 + difference 2 1) (sourceB1380 + difference 1 2) sourceC1380) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 925) := by
    have ha : (tripleCharges (sourceA1380 + difference 2 1) (sourceB1380 + difference 1 2) sourceC1380) = raw21687 := by
      apply Matrix.ext; unfold tripleCharges sourceA1380 sourceB1380 sourceC1380 difference raw21687; decide +kernel
    rw [ha]
    exact (canonical21687 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1380 + difference 3 1) (sourceB1380 + difference 1 3) sourceC1380) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 925) := by
    have ha : (tripleCharges (sourceA1380 + difference 3 1) (sourceB1380 + difference 1 3) sourceC1380) = raw21688 := by
      apply Matrix.ext; unfold tripleCharges sourceA1380 sourceB1380 sourceC1380 difference raw21688; decide +kernel
    rw [ha]
    exact (canonical21688 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1380 + difference 4 1) (sourceB1380 + difference 1 4) sourceC1380) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 939) := by
    have ha : (tripleCharges (sourceA1380 + difference 4 1) (sourceB1380 + difference 1 4) sourceC1380) = raw21689 := by
      apply Matrix.ext; unfold tripleCharges sourceA1380 sourceB1380 sourceC1380 difference raw21689; decide +kernel
    rw [ha]
    exact (canonical21689 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1380 + difference 5 1) (sourceB1380 + difference 1 5) sourceC1380) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 936) := by
    have ha : (tripleCharges (sourceA1380 + difference 5 1) (sourceB1380 + difference 1 5) sourceC1380) = raw19408 := by
      apply Matrix.ext; unfold tripleCharges sourceA1380 sourceB1380 sourceC1380 difference raw19408; decide +kernel
    rw [ha]
    exact (canonical19408 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1380 + sourceB1380) sourceC1380) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1380 + sourceB1380) sourceC1380) = raw19413 := by
      apply Matrix.ext; unfold doubleCharges sourceA1380 sourceB1380 sourceC1380 raw19413; decide +kernel
    rw [ha]
    exact (canonical19413 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1380 sourceB1380 sourceC1380
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1380, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1381 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1381 : Charge := ![3, 0, 0, 0, -2, -1]
def sourceC1381 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceForm1381 : Integer.Sparse Master := [(Sum.inr 4128, 3), (Sum.inr 4134, 1), (Sum.inr 4138, 1), (Sum.inr 4309, 6), (Sum.inr 4315, 3), (Sum.inr 4319, 3), (Sum.inr 4463, 3), (Sum.inr 4468, 1), (Sum.inr 4503, 3), (Sum.inr 4510, 1), (Sum.inr 5109, 3), (Sum.inr 5296, 1), (Sum.inr 5310, 1)]

theorem sourceEq1381 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1381 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1381 + difference 0 1) (sourceB1381 + difference 1 0) sourceC1381) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5109) := by
    have ha : (tripleCharges (sourceA1381 + difference 0 1) (sourceB1381 + difference 1 0) sourceC1381) = raw7611 := by
      apply Matrix.ext; unfold tripleCharges sourceA1381 sourceB1381 sourceC1381 difference raw7611; decide +kernel
    rw [ha]
    exact (canonical7611 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1381 + difference 0 2) (sourceB1381 + difference 2 0) sourceC1381) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5109) := by
    have ha : (tripleCharges (sourceA1381 + difference 0 2) (sourceB1381 + difference 2 0) sourceC1381) = raw7612 := by
      apply Matrix.ext; unfold tripleCharges sourceA1381 sourceB1381 sourceC1381 difference raw7612; decide +kernel
    rw [ha]
    exact (canonical7612 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1381 + difference 0 3) (sourceB1381 + difference 3 0) sourceC1381) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5109) := by
    have ha : (tripleCharges (sourceA1381 + difference 0 3) (sourceB1381 + difference 3 0) sourceC1381) = raw7613 := by
      apply Matrix.ext; unfold tripleCharges sourceA1381 sourceB1381 sourceC1381 difference raw7613; decide +kernel
    rw [ha]
    exact (canonical7613 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1381 + difference 0 4) (sourceB1381 + difference 4 0) sourceC1381) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5296) := by
    have ha : (tripleCharges (sourceA1381 + difference 0 4) (sourceB1381 + difference 4 0) sourceC1381) = raw2876 := by
      apply Matrix.ext; unfold tripleCharges sourceA1381 sourceB1381 sourceC1381 difference raw2876; decide +kernel
    rw [ha]
    exact (canonical2876 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1381 + difference 0 5) (sourceB1381 + difference 5 0) sourceC1381) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5310) := by
    have ha : (tripleCharges (sourceA1381 + difference 0 5) (sourceB1381 + difference 5 0) sourceC1381) = raw2871 := by
      apply Matrix.ext; unfold tripleCharges sourceA1381 sourceB1381 sourceC1381 difference raw2871; decide +kernel
    rw [ha]
    exact (canonical2871 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1381 + difference 1 0) (sourceB1381 + difference 0 1) sourceC1381) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4128) := by
    have ha : (tripleCharges (sourceA1381 + difference 1 0) (sourceB1381 + difference 0 1) sourceC1381) = raw21690 := by
      apply Matrix.ext; unfold tripleCharges sourceA1381 sourceB1381 sourceC1381 difference raw21690; decide +kernel
    rw [ha]
    exact (canonical21690 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1381 + difference 1 2) (sourceB1381 + difference 2 1) sourceC1381) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4309) := by
    have ha : (tripleCharges (sourceA1381 + difference 1 2) (sourceB1381 + difference 2 1) sourceC1381) = raw21691 := by
      apply Matrix.ext; unfold tripleCharges sourceA1381 sourceB1381 sourceC1381 difference raw21691; decide +kernel
    rw [ha]
    exact (canonical21691 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1381 + difference 1 3) (sourceB1381 + difference 3 1) sourceC1381) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4309) := by
    have ha : (tripleCharges (sourceA1381 + difference 1 3) (sourceB1381 + difference 3 1) sourceC1381) = raw21692 := by
      apply Matrix.ext; unfold tripleCharges sourceA1381 sourceB1381 sourceC1381 difference raw21692; decide +kernel
    rw [ha]
    exact (canonical21692 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1381 + difference 1 4) (sourceB1381 + difference 4 1) sourceC1381) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4463) := by
    have ha : (tripleCharges (sourceA1381 + difference 1 4) (sourceB1381 + difference 4 1) sourceC1381) = raw21693 := by
      apply Matrix.ext; unfold tripleCharges sourceA1381 sourceB1381 sourceC1381 difference raw21693; decide +kernel
    rw [ha]
    exact (canonical21693 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1381 + difference 1 5) (sourceB1381 + difference 5 1) sourceC1381) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4503) := by
    have ha : (tripleCharges (sourceA1381 + difference 1 5) (sourceB1381 + difference 5 1) sourceC1381) = raw7597 := by
      apply Matrix.ext; unfold tripleCharges sourceA1381 sourceB1381 sourceC1381 difference raw7597; decide +kernel
    rw [ha]
    exact (canonical7597 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1381 + difference 2 0) (sourceB1381 + difference 0 2) sourceC1381) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4128) := by
    have ha : (tripleCharges (sourceA1381 + difference 2 0) (sourceB1381 + difference 0 2) sourceC1381) = raw21694 := by
      apply Matrix.ext; unfold tripleCharges sourceA1381 sourceB1381 sourceC1381 difference raw21694; decide +kernel
    rw [ha]
    exact (canonical21694 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1381 + difference 2 1) (sourceB1381 + difference 1 2) sourceC1381) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4309) := by
    have ha : (tripleCharges (sourceA1381 + difference 2 1) (sourceB1381 + difference 1 2) sourceC1381) = raw21695 := by
      apply Matrix.ext; unfold tripleCharges sourceA1381 sourceB1381 sourceC1381 difference raw21695; decide +kernel
    rw [ha]
    exact (canonical21695 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1381 + difference 2 3) (sourceB1381 + difference 3 2) sourceC1381) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4309) := by
    have ha : (tripleCharges (sourceA1381 + difference 2 3) (sourceB1381 + difference 3 2) sourceC1381) = raw21696 := by
      apply Matrix.ext; unfold tripleCharges sourceA1381 sourceB1381 sourceC1381 difference raw21696; decide +kernel
    rw [ha]
    exact (canonical21696 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1381 + difference 2 4) (sourceB1381 + difference 4 2) sourceC1381) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4463) := by
    have ha : (tripleCharges (sourceA1381 + difference 2 4) (sourceB1381 + difference 4 2) sourceC1381) = raw21697 := by
      apply Matrix.ext; unfold tripleCharges sourceA1381 sourceB1381 sourceC1381 difference raw21697; decide +kernel
    rw [ha]
    exact (canonical21697 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1381 + difference 2 5) (sourceB1381 + difference 5 2) sourceC1381) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4503) := by
    have ha : (tripleCharges (sourceA1381 + difference 2 5) (sourceB1381 + difference 5 2) sourceC1381) = raw7600 := by
      apply Matrix.ext; unfold tripleCharges sourceA1381 sourceB1381 sourceC1381 difference raw7600; decide +kernel
    rw [ha]
    exact (canonical7600 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1381 + difference 3 0) (sourceB1381 + difference 0 3) sourceC1381) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4128) := by
    have ha : (tripleCharges (sourceA1381 + difference 3 0) (sourceB1381 + difference 0 3) sourceC1381) = raw21698 := by
      apply Matrix.ext; unfold tripleCharges sourceA1381 sourceB1381 sourceC1381 difference raw21698; decide +kernel
    rw [ha]
    exact (canonical21698 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1381 + difference 3 1) (sourceB1381 + difference 1 3) sourceC1381) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4309) := by
    have ha : (tripleCharges (sourceA1381 + difference 3 1) (sourceB1381 + difference 1 3) sourceC1381) = raw21699 := by
      apply Matrix.ext; unfold tripleCharges sourceA1381 sourceB1381 sourceC1381 difference raw21699; decide +kernel
    rw [ha]
    exact (canonical21699 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1381 + difference 3 2) (sourceB1381 + difference 2 3) sourceC1381) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4309) := by
    have ha : (tripleCharges (sourceA1381 + difference 3 2) (sourceB1381 + difference 2 3) sourceC1381) = raw21700 := by
      apply Matrix.ext; unfold tripleCharges sourceA1381 sourceB1381 sourceC1381 difference raw21700; decide +kernel
    rw [ha]
    exact (canonical21700 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1381 + difference 3 4) (sourceB1381 + difference 4 3) sourceC1381) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4463) := by
    have ha : (tripleCharges (sourceA1381 + difference 3 4) (sourceB1381 + difference 4 3) sourceC1381) = raw21701 := by
      apply Matrix.ext; unfold tripleCharges sourceA1381 sourceB1381 sourceC1381 difference raw21701; decide +kernel
    rw [ha]
    exact (canonical21701 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1381 + difference 3 5) (sourceB1381 + difference 5 3) sourceC1381) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4503) := by
    have ha : (tripleCharges (sourceA1381 + difference 3 5) (sourceB1381 + difference 5 3) sourceC1381) = raw7603 := by
      apply Matrix.ext; unfold tripleCharges sourceA1381 sourceB1381 sourceC1381 difference raw7603; decide +kernel
    rw [ha]
    exact (canonical7603 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1381 + difference 4 0) (sourceB1381 + difference 0 4) sourceC1381) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4138) := by
    have ha : (tripleCharges (sourceA1381 + difference 4 0) (sourceB1381 + difference 0 4) sourceC1381) = raw21702 := by
      apply Matrix.ext; unfold tripleCharges sourceA1381 sourceB1381 sourceC1381 difference raw21702; decide +kernel
    rw [ha]
    exact (canonical21702 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1381 + difference 4 1) (sourceB1381 + difference 1 4) sourceC1381) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4319) := by
    have ha : (tripleCharges (sourceA1381 + difference 4 1) (sourceB1381 + difference 1 4) sourceC1381) = raw21703 := by
      apply Matrix.ext; unfold tripleCharges sourceA1381 sourceB1381 sourceC1381 difference raw21703; decide +kernel
    rw [ha]
    exact (canonical21703 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1381 + difference 4 2) (sourceB1381 + difference 2 4) sourceC1381) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4319) := by
    have ha : (tripleCharges (sourceA1381 + difference 4 2) (sourceB1381 + difference 2 4) sourceC1381) = raw21704 := by
      apply Matrix.ext; unfold tripleCharges sourceA1381 sourceB1381 sourceC1381 difference raw21704; decide +kernel
    rw [ha]
    exact (canonical21704 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1381 + difference 4 3) (sourceB1381 + difference 3 4) sourceC1381) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4319) := by
    have ha : (tripleCharges (sourceA1381 + difference 4 3) (sourceB1381 + difference 3 4) sourceC1381) = raw21705 := by
      apply Matrix.ext; unfold tripleCharges sourceA1381 sourceB1381 sourceC1381 difference raw21705; decide +kernel
    rw [ha]
    exact (canonical21705 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1381 + difference 4 5) (sourceB1381 + difference 5 4) sourceC1381) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4510) := by
    have ha : (tripleCharges (sourceA1381 + difference 4 5) (sourceB1381 + difference 5 4) sourceC1381) = raw7606 := by
      apply Matrix.ext; unfold tripleCharges sourceA1381 sourceB1381 sourceC1381 difference raw7606; decide +kernel
    rw [ha]
    exact (canonical7606 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1381 + difference 5 0) (sourceB1381 + difference 0 5) sourceC1381) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4134) := by
    have ha : (tripleCharges (sourceA1381 + difference 5 0) (sourceB1381 + difference 0 5) sourceC1381) = raw21706 := by
      apply Matrix.ext; unfold tripleCharges sourceA1381 sourceB1381 sourceC1381 difference raw21706; decide +kernel
    rw [ha]
    exact (canonical21706 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1381 + difference 5 1) (sourceB1381 + difference 1 5) sourceC1381) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4315) := by
    have ha : (tripleCharges (sourceA1381 + difference 5 1) (sourceB1381 + difference 1 5) sourceC1381) = raw21707 := by
      apply Matrix.ext; unfold tripleCharges sourceA1381 sourceB1381 sourceC1381 difference raw21707; decide +kernel
    rw [ha]
    exact (canonical21707 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1381 + difference 5 2) (sourceB1381 + difference 2 5) sourceC1381) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4315) := by
    have ha : (tripleCharges (sourceA1381 + difference 5 2) (sourceB1381 + difference 2 5) sourceC1381) = raw21708 := by
      apply Matrix.ext; unfold tripleCharges sourceA1381 sourceB1381 sourceC1381 difference raw21708; decide +kernel
    rw [ha]
    exact (canonical21708 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1381 + difference 5 3) (sourceB1381 + difference 3 5) sourceC1381) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4315) := by
    have ha : (tripleCharges (sourceA1381 + difference 5 3) (sourceB1381 + difference 3 5) sourceC1381) = raw21709 := by
      apply Matrix.ext; unfold tripleCharges sourceA1381 sourceB1381 sourceC1381 difference raw21709; decide +kernel
    rw [ha]
    exact (canonical21709 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1381 + difference 5 4) (sourceB1381 + difference 4 5) sourceC1381) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4468) := by
    have ha : (tripleCharges (sourceA1381 + difference 5 4) (sourceB1381 + difference 4 5) sourceC1381) = raw21710 := by
      apply Matrix.ext; unfold tripleCharges sourceA1381 sourceB1381 sourceC1381 difference raw21710; decide +kernel
    rw [ha]
    exact (canonical21710 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1381 sourceB1381 sourceC1381
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1381, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1382 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1382 : Charge := ![3, 0, 0, 0, -2, -1]
def sourceC1382 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceForm1382 : Integer.Sparse Master := [(Sum.inr 559, 3), (Sum.inr 564, 1), (Sum.inr 566, 1), (Sum.inr 887, 6), (Sum.inr 893, 3), (Sum.inr 897, 3), (Sum.inr 1046, 3), (Sum.inr 1051, 1), (Sum.inr 1087, 3), (Sum.inr 1094, 1), (Sum.inr 2519, 3), (Sum.inr 2770, 1), (Sum.inr 2788, 1)]

theorem sourceEq1382 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1382 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1382 + difference 0 1) (sourceB1382 + difference 1 0) sourceC1382) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2519) := by
    have ha : (tripleCharges (sourceA1382 + difference 0 1) (sourceB1382 + difference 1 0) sourceC1382) = raw7640 := by
      apply Matrix.ext; unfold tripleCharges sourceA1382 sourceB1382 sourceC1382 difference raw7640; decide +kernel
    rw [ha]
    exact (canonical7640 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1382 + difference 0 2) (sourceB1382 + difference 2 0) sourceC1382) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2519) := by
    have ha : (tripleCharges (sourceA1382 + difference 0 2) (sourceB1382 + difference 2 0) sourceC1382) = raw7641 := by
      apply Matrix.ext; unfold tripleCharges sourceA1382 sourceB1382 sourceC1382 difference raw7641; decide +kernel
    rw [ha]
    exact (canonical7641 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1382 + difference 0 3) (sourceB1382 + difference 3 0) sourceC1382) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2519) := by
    have ha : (tripleCharges (sourceA1382 + difference 0 3) (sourceB1382 + difference 3 0) sourceC1382) = raw7642 := by
      apply Matrix.ext; unfold tripleCharges sourceA1382 sourceB1382 sourceC1382 difference raw7642; decide +kernel
    rw [ha]
    exact (canonical7642 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1382 + difference 0 4) (sourceB1382 + difference 4 0) sourceC1382) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2770) := by
    have ha : (tripleCharges (sourceA1382 + difference 0 4) (sourceB1382 + difference 4 0) sourceC1382) = raw7643 := by
      apply Matrix.ext; unfold tripleCharges sourceA1382 sourceB1382 sourceC1382 difference raw7643; decide +kernel
    rw [ha]
    exact (canonical7643 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1382 + difference 0 5) (sourceB1382 + difference 5 0) sourceC1382) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2788) := by
    have ha : (tripleCharges (sourceA1382 + difference 0 5) (sourceB1382 + difference 5 0) sourceC1382) = raw21711 := by
      apply Matrix.ext; unfold tripleCharges sourceA1382 sourceB1382 sourceC1382 difference raw21711; decide +kernel
    rw [ha]
    exact (canonical21711 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1382 + difference 1 0) (sourceB1382 + difference 0 1) sourceC1382) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 559) := by
    have ha : (tripleCharges (sourceA1382 + difference 1 0) (sourceB1382 + difference 0 1) sourceC1382) = raw21712 := by
      apply Matrix.ext; unfold tripleCharges sourceA1382 sourceB1382 sourceC1382 difference raw21712; decide +kernel
    rw [ha]
    exact (canonical21712 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1382 + difference 1 2) (sourceB1382 + difference 2 1) sourceC1382) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 887) := by
    have ha : (tripleCharges (sourceA1382 + difference 1 2) (sourceB1382 + difference 2 1) sourceC1382) = raw21713 := by
      apply Matrix.ext; unfold tripleCharges sourceA1382 sourceB1382 sourceC1382 difference raw21713; decide +kernel
    rw [ha]
    exact (canonical21713 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1382 + difference 1 3) (sourceB1382 + difference 3 1) sourceC1382) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 887) := by
    have ha : (tripleCharges (sourceA1382 + difference 1 3) (sourceB1382 + difference 3 1) sourceC1382) = raw21714 := by
      apply Matrix.ext; unfold tripleCharges sourceA1382 sourceB1382 sourceC1382 difference raw21714; decide +kernel
    rw [ha]
    exact (canonical21714 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1382 + difference 1 4) (sourceB1382 + difference 4 1) sourceC1382) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1046) := by
    have ha : (tripleCharges (sourceA1382 + difference 1 4) (sourceB1382 + difference 4 1) sourceC1382) = raw21715 := by
      apply Matrix.ext; unfold tripleCharges sourceA1382 sourceB1382 sourceC1382 difference raw21715; decide +kernel
    rw [ha]
    exact (canonical21715 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1382 + difference 1 5) (sourceB1382 + difference 5 1) sourceC1382) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1087) := by
    have ha : (tripleCharges (sourceA1382 + difference 1 5) (sourceB1382 + difference 5 1) sourceC1382) = raw7619 := by
      apply Matrix.ext; unfold tripleCharges sourceA1382 sourceB1382 sourceC1382 difference raw7619; decide +kernel
    rw [ha]
    exact (canonical7619 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1382 + difference 2 0) (sourceB1382 + difference 0 2) sourceC1382) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 559) := by
    have ha : (tripleCharges (sourceA1382 + difference 2 0) (sourceB1382 + difference 0 2) sourceC1382) = raw21716 := by
      apply Matrix.ext; unfold tripleCharges sourceA1382 sourceB1382 sourceC1382 difference raw21716; decide +kernel
    rw [ha]
    exact (canonical21716 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1382 + difference 2 1) (sourceB1382 + difference 1 2) sourceC1382) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 887) := by
    have ha : (tripleCharges (sourceA1382 + difference 2 1) (sourceB1382 + difference 1 2) sourceC1382) = raw21717 := by
      apply Matrix.ext; unfold tripleCharges sourceA1382 sourceB1382 sourceC1382 difference raw21717; decide +kernel
    rw [ha]
    exact (canonical21717 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1382 + difference 2 3) (sourceB1382 + difference 3 2) sourceC1382) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 887) := by
    have ha : (tripleCharges (sourceA1382 + difference 2 3) (sourceB1382 + difference 3 2) sourceC1382) = raw21718 := by
      apply Matrix.ext; unfold tripleCharges sourceA1382 sourceB1382 sourceC1382 difference raw21718; decide +kernel
    rw [ha]
    exact (canonical21718 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1382 + difference 2 4) (sourceB1382 + difference 4 2) sourceC1382) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1046) := by
    have ha : (tripleCharges (sourceA1382 + difference 2 4) (sourceB1382 + difference 4 2) sourceC1382) = raw21719 := by
      apply Matrix.ext; unfold tripleCharges sourceA1382 sourceB1382 sourceC1382 difference raw21719; decide +kernel
    rw [ha]
    exact (canonical21719 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1382 + difference 2 5) (sourceB1382 + difference 5 2) sourceC1382) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1087) := by
    have ha : (tripleCharges (sourceA1382 + difference 2 5) (sourceB1382 + difference 5 2) sourceC1382) = raw7624 := by
      apply Matrix.ext; unfold tripleCharges sourceA1382 sourceB1382 sourceC1382 difference raw7624; decide +kernel
    rw [ha]
    exact (canonical7624 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1382 + difference 3 0) (sourceB1382 + difference 0 3) sourceC1382) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 559) := by
    have ha : (tripleCharges (sourceA1382 + difference 3 0) (sourceB1382 + difference 0 3) sourceC1382) = raw21720 := by
      apply Matrix.ext; unfold tripleCharges sourceA1382 sourceB1382 sourceC1382 difference raw21720; decide +kernel
    rw [ha]
    exact (canonical21720 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1382 + difference 3 1) (sourceB1382 + difference 1 3) sourceC1382) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 887) := by
    have ha : (tripleCharges (sourceA1382 + difference 3 1) (sourceB1382 + difference 1 3) sourceC1382) = raw21721 := by
      apply Matrix.ext; unfold tripleCharges sourceA1382 sourceB1382 sourceC1382 difference raw21721; decide +kernel
    rw [ha]
    exact (canonical21721 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1382 + difference 3 2) (sourceB1382 + difference 2 3) sourceC1382) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 887) := by
    have ha : (tripleCharges (sourceA1382 + difference 3 2) (sourceB1382 + difference 2 3) sourceC1382) = raw21722 := by
      apply Matrix.ext; unfold tripleCharges sourceA1382 sourceB1382 sourceC1382 difference raw21722; decide +kernel
    rw [ha]
    exact (canonical21722 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1382 + difference 3 4) (sourceB1382 + difference 4 3) sourceC1382) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1046) := by
    have ha : (tripleCharges (sourceA1382 + difference 3 4) (sourceB1382 + difference 4 3) sourceC1382) = raw21723 := by
      apply Matrix.ext; unfold tripleCharges sourceA1382 sourceB1382 sourceC1382 difference raw21723; decide +kernel
    rw [ha]
    exact (canonical21723 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1382 + difference 3 5) (sourceB1382 + difference 5 3) sourceC1382) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1087) := by
    have ha : (tripleCharges (sourceA1382 + difference 3 5) (sourceB1382 + difference 5 3) sourceC1382) = raw7629 := by
      apply Matrix.ext; unfold tripleCharges sourceA1382 sourceB1382 sourceC1382 difference raw7629; decide +kernel
    rw [ha]
    exact (canonical7629 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1382 + difference 4 0) (sourceB1382 + difference 0 4) sourceC1382) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 566) := by
    have ha : (tripleCharges (sourceA1382 + difference 4 0) (sourceB1382 + difference 0 4) sourceC1382) = raw21724 := by
      apply Matrix.ext; unfold tripleCharges sourceA1382 sourceB1382 sourceC1382 difference raw21724; decide +kernel
    rw [ha]
    exact (canonical21724 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1382 + difference 4 1) (sourceB1382 + difference 1 4) sourceC1382) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 897) := by
    have ha : (tripleCharges (sourceA1382 + difference 4 1) (sourceB1382 + difference 1 4) sourceC1382) = raw21725 := by
      apply Matrix.ext; unfold tripleCharges sourceA1382 sourceB1382 sourceC1382 difference raw21725; decide +kernel
    rw [ha]
    exact (canonical21725 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1382 + difference 4 2) (sourceB1382 + difference 2 4) sourceC1382) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 897) := by
    have ha : (tripleCharges (sourceA1382 + difference 4 2) (sourceB1382 + difference 2 4) sourceC1382) = raw21726 := by
      apply Matrix.ext; unfold tripleCharges sourceA1382 sourceB1382 sourceC1382 difference raw21726; decide +kernel
    rw [ha]
    exact (canonical21726 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1382 + difference 4 3) (sourceB1382 + difference 3 4) sourceC1382) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 897) := by
    have ha : (tripleCharges (sourceA1382 + difference 4 3) (sourceB1382 + difference 3 4) sourceC1382) = raw21727 := by
      apply Matrix.ext; unfold tripleCharges sourceA1382 sourceB1382 sourceC1382 difference raw21727; decide +kernel
    rw [ha]
    exact (canonical21727 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1382 + difference 4 5) (sourceB1382 + difference 5 4) sourceC1382) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1094) := by
    have ha : (tripleCharges (sourceA1382 + difference 4 5) (sourceB1382 + difference 5 4) sourceC1382) = raw7634 := by
      apply Matrix.ext; unfold tripleCharges sourceA1382 sourceB1382 sourceC1382 difference raw7634; decide +kernel
    rw [ha]
    exact (canonical7634 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1382 + difference 5 0) (sourceB1382 + difference 0 5) sourceC1382) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 564) := by
    have ha : (tripleCharges (sourceA1382 + difference 5 0) (sourceB1382 + difference 0 5) sourceC1382) = raw21728 := by
      apply Matrix.ext; unfold tripleCharges sourceA1382 sourceB1382 sourceC1382 difference raw21728; decide +kernel
    rw [ha]
    exact (canonical21728 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1382 + difference 5 1) (sourceB1382 + difference 1 5) sourceC1382) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 893) := by
    have ha : (tripleCharges (sourceA1382 + difference 5 1) (sourceB1382 + difference 1 5) sourceC1382) = raw21729 := by
      apply Matrix.ext; unfold tripleCharges sourceA1382 sourceB1382 sourceC1382 difference raw21729; decide +kernel
    rw [ha]
    exact (canonical21729 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1382 + difference 5 2) (sourceB1382 + difference 2 5) sourceC1382) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 893) := by
    have ha : (tripleCharges (sourceA1382 + difference 5 2) (sourceB1382 + difference 2 5) sourceC1382) = raw21730 := by
      apply Matrix.ext; unfold tripleCharges sourceA1382 sourceB1382 sourceC1382 difference raw21730; decide +kernel
    rw [ha]
    exact (canonical21730 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1382 + difference 5 3) (sourceB1382 + difference 3 5) sourceC1382) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 893) := by
    have ha : (tripleCharges (sourceA1382 + difference 5 3) (sourceB1382 + difference 3 5) sourceC1382) = raw21731 := by
      apply Matrix.ext; unfold tripleCharges sourceA1382 sourceB1382 sourceC1382 difference raw21731; decide +kernel
    rw [ha]
    exact (canonical21731 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1382 + difference 5 4) (sourceB1382 + difference 4 5) sourceC1382) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1051) := by
    have ha : (tripleCharges (sourceA1382 + difference 5 4) (sourceB1382 + difference 4 5) sourceC1382) = raw21732 := by
      apply Matrix.ext; unfold tripleCharges sourceA1382 sourceB1382 sourceC1382 difference raw21732; decide +kernel
    rw [ha]
    exact (canonical21732 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1382 sourceB1382 sourceC1382
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1382, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1383 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceB1383 : Charge := ![3, 0, 0, 0, -2, -1]
def sourceC1383 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1383 : Integer.Sparse Master := [(Sum.inr 4270, 3), (Sum.inr 4284, 1), (Sum.inr 4285, 1), (Sum.inr 4402, 6), (Sum.inr 4428, 3), (Sum.inr 4429, 3), (Sum.inr 4463, 3), (Sum.inr 4464, 3), (Sum.inr 4505, 1), (Sum.inr 4508, 1), (Sum.inr 4609, 3), (Sum.inr 4621, 1), (Sum.inr 4625, 1)]

theorem sourceEq1383 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1383 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1383 + difference 0 1) (sourceB1383 + difference 1 0) sourceC1383) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4609) := by
    have ha : (tripleCharges (sourceA1383 + difference 0 1) (sourceB1383 + difference 1 0) sourceC1383) = raw21733 := by
      apply Matrix.ext; unfold tripleCharges sourceA1383 sourceB1383 sourceC1383 difference raw21733; decide +kernel
    rw [ha]
    exact (canonical21733 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1383 + difference 0 2) (sourceB1383 + difference 2 0) sourceC1383) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4609) := by
    have ha : (tripleCharges (sourceA1383 + difference 0 2) (sourceB1383 + difference 2 0) sourceC1383) = raw21734 := by
      apply Matrix.ext; unfold tripleCharges sourceA1383 sourceB1383 sourceC1383 difference raw21734; decide +kernel
    rw [ha]
    exact (canonical21734 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1383 + difference 0 3) (sourceB1383 + difference 3 0) sourceC1383) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4609) := by
    have ha : (tripleCharges (sourceA1383 + difference 0 3) (sourceB1383 + difference 3 0) sourceC1383) = raw20807 := by
      apply Matrix.ext; unfold tripleCharges sourceA1383 sourceB1383 sourceC1383 difference raw20807; decide +kernel
    rw [ha]
    exact (canonical20807 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1383 + difference 0 4) (sourceB1383 + difference 4 0) sourceC1383) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4625) := by
    have ha : (tripleCharges (sourceA1383 + difference 0 4) (sourceB1383 + difference 4 0) sourceC1383) = raw20438 := by
      apply Matrix.ext; unfold tripleCharges sourceA1383 sourceB1383 sourceC1383 difference raw20438; decide +kernel
    rw [ha]
    exact (canonical20438 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1383 + difference 0 5) (sourceB1383 + difference 5 0) sourceC1383) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4621) := by
    have ha : (tripleCharges (sourceA1383 + difference 0 5) (sourceB1383 + difference 5 0) sourceC1383) = raw21735 := by
      apply Matrix.ext; unfold tripleCharges sourceA1383 sourceB1383 sourceC1383 difference raw21735; decide +kernel
    rw [ha]
    exact (canonical21735 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1383 + difference 1 0) (sourceB1383 + difference 0 1) sourceC1383) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4270) := by
    have ha : (tripleCharges (sourceA1383 + difference 1 0) (sourceB1383 + difference 0 1) sourceC1383) = raw21308 := by
      apply Matrix.ext; unfold tripleCharges sourceA1383 sourceB1383 sourceC1383 difference raw21308; decide +kernel
    rw [ha]
    exact (canonical21308 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1383 + difference 1 2) (sourceB1383 + difference 2 1) sourceC1383) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4402) := by
    have ha : (tripleCharges (sourceA1383 + difference 1 2) (sourceB1383 + difference 2 1) sourceC1383) = raw21310 := by
      apply Matrix.ext; unfold tripleCharges sourceA1383 sourceB1383 sourceC1383 difference raw21310; decide +kernel
    rw [ha]
    exact (canonical21310 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1383 + difference 1 3) (sourceB1383 + difference 3 1) sourceC1383) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4402) := by
    have ha : (tripleCharges (sourceA1383 + difference 1 3) (sourceB1383 + difference 3 1) sourceC1383) = raw21311 := by
      apply Matrix.ext; unfold tripleCharges sourceA1383 sourceB1383 sourceC1383 difference raw21311; decide +kernel
    rw [ha]
    exact (canonical21311 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1383 + difference 1 4) (sourceB1383 + difference 4 1) sourceC1383) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4463) := by
    have ha : (tripleCharges (sourceA1383 + difference 1 4) (sourceB1383 + difference 4 1) sourceC1383) = raw21530 := by
      apply Matrix.ext; unfold tripleCharges sourceA1383 sourceB1383 sourceC1383 difference raw21530; decide +kernel
    rw [ha]
    exact (canonical21530 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1383 + difference 1 5) (sourceB1383 + difference 5 1) sourceC1383) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4464) := by
    have ha : (tripleCharges (sourceA1383 + difference 1 5) (sourceB1383 + difference 5 1) sourceC1383) = raw21312 := by
      apply Matrix.ext; unfold tripleCharges sourceA1383 sourceB1383 sourceC1383 difference raw21312; decide +kernel
    rw [ha]
    exact (canonical21312 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1383 + difference 2 0) (sourceB1383 + difference 0 2) sourceC1383) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4270) := by
    have ha : (tripleCharges (sourceA1383 + difference 2 0) (sourceB1383 + difference 0 2) sourceC1383) = raw21736 := by
      apply Matrix.ext; unfold tripleCharges sourceA1383 sourceB1383 sourceC1383 difference raw21736; decide +kernel
    rw [ha]
    exact (canonical21736 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1383 + difference 2 1) (sourceB1383 + difference 1 2) sourceC1383) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4402) := by
    have ha : (tripleCharges (sourceA1383 + difference 2 1) (sourceB1383 + difference 1 2) sourceC1383) = raw21737 := by
      apply Matrix.ext; unfold tripleCharges sourceA1383 sourceB1383 sourceC1383 difference raw21737; decide +kernel
    rw [ha]
    exact (canonical21737 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1383 + difference 2 3) (sourceB1383 + difference 3 2) sourceC1383) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4402) := by
    have ha : (tripleCharges (sourceA1383 + difference 2 3) (sourceB1383 + difference 3 2) sourceC1383) = raw21738 := by
      apply Matrix.ext; unfold tripleCharges sourceA1383 sourceB1383 sourceC1383 difference raw21738; decide +kernel
    rw [ha]
    exact (canonical21738 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1383 + difference 2 4) (sourceB1383 + difference 4 2) sourceC1383) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4463) := by
    have ha : (tripleCharges (sourceA1383 + difference 2 4) (sourceB1383 + difference 4 2) sourceC1383) = raw21299 := by
      apply Matrix.ext; unfold tripleCharges sourceA1383 sourceB1383 sourceC1383 difference raw21299; decide +kernel
    rw [ha]
    exact (canonical21299 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1383 + difference 2 5) (sourceB1383 + difference 5 2) sourceC1383) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4464) := by
    have ha : (tripleCharges (sourceA1383 + difference 2 5) (sourceB1383 + difference 5 2) sourceC1383) = raw21739 := by
      apply Matrix.ext; unfold tripleCharges sourceA1383 sourceB1383 sourceC1383 difference raw21739; decide +kernel
    rw [ha]
    exact (canonical21739 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1383 + difference 3 0) (sourceB1383 + difference 0 3) sourceC1383) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4270) := by
    have ha : (tripleCharges (sourceA1383 + difference 3 0) (sourceB1383 + difference 0 3) sourceC1383) = raw21740 := by
      apply Matrix.ext; unfold tripleCharges sourceA1383 sourceB1383 sourceC1383 difference raw21740; decide +kernel
    rw [ha]
    exact (canonical21740 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1383 + difference 3 1) (sourceB1383 + difference 1 3) sourceC1383) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4402) := by
    have ha : (tripleCharges (sourceA1383 + difference 3 1) (sourceB1383 + difference 1 3) sourceC1383) = raw21741 := by
      apply Matrix.ext; unfold tripleCharges sourceA1383 sourceB1383 sourceC1383 difference raw21741; decide +kernel
    rw [ha]
    exact (canonical21741 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1383 + difference 3 2) (sourceB1383 + difference 2 3) sourceC1383) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4402) := by
    have ha : (tripleCharges (sourceA1383 + difference 3 2) (sourceB1383 + difference 2 3) sourceC1383) = raw21742 := by
      apply Matrix.ext; unfold tripleCharges sourceA1383 sourceB1383 sourceC1383 difference raw21742; decide +kernel
    rw [ha]
    exact (canonical21742 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1383 + difference 3 4) (sourceB1383 + difference 4 3) sourceC1383) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4463) := by
    have ha : (tripleCharges (sourceA1383 + difference 3 4) (sourceB1383 + difference 4 3) sourceC1383) = raw21304 := by
      apply Matrix.ext; unfold tripleCharges sourceA1383 sourceB1383 sourceC1383 difference raw21304; decide +kernel
    rw [ha]
    exact (canonical21304 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1383 + difference 3 5) (sourceB1383 + difference 5 3) sourceC1383) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4464) := by
    have ha : (tripleCharges (sourceA1383 + difference 3 5) (sourceB1383 + difference 5 3) sourceC1383) = raw21743 := by
      apply Matrix.ext; unfold tripleCharges sourceA1383 sourceB1383 sourceC1383 difference raw21743; decide +kernel
    rw [ha]
    exact (canonical21743 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1383 + difference 4 0) (sourceB1383 + difference 0 4) sourceC1383) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4285) := by
    have ha : (tripleCharges (sourceA1383 + difference 4 0) (sourceB1383 + difference 0 4) sourceC1383) = raw21744 := by
      apply Matrix.ext; unfold tripleCharges sourceA1383 sourceB1383 sourceC1383 difference raw21744; decide +kernel
    rw [ha]
    exact (canonical21744 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1383 + difference 4 1) (sourceB1383 + difference 1 4) sourceC1383) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4429) := by
    have ha : (tripleCharges (sourceA1383 + difference 4 1) (sourceB1383 + difference 1 4) sourceC1383) = raw21745 := by
      apply Matrix.ext; unfold tripleCharges sourceA1383 sourceB1383 sourceC1383 difference raw21745; decide +kernel
    rw [ha]
    exact (canonical21745 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1383 + difference 4 2) (sourceB1383 + difference 2 4) sourceC1383) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4429) := by
    have ha : (tripleCharges (sourceA1383 + difference 4 2) (sourceB1383 + difference 2 4) sourceC1383) = raw21746 := by
      apply Matrix.ext; unfold tripleCharges sourceA1383 sourceB1383 sourceC1383 difference raw21746; decide +kernel
    rw [ha]
    exact (canonical21746 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1383 + difference 4 3) (sourceB1383 + difference 3 4) sourceC1383) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4429) := by
    have ha : (tripleCharges (sourceA1383 + difference 4 3) (sourceB1383 + difference 3 4) sourceC1383) = raw21747 := by
      apply Matrix.ext; unfold tripleCharges sourceA1383 sourceB1383 sourceC1383 difference raw21747; decide +kernel
    rw [ha]
    exact (canonical21747 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1383 + difference 4 5) (sourceB1383 + difference 5 4) sourceC1383) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4508) := by
    have ha : (tripleCharges (sourceA1383 + difference 4 5) (sourceB1383 + difference 5 4) sourceC1383) = raw21748 := by
      apply Matrix.ext; unfold tripleCharges sourceA1383 sourceB1383 sourceC1383 difference raw21748; decide +kernel
    rw [ha]
    exact (canonical21748 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1383 + difference 5 0) (sourceB1383 + difference 0 5) sourceC1383) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4284) := by
    have ha : (tripleCharges (sourceA1383 + difference 5 0) (sourceB1383 + difference 0 5) sourceC1383) = raw21749 := by
      apply Matrix.ext; unfold tripleCharges sourceA1383 sourceB1383 sourceC1383 difference raw21749; decide +kernel
    rw [ha]
    exact (canonical21749 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1383 + difference 5 1) (sourceB1383 + difference 1 5) sourceC1383) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4428) := by
    have ha : (tripleCharges (sourceA1383 + difference 5 1) (sourceB1383 + difference 1 5) sourceC1383) = raw21750 := by
      apply Matrix.ext; unfold tripleCharges sourceA1383 sourceB1383 sourceC1383 difference raw21750; decide +kernel
    rw [ha]
    exact (canonical21750 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1383 + difference 5 2) (sourceB1383 + difference 2 5) sourceC1383) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4428) := by
    have ha : (tripleCharges (sourceA1383 + difference 5 2) (sourceB1383 + difference 2 5) sourceC1383) = raw21751 := by
      apply Matrix.ext; unfold tripleCharges sourceA1383 sourceB1383 sourceC1383 difference raw21751; decide +kernel
    rw [ha]
    exact (canonical21751 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1383 + difference 5 3) (sourceB1383 + difference 3 5) sourceC1383) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4428) := by
    have ha : (tripleCharges (sourceA1383 + difference 5 3) (sourceB1383 + difference 3 5) sourceC1383) = raw20803 := by
      apply Matrix.ext; unfold tripleCharges sourceA1383 sourceB1383 sourceC1383 difference raw20803; decide +kernel
    rw [ha]
    exact (canonical20803 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1383 + difference 5 4) (sourceB1383 + difference 4 5) sourceC1383) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4505) := by
    have ha : (tripleCharges (sourceA1383 + difference 5 4) (sourceB1383 + difference 4 5) sourceC1383) = raw20434 := by
      apply Matrix.ext; unfold tripleCharges sourceA1383 sourceB1383 sourceC1383 difference raw20434; decide +kernel
    rw [ha]
    exact (canonical20434 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1383 sourceB1383 sourceC1383
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1383, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1384 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceB1384 : Charge := ![3, 0, 0, 0, -2, -1]
def sourceC1384 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1384 : Integer.Sparse Master := [(Sum.inr 813, 3), (Sum.inr 859, 1), (Sum.inr 860, 1), (Sum.inr 983, 6), (Sum.inr 1009, 3), (Sum.inr 1010, 3), (Sum.inr 1046, 3), (Sum.inr 1047, 3), (Sum.inr 1089, 1), (Sum.inr 1092, 1), (Sum.inr 1243, 3), (Sum.inr 1307, 1), (Sum.inr 1308, 1)]

theorem sourceEq1384 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1384 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1384 + difference 0 1) (sourceB1384 + difference 1 0) sourceC1384) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1243) := by
    have ha : (tripleCharges (sourceA1384 + difference 0 1) (sourceB1384 + difference 1 0) sourceC1384) = raw21752 := by
      apply Matrix.ext; unfold tripleCharges sourceA1384 sourceB1384 sourceC1384 difference raw21752; decide +kernel
    rw [ha]
    exact (canonical21752 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1384 + difference 0 2) (sourceB1384 + difference 2 0) sourceC1384) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1243) := by
    have ha : (tripleCharges (sourceA1384 + difference 0 2) (sourceB1384 + difference 2 0) sourceC1384) = raw21753 := by
      apply Matrix.ext; unfold tripleCharges sourceA1384 sourceB1384 sourceC1384 difference raw21753; decide +kernel
    rw [ha]
    exact (canonical21753 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1384 + difference 0 3) (sourceB1384 + difference 3 0) sourceC1384) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1243) := by
    have ha : (tripleCharges (sourceA1384 + difference 0 3) (sourceB1384 + difference 3 0) sourceC1384) = raw20835 := by
      apply Matrix.ext; unfold tripleCharges sourceA1384 sourceB1384 sourceC1384 difference raw20835; decide +kernel
    rw [ha]
    exact (canonical20835 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1384 + difference 0 4) (sourceB1384 + difference 4 0) sourceC1384) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1307) := by
    have ha : (tripleCharges (sourceA1384 + difference 0 4) (sourceB1384 + difference 4 0) sourceC1384) = raw20830 := by
      apply Matrix.ext; unfold tripleCharges sourceA1384 sourceB1384 sourceC1384 difference raw20830; decide +kernel
    rw [ha]
    exact (canonical20830 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1384 + difference 0 5) (sourceB1384 + difference 5 0) sourceC1384) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1308) := by
    have ha : (tripleCharges (sourceA1384 + difference 0 5) (sourceB1384 + difference 5 0) sourceC1384) = raw21754 := by
      apply Matrix.ext; unfold tripleCharges sourceA1384 sourceB1384 sourceC1384 difference raw21754; decide +kernel
    rw [ha]
    exact (canonical21754 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1384 + difference 1 0) (sourceB1384 + difference 0 1) sourceC1384) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 813) := by
    have ha : (tripleCharges (sourceA1384 + difference 1 0) (sourceB1384 + difference 0 1) sourceC1384) = raw21333 := by
      apply Matrix.ext; unfold tripleCharges sourceA1384 sourceB1384 sourceC1384 difference raw21333; decide +kernel
    rw [ha]
    exact (canonical21333 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1384 + difference 1 2) (sourceB1384 + difference 2 1) sourceC1384) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 983) := by
    have ha : (tripleCharges (sourceA1384 + difference 1 2) (sourceB1384 + difference 2 1) sourceC1384) = raw21335 := by
      apply Matrix.ext; unfold tripleCharges sourceA1384 sourceB1384 sourceC1384 difference raw21335; decide +kernel
    rw [ha]
    exact (canonical21335 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1384 + difference 1 3) (sourceB1384 + difference 3 1) sourceC1384) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 983) := by
    have ha : (tripleCharges (sourceA1384 + difference 1 3) (sourceB1384 + difference 3 1) sourceC1384) = raw21336 := by
      apply Matrix.ext; unfold tripleCharges sourceA1384 sourceB1384 sourceC1384 difference raw21336; decide +kernel
    rw [ha]
    exact (canonical21336 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1384 + difference 1 4) (sourceB1384 + difference 4 1) sourceC1384) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1046) := by
    have ha : (tripleCharges (sourceA1384 + difference 1 4) (sourceB1384 + difference 4 1) sourceC1384) = raw21546 := by
      apply Matrix.ext; unfold tripleCharges sourceA1384 sourceB1384 sourceC1384 difference raw21546; decide +kernel
    rw [ha]
    exact (canonical21546 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1384 + difference 1 5) (sourceB1384 + difference 5 1) sourceC1384) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1047) := by
    have ha : (tripleCharges (sourceA1384 + difference 1 5) (sourceB1384 + difference 5 1) sourceC1384) = raw21337 := by
      apply Matrix.ext; unfold tripleCharges sourceA1384 sourceB1384 sourceC1384 difference raw21337; decide +kernel
    rw [ha]
    exact (canonical21337 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1384 + difference 2 0) (sourceB1384 + difference 0 2) sourceC1384) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 813) := by
    have ha : (tripleCharges (sourceA1384 + difference 2 0) (sourceB1384 + difference 0 2) sourceC1384) = raw21755 := by
      apply Matrix.ext; unfold tripleCharges sourceA1384 sourceB1384 sourceC1384 difference raw21755; decide +kernel
    rw [ha]
    exact (canonical21755 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1384 + difference 2 1) (sourceB1384 + difference 1 2) sourceC1384) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 983) := by
    have ha : (tripleCharges (sourceA1384 + difference 2 1) (sourceB1384 + difference 1 2) sourceC1384) = raw21756 := by
      apply Matrix.ext; unfold tripleCharges sourceA1384 sourceB1384 sourceC1384 difference raw21756; decide +kernel
    rw [ha]
    exact (canonical21756 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1384 + difference 2 3) (sourceB1384 + difference 3 2) sourceC1384) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 983) := by
    have ha : (tripleCharges (sourceA1384 + difference 2 3) (sourceB1384 + difference 3 2) sourceC1384) = raw21757 := by
      apply Matrix.ext; unfold tripleCharges sourceA1384 sourceB1384 sourceC1384 difference raw21757; decide +kernel
    rw [ha]
    exact (canonical21757 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1384 + difference 2 4) (sourceB1384 + difference 4 2) sourceC1384) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1046) := by
    have ha : (tripleCharges (sourceA1384 + difference 2 4) (sourceB1384 + difference 4 2) sourceC1384) = raw21324 := by
      apply Matrix.ext; unfold tripleCharges sourceA1384 sourceB1384 sourceC1384 difference raw21324; decide +kernel
    rw [ha]
    exact (canonical21324 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1384 + difference 2 5) (sourceB1384 + difference 5 2) sourceC1384) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1047) := by
    have ha : (tripleCharges (sourceA1384 + difference 2 5) (sourceB1384 + difference 5 2) sourceC1384) = raw21758 := by
      apply Matrix.ext; unfold tripleCharges sourceA1384 sourceB1384 sourceC1384 difference raw21758; decide +kernel
    rw [ha]
    exact (canonical21758 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1384 + difference 3 0) (sourceB1384 + difference 0 3) sourceC1384) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 813) := by
    have ha : (tripleCharges (sourceA1384 + difference 3 0) (sourceB1384 + difference 0 3) sourceC1384) = raw21759 := by
      apply Matrix.ext; unfold tripleCharges sourceA1384 sourceB1384 sourceC1384 difference raw21759; decide +kernel
    rw [ha]
    exact (canonical21759 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1384 + difference 3 1) (sourceB1384 + difference 1 3) sourceC1384) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 983) := by
    have ha : (tripleCharges (sourceA1384 + difference 3 1) (sourceB1384 + difference 1 3) sourceC1384) = raw21760 := by
      apply Matrix.ext; unfold tripleCharges sourceA1384 sourceB1384 sourceC1384 difference raw21760; decide +kernel
    rw [ha]
    exact (canonical21760 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1384 + difference 3 2) (sourceB1384 + difference 2 3) sourceC1384) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 983) := by
    have ha : (tripleCharges (sourceA1384 + difference 3 2) (sourceB1384 + difference 2 3) sourceC1384) = raw21761 := by
      apply Matrix.ext; unfold tripleCharges sourceA1384 sourceB1384 sourceC1384 difference raw21761; decide +kernel
    rw [ha]
    exact (canonical21761 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1384 + difference 3 4) (sourceB1384 + difference 4 3) sourceC1384) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1046) := by
    have ha : (tripleCharges (sourceA1384 + difference 3 4) (sourceB1384 + difference 4 3) sourceC1384) = raw21329 := by
      apply Matrix.ext; unfold tripleCharges sourceA1384 sourceB1384 sourceC1384 difference raw21329; decide +kernel
    rw [ha]
    exact (canonical21329 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1384 + difference 3 5) (sourceB1384 + difference 5 3) sourceC1384) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1047) := by
    have ha : (tripleCharges (sourceA1384 + difference 3 5) (sourceB1384 + difference 5 3) sourceC1384) = raw21762 := by
      apply Matrix.ext; unfold tripleCharges sourceA1384 sourceB1384 sourceC1384 difference raw21762; decide +kernel
    rw [ha]
    exact (canonical21762 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1384 + difference 4 0) (sourceB1384 + difference 0 4) sourceC1384) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 860) := by
    have ha : (tripleCharges (sourceA1384 + difference 4 0) (sourceB1384 + difference 0 4) sourceC1384) = raw21763 := by
      apply Matrix.ext; unfold tripleCharges sourceA1384 sourceB1384 sourceC1384 difference raw21763; decide +kernel
    rw [ha]
    exact (canonical21763 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1384 + difference 4 1) (sourceB1384 + difference 1 4) sourceC1384) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1010) := by
    have ha : (tripleCharges (sourceA1384 + difference 4 1) (sourceB1384 + difference 1 4) sourceC1384) = raw21764 := by
      apply Matrix.ext; unfold tripleCharges sourceA1384 sourceB1384 sourceC1384 difference raw21764; decide +kernel
    rw [ha]
    exact (canonical21764 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1384 + difference 4 2) (sourceB1384 + difference 2 4) sourceC1384) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1010) := by
    have ha : (tripleCharges (sourceA1384 + difference 4 2) (sourceB1384 + difference 2 4) sourceC1384) = raw21765 := by
      apply Matrix.ext; unfold tripleCharges sourceA1384 sourceB1384 sourceC1384 difference raw21765; decide +kernel
    rw [ha]
    exact (canonical21765 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1384 + difference 4 3) (sourceB1384 + difference 3 4) sourceC1384) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1010) := by
    have ha : (tripleCharges (sourceA1384 + difference 4 3) (sourceB1384 + difference 3 4) sourceC1384) = raw21766 := by
      apply Matrix.ext; unfold tripleCharges sourceA1384 sourceB1384 sourceC1384 difference raw21766; decide +kernel
    rw [ha]
    exact (canonical21766 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1384 + difference 4 5) (sourceB1384 + difference 5 4) sourceC1384) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1092) := by
    have ha : (tripleCharges (sourceA1384 + difference 4 5) (sourceB1384 + difference 5 4) sourceC1384) = raw21767 := by
      apply Matrix.ext; unfold tripleCharges sourceA1384 sourceB1384 sourceC1384 difference raw21767; decide +kernel
    rw [ha]
    exact (canonical21767 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1384 + difference 5 0) (sourceB1384 + difference 0 5) sourceC1384) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 859) := by
    have ha : (tripleCharges (sourceA1384 + difference 5 0) (sourceB1384 + difference 0 5) sourceC1384) = raw21768 := by
      apply Matrix.ext; unfold tripleCharges sourceA1384 sourceB1384 sourceC1384 difference raw21768; decide +kernel
    rw [ha]
    exact (canonical21768 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1384 + difference 5 1) (sourceB1384 + difference 1 5) sourceC1384) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1009) := by
    have ha : (tripleCharges (sourceA1384 + difference 5 1) (sourceB1384 + difference 1 5) sourceC1384) = raw21769 := by
      apply Matrix.ext; unfold tripleCharges sourceA1384 sourceB1384 sourceC1384 difference raw21769; decide +kernel
    rw [ha]
    exact (canonical21769 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1384 + difference 5 2) (sourceB1384 + difference 2 5) sourceC1384) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1009) := by
    have ha : (tripleCharges (sourceA1384 + difference 5 2) (sourceB1384 + difference 2 5) sourceC1384) = raw21770 := by
      apply Matrix.ext; unfold tripleCharges sourceA1384 sourceB1384 sourceC1384 difference raw21770; decide +kernel
    rw [ha]
    exact (canonical21770 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1384 + difference 5 3) (sourceB1384 + difference 3 5) sourceC1384) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1009) := by
    have ha : (tripleCharges (sourceA1384 + difference 5 3) (sourceB1384 + difference 3 5) sourceC1384) = raw20831 := by
      apply Matrix.ext; unfold tripleCharges sourceA1384 sourceB1384 sourceC1384 difference raw20831; decide +kernel
    rw [ha]
    exact (canonical20831 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1384 + difference 5 4) (sourceB1384 + difference 4 5) sourceC1384) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1089) := by
    have ha : (tripleCharges (sourceA1384 + difference 5 4) (sourceB1384 + difference 4 5) sourceC1384) = raw20827 := by
      apply Matrix.ext; unfold tripleCharges sourceA1384 sourceB1384 sourceC1384 difference raw20827; decide +kernel
    rw [ha]
    exact (canonical20827 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1384 sourceB1384 sourceC1384
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1384, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1385 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1385 : Charge := ![1, 0, 0, 0, 0, -1]
def sourceC1385 : Charge := ![3, 0, 0, 0, -1, -2]
def sourceForm1385 : Integer.Sparse Master := [(Sum.inr 4084, 1), (Sum.inr 4177, 3), (Sum.inr 4187, 1), (Sum.inr 4191, 1), (Sum.inr 4346, 6), (Sum.inr 4356, 3), (Sum.inr 4360, 3), (Sum.inr 4460, 3), (Sum.inr 4468, 1), (Sum.inr 4498, 3), (Sum.inr 4511, 1), (Sum.inr 4841, 3), (Sum.inr 4897, 1)]

theorem sourceEq1385 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1385 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1385 + difference 0 1) (sourceB1385 + difference 1 0) sourceC1385) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4841) := by
    have ha : (tripleCharges (sourceA1385 + difference 0 1) (sourceB1385 + difference 1 0) sourceC1385) = raw21771 := by
      apply Matrix.ext; unfold tripleCharges sourceA1385 sourceB1385 sourceC1385 difference raw21771; decide +kernel
    rw [ha]
    exact (canonical21771 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1385 + difference 0 2) (sourceB1385 + difference 2 0) sourceC1385) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4841) := by
    have ha : (tripleCharges (sourceA1385 + difference 0 2) (sourceB1385 + difference 2 0) sourceC1385) = raw21772 := by
      apply Matrix.ext; unfold tripleCharges sourceA1385 sourceB1385 sourceC1385 difference raw21772; decide +kernel
    rw [ha]
    exact (canonical21772 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1385 + difference 0 3) (sourceB1385 + difference 3 0) sourceC1385) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4841) := by
    have ha : (tripleCharges (sourceA1385 + difference 0 3) (sourceB1385 + difference 3 0) sourceC1385) = raw21773 := by
      apply Matrix.ext; unfold tripleCharges sourceA1385 sourceB1385 sourceC1385 difference raw21773; decide +kernel
    rw [ha]
    exact (canonical21773 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1385 + difference 0 4) (sourceB1385 + difference 4 0) sourceC1385) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4897) := by
    have ha : (tripleCharges (sourceA1385 + difference 0 4) (sourceB1385 + difference 4 0) sourceC1385) = raw21774 := by
      apply Matrix.ext; unfold tripleCharges sourceA1385 sourceB1385 sourceC1385 difference raw21774; decide +kernel
    rw [ha]
    exact (canonical21774 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1385 + difference 0 5) (sourceB1385 + difference 5 0) sourceC1385) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA1385 + difference 0 5) (sourceB1385 + difference 5 0) sourceC1385) = raw21775 := by
      apply Matrix.ext; unfold tripleCharges sourceA1385 sourceB1385 sourceC1385 difference raw21775; decide +kernel
    rw [ha]
    exact (canonical21775 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1385 + difference 1 0) (sourceB1385 + difference 0 1) sourceC1385) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4177) := by
    have ha : (tripleCharges (sourceA1385 + difference 1 0) (sourceB1385 + difference 0 1) sourceC1385) = raw21776 := by
      apply Matrix.ext; unfold tripleCharges sourceA1385 sourceB1385 sourceC1385 difference raw21776; decide +kernel
    rw [ha]
    exact (canonical21776 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1385 + difference 1 2) (sourceB1385 + difference 2 1) sourceC1385) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4346) := by
    have ha : (tripleCharges (sourceA1385 + difference 1 2) (sourceB1385 + difference 2 1) sourceC1385) = raw21777 := by
      apply Matrix.ext; unfold tripleCharges sourceA1385 sourceB1385 sourceC1385 difference raw21777; decide +kernel
    rw [ha]
    exact (canonical21777 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1385 + difference 1 3) (sourceB1385 + difference 3 1) sourceC1385) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4346) := by
    have ha : (tripleCharges (sourceA1385 + difference 1 3) (sourceB1385 + difference 3 1) sourceC1385) = raw21778 := by
      apply Matrix.ext; unfold tripleCharges sourceA1385 sourceB1385 sourceC1385 difference raw21778; decide +kernel
    rw [ha]
    exact (canonical21778 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1385 + difference 1 4) (sourceB1385 + difference 4 1) sourceC1385) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4460) := by
    have ha : (tripleCharges (sourceA1385 + difference 1 4) (sourceB1385 + difference 4 1) sourceC1385) = raw21779 := by
      apply Matrix.ext; unfold tripleCharges sourceA1385 sourceB1385 sourceC1385 difference raw21779; decide +kernel
    rw [ha]
    exact (canonical21779 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1385 + difference 1 5) (sourceB1385 + difference 5 1) sourceC1385) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4498) := by
    have ha : (tripleCharges (sourceA1385 + difference 1 5) (sourceB1385 + difference 5 1) sourceC1385) = raw21780 := by
      apply Matrix.ext; unfold tripleCharges sourceA1385 sourceB1385 sourceC1385 difference raw21780; decide +kernel
    rw [ha]
    exact (canonical21780 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1385 + difference 2 0) (sourceB1385 + difference 0 2) sourceC1385) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4177) := by
    have ha : (tripleCharges (sourceA1385 + difference 2 0) (sourceB1385 + difference 0 2) sourceC1385) = raw21781 := by
      apply Matrix.ext; unfold tripleCharges sourceA1385 sourceB1385 sourceC1385 difference raw21781; decide +kernel
    rw [ha]
    exact (canonical21781 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1385 + difference 2 1) (sourceB1385 + difference 1 2) sourceC1385) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4346) := by
    have ha : (tripleCharges (sourceA1385 + difference 2 1) (sourceB1385 + difference 1 2) sourceC1385) = raw21782 := by
      apply Matrix.ext; unfold tripleCharges sourceA1385 sourceB1385 sourceC1385 difference raw21782; decide +kernel
    rw [ha]
    exact (canonical21782 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1385 + difference 2 3) (sourceB1385 + difference 3 2) sourceC1385) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4346) := by
    have ha : (tripleCharges (sourceA1385 + difference 2 3) (sourceB1385 + difference 3 2) sourceC1385) = raw21783 := by
      apply Matrix.ext; unfold tripleCharges sourceA1385 sourceB1385 sourceC1385 difference raw21783; decide +kernel
    rw [ha]
    exact (canonical21783 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1385 + difference 2 4) (sourceB1385 + difference 4 2) sourceC1385) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4460) := by
    have ha : (tripleCharges (sourceA1385 + difference 2 4) (sourceB1385 + difference 4 2) sourceC1385) = raw21784 := by
      apply Matrix.ext; unfold tripleCharges sourceA1385 sourceB1385 sourceC1385 difference raw21784; decide +kernel
    rw [ha]
    exact (canonical21784 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1385 + difference 2 5) (sourceB1385 + difference 5 2) sourceC1385) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4498) := by
    have ha : (tripleCharges (sourceA1385 + difference 2 5) (sourceB1385 + difference 5 2) sourceC1385) = raw21785 := by
      apply Matrix.ext; unfold tripleCharges sourceA1385 sourceB1385 sourceC1385 difference raw21785; decide +kernel
    rw [ha]
    exact (canonical21785 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1385 + difference 3 0) (sourceB1385 + difference 0 3) sourceC1385) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4177) := by
    have ha : (tripleCharges (sourceA1385 + difference 3 0) (sourceB1385 + difference 0 3) sourceC1385) = raw21786 := by
      apply Matrix.ext; unfold tripleCharges sourceA1385 sourceB1385 sourceC1385 difference raw21786; decide +kernel
    rw [ha]
    exact (canonical21786 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1385 + difference 3 1) (sourceB1385 + difference 1 3) sourceC1385) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4346) := by
    have ha : (tripleCharges (sourceA1385 + difference 3 1) (sourceB1385 + difference 1 3) sourceC1385) = raw21787 := by
      apply Matrix.ext; unfold tripleCharges sourceA1385 sourceB1385 sourceC1385 difference raw21787; decide +kernel
    rw [ha]
    exact (canonical21787 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1385 + difference 3 2) (sourceB1385 + difference 2 3) sourceC1385) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4346) := by
    have ha : (tripleCharges (sourceA1385 + difference 3 2) (sourceB1385 + difference 2 3) sourceC1385) = raw21788 := by
      apply Matrix.ext; unfold tripleCharges sourceA1385 sourceB1385 sourceC1385 difference raw21788; decide +kernel
    rw [ha]
    exact (canonical21788 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1385 + difference 3 4) (sourceB1385 + difference 4 3) sourceC1385) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4460) := by
    have ha : (tripleCharges (sourceA1385 + difference 3 4) (sourceB1385 + difference 4 3) sourceC1385) = raw21789 := by
      apply Matrix.ext; unfold tripleCharges sourceA1385 sourceB1385 sourceC1385 difference raw21789; decide +kernel
    rw [ha]
    exact (canonical21789 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1385 + difference 3 5) (sourceB1385 + difference 5 3) sourceC1385) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4498) := by
    have ha : (tripleCharges (sourceA1385 + difference 3 5) (sourceB1385 + difference 5 3) sourceC1385) = raw21790 := by
      apply Matrix.ext; unfold tripleCharges sourceA1385 sourceB1385 sourceC1385 difference raw21790; decide +kernel
    rw [ha]
    exact (canonical21790 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1385 + difference 4 0) (sourceB1385 + difference 0 4) sourceC1385) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4191) := by
    have ha : (tripleCharges (sourceA1385 + difference 4 0) (sourceB1385 + difference 0 4) sourceC1385) = raw21791 := by
      apply Matrix.ext; unfold tripleCharges sourceA1385 sourceB1385 sourceC1385 difference raw21791; decide +kernel
    rw [ha]
    exact (canonical21791 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1385 + difference 4 1) (sourceB1385 + difference 1 4) sourceC1385) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4360) := by
    have ha : (tripleCharges (sourceA1385 + difference 4 1) (sourceB1385 + difference 1 4) sourceC1385) = raw21792 := by
      apply Matrix.ext; unfold tripleCharges sourceA1385 sourceB1385 sourceC1385 difference raw21792; decide +kernel
    rw [ha]
    exact (canonical21792 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1385 + difference 4 2) (sourceB1385 + difference 2 4) sourceC1385) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4360) := by
    have ha : (tripleCharges (sourceA1385 + difference 4 2) (sourceB1385 + difference 2 4) sourceC1385) = raw21793 := by
      apply Matrix.ext; unfold tripleCharges sourceA1385 sourceB1385 sourceC1385 difference raw21793; decide +kernel
    rw [ha]
    exact (canonical21793 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1385 + difference 4 3) (sourceB1385 + difference 3 4) sourceC1385) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4360) := by
    have ha : (tripleCharges (sourceA1385 + difference 4 3) (sourceB1385 + difference 3 4) sourceC1385) = raw21794 := by
      apply Matrix.ext; unfold tripleCharges sourceA1385 sourceB1385 sourceC1385 difference raw21794; decide +kernel
    rw [ha]
    exact (canonical21794 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1385 + difference 4 5) (sourceB1385 + difference 5 4) sourceC1385) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4511) := by
    have ha : (tripleCharges (sourceA1385 + difference 4 5) (sourceB1385 + difference 5 4) sourceC1385) = raw21795 := by
      apply Matrix.ext; unfold tripleCharges sourceA1385 sourceB1385 sourceC1385 difference raw21795; decide +kernel
    rw [ha]
    exact (canonical21795 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1385 + difference 5 0) (sourceB1385 + difference 0 5) sourceC1385) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4187) := by
    have ha : (tripleCharges (sourceA1385 + difference 5 0) (sourceB1385 + difference 0 5) sourceC1385) = raw21796 := by
      apply Matrix.ext; unfold tripleCharges sourceA1385 sourceB1385 sourceC1385 difference raw21796; decide +kernel
    rw [ha]
    exact (canonical21796 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1385 + difference 5 1) (sourceB1385 + difference 1 5) sourceC1385) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4356) := by
    have ha : (tripleCharges (sourceA1385 + difference 5 1) (sourceB1385 + difference 1 5) sourceC1385) = raw21797 := by
      apply Matrix.ext; unfold tripleCharges sourceA1385 sourceB1385 sourceC1385 difference raw21797; decide +kernel
    rw [ha]
    exact (canonical21797 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1385 + difference 5 2) (sourceB1385 + difference 2 5) sourceC1385) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4356) := by
    have ha : (tripleCharges (sourceA1385 + difference 5 2) (sourceB1385 + difference 2 5) sourceC1385) = raw21798 := by
      apply Matrix.ext; unfold tripleCharges sourceA1385 sourceB1385 sourceC1385 difference raw21798; decide +kernel
    rw [ha]
    exact (canonical21798 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1385 + difference 5 3) (sourceB1385 + difference 3 5) sourceC1385) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4356) := by
    have ha : (tripleCharges (sourceA1385 + difference 5 3) (sourceB1385 + difference 3 5) sourceC1385) = raw21799 := by
      apply Matrix.ext; unfold tripleCharges sourceA1385 sourceB1385 sourceC1385 difference raw21799; decide +kernel
    rw [ha]
    exact (canonical21799 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1385 + difference 5 4) (sourceB1385 + difference 4 5) sourceC1385) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4468) := by
    have ha : (tripleCharges (sourceA1385 + difference 5 4) (sourceB1385 + difference 4 5) sourceC1385) = raw21800 := by
      apply Matrix.ext; unfold tripleCharges sourceA1385 sourceB1385 sourceC1385 difference raw21800; decide +kernel
    rw [ha]
    exact (canonical21800 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1385 sourceB1385 sourceC1385
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1385, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1386 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1386 : Charge := ![1, 0, 0, 0, 0, -1]
def sourceC1386 : Charge := ![3, 0, 0, 0, -1, -2]
def sourceForm1386 : Integer.Sparse Master := [(Sum.inr 1518, 3), (Sum.inr 1537, 1), (Sum.inr 1538, 1), (Sum.inr 1674, 6), (Sum.inr 1692, 3), (Sum.inr 1693, 3), (Sum.inr 1725, 3), (Sum.inr 1727, 3), (Sum.inr 1752, 1), (Sum.inr 1755, 1), (Sum.inr 2228, 3), (Sum.inr 2292, 1), (Sum.inr 4084, 1)]

theorem sourceEq1386 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1386 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1386 + difference 0 1) (sourceB1386 + difference 1 0) sourceC1386) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2228) := by
    have ha : (tripleCharges (sourceA1386 + difference 0 1) (sourceB1386 + difference 1 0) sourceC1386) = raw21801 := by
      apply Matrix.ext; unfold tripleCharges sourceA1386 sourceB1386 sourceC1386 difference raw21801; decide +kernel
    rw [ha]
    exact (canonical21801 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1386 + difference 0 2) (sourceB1386 + difference 2 0) sourceC1386) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2228) := by
    have ha : (tripleCharges (sourceA1386 + difference 0 2) (sourceB1386 + difference 2 0) sourceC1386) = raw21802 := by
      apply Matrix.ext; unfold tripleCharges sourceA1386 sourceB1386 sourceC1386 difference raw21802; decide +kernel
    rw [ha]
    exact (canonical21802 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1386 + difference 0 3) (sourceB1386 + difference 3 0) sourceC1386) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2228) := by
    have ha : (tripleCharges (sourceA1386 + difference 0 3) (sourceB1386 + difference 3 0) sourceC1386) = raw21803 := by
      apply Matrix.ext; unfold tripleCharges sourceA1386 sourceB1386 sourceC1386 difference raw21803; decide +kernel
    rw [ha]
    exact (canonical21803 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1386 + difference 0 4) (sourceB1386 + difference 4 0) sourceC1386) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2292) := by
    have ha : (tripleCharges (sourceA1386 + difference 0 4) (sourceB1386 + difference 4 0) sourceC1386) = raw21804 := by
      apply Matrix.ext; unfold tripleCharges sourceA1386 sourceB1386 sourceC1386 difference raw21804; decide +kernel
    rw [ha]
    exact (canonical21804 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1386 + difference 0 5) (sourceB1386 + difference 5 0) sourceC1386) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA1386 + difference 0 5) (sourceB1386 + difference 5 0) sourceC1386) = raw21805 := by
      apply Matrix.ext; unfold tripleCharges sourceA1386 sourceB1386 sourceC1386 difference raw21805; decide +kernel
    rw [ha]
    exact (canonical21805 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1386 + difference 1 0) (sourceB1386 + difference 0 1) sourceC1386) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1518) := by
    have ha : (tripleCharges (sourceA1386 + difference 1 0) (sourceB1386 + difference 0 1) sourceC1386) = raw21806 := by
      apply Matrix.ext; unfold tripleCharges sourceA1386 sourceB1386 sourceC1386 difference raw21806; decide +kernel
    rw [ha]
    exact (canonical21806 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1386 + difference 1 2) (sourceB1386 + difference 2 1) sourceC1386) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1674) := by
    have ha : (tripleCharges (sourceA1386 + difference 1 2) (sourceB1386 + difference 2 1) sourceC1386) = raw21807 := by
      apply Matrix.ext; unfold tripleCharges sourceA1386 sourceB1386 sourceC1386 difference raw21807; decide +kernel
    rw [ha]
    exact (canonical21807 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1386 + difference 1 3) (sourceB1386 + difference 3 1) sourceC1386) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1674) := by
    have ha : (tripleCharges (sourceA1386 + difference 1 3) (sourceB1386 + difference 3 1) sourceC1386) = raw21808 := by
      apply Matrix.ext; unfold tripleCharges sourceA1386 sourceB1386 sourceC1386 difference raw21808; decide +kernel
    rw [ha]
    exact (canonical21808 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1386 + difference 1 4) (sourceB1386 + difference 4 1) sourceC1386) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1725) := by
    have ha : (tripleCharges (sourceA1386 + difference 1 4) (sourceB1386 + difference 4 1) sourceC1386) = raw21809 := by
      apply Matrix.ext; unfold tripleCharges sourceA1386 sourceB1386 sourceC1386 difference raw21809; decide +kernel
    rw [ha]
    exact (canonical21809 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1386 + difference 1 5) (sourceB1386 + difference 5 1) sourceC1386) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1727) := by
    have ha : (tripleCharges (sourceA1386 + difference 1 5) (sourceB1386 + difference 5 1) sourceC1386) = raw21810 := by
      apply Matrix.ext; unfold tripleCharges sourceA1386 sourceB1386 sourceC1386 difference raw21810; decide +kernel
    rw [ha]
    exact (canonical21810 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1386 + difference 2 0) (sourceB1386 + difference 0 2) sourceC1386) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1518) := by
    have ha : (tripleCharges (sourceA1386 + difference 2 0) (sourceB1386 + difference 0 2) sourceC1386) = raw21811 := by
      apply Matrix.ext; unfold tripleCharges sourceA1386 sourceB1386 sourceC1386 difference raw21811; decide +kernel
    rw [ha]
    exact (canonical21811 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1386 + difference 2 1) (sourceB1386 + difference 1 2) sourceC1386) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1674) := by
    have ha : (tripleCharges (sourceA1386 + difference 2 1) (sourceB1386 + difference 1 2) sourceC1386) = raw21812 := by
      apply Matrix.ext; unfold tripleCharges sourceA1386 sourceB1386 sourceC1386 difference raw21812; decide +kernel
    rw [ha]
    exact (canonical21812 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1386 + difference 2 3) (sourceB1386 + difference 3 2) sourceC1386) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1674) := by
    have ha : (tripleCharges (sourceA1386 + difference 2 3) (sourceB1386 + difference 3 2) sourceC1386) = raw21813 := by
      apply Matrix.ext; unfold tripleCharges sourceA1386 sourceB1386 sourceC1386 difference raw21813; decide +kernel
    rw [ha]
    exact (canonical21813 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1386 + difference 2 4) (sourceB1386 + difference 4 2) sourceC1386) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1725) := by
    have ha : (tripleCharges (sourceA1386 + difference 2 4) (sourceB1386 + difference 4 2) sourceC1386) = raw21814 := by
      apply Matrix.ext; unfold tripleCharges sourceA1386 sourceB1386 sourceC1386 difference raw21814; decide +kernel
    rw [ha]
    exact (canonical21814 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1386 + difference 2 5) (sourceB1386 + difference 5 2) sourceC1386) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1727) := by
    have ha : (tripleCharges (sourceA1386 + difference 2 5) (sourceB1386 + difference 5 2) sourceC1386) = raw21815 := by
      apply Matrix.ext; unfold tripleCharges sourceA1386 sourceB1386 sourceC1386 difference raw21815; decide +kernel
    rw [ha]
    exact (canonical21815 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1386 + difference 3 0) (sourceB1386 + difference 0 3) sourceC1386) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1518) := by
    have ha : (tripleCharges (sourceA1386 + difference 3 0) (sourceB1386 + difference 0 3) sourceC1386) = raw21816 := by
      apply Matrix.ext; unfold tripleCharges sourceA1386 sourceB1386 sourceC1386 difference raw21816; decide +kernel
    rw [ha]
    exact (canonical21816 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1386 + difference 3 1) (sourceB1386 + difference 1 3) sourceC1386) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1674) := by
    have ha : (tripleCharges (sourceA1386 + difference 3 1) (sourceB1386 + difference 1 3) sourceC1386) = raw21817 := by
      apply Matrix.ext; unfold tripleCharges sourceA1386 sourceB1386 sourceC1386 difference raw21817; decide +kernel
    rw [ha]
    exact (canonical21817 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1386 + difference 3 2) (sourceB1386 + difference 2 3) sourceC1386) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1674) := by
    have ha : (tripleCharges (sourceA1386 + difference 3 2) (sourceB1386 + difference 2 3) sourceC1386) = raw21818 := by
      apply Matrix.ext; unfold tripleCharges sourceA1386 sourceB1386 sourceC1386 difference raw21818; decide +kernel
    rw [ha]
    exact (canonical21818 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1386 + difference 3 4) (sourceB1386 + difference 4 3) sourceC1386) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1725) := by
    have ha : (tripleCharges (sourceA1386 + difference 3 4) (sourceB1386 + difference 4 3) sourceC1386) = raw21819 := by
      apply Matrix.ext; unfold tripleCharges sourceA1386 sourceB1386 sourceC1386 difference raw21819; decide +kernel
    rw [ha]
    exact (canonical21819 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1386 + difference 3 5) (sourceB1386 + difference 5 3) sourceC1386) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1727) := by
    have ha : (tripleCharges (sourceA1386 + difference 3 5) (sourceB1386 + difference 5 3) sourceC1386) = raw21820 := by
      apply Matrix.ext; unfold tripleCharges sourceA1386 sourceB1386 sourceC1386 difference raw21820; decide +kernel
    rw [ha]
    exact (canonical21820 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1386 + difference 4 0) (sourceB1386 + difference 0 4) sourceC1386) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1538) := by
    have ha : (tripleCharges (sourceA1386 + difference 4 0) (sourceB1386 + difference 0 4) sourceC1386) = raw21821 := by
      apply Matrix.ext; unfold tripleCharges sourceA1386 sourceB1386 sourceC1386 difference raw21821; decide +kernel
    rw [ha]
    exact (canonical21821 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1386 + difference 4 1) (sourceB1386 + difference 1 4) sourceC1386) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1693) := by
    have ha : (tripleCharges (sourceA1386 + difference 4 1) (sourceB1386 + difference 1 4) sourceC1386) = raw21822 := by
      apply Matrix.ext; unfold tripleCharges sourceA1386 sourceB1386 sourceC1386 difference raw21822; decide +kernel
    rw [ha]
    exact (canonical21822 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1386 + difference 4 2) (sourceB1386 + difference 2 4) sourceC1386) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1693) := by
    have ha : (tripleCharges (sourceA1386 + difference 4 2) (sourceB1386 + difference 2 4) sourceC1386) = raw21823 := by
      apply Matrix.ext; unfold tripleCharges sourceA1386 sourceB1386 sourceC1386 difference raw21823; decide +kernel
    rw [ha]
    exact (canonical21823 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1386 + difference 4 3) (sourceB1386 + difference 3 4) sourceC1386) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1693) := by
    have ha : (tripleCharges (sourceA1386 + difference 4 3) (sourceB1386 + difference 3 4) sourceC1386) = raw21824 := by
      apply Matrix.ext; unfold tripleCharges sourceA1386 sourceB1386 sourceC1386 difference raw21824; decide +kernel
    rw [ha]
    exact (canonical21824 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1386 + difference 4 5) (sourceB1386 + difference 5 4) sourceC1386) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1755) := by
    have ha : (tripleCharges (sourceA1386 + difference 4 5) (sourceB1386 + difference 5 4) sourceC1386) = raw21825 := by
      apply Matrix.ext; unfold tripleCharges sourceA1386 sourceB1386 sourceC1386 difference raw21825; decide +kernel
    rw [ha]
    exact (canonical21825 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1386 + difference 5 0) (sourceB1386 + difference 0 5) sourceC1386) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1537) := by
    have ha : (tripleCharges (sourceA1386 + difference 5 0) (sourceB1386 + difference 0 5) sourceC1386) = raw21826 := by
      apply Matrix.ext; unfold tripleCharges sourceA1386 sourceB1386 sourceC1386 difference raw21826; decide +kernel
    rw [ha]
    exact (canonical21826 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1386 + difference 5 1) (sourceB1386 + difference 1 5) sourceC1386) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1692) := by
    have ha : (tripleCharges (sourceA1386 + difference 5 1) (sourceB1386 + difference 1 5) sourceC1386) = raw21827 := by
      apply Matrix.ext; unfold tripleCharges sourceA1386 sourceB1386 sourceC1386 difference raw21827; decide +kernel
    rw [ha]
    exact (canonical21827 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1386 + difference 5 2) (sourceB1386 + difference 2 5) sourceC1386) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1692) := by
    have ha : (tripleCharges (sourceA1386 + difference 5 2) (sourceB1386 + difference 2 5) sourceC1386) = raw21828 := by
      apply Matrix.ext; unfold tripleCharges sourceA1386 sourceB1386 sourceC1386 difference raw21828; decide +kernel
    rw [ha]
    exact (canonical21828 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1386 + difference 5 3) (sourceB1386 + difference 3 5) sourceC1386) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1692) := by
    have ha : (tripleCharges (sourceA1386 + difference 5 3) (sourceB1386 + difference 3 5) sourceC1386) = raw21829 := by
      apply Matrix.ext; unfold tripleCharges sourceA1386 sourceB1386 sourceC1386 difference raw21829; decide +kernel
    rw [ha]
    exact (canonical21829 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1386 + difference 5 4) (sourceB1386 + difference 4 5) sourceC1386) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1752) := by
    have ha : (tripleCharges (sourceA1386 + difference 5 4) (sourceB1386 + difference 4 5) sourceC1386) = raw21830 := by
      apply Matrix.ext; unfold tripleCharges sourceA1386 sourceB1386 sourceC1386 difference raw21830; decide +kernel
    rw [ha]
    exact (canonical21830 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1386 sourceB1386 sourceC1386
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1386, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1387 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1387 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceC1387 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceForm1387 : Integer.Sparse Master := [(Sum.inr 4085, 1), (Sum.inr 4174, 3), (Sum.inr 4181, 1), (Sum.inr 4190, 1), (Sum.inr 4343, 6), (Sum.inr 4350, 3), (Sum.inr 4359, 3), (Sum.inr 4496, 3), (Sum.inr 4501, 3), (Sum.inr 4510, 1), (Sum.inr 4512, 1), (Sum.inr 4837, 3), (Sum.inr 4897, 1)]

theorem sourceEq1387 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1387 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1387 + difference 0 1) (sourceB1387 + difference 1 0) sourceC1387) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4837) := by
    have ha : (tripleCharges (sourceA1387 + difference 0 1) (sourceB1387 + difference 1 0) sourceC1387) = raw21831 := by
      apply Matrix.ext; unfold tripleCharges sourceA1387 sourceB1387 sourceC1387 difference raw21831; decide +kernel
    rw [ha]
    exact (canonical21831 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1387 + difference 0 2) (sourceB1387 + difference 2 0) sourceC1387) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4837) := by
    have ha : (tripleCharges (sourceA1387 + difference 0 2) (sourceB1387 + difference 2 0) sourceC1387) = raw21832 := by
      apply Matrix.ext; unfold tripleCharges sourceA1387 sourceB1387 sourceC1387 difference raw21832; decide +kernel
    rw [ha]
    exact (canonical21832 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1387 + difference 0 3) (sourceB1387 + difference 3 0) sourceC1387) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4837) := by
    have ha : (tripleCharges (sourceA1387 + difference 0 3) (sourceB1387 + difference 3 0) sourceC1387) = raw21833 := by
      apply Matrix.ext; unfold tripleCharges sourceA1387 sourceB1387 sourceC1387 difference raw21833; decide +kernel
    rw [ha]
    exact (canonical21833 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1387 + difference 0 4) (sourceB1387 + difference 4 0) sourceC1387) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (tripleCharges (sourceA1387 + difference 0 4) (sourceB1387 + difference 4 0) sourceC1387) = raw19891 := by
      apply Matrix.ext; unfold tripleCharges sourceA1387 sourceB1387 sourceC1387 difference raw19891; decide +kernel
    rw [ha]
    exact (canonical19891 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1387 + difference 0 5) (sourceB1387 + difference 5 0) sourceC1387) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4897) := by
    have ha : (tripleCharges (sourceA1387 + difference 0 5) (sourceB1387 + difference 5 0) sourceC1387) = raw21834 := by
      apply Matrix.ext; unfold tripleCharges sourceA1387 sourceB1387 sourceC1387 difference raw21834; decide +kernel
    rw [ha]
    exact (canonical21834 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1387 + difference 1 0) (sourceB1387 + difference 0 1) sourceC1387) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4174) := by
    have ha : (tripleCharges (sourceA1387 + difference 1 0) (sourceB1387 + difference 0 1) sourceC1387) = raw21835 := by
      apply Matrix.ext; unfold tripleCharges sourceA1387 sourceB1387 sourceC1387 difference raw21835; decide +kernel
    rw [ha]
    exact (canonical21835 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1387 + difference 1 2) (sourceB1387 + difference 2 1) sourceC1387) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4343) := by
    have ha : (tripleCharges (sourceA1387 + difference 1 2) (sourceB1387 + difference 2 1) sourceC1387) = raw21836 := by
      apply Matrix.ext; unfold tripleCharges sourceA1387 sourceB1387 sourceC1387 difference raw21836; decide +kernel
    rw [ha]
    exact (canonical21836 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1387 + difference 1 3) (sourceB1387 + difference 3 1) sourceC1387) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4343) := by
    have ha : (tripleCharges (sourceA1387 + difference 1 3) (sourceB1387 + difference 3 1) sourceC1387) = raw21837 := by
      apply Matrix.ext; unfold tripleCharges sourceA1387 sourceB1387 sourceC1387 difference raw21837; decide +kernel
    rw [ha]
    exact (canonical21837 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1387 + difference 1 4) (sourceB1387 + difference 4 1) sourceC1387) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4501) := by
    have ha : (tripleCharges (sourceA1387 + difference 1 4) (sourceB1387 + difference 4 1) sourceC1387) = raw19896 := by
      apply Matrix.ext; unfold tripleCharges sourceA1387 sourceB1387 sourceC1387 difference raw19896; decide +kernel
    rw [ha]
    exact (canonical19896 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1387 + difference 1 5) (sourceB1387 + difference 5 1) sourceC1387) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4496) := by
    have ha : (tripleCharges (sourceA1387 + difference 1 5) (sourceB1387 + difference 5 1) sourceC1387) = raw21838 := by
      apply Matrix.ext; unfold tripleCharges sourceA1387 sourceB1387 sourceC1387 difference raw21838; decide +kernel
    rw [ha]
    exact (canonical21838 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1387 + difference 2 0) (sourceB1387 + difference 0 2) sourceC1387) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4174) := by
    have ha : (tripleCharges (sourceA1387 + difference 2 0) (sourceB1387 + difference 0 2) sourceC1387) = raw21839 := by
      apply Matrix.ext; unfold tripleCharges sourceA1387 sourceB1387 sourceC1387 difference raw21839; decide +kernel
    rw [ha]
    exact (canonical21839 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1387 + difference 2 1) (sourceB1387 + difference 1 2) sourceC1387) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4343) := by
    have ha : (tripleCharges (sourceA1387 + difference 2 1) (sourceB1387 + difference 1 2) sourceC1387) = raw21840 := by
      apply Matrix.ext; unfold tripleCharges sourceA1387 sourceB1387 sourceC1387 difference raw21840; decide +kernel
    rw [ha]
    exact (canonical21840 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1387 + difference 2 3) (sourceB1387 + difference 3 2) sourceC1387) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4343) := by
    have ha : (tripleCharges (sourceA1387 + difference 2 3) (sourceB1387 + difference 3 2) sourceC1387) = raw21841 := by
      apply Matrix.ext; unfold tripleCharges sourceA1387 sourceB1387 sourceC1387 difference raw21841; decide +kernel
    rw [ha]
    exact (canonical21841 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1387 + difference 2 4) (sourceB1387 + difference 4 2) sourceC1387) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4501) := by
    have ha : (tripleCharges (sourceA1387 + difference 2 4) (sourceB1387 + difference 4 2) sourceC1387) = raw19901 := by
      apply Matrix.ext; unfold tripleCharges sourceA1387 sourceB1387 sourceC1387 difference raw19901; decide +kernel
    rw [ha]
    exact (canonical19901 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1387 + difference 2 5) (sourceB1387 + difference 5 2) sourceC1387) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4496) := by
    have ha : (tripleCharges (sourceA1387 + difference 2 5) (sourceB1387 + difference 5 2) sourceC1387) = raw21842 := by
      apply Matrix.ext; unfold tripleCharges sourceA1387 sourceB1387 sourceC1387 difference raw21842; decide +kernel
    rw [ha]
    exact (canonical21842 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1387 + difference 3 0) (sourceB1387 + difference 0 3) sourceC1387) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4174) := by
    have ha : (tripleCharges (sourceA1387 + difference 3 0) (sourceB1387 + difference 0 3) sourceC1387) = raw21843 := by
      apply Matrix.ext; unfold tripleCharges sourceA1387 sourceB1387 sourceC1387 difference raw21843; decide +kernel
    rw [ha]
    exact (canonical21843 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1387 + difference 3 1) (sourceB1387 + difference 1 3) sourceC1387) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4343) := by
    have ha : (tripleCharges (sourceA1387 + difference 3 1) (sourceB1387 + difference 1 3) sourceC1387) = raw21844 := by
      apply Matrix.ext; unfold tripleCharges sourceA1387 sourceB1387 sourceC1387 difference raw21844; decide +kernel
    rw [ha]
    exact (canonical21844 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1387 + difference 3 2) (sourceB1387 + difference 2 3) sourceC1387) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4343) := by
    have ha : (tripleCharges (sourceA1387 + difference 3 2) (sourceB1387 + difference 2 3) sourceC1387) = raw21845 := by
      apply Matrix.ext; unfold tripleCharges sourceA1387 sourceB1387 sourceC1387 difference raw21845; decide +kernel
    rw [ha]
    exact (canonical21845 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1387 + difference 3 4) (sourceB1387 + difference 4 3) sourceC1387) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4501) := by
    have ha : (tripleCharges (sourceA1387 + difference 3 4) (sourceB1387 + difference 4 3) sourceC1387) = raw19906 := by
      apply Matrix.ext; unfold tripleCharges sourceA1387 sourceB1387 sourceC1387 difference raw19906; decide +kernel
    rw [ha]
    exact (canonical19906 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1387 + difference 3 5) (sourceB1387 + difference 5 3) sourceC1387) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4496) := by
    have ha : (tripleCharges (sourceA1387 + difference 3 5) (sourceB1387 + difference 5 3) sourceC1387) = raw21846 := by
      apply Matrix.ext; unfold tripleCharges sourceA1387 sourceB1387 sourceC1387 difference raw21846; decide +kernel
    rw [ha]
    exact (canonical21846 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1387 + difference 4 0) (sourceB1387 + difference 0 4) sourceC1387) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4190) := by
    have ha : (tripleCharges (sourceA1387 + difference 4 0) (sourceB1387 + difference 0 4) sourceC1387) = raw21847 := by
      apply Matrix.ext; unfold tripleCharges sourceA1387 sourceB1387 sourceC1387 difference raw21847; decide +kernel
    rw [ha]
    exact (canonical21847 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1387 + difference 4 1) (sourceB1387 + difference 1 4) sourceC1387) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4359) := by
    have ha : (tripleCharges (sourceA1387 + difference 4 1) (sourceB1387 + difference 1 4) sourceC1387) = raw21848 := by
      apply Matrix.ext; unfold tripleCharges sourceA1387 sourceB1387 sourceC1387 difference raw21848; decide +kernel
    rw [ha]
    exact (canonical21848 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1387 + difference 4 2) (sourceB1387 + difference 2 4) sourceC1387) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4359) := by
    have ha : (tripleCharges (sourceA1387 + difference 4 2) (sourceB1387 + difference 2 4) sourceC1387) = raw21849 := by
      apply Matrix.ext; unfold tripleCharges sourceA1387 sourceB1387 sourceC1387 difference raw21849; decide +kernel
    rw [ha]
    exact (canonical21849 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1387 + difference 4 3) (sourceB1387 + difference 3 4) sourceC1387) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4359) := by
    have ha : (tripleCharges (sourceA1387 + difference 4 3) (sourceB1387 + difference 3 4) sourceC1387) = raw21850 := by
      apply Matrix.ext; unfold tripleCharges sourceA1387 sourceB1387 sourceC1387 difference raw21850; decide +kernel
    rw [ha]
    exact (canonical21850 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1387 + difference 4 5) (sourceB1387 + difference 5 4) sourceC1387) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4510) := by
    have ha : (tripleCharges (sourceA1387 + difference 4 5) (sourceB1387 + difference 5 4) sourceC1387) = raw21851 := by
      apply Matrix.ext; unfold tripleCharges sourceA1387 sourceB1387 sourceC1387 difference raw21851; decide +kernel
    rw [ha]
    exact (canonical21851 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1387 + difference 5 0) (sourceB1387 + difference 0 5) sourceC1387) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4181) := by
    have ha : (tripleCharges (sourceA1387 + difference 5 0) (sourceB1387 + difference 0 5) sourceC1387) = raw19907 := by
      apply Matrix.ext; unfold tripleCharges sourceA1387 sourceB1387 sourceC1387 difference raw19907; decide +kernel
    rw [ha]
    exact (canonical19907 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1387 + difference 5 1) (sourceB1387 + difference 1 5) sourceC1387) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4350) := by
    have ha : (tripleCharges (sourceA1387 + difference 5 1) (sourceB1387 + difference 1 5) sourceC1387) = raw19908 := by
      apply Matrix.ext; unfold tripleCharges sourceA1387 sourceB1387 sourceC1387 difference raw19908; decide +kernel
    rw [ha]
    exact (canonical19908 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1387 + difference 5 2) (sourceB1387 + difference 2 5) sourceC1387) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4350) := by
    have ha : (tripleCharges (sourceA1387 + difference 5 2) (sourceB1387 + difference 2 5) sourceC1387) = raw19909 := by
      apply Matrix.ext; unfold tripleCharges sourceA1387 sourceB1387 sourceC1387 difference raw19909; decide +kernel
    rw [ha]
    exact (canonical19909 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1387 + difference 5 3) (sourceB1387 + difference 3 5) sourceC1387) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4350) := by
    have ha : (tripleCharges (sourceA1387 + difference 5 3) (sourceB1387 + difference 3 5) sourceC1387) = raw19910 := by
      apply Matrix.ext; unfold tripleCharges sourceA1387 sourceB1387 sourceC1387 difference raw19910; decide +kernel
    rw [ha]
    exact (canonical19910 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1387 + difference 5 4) (sourceB1387 + difference 4 5) sourceC1387) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4512) := by
    have ha : (tripleCharges (sourceA1387 + difference 5 4) (sourceB1387 + difference 4 5) sourceC1387) = raw21852 := by
      apply Matrix.ext; unfold tripleCharges sourceA1387 sourceB1387 sourceC1387 difference raw21852; decide +kernel
    rw [ha]
    exact (canonical21852 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1387 sourceB1387 sourceC1387
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1387, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1388 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1388 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceC1388 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceForm1388 : Integer.Sparse Master := [(Sum.inr 1509, 3), (Sum.inr 1521, 1), (Sum.inr 1527, 1), (Sum.inr 1666, 6), (Sum.inr 1677, 3), (Sum.inr 1683, 3), (Sum.inr 1710, 3), (Sum.inr 1730, 3), (Sum.inr 1741, 1), (Sum.inr 1758, 1), (Sum.inr 2208, 3), (Sum.inr 2268, 1), (Sum.inr 4085, 1)]

theorem sourceEq1388 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1388 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1388 + difference 0 1) (sourceB1388 + difference 1 0) sourceC1388) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2208) := by
    have ha : (tripleCharges (sourceA1388 + difference 0 1) (sourceB1388 + difference 1 0) sourceC1388) = raw21853 := by
      apply Matrix.ext; unfold tripleCharges sourceA1388 sourceB1388 sourceC1388 difference raw21853; decide +kernel
    rw [ha]
    exact (canonical21853 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1388 + difference 0 2) (sourceB1388 + difference 2 0) sourceC1388) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2208) := by
    have ha : (tripleCharges (sourceA1388 + difference 0 2) (sourceB1388 + difference 2 0) sourceC1388) = raw21854 := by
      apply Matrix.ext; unfold tripleCharges sourceA1388 sourceB1388 sourceC1388 difference raw21854; decide +kernel
    rw [ha]
    exact (canonical21854 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1388 + difference 0 3) (sourceB1388 + difference 3 0) sourceC1388) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2208) := by
    have ha : (tripleCharges (sourceA1388 + difference 0 3) (sourceB1388 + difference 3 0) sourceC1388) = raw21855 := by
      apply Matrix.ext; unfold tripleCharges sourceA1388 sourceB1388 sourceC1388 difference raw21855; decide +kernel
    rw [ha]
    exact (canonical21855 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1388 + difference 0 4) (sourceB1388 + difference 4 0) sourceC1388) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (tripleCharges (sourceA1388 + difference 0 4) (sourceB1388 + difference 4 0) sourceC1388) = raw19921 := by
      apply Matrix.ext; unfold tripleCharges sourceA1388 sourceB1388 sourceC1388 difference raw19921; decide +kernel
    rw [ha]
    exact (canonical19921 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1388 + difference 0 5) (sourceB1388 + difference 5 0) sourceC1388) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2268) := by
    have ha : (tripleCharges (sourceA1388 + difference 0 5) (sourceB1388 + difference 5 0) sourceC1388) = raw21856 := by
      apply Matrix.ext; unfold tripleCharges sourceA1388 sourceB1388 sourceC1388 difference raw21856; decide +kernel
    rw [ha]
    exact (canonical21856 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1388 + difference 1 0) (sourceB1388 + difference 0 1) sourceC1388) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1509) := by
    have ha : (tripleCharges (sourceA1388 + difference 1 0) (sourceB1388 + difference 0 1) sourceC1388) = raw21857 := by
      apply Matrix.ext; unfold tripleCharges sourceA1388 sourceB1388 sourceC1388 difference raw21857; decide +kernel
    rw [ha]
    exact (canonical21857 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1388 + difference 1 2) (sourceB1388 + difference 2 1) sourceC1388) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1666) := by
    have ha : (tripleCharges (sourceA1388 + difference 1 2) (sourceB1388 + difference 2 1) sourceC1388) = raw21858 := by
      apply Matrix.ext; unfold tripleCharges sourceA1388 sourceB1388 sourceC1388 difference raw21858; decide +kernel
    rw [ha]
    exact (canonical21858 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1388 + difference 1 3) (sourceB1388 + difference 3 1) sourceC1388) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1666) := by
    have ha : (tripleCharges (sourceA1388 + difference 1 3) (sourceB1388 + difference 3 1) sourceC1388) = raw21859 := by
      apply Matrix.ext; unfold tripleCharges sourceA1388 sourceB1388 sourceC1388 difference raw21859; decide +kernel
    rw [ha]
    exact (canonical21859 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1388 + difference 1 4) (sourceB1388 + difference 4 1) sourceC1388) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1730) := by
    have ha : (tripleCharges (sourceA1388 + difference 1 4) (sourceB1388 + difference 4 1) sourceC1388) = raw19926 := by
      apply Matrix.ext; unfold tripleCharges sourceA1388 sourceB1388 sourceC1388 difference raw19926; decide +kernel
    rw [ha]
    exact (canonical19926 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1388 + difference 1 5) (sourceB1388 + difference 5 1) sourceC1388) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1710) := by
    have ha : (tripleCharges (sourceA1388 + difference 1 5) (sourceB1388 + difference 5 1) sourceC1388) = raw21860 := by
      apply Matrix.ext; unfold tripleCharges sourceA1388 sourceB1388 sourceC1388 difference raw21860; decide +kernel
    rw [ha]
    exact (canonical21860 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1388 + difference 2 0) (sourceB1388 + difference 0 2) sourceC1388) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1509) := by
    have ha : (tripleCharges (sourceA1388 + difference 2 0) (sourceB1388 + difference 0 2) sourceC1388) = raw21861 := by
      apply Matrix.ext; unfold tripleCharges sourceA1388 sourceB1388 sourceC1388 difference raw21861; decide +kernel
    rw [ha]
    exact (canonical21861 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1388 + difference 2 1) (sourceB1388 + difference 1 2) sourceC1388) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1666) := by
    have ha : (tripleCharges (sourceA1388 + difference 2 1) (sourceB1388 + difference 1 2) sourceC1388) = raw21862 := by
      apply Matrix.ext; unfold tripleCharges sourceA1388 sourceB1388 sourceC1388 difference raw21862; decide +kernel
    rw [ha]
    exact (canonical21862 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1388 + difference 2 3) (sourceB1388 + difference 3 2) sourceC1388) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1666) := by
    have ha : (tripleCharges (sourceA1388 + difference 2 3) (sourceB1388 + difference 3 2) sourceC1388) = raw21863 := by
      apply Matrix.ext; unfold tripleCharges sourceA1388 sourceB1388 sourceC1388 difference raw21863; decide +kernel
    rw [ha]
    exact (canonical21863 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1388 + difference 2 4) (sourceB1388 + difference 4 2) sourceC1388) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1730) := by
    have ha : (tripleCharges (sourceA1388 + difference 2 4) (sourceB1388 + difference 4 2) sourceC1388) = raw19931 := by
      apply Matrix.ext; unfold tripleCharges sourceA1388 sourceB1388 sourceC1388 difference raw19931; decide +kernel
    rw [ha]
    exact (canonical19931 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1388 + difference 2 5) (sourceB1388 + difference 5 2) sourceC1388) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1710) := by
    have ha : (tripleCharges (sourceA1388 + difference 2 5) (sourceB1388 + difference 5 2) sourceC1388) = raw21864 := by
      apply Matrix.ext; unfold tripleCharges sourceA1388 sourceB1388 sourceC1388 difference raw21864; decide +kernel
    rw [ha]
    exact (canonical21864 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1388 + difference 3 0) (sourceB1388 + difference 0 3) sourceC1388) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1509) := by
    have ha : (tripleCharges (sourceA1388 + difference 3 0) (sourceB1388 + difference 0 3) sourceC1388) = raw21865 := by
      apply Matrix.ext; unfold tripleCharges sourceA1388 sourceB1388 sourceC1388 difference raw21865; decide +kernel
    rw [ha]
    exact (canonical21865 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1388 + difference 3 1) (sourceB1388 + difference 1 3) sourceC1388) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1666) := by
    have ha : (tripleCharges (sourceA1388 + difference 3 1) (sourceB1388 + difference 1 3) sourceC1388) = raw21866 := by
      apply Matrix.ext; unfold tripleCharges sourceA1388 sourceB1388 sourceC1388 difference raw21866; decide +kernel
    rw [ha]
    exact (canonical21866 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1388 + difference 3 2) (sourceB1388 + difference 2 3) sourceC1388) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1666) := by
    have ha : (tripleCharges (sourceA1388 + difference 3 2) (sourceB1388 + difference 2 3) sourceC1388) = raw21867 := by
      apply Matrix.ext; unfold tripleCharges sourceA1388 sourceB1388 sourceC1388 difference raw21867; decide +kernel
    rw [ha]
    exact (canonical21867 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1388 + difference 3 4) (sourceB1388 + difference 4 3) sourceC1388) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1730) := by
    have ha : (tripleCharges (sourceA1388 + difference 3 4) (sourceB1388 + difference 4 3) sourceC1388) = raw19936 := by
      apply Matrix.ext; unfold tripleCharges sourceA1388 sourceB1388 sourceC1388 difference raw19936; decide +kernel
    rw [ha]
    exact (canonical19936 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1388 + difference 3 5) (sourceB1388 + difference 5 3) sourceC1388) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1710) := by
    have ha : (tripleCharges (sourceA1388 + difference 3 5) (sourceB1388 + difference 5 3) sourceC1388) = raw21868 := by
      apply Matrix.ext; unfold tripleCharges sourceA1388 sourceB1388 sourceC1388 difference raw21868; decide +kernel
    rw [ha]
    exact (canonical21868 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1388 + difference 4 0) (sourceB1388 + difference 0 4) sourceC1388) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1527) := by
    have ha : (tripleCharges (sourceA1388 + difference 4 0) (sourceB1388 + difference 0 4) sourceC1388) = raw21869 := by
      apply Matrix.ext; unfold tripleCharges sourceA1388 sourceB1388 sourceC1388 difference raw21869; decide +kernel
    rw [ha]
    exact (canonical21869 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1388 + difference 4 1) (sourceB1388 + difference 1 4) sourceC1388) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1683) := by
    have ha : (tripleCharges (sourceA1388 + difference 4 1) (sourceB1388 + difference 1 4) sourceC1388) = raw21870 := by
      apply Matrix.ext; unfold tripleCharges sourceA1388 sourceB1388 sourceC1388 difference raw21870; decide +kernel
    rw [ha]
    exact (canonical21870 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1388 + difference 4 2) (sourceB1388 + difference 2 4) sourceC1388) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1683) := by
    have ha : (tripleCharges (sourceA1388 + difference 4 2) (sourceB1388 + difference 2 4) sourceC1388) = raw21871 := by
      apply Matrix.ext; unfold tripleCharges sourceA1388 sourceB1388 sourceC1388 difference raw21871; decide +kernel
    rw [ha]
    exact (canonical21871 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1388 + difference 4 3) (sourceB1388 + difference 3 4) sourceC1388) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1683) := by
    have ha : (tripleCharges (sourceA1388 + difference 4 3) (sourceB1388 + difference 3 4) sourceC1388) = raw21872 := by
      apply Matrix.ext; unfold tripleCharges sourceA1388 sourceB1388 sourceC1388 difference raw21872; decide +kernel
    rw [ha]
    exact (canonical21872 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1388 + difference 4 5) (sourceB1388 + difference 5 4) sourceC1388) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1741) := by
    have ha : (tripleCharges (sourceA1388 + difference 4 5) (sourceB1388 + difference 5 4) sourceC1388) = raw21873 := by
      apply Matrix.ext; unfold tripleCharges sourceA1388 sourceB1388 sourceC1388 difference raw21873; decide +kernel
    rw [ha]
    exact (canonical21873 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1388 + difference 5 0) (sourceB1388 + difference 0 5) sourceC1388) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1521) := by
    have ha : (tripleCharges (sourceA1388 + difference 5 0) (sourceB1388 + difference 0 5) sourceC1388) = raw19937 := by
      apply Matrix.ext; unfold tripleCharges sourceA1388 sourceB1388 sourceC1388 difference raw19937; decide +kernel
    rw [ha]
    exact (canonical19937 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1388 + difference 5 1) (sourceB1388 + difference 1 5) sourceC1388) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1677) := by
    have ha : (tripleCharges (sourceA1388 + difference 5 1) (sourceB1388 + difference 1 5) sourceC1388) = raw19938 := by
      apply Matrix.ext; unfold tripleCharges sourceA1388 sourceB1388 sourceC1388 difference raw19938; decide +kernel
    rw [ha]
    exact (canonical19938 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1388 + difference 5 2) (sourceB1388 + difference 2 5) sourceC1388) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1677) := by
    have ha : (tripleCharges (sourceA1388 + difference 5 2) (sourceB1388 + difference 2 5) sourceC1388) = raw19939 := by
      apply Matrix.ext; unfold tripleCharges sourceA1388 sourceB1388 sourceC1388 difference raw19939; decide +kernel
    rw [ha]
    exact (canonical19939 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1388 + difference 5 3) (sourceB1388 + difference 3 5) sourceC1388) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1677) := by
    have ha : (tripleCharges (sourceA1388 + difference 5 3) (sourceB1388 + difference 3 5) sourceC1388) = raw19940 := by
      apply Matrix.ext; unfold tripleCharges sourceA1388 sourceB1388 sourceC1388 difference raw19940; decide +kernel
    rw [ha]
    exact (canonical19940 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1388 + difference 5 4) (sourceB1388 + difference 4 5) sourceC1388) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1758) := by
    have ha : (tripleCharges (sourceA1388 + difference 5 4) (sourceB1388 + difference 4 5) sourceC1388) = raw21874 := by
      apply Matrix.ext; unfold tripleCharges sourceA1388 sourceB1388 sourceC1388 difference raw21874; decide +kernel
    rw [ha]
    exact (canonical21874 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1388 sourceB1388 sourceC1388
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1388, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1389 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1389 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceC1389 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceForm1389 : Integer.Sparse Master := [(Sum.inr 602, 3), (Sum.inr 609, 1), (Sum.inr 618, 1), (Sum.inr 1085, 1), (Sum.inr 4085, -1)]

theorem sourceEq1389 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1389 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1389 + difference 0 0) (sourceB1389 + difference 0 0) sourceC1389) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1085) := by
    have ha : (tripleCharges (sourceA1389 + difference 0 0) (sourceB1389 + difference 0 0) sourceC1389) = raw21875 := by
      apply Matrix.ext; unfold tripleCharges sourceA1389 sourceB1389 sourceC1389 difference raw21875; decide +kernel
    rw [ha]
    exact (canonical21875 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1389 + difference 1 0) (sourceB1389 + difference 0 1) sourceC1389) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 602) := by
    have ha : (tripleCharges (sourceA1389 + difference 1 0) (sourceB1389 + difference 0 1) sourceC1389) = raw21876 := by
      apply Matrix.ext; unfold tripleCharges sourceA1389 sourceB1389 sourceC1389 difference raw21876; decide +kernel
    rw [ha]
    exact (canonical21876 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1389 + difference 2 0) (sourceB1389 + difference 0 2) sourceC1389) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 602) := by
    have ha : (tripleCharges (sourceA1389 + difference 2 0) (sourceB1389 + difference 0 2) sourceC1389) = raw21877 := by
      apply Matrix.ext; unfold tripleCharges sourceA1389 sourceB1389 sourceC1389 difference raw21877; decide +kernel
    rw [ha]
    exact (canonical21877 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1389 + difference 3 0) (sourceB1389 + difference 0 3) sourceC1389) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 602) := by
    have ha : (tripleCharges (sourceA1389 + difference 3 0) (sourceB1389 + difference 0 3) sourceC1389) = raw21878 := by
      apply Matrix.ext; unfold tripleCharges sourceA1389 sourceB1389 sourceC1389 difference raw21878; decide +kernel
    rw [ha]
    exact (canonical21878 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1389 + difference 4 0) (sourceB1389 + difference 0 4) sourceC1389) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 618) := by
    have ha : (tripleCharges (sourceA1389 + difference 4 0) (sourceB1389 + difference 0 4) sourceC1389) = raw21879 := by
      apply Matrix.ext; unfold tripleCharges sourceA1389 sourceB1389 sourceC1389 difference raw21879; decide +kernel
    rw [ha]
    exact (canonical21879 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1389 + difference 5 0) (sourceB1389 + difference 0 5) sourceC1389) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 609) := by
    have ha : (tripleCharges (sourceA1389 + difference 5 0) (sourceB1389 + difference 0 5) sourceC1389) = raw19951 := by
      apply Matrix.ext; unfold tripleCharges sourceA1389 sourceB1389 sourceC1389 difference raw19951; decide +kernel
    rw [ha]
    exact (canonical19951 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1389 + sourceB1389) sourceC1389) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA1389 + sourceB1389) sourceC1389) = raw19953 := by
      apply Matrix.ext; unfold doubleCharges sourceA1389 sourceB1389 sourceC1389 raw19953; decide +kernel
    rw [ha]
    exact (canonical19953 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1389 sourceB1389 sourceC1389
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1389, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1390 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1390 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceC1390 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceForm1390 : Integer.Sparse Master := [(Sum.inr 602, 1), (Sum.inr 921, 2), (Sum.inr 1080, 1), (Sum.inr 1085, 2), (Sum.inr 4085, -1)]

theorem sourceEq1390 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1390 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1390 + difference 1 0) (sourceB1390 + difference 0 1) sourceC1390) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 602) := by
    have ha : (tripleCharges (sourceA1390 + difference 1 0) (sourceB1390 + difference 0 1) sourceC1390) = raw21876 := by
      apply Matrix.ext; unfold tripleCharges sourceA1390 sourceB1390 sourceC1390 difference raw21876; decide +kernel
    rw [ha]
    exact (canonical21876 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1390 + difference 1 1) (sourceB1390 + difference 1 1) sourceC1390) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1085) := by
    have ha : (tripleCharges (sourceA1390 + difference 1 1) (sourceB1390 + difference 1 1) sourceC1390) = raw21875 := by
      apply Matrix.ext; unfold tripleCharges sourceA1390 sourceB1390 sourceC1390 difference raw21875; decide +kernel
    rw [ha]
    exact (canonical21875 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1390 + difference 1 2) (sourceB1390 + difference 2 1) sourceC1390) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 921) := by
    have ha : (tripleCharges (sourceA1390 + difference 1 2) (sourceB1390 + difference 2 1) sourceC1390) = raw21880 := by
      apply Matrix.ext; unfold tripleCharges sourceA1390 sourceB1390 sourceC1390 difference raw21880; decide +kernel
    rw [ha]
    exact (canonical21880 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1390 + difference 1 3) (sourceB1390 + difference 3 1) sourceC1390) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 921) := by
    have ha : (tripleCharges (sourceA1390 + difference 1 3) (sourceB1390 + difference 3 1) sourceC1390) = raw21881 := by
      apply Matrix.ext; unfold tripleCharges sourceA1390 sourceB1390 sourceC1390 difference raw21881; decide +kernel
    rw [ha]
    exact (canonical21881 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1390 + difference 1 4) (sourceB1390 + difference 4 1) sourceC1390) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1085) := by
    have ha : (tripleCharges (sourceA1390 + difference 1 4) (sourceB1390 + difference 4 1) sourceC1390) = raw21882 := by
      apply Matrix.ext; unfold tripleCharges sourceA1390 sourceB1390 sourceC1390 difference raw21882; decide +kernel
    rw [ha]
    exact (canonical21882 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1390 + difference 1 5) (sourceB1390 + difference 5 1) sourceC1390) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1080) := by
    have ha : (tripleCharges (sourceA1390 + difference 1 5) (sourceB1390 + difference 5 1) sourceC1390) = raw21883 := by
      apply Matrix.ext; unfold tripleCharges sourceA1390 sourceB1390 sourceC1390 difference raw21883; decide +kernel
    rw [ha]
    exact (canonical21883 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1390 + sourceB1390) sourceC1390) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA1390 + sourceB1390) sourceC1390) = raw19953 := by
      apply Matrix.ext; unfold doubleCharges sourceA1390 sourceB1390 sourceC1390 raw19953; decide +kernel
    rw [ha]
    exact (canonical19953 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1390 sourceB1390 sourceC1390
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1390, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1391 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1391 : Charge := ![1, 0, 0, -1, 2, -2]
def sourceC1391 : Charge := ![3, 0, 0, 1, -3, -1]
def sourceForm1391 : Integer.Sparse Master := [(Sum.inr 1010, 1), (Sum.inr 1951, 1), (Sum.inr 2004, 2), (Sum.inr 2222, 1), (Sum.inr 2230, 1), (Sum.inr 4081, -1)]

theorem sourceEq1391 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1391 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1391 + difference 0 0) (sourceB1391 + difference 0 0) sourceC1391) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1010) := by
    have ha : (tripleCharges (sourceA1391 + difference 0 0) (sourceB1391 + difference 0 0) sourceC1391) = raw21884 := by
      apply Matrix.ext; unfold tripleCharges sourceA1391 sourceB1391 sourceC1391 difference raw21884; decide +kernel
    rw [ha]
    exact (canonical21884 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1391 + difference 0 1) (sourceB1391 + difference 1 0) sourceC1391) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2004) := by
    have ha : (tripleCharges (sourceA1391 + difference 0 1) (sourceB1391 + difference 1 0) sourceC1391) = raw21885 := by
      apply Matrix.ext; unfold tripleCharges sourceA1391 sourceB1391 sourceC1391 difference raw21885; decide +kernel
    rw [ha]
    exact (canonical21885 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1391 + difference 0 2) (sourceB1391 + difference 2 0) sourceC1391) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2004) := by
    have ha : (tripleCharges (sourceA1391 + difference 0 2) (sourceB1391 + difference 2 0) sourceC1391) = raw21886 := by
      apply Matrix.ext; unfold tripleCharges sourceA1391 sourceB1391 sourceC1391 difference raw21886; decide +kernel
    rw [ha]
    exact (canonical21886 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1391 + difference 0 3) (sourceB1391 + difference 3 0) sourceC1391) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1951) := by
    have ha : (tripleCharges (sourceA1391 + difference 0 3) (sourceB1391 + difference 3 0) sourceC1391) = raw21887 := by
      apply Matrix.ext; unfold tripleCharges sourceA1391 sourceB1391 sourceC1391 difference raw21887; decide +kernel
    rw [ha]
    exact (canonical21887 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1391 + difference 0 4) (sourceB1391 + difference 4 0) sourceC1391) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2222) := by
    have ha : (tripleCharges (sourceA1391 + difference 0 4) (sourceB1391 + difference 4 0) sourceC1391) = raw21888 := by
      apply Matrix.ext; unfold tripleCharges sourceA1391 sourceB1391 sourceC1391 difference raw21888; decide +kernel
    rw [ha]
    exact (canonical21888 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1391 + difference 0 5) (sourceB1391 + difference 5 0) sourceC1391) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2230) := by
    have ha : (tripleCharges (sourceA1391 + difference 0 5) (sourceB1391 + difference 5 0) sourceC1391) = raw21889 := by
      apply Matrix.ext; unfold tripleCharges sourceA1391 sourceB1391 sourceC1391 difference raw21889; decide +kernel
    rw [ha]
    exact (canonical21889 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1391 + sourceB1391) sourceC1391) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1391 + sourceB1391) sourceC1391) = raw21890 := by
      apply Matrix.ext; unfold doubleCharges sourceA1391 sourceB1391 sourceC1391 raw21890; decide +kernel
    rw [ha]
    exact (canonical21890 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1391 sourceB1391 sourceC1391
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1391, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1392 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1392 : Charge := ![1, 0, 0, -1, 2, -2]
def sourceC1392 : Charge := ![3, 0, 0, 1, -3, -1]
def sourceForm1392 : Integer.Sparse Master := [(Sum.inr 1001, 2), (Sum.inr 1010, 1), (Sum.inr 1012, 1), (Sum.inr 1076, 1), (Sum.inr 2230, 1), (Sum.inr 4081, -1)]

theorem sourceEq1392 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1392 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1392 + difference 0 5) (sourceB1392 + difference 5 0) sourceC1392) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2230) := by
    have ha : (tripleCharges (sourceA1392 + difference 0 5) (sourceB1392 + difference 5 0) sourceC1392) = raw21889 := by
      apply Matrix.ext; unfold tripleCharges sourceA1392 sourceB1392 sourceC1392 difference raw21889; decide +kernel
    rw [ha]
    exact (canonical21889 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1392 + difference 1 5) (sourceB1392 + difference 5 1) sourceC1392) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1001) := by
    have ha : (tripleCharges (sourceA1392 + difference 1 5) (sourceB1392 + difference 5 1) sourceC1392) = raw21891 := by
      apply Matrix.ext; unfold tripleCharges sourceA1392 sourceB1392 sourceC1392 difference raw21891; decide +kernel
    rw [ha]
    exact (canonical21891 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1392 + difference 2 5) (sourceB1392 + difference 5 2) sourceC1392) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1001) := by
    have ha : (tripleCharges (sourceA1392 + difference 2 5) (sourceB1392 + difference 5 2) sourceC1392) = raw21892 := by
      apply Matrix.ext; unfold tripleCharges sourceA1392 sourceB1392 sourceC1392 difference raw21892; decide +kernel
    rw [ha]
    exact (canonical21892 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1392 + difference 3 5) (sourceB1392 + difference 5 3) sourceC1392) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1076) := by
    have ha : (tripleCharges (sourceA1392 + difference 3 5) (sourceB1392 + difference 5 3) sourceC1392) = raw21893 := by
      apply Matrix.ext; unfold tripleCharges sourceA1392 sourceB1392 sourceC1392 difference raw21893; decide +kernel
    rw [ha]
    exact (canonical21893 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1392 + difference 4 5) (sourceB1392 + difference 5 4) sourceC1392) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1012) := by
    have ha : (tripleCharges (sourceA1392 + difference 4 5) (sourceB1392 + difference 5 4) sourceC1392) = raw21894 := by
      apply Matrix.ext; unfold tripleCharges sourceA1392 sourceB1392 sourceC1392 difference raw21894; decide +kernel
    rw [ha]
    exact (canonical21894 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1392 + difference 5 5) (sourceB1392 + difference 5 5) sourceC1392) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1010) := by
    have ha : (tripleCharges (sourceA1392 + difference 5 5) (sourceB1392 + difference 5 5) sourceC1392) = raw21884 := by
      apply Matrix.ext; unfold tripleCharges sourceA1392 sourceB1392 sourceC1392 difference raw21884; decide +kernel
    rw [ha]
    exact (canonical21884 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1392 + sourceB1392) sourceC1392) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1392 + sourceB1392) sourceC1392) = raw21890 := by
      apply Matrix.ext; unfold doubleCharges sourceA1392 sourceB1392 sourceC1392 raw21890; decide +kernel
    rw [ha]
    exact (canonical21890 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1392 sourceB1392 sourceC1392
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1392, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1393 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1393 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceC1393 : Charge := ![3, 0, 0, 1, -2, -2]
def sourceForm1393 : Integer.Sparse Master := [(Sum.inr 1009, 1), (Sum.inr 1950, 1), (Sum.inr 2003, 2), (Sum.inr 2218, 1), (Sum.inr 2229, 1), (Sum.inr 4082, -1)]

theorem sourceEq1393 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1393 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1393 + difference 0 0) (sourceB1393 + difference 0 0) sourceC1393) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1009) := by
    have ha : (tripleCharges (sourceA1393 + difference 0 0) (sourceB1393 + difference 0 0) sourceC1393) = raw21895 := by
      apply Matrix.ext; unfold tripleCharges sourceA1393 sourceB1393 sourceC1393 difference raw21895; decide +kernel
    rw [ha]
    exact (canonical21895 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1393 + difference 0 1) (sourceB1393 + difference 1 0) sourceC1393) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2003) := by
    have ha : (tripleCharges (sourceA1393 + difference 0 1) (sourceB1393 + difference 1 0) sourceC1393) = raw21896 := by
      apply Matrix.ext; unfold tripleCharges sourceA1393 sourceB1393 sourceC1393 difference raw21896; decide +kernel
    rw [ha]
    exact (canonical21896 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1393 + difference 0 2) (sourceB1393 + difference 2 0) sourceC1393) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2003) := by
    have ha : (tripleCharges (sourceA1393 + difference 0 2) (sourceB1393 + difference 2 0) sourceC1393) = raw21897 := by
      apply Matrix.ext; unfold tripleCharges sourceA1393 sourceB1393 sourceC1393 difference raw21897; decide +kernel
    rw [ha]
    exact (canonical21897 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1393 + difference 0 3) (sourceB1393 + difference 3 0) sourceC1393) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1950) := by
    have ha : (tripleCharges (sourceA1393 + difference 0 3) (sourceB1393 + difference 3 0) sourceC1393) = raw21898 := by
      apply Matrix.ext; unfold tripleCharges sourceA1393 sourceB1393 sourceC1393 difference raw21898; decide +kernel
    rw [ha]
    exact (canonical21898 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1393 + difference 0 4) (sourceB1393 + difference 4 0) sourceC1393) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2218) := by
    have ha : (tripleCharges (sourceA1393 + difference 0 4) (sourceB1393 + difference 4 0) sourceC1393) = raw21899 := by
      apply Matrix.ext; unfold tripleCharges sourceA1393 sourceB1393 sourceC1393 difference raw21899; decide +kernel
    rw [ha]
    exact (canonical21899 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1393 + difference 0 5) (sourceB1393 + difference 5 0) sourceC1393) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2229) := by
    have ha : (tripleCharges (sourceA1393 + difference 0 5) (sourceB1393 + difference 5 0) sourceC1393) = raw21900 := by
      apply Matrix.ext; unfold tripleCharges sourceA1393 sourceB1393 sourceC1393 difference raw21900; decide +kernel
    rw [ha]
    exact (canonical21900 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1393 + sourceB1393) sourceC1393) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA1393 + sourceB1393) sourceC1393) = raw21901 := by
      apply Matrix.ext; unfold doubleCharges sourceA1393 sourceB1393 sourceC1393 raw21901; decide +kernel
    rw [ha]
    exact (canonical21901 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1393 sourceB1393 sourceC1393
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1393, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1394 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1394 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceC1394 : Charge := ![3, 0, 0, 1, -2, -2]
def sourceForm1394 : Integer.Sparse Master := [(Sum.inr 881, 2), (Sum.inr 893, 1), (Sum.inr 896, 1), (Sum.inr 1009, 1), (Sum.inr 1950, 1), (Sum.inr 4082, -1)]

theorem sourceEq1394 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1394 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1394 + difference 0 3) (sourceB1394 + difference 3 0) sourceC1394) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1950) := by
    have ha : (tripleCharges (sourceA1394 + difference 0 3) (sourceB1394 + difference 3 0) sourceC1394) = raw21898 := by
      apply Matrix.ext; unfold tripleCharges sourceA1394 sourceB1394 sourceC1394 difference raw21898; decide +kernel
    rw [ha]
    exact (canonical21898 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1394 + difference 1 3) (sourceB1394 + difference 3 1) sourceC1394) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 881) := by
    have ha : (tripleCharges (sourceA1394 + difference 1 3) (sourceB1394 + difference 3 1) sourceC1394) = raw21902 := by
      apply Matrix.ext; unfold tripleCharges sourceA1394 sourceB1394 sourceC1394 difference raw21902; decide +kernel
    rw [ha]
    exact (canonical21902 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1394 + difference 2 3) (sourceB1394 + difference 3 2) sourceC1394) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 881) := by
    have ha : (tripleCharges (sourceA1394 + difference 2 3) (sourceB1394 + difference 3 2) sourceC1394) = raw21903 := by
      apply Matrix.ext; unfold tripleCharges sourceA1394 sourceB1394 sourceC1394 difference raw21903; decide +kernel
    rw [ha]
    exact (canonical21903 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1394 + difference 3 3) (sourceB1394 + difference 3 3) sourceC1394) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1009) := by
    have ha : (tripleCharges (sourceA1394 + difference 3 3) (sourceB1394 + difference 3 3) sourceC1394) = raw21895 := by
      apply Matrix.ext; unfold tripleCharges sourceA1394 sourceB1394 sourceC1394 difference raw21895; decide +kernel
    rw [ha]
    exact (canonical21895 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1394 + difference 4 3) (sourceB1394 + difference 3 4) sourceC1394) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 896) := by
    have ha : (tripleCharges (sourceA1394 + difference 4 3) (sourceB1394 + difference 3 4) sourceC1394) = raw21904 := by
      apply Matrix.ext; unfold tripleCharges sourceA1394 sourceB1394 sourceC1394 difference raw21904; decide +kernel
    rw [ha]
    exact (canonical21904 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1394 + difference 5 3) (sourceB1394 + difference 3 5) sourceC1394) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 893) := by
    have ha : (tripleCharges (sourceA1394 + difference 5 3) (sourceB1394 + difference 3 5) sourceC1394) = raw21905 := by
      apply Matrix.ext; unfold tripleCharges sourceA1394 sourceB1394 sourceC1394 difference raw21905; decide +kernel
    rw [ha]
    exact (canonical21905 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1394 + sourceB1394) sourceC1394) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA1394 + sourceB1394) sourceC1394) = raw21901 := by
      apply Matrix.ext; unfold doubleCharges sourceA1394 sourceB1394 sourceC1394 raw21901; decide +kernel
    rw [ha]
    exact (canonical21901 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1394 sourceB1394 sourceC1394
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1394, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1395 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1395 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceC1395 : Charge := ![3, 0, 0, 1, -2, -2]
def sourceForm1395 : Integer.Sparse Master := [(Sum.inr 576, 1), (Sum.inr 896, 1), (Sum.inr 903, 2), (Sum.inr 1009, 1), (Sum.inr 1013, 1), (Sum.inr 4082, -1)]

theorem sourceEq1395 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1395 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1395 + difference 4 0) (sourceB1395 + difference 0 4) sourceC1395) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 576) := by
    have ha : (tripleCharges (sourceA1395 + difference 4 0) (sourceB1395 + difference 0 4) sourceC1395) = raw21906 := by
      apply Matrix.ext; unfold tripleCharges sourceA1395 sourceB1395 sourceC1395 difference raw21906; decide +kernel
    rw [ha]
    exact (canonical21906 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1395 + difference 4 1) (sourceB1395 + difference 1 4) sourceC1395) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 903) := by
    have ha : (tripleCharges (sourceA1395 + difference 4 1) (sourceB1395 + difference 1 4) sourceC1395) = raw21907 := by
      apply Matrix.ext; unfold tripleCharges sourceA1395 sourceB1395 sourceC1395 difference raw21907; decide +kernel
    rw [ha]
    exact (canonical21907 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1395 + difference 4 2) (sourceB1395 + difference 2 4) sourceC1395) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 903) := by
    have ha : (tripleCharges (sourceA1395 + difference 4 2) (sourceB1395 + difference 2 4) sourceC1395) = raw21908 := by
      apply Matrix.ext; unfold tripleCharges sourceA1395 sourceB1395 sourceC1395 difference raw21908; decide +kernel
    rw [ha]
    exact (canonical21908 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1395 + difference 4 3) (sourceB1395 + difference 3 4) sourceC1395) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 896) := by
    have ha : (tripleCharges (sourceA1395 + difference 4 3) (sourceB1395 + difference 3 4) sourceC1395) = raw21904 := by
      apply Matrix.ext; unfold tripleCharges sourceA1395 sourceB1395 sourceC1395 difference raw21904; decide +kernel
    rw [ha]
    exact (canonical21904 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1395 + difference 4 4) (sourceB1395 + difference 4 4) sourceC1395) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1009) := by
    have ha : (tripleCharges (sourceA1395 + difference 4 4) (sourceB1395 + difference 4 4) sourceC1395) = raw21895 := by
      apply Matrix.ext; unfold tripleCharges sourceA1395 sourceB1395 sourceC1395 difference raw21895; decide +kernel
    rw [ha]
    exact (canonical21895 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1395 + difference 4 5) (sourceB1395 + difference 5 4) sourceC1395) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1013) := by
    have ha : (tripleCharges (sourceA1395 + difference 4 5) (sourceB1395 + difference 5 4) sourceC1395) = raw21909 := by
      apply Matrix.ext; unfold tripleCharges sourceA1395 sourceB1395 sourceC1395 difference raw21909; decide +kernel
    rw [ha]
    exact (canonical21909 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1395 + sourceB1395) sourceC1395) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA1395 + sourceB1395) sourceC1395) = raw21901 := by
      apply Matrix.ext; unfold doubleCharges sourceA1395 sourceB1395 sourceC1395 raw21901; decide +kernel
    rw [ha]
    exact (canonical21901 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1395 sourceB1395 sourceC1395
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1395, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1396 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1396 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceC1396 : Charge := ![3, 0, 0, 1, -2, -2]
def sourceForm1396 : Integer.Sparse Master := [(Sum.inr 1000, 2), (Sum.inr 1009, 1), (Sum.inr 1013, 1), (Sum.inr 1075, 1), (Sum.inr 2229, 1), (Sum.inr 4082, -1)]

theorem sourceEq1396 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1396 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1396 + difference 0 5) (sourceB1396 + difference 5 0) sourceC1396) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2229) := by
    have ha : (tripleCharges (sourceA1396 + difference 0 5) (sourceB1396 + difference 5 0) sourceC1396) = raw21900 := by
      apply Matrix.ext; unfold tripleCharges sourceA1396 sourceB1396 sourceC1396 difference raw21900; decide +kernel
    rw [ha]
    exact (canonical21900 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1396 + difference 1 5) (sourceB1396 + difference 5 1) sourceC1396) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1000) := by
    have ha : (tripleCharges (sourceA1396 + difference 1 5) (sourceB1396 + difference 5 1) sourceC1396) = raw21910 := by
      apply Matrix.ext; unfold tripleCharges sourceA1396 sourceB1396 sourceC1396 difference raw21910; decide +kernel
    rw [ha]
    exact (canonical21910 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1396 + difference 2 5) (sourceB1396 + difference 5 2) sourceC1396) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1000) := by
    have ha : (tripleCharges (sourceA1396 + difference 2 5) (sourceB1396 + difference 5 2) sourceC1396) = raw21911 := by
      apply Matrix.ext; unfold tripleCharges sourceA1396 sourceB1396 sourceC1396 difference raw21911; decide +kernel
    rw [ha]
    exact (canonical21911 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1396 + difference 3 5) (sourceB1396 + difference 5 3) sourceC1396) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1075) := by
    have ha : (tripleCharges (sourceA1396 + difference 3 5) (sourceB1396 + difference 5 3) sourceC1396) = raw21912 := by
      apply Matrix.ext; unfold tripleCharges sourceA1396 sourceB1396 sourceC1396 difference raw21912; decide +kernel
    rw [ha]
    exact (canonical21912 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1396 + difference 4 5) (sourceB1396 + difference 5 4) sourceC1396) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1013) := by
    have ha : (tripleCharges (sourceA1396 + difference 4 5) (sourceB1396 + difference 5 4) sourceC1396) = raw21909 := by
      apply Matrix.ext; unfold tripleCharges sourceA1396 sourceB1396 sourceC1396 difference raw21909; decide +kernel
    rw [ha]
    exact (canonical21909 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1396 + difference 5 5) (sourceB1396 + difference 5 5) sourceC1396) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1009) := by
    have ha : (tripleCharges (sourceA1396 + difference 5 5) (sourceB1396 + difference 5 5) sourceC1396) = raw21895 := by
      apply Matrix.ext; unfold tripleCharges sourceA1396 sourceB1396 sourceC1396 difference raw21895; decide +kernel
    rw [ha]
    exact (canonical21895 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1396 + sourceB1396) sourceC1396) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA1396 + sourceB1396) sourceC1396) = raw21901 := by
      apply Matrix.ext; unfold doubleCharges sourceA1396 sourceB1396 sourceC1396 raw21901; decide +kernel
    rw [ha]
    exact (canonical21901 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1396 sourceB1396 sourceC1396
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1396, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1397 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceB1397 : Charge := ![3, 0, 0, 1, -2, -2]
def sourceC1397 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1397 : Integer.Sparse Master := [(Sum.inr 716, 2), (Sum.inr 728, 1), (Sum.inr 729, 1), (Sum.inr 863, 1), (Sum.inr 1630, 1), (Sum.inr 4070, -1)]

theorem sourceEq1397 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1397 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1397 + difference 0 0) (sourceB1397 + difference 0 0) sourceC1397) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1630) := by
    have ha : (tripleCharges (sourceA1397 + difference 0 0) (sourceB1397 + difference 0 0) sourceC1397) = raw20842 := by
      apply Matrix.ext; unfold tripleCharges sourceA1397 sourceB1397 sourceC1397 difference raw20842; decide +kernel
    rw [ha]
    exact (canonical20842 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1397 + difference 1 0) (sourceB1397 + difference 0 1) sourceC1397) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 716) := by
    have ha : (tripleCharges (sourceA1397 + difference 1 0) (sourceB1397 + difference 0 1) sourceC1397) = raw21611 := by
      apply Matrix.ext; unfold tripleCharges sourceA1397 sourceB1397 sourceC1397 difference raw21611; decide +kernel
    rw [ha]
    exact (canonical21611 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1397 + difference 2 0) (sourceB1397 + difference 0 2) sourceC1397) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 716) := by
    have ha : (tripleCharges (sourceA1397 + difference 2 0) (sourceB1397 + difference 0 2) sourceC1397) = raw21913 := by
      apply Matrix.ext; unfold tripleCharges sourceA1397 sourceB1397 sourceC1397 difference raw21913; decide +kernel
    rw [ha]
    exact (canonical21913 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1397 + difference 3 0) (sourceB1397 + difference 0 3) sourceC1397) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 863) := by
    have ha : (tripleCharges (sourceA1397 + difference 3 0) (sourceB1397 + difference 0 3) sourceC1397) = raw21914 := by
      apply Matrix.ext; unfold tripleCharges sourceA1397 sourceB1397 sourceC1397 difference raw21914; decide +kernel
    rw [ha]
    exact (canonical21914 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1397 + difference 4 0) (sourceB1397 + difference 0 4) sourceC1397) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 729) := by
    have ha : (tripleCharges (sourceA1397 + difference 4 0) (sourceB1397 + difference 0 4) sourceC1397) = raw21915 := by
      apply Matrix.ext; unfold tripleCharges sourceA1397 sourceB1397 sourceC1397 difference raw21915; decide +kernel
    rw [ha]
    exact (canonical21915 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1397 + difference 5 0) (sourceB1397 + difference 0 5) sourceC1397) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 728) := by
    have ha : (tripleCharges (sourceA1397 + difference 5 0) (sourceB1397 + difference 0 5) sourceC1397) = raw21916 := by
      apply Matrix.ext; unfold tripleCharges sourceA1397 sourceB1397 sourceC1397 difference raw21916; decide +kernel
    rw [ha]
    exact (canonical21916 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1397 + sourceB1397) sourceC1397) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1397 + sourceB1397) sourceC1397) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1397 sourceB1397 sourceC1397 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1397 sourceB1397 sourceC1397
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1397, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1398 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceB1398 : Charge := ![3, 0, 0, 1, -2, -2]
def sourceC1398 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1398 : Integer.Sparse Master := [(Sum.inr 728, 1), (Sum.inr 1548, 1), (Sum.inr 1584, 2), (Sum.inr 1625, 1), (Sum.inr 1630, 1), (Sum.inr 4070, -1)]

theorem sourceEq1398 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1398 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1398 + difference 5 0) (sourceB1398 + difference 0 5) sourceC1398) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 728) := by
    have ha : (tripleCharges (sourceA1398 + difference 5 0) (sourceB1398 + difference 0 5) sourceC1398) = raw21916 := by
      apply Matrix.ext; unfold tripleCharges sourceA1398 sourceB1398 sourceC1398 difference raw21916; decide +kernel
    rw [ha]
    exact (canonical21916 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1398 + difference 5 1) (sourceB1398 + difference 1 5) sourceC1398) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1584) := by
    have ha : (tripleCharges (sourceA1398 + difference 5 1) (sourceB1398 + difference 1 5) sourceC1398) = raw21917 := by
      apply Matrix.ext; unfold tripleCharges sourceA1398 sourceB1398 sourceC1398 difference raw21917; decide +kernel
    rw [ha]
    exact (canonical21917 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1398 + difference 5 2) (sourceB1398 + difference 2 5) sourceC1398) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1584) := by
    have ha : (tripleCharges (sourceA1398 + difference 5 2) (sourceB1398 + difference 2 5) sourceC1398) = raw21069 := by
      apply Matrix.ext; unfold tripleCharges sourceA1398 sourceB1398 sourceC1398 difference raw21069; decide +kernel
    rw [ha]
    exact (canonical21069 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1398 + difference 5 3) (sourceB1398 + difference 3 5) sourceC1398) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1548) := by
    have ha : (tripleCharges (sourceA1398 + difference 5 3) (sourceB1398 + difference 3 5) sourceC1398) = raw21031 := by
      apply Matrix.ext; unfold tripleCharges sourceA1398 sourceB1398 sourceC1398 difference raw21031; decide +kernel
    rw [ha]
    exact (canonical21031 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1398 + difference 5 4) (sourceB1398 + difference 4 5) sourceC1398) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1625) := by
    have ha : (tripleCharges (sourceA1398 + difference 5 4) (sourceB1398 + difference 4 5) sourceC1398) = raw20843 := by
      apply Matrix.ext; unfold tripleCharges sourceA1398 sourceB1398 sourceC1398 difference raw20843; decide +kernel
    rw [ha]
    exact (canonical20843 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1398 + difference 5 5) (sourceB1398 + difference 5 5) sourceC1398) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1630) := by
    have ha : (tripleCharges (sourceA1398 + difference 5 5) (sourceB1398 + difference 5 5) sourceC1398) = raw20842 := by
      apply Matrix.ext; unfold tripleCharges sourceA1398 sourceB1398 sourceC1398 difference raw20842; decide +kernel
    rw [ha]
    exact (canonical20842 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1398 + sourceB1398) sourceC1398) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1398 + sourceB1398) sourceC1398) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1398 sourceB1398 sourceC1398 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1398 sourceB1398 sourceC1398
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1398, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1399 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1399 : Charge := ![1, 0, 0, -1, 0, 0]
def sourceC1399 : Charge := ![3, 0, 0, 1, -1, -3]
def sourceForm1399 : Integer.Sparse Master := [(Sum.inr 4081, 1), (Sum.inr 4140, 2), (Sum.inr 4146, 1), (Sum.inr 4147, 1), (Sum.inr 4166, 1), (Sum.inr 4289, 2), (Sum.inr 4302, 2), (Sum.inr 4312, 1), (Sum.inr 4317, 1), (Sum.inr 4320, 2), (Sum.inr 4324, 2), (Sum.inr 4338, 2), (Sum.inr 4398, 2), (Sum.inr 4405, 1), (Sum.inr 4418, 2), (Sum.inr 4431, 1), (Sum.inr 4454, 1), (Sum.inr 4490, 1), (Sum.inr 4738, 2), (Sum.inr 4837, 1), (Sum.inr 4841, 1)]

theorem sourceEq1399 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1399 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1399 + difference 0 1) (sourceB1399 + difference 1 0) sourceC1399) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4738) := by
    have ha : (tripleCharges (sourceA1399 + difference 0 1) (sourceB1399 + difference 1 0) sourceC1399) = raw21918 := by
      apply Matrix.ext; unfold tripleCharges sourceA1399 sourceB1399 sourceC1399 difference raw21918; decide +kernel
    rw [ha]
    exact (canonical21918 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1399 + difference 0 2) (sourceB1399 + difference 2 0) sourceC1399) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4738) := by
    have ha : (tripleCharges (sourceA1399 + difference 0 2) (sourceB1399 + difference 2 0) sourceC1399) = raw21919 := by
      apply Matrix.ext; unfold tripleCharges sourceA1399 sourceB1399 sourceC1399 difference raw21919; decide +kernel
    rw [ha]
    exact (canonical21919 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1399 + difference 0 3) (sourceB1399 + difference 3 0) sourceC1399) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (tripleCharges (sourceA1399 + difference 0 3) (sourceB1399 + difference 3 0) sourceC1399) = raw21920 := by
      apply Matrix.ext; unfold tripleCharges sourceA1399 sourceB1399 sourceC1399 difference raw21920; decide +kernel
    rw [ha]
    exact (canonical21920 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1399 + difference 0 4) (sourceB1399 + difference 4 0) sourceC1399) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4837) := by
    have ha : (tripleCharges (sourceA1399 + difference 0 4) (sourceB1399 + difference 4 0) sourceC1399) = raw21921 := by
      apply Matrix.ext; unfold tripleCharges sourceA1399 sourceB1399 sourceC1399 difference raw21921; decide +kernel
    rw [ha]
    exact (canonical21921 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1399 + difference 0 5) (sourceB1399 + difference 5 0) sourceC1399) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4841) := by
    have ha : (tripleCharges (sourceA1399 + difference 0 5) (sourceB1399 + difference 5 0) sourceC1399) = raw21922 := by
      apply Matrix.ext; unfold tripleCharges sourceA1399 sourceB1399 sourceC1399 difference raw21922; decide +kernel
    rw [ha]
    exact (canonical21922 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1399 + difference 1 0) (sourceB1399 + difference 0 1) sourceC1399) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4140) := by
    have ha : (tripleCharges (sourceA1399 + difference 1 0) (sourceB1399 + difference 0 1) sourceC1399) = raw21923 := by
      apply Matrix.ext; unfold tripleCharges sourceA1399 sourceB1399 sourceC1399 difference raw21923; decide +kernel
    rw [ha]
    exact (canonical21923 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1399 + difference 1 2) (sourceB1399 + difference 2 1) sourceC1399) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4320) := by
    have ha : (tripleCharges (sourceA1399 + difference 1 2) (sourceB1399 + difference 2 1) sourceC1399) = raw21924 := by
      apply Matrix.ext; unfold tripleCharges sourceA1399 sourceB1399 sourceC1399 difference raw21924; decide +kernel
    rw [ha]
    exact (canonical21924 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1399 + difference 1 3) (sourceB1399 + difference 3 1) sourceC1399) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4302) := by
    have ha : (tripleCharges (sourceA1399 + difference 1 3) (sourceB1399 + difference 3 1) sourceC1399) = raw21925 := by
      apply Matrix.ext; unfold tripleCharges sourceA1399 sourceB1399 sourceC1399 difference raw21925; decide +kernel
    rw [ha]
    exact (canonical21925 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1399 + difference 1 4) (sourceB1399 + difference 4 1) sourceC1399) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4398) := by
    have ha : (tripleCharges (sourceA1399 + difference 1 4) (sourceB1399 + difference 4 1) sourceC1399) = raw21926 := by
      apply Matrix.ext; unfold tripleCharges sourceA1399 sourceB1399 sourceC1399 difference raw21926; decide +kernel
    rw [ha]
    exact (canonical21926 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1399 + difference 1 5) (sourceB1399 + difference 5 1) sourceC1399) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4418) := by
    have ha : (tripleCharges (sourceA1399 + difference 1 5) (sourceB1399 + difference 5 1) sourceC1399) = raw21927 := by
      apply Matrix.ext; unfold tripleCharges sourceA1399 sourceB1399 sourceC1399 difference raw21927; decide +kernel
    rw [ha]
    exact (canonical21927 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1399 + difference 2 0) (sourceB1399 + difference 0 2) sourceC1399) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4140) := by
    have ha : (tripleCharges (sourceA1399 + difference 2 0) (sourceB1399 + difference 0 2) sourceC1399) = raw21928 := by
      apply Matrix.ext; unfold tripleCharges sourceA1399 sourceB1399 sourceC1399 difference raw21928; decide +kernel
    rw [ha]
    exact (canonical21928 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1399 + difference 2 1) (sourceB1399 + difference 1 2) sourceC1399) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4320) := by
    have ha : (tripleCharges (sourceA1399 + difference 2 1) (sourceB1399 + difference 1 2) sourceC1399) = raw21929 := by
      apply Matrix.ext; unfold tripleCharges sourceA1399 sourceB1399 sourceC1399 difference raw21929; decide +kernel
    rw [ha]
    exact (canonical21929 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1399 + difference 2 3) (sourceB1399 + difference 3 2) sourceC1399) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4302) := by
    have ha : (tripleCharges (sourceA1399 + difference 2 3) (sourceB1399 + difference 3 2) sourceC1399) = raw21930 := by
      apply Matrix.ext; unfold tripleCharges sourceA1399 sourceB1399 sourceC1399 difference raw21930; decide +kernel
    rw [ha]
    exact (canonical21930 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1399 + difference 2 4) (sourceB1399 + difference 4 2) sourceC1399) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4398) := by
    have ha : (tripleCharges (sourceA1399 + difference 2 4) (sourceB1399 + difference 4 2) sourceC1399) = raw21931 := by
      apply Matrix.ext; unfold tripleCharges sourceA1399 sourceB1399 sourceC1399 difference raw21931; decide +kernel
    rw [ha]
    exact (canonical21931 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1399 + difference 2 5) (sourceB1399 + difference 5 2) sourceC1399) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4418) := by
    have ha : (tripleCharges (sourceA1399 + difference 2 5) (sourceB1399 + difference 5 2) sourceC1399) = raw21932 := by
      apply Matrix.ext; unfold tripleCharges sourceA1399 sourceB1399 sourceC1399 difference raw21932; decide +kernel
    rw [ha]
    exact (canonical21932 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1399 + difference 3 0) (sourceB1399 + difference 0 3) sourceC1399) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4166) := by
    have ha : (tripleCharges (sourceA1399 + difference 3 0) (sourceB1399 + difference 0 3) sourceC1399) = raw21933 := by
      apply Matrix.ext; unfold tripleCharges sourceA1399 sourceB1399 sourceC1399 difference raw21933; decide +kernel
    rw [ha]
    exact (canonical21933 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1399 + difference 3 1) (sourceB1399 + difference 1 3) sourceC1399) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4338) := by
    have ha : (tripleCharges (sourceA1399 + difference 3 1) (sourceB1399 + difference 1 3) sourceC1399) = raw21934 := by
      apply Matrix.ext; unfold tripleCharges sourceA1399 sourceB1399 sourceC1399 difference raw21934; decide +kernel
    rw [ha]
    exact (canonical21934 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1399 + difference 3 2) (sourceB1399 + difference 2 3) sourceC1399) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4338) := by
    have ha : (tripleCharges (sourceA1399 + difference 3 2) (sourceB1399 + difference 2 3) sourceC1399) = raw21935 := by
      apply Matrix.ext; unfold tripleCharges sourceA1399 sourceB1399 sourceC1399 difference raw21935; decide +kernel
    rw [ha]
    exact (canonical21935 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1399 + difference 3 4) (sourceB1399 + difference 4 3) sourceC1399) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4454) := by
    have ha : (tripleCharges (sourceA1399 + difference 3 4) (sourceB1399 + difference 4 3) sourceC1399) = raw21936 := by
      apply Matrix.ext; unfold tripleCharges sourceA1399 sourceB1399 sourceC1399 difference raw21936; decide +kernel
    rw [ha]
    exact (canonical21936 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1399 + difference 3 5) (sourceB1399 + difference 5 3) sourceC1399) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4490) := by
    have ha : (tripleCharges (sourceA1399 + difference 3 5) (sourceB1399 + difference 5 3) sourceC1399) = raw21937 := by
      apply Matrix.ext; unfold tripleCharges sourceA1399 sourceB1399 sourceC1399 difference raw21937; decide +kernel
    rw [ha]
    exact (canonical21937 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1399 + difference 4 0) (sourceB1399 + difference 0 4) sourceC1399) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4147) := by
    have ha : (tripleCharges (sourceA1399 + difference 4 0) (sourceB1399 + difference 0 4) sourceC1399) = raw21938 := by
      apply Matrix.ext; unfold tripleCharges sourceA1399 sourceB1399 sourceC1399 difference raw21938; decide +kernel
    rw [ha]
    exact (canonical21938 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1399 + difference 4 1) (sourceB1399 + difference 1 4) sourceC1399) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4324) := by
    have ha : (tripleCharges (sourceA1399 + difference 4 1) (sourceB1399 + difference 1 4) sourceC1399) = raw21939 := by
      apply Matrix.ext; unfold tripleCharges sourceA1399 sourceB1399 sourceC1399 difference raw21939; decide +kernel
    rw [ha]
    exact (canonical21939 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1399 + difference 4 2) (sourceB1399 + difference 2 4) sourceC1399) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4324) := by
    have ha : (tripleCharges (sourceA1399 + difference 4 2) (sourceB1399 + difference 2 4) sourceC1399) = raw21940 := by
      apply Matrix.ext; unfold tripleCharges sourceA1399 sourceB1399 sourceC1399 difference raw21940; decide +kernel
    rw [ha]
    exact (canonical21940 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1399 + difference 4 3) (sourceB1399 + difference 3 4) sourceC1399) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4317) := by
    have ha : (tripleCharges (sourceA1399 + difference 4 3) (sourceB1399 + difference 3 4) sourceC1399) = raw21941 := by
      apply Matrix.ext; unfold tripleCharges sourceA1399 sourceB1399 sourceC1399 difference raw21941; decide +kernel
    rw [ha]
    exact (canonical21941 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1399 + difference 4 5) (sourceB1399 + difference 5 4) sourceC1399) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4431) := by
    have ha : (tripleCharges (sourceA1399 + difference 4 5) (sourceB1399 + difference 5 4) sourceC1399) = raw21942 := by
      apply Matrix.ext; unfold tripleCharges sourceA1399 sourceB1399 sourceC1399 difference raw21942; decide +kernel
    rw [ha]
    exact (canonical21942 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1399 + difference 5 0) (sourceB1399 + difference 0 5) sourceC1399) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4146) := by
    have ha : (tripleCharges (sourceA1399 + difference 5 0) (sourceB1399 + difference 0 5) sourceC1399) = raw21943 := by
      apply Matrix.ext; unfold tripleCharges sourceA1399 sourceB1399 sourceC1399 difference raw21943; decide +kernel
    rw [ha]
    exact (canonical21943 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1399 + difference 5 1) (sourceB1399 + difference 1 5) sourceC1399) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4289) := by
    have ha : (tripleCharges (sourceA1399 + difference 5 1) (sourceB1399 + difference 1 5) sourceC1399) = raw21944 := by
      apply Matrix.ext; unfold tripleCharges sourceA1399 sourceB1399 sourceC1399 difference raw21944; decide +kernel
    rw [ha]
    exact (canonical21944 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1399 + difference 5 2) (sourceB1399 + difference 2 5) sourceC1399) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4289) := by
    have ha : (tripleCharges (sourceA1399 + difference 5 2) (sourceB1399 + difference 2 5) sourceC1399) = raw21945 := by
      apply Matrix.ext; unfold tripleCharges sourceA1399 sourceB1399 sourceC1399 difference raw21945; decide +kernel
    rw [ha]
    exact (canonical21945 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1399 + difference 5 3) (sourceB1399 + difference 3 5) sourceC1399) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4312) := by
    have ha : (tripleCharges (sourceA1399 + difference 5 3) (sourceB1399 + difference 3 5) sourceC1399) = raw21946 := by
      apply Matrix.ext; unfold tripleCharges sourceA1399 sourceB1399 sourceC1399 difference raw21946; decide +kernel
    rw [ha]
    exact (canonical21946 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1399 + difference 5 4) (sourceB1399 + difference 4 5) sourceC1399) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4405) := by
    have ha : (tripleCharges (sourceA1399 + difference 5 4) (sourceB1399 + difference 4 5) sourceC1399) = raw21947 := by
      apply Matrix.ext; unfold tripleCharges sourceA1399 sourceB1399 sourceC1399 difference raw21947; decide +kernel
    rw [ha]
    exact (canonical21947 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1399 sourceB1399 sourceC1399
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1399, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1400 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1400 : Charge := ![1, 0, 0, -1, 0, 0]
def sourceC1400 : Charge := ![3, 0, 0, 1, -1, -3]
def sourceForm1400 : Integer.Sparse Master := [(Sum.inr 1489, 2), (Sum.inr 1494, 1), (Sum.inr 1495, 1), (Sum.inr 1499, 1), (Sum.inr 1555, 2), (Sum.inr 1557, 2), (Sum.inr 1574, 1), (Sum.inr 1576, 1), (Sum.inr 1586, 2), (Sum.inr 1590, 2), (Sum.inr 1599, 2), (Sum.inr 1602, 2), (Sum.inr 1620, 1), (Sum.inr 1627, 1), (Sum.inr 1633, 2), (Sum.inr 1647, 1), (Sum.inr 1650, 1), (Sum.inr 1911, 2), (Sum.inr 2056, 1), (Sum.inr 2060, 1), (Sum.inr 4081, 1)]

theorem sourceEq1400 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1400 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1400 + difference 0 1) (sourceB1400 + difference 1 0) sourceC1400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1911) := by
    have ha : (tripleCharges (sourceA1400 + difference 0 1) (sourceB1400 + difference 1 0) sourceC1400) = raw21948 := by
      apply Matrix.ext; unfold tripleCharges sourceA1400 sourceB1400 sourceC1400 difference raw21948; decide +kernel
    rw [ha]
    exact (canonical21948 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1400 + difference 0 2) (sourceB1400 + difference 2 0) sourceC1400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1911) := by
    have ha : (tripleCharges (sourceA1400 + difference 0 2) (sourceB1400 + difference 2 0) sourceC1400) = raw21949 := by
      apply Matrix.ext; unfold tripleCharges sourceA1400 sourceB1400 sourceC1400 difference raw21949; decide +kernel
    rw [ha]
    exact (canonical21949 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1400 + difference 0 3) (sourceB1400 + difference 3 0) sourceC1400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (tripleCharges (sourceA1400 + difference 0 3) (sourceB1400 + difference 3 0) sourceC1400) = raw21950 := by
      apply Matrix.ext; unfold tripleCharges sourceA1400 sourceB1400 sourceC1400 difference raw21950; decide +kernel
    rw [ha]
    exact (canonical21950 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1400 + difference 0 4) (sourceB1400 + difference 4 0) sourceC1400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2056) := by
    have ha : (tripleCharges (sourceA1400 + difference 0 4) (sourceB1400 + difference 4 0) sourceC1400) = raw21951 := by
      apply Matrix.ext; unfold tripleCharges sourceA1400 sourceB1400 sourceC1400 difference raw21951; decide +kernel
    rw [ha]
    exact (canonical21951 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1400 + difference 0 5) (sourceB1400 + difference 5 0) sourceC1400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2060) := by
    have ha : (tripleCharges (sourceA1400 + difference 0 5) (sourceB1400 + difference 5 0) sourceC1400) = raw21952 := by
      apply Matrix.ext; unfold tripleCharges sourceA1400 sourceB1400 sourceC1400 difference raw21952; decide +kernel
    rw [ha]
    exact (canonical21952 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1400 + difference 1 0) (sourceB1400 + difference 0 1) sourceC1400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1489) := by
    have ha : (tripleCharges (sourceA1400 + difference 1 0) (sourceB1400 + difference 0 1) sourceC1400) = raw21953 := by
      apply Matrix.ext; unfold tripleCharges sourceA1400 sourceB1400 sourceC1400 difference raw21953; decide +kernel
    rw [ha]
    exact (canonical21953 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1400 + difference 1 2) (sourceB1400 + difference 2 1) sourceC1400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1586) := by
    have ha : (tripleCharges (sourceA1400 + difference 1 2) (sourceB1400 + difference 2 1) sourceC1400) = raw21954 := by
      apply Matrix.ext; unfold tripleCharges sourceA1400 sourceB1400 sourceC1400 difference raw21954; decide +kernel
    rw [ha]
    exact (canonical21954 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1400 + difference 1 3) (sourceB1400 + difference 3 1) sourceC1400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1557) := by
    have ha : (tripleCharges (sourceA1400 + difference 1 3) (sourceB1400 + difference 3 1) sourceC1400) = raw21955 := by
      apply Matrix.ext; unfold tripleCharges sourceA1400 sourceB1400 sourceC1400 difference raw21955; decide +kernel
    rw [ha]
    exact (canonical21955 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1400 + difference 1 4) (sourceB1400 + difference 4 1) sourceC1400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1599) := by
    have ha : (tripleCharges (sourceA1400 + difference 1 4) (sourceB1400 + difference 4 1) sourceC1400) = raw21956 := by
      apply Matrix.ext; unfold tripleCharges sourceA1400 sourceB1400 sourceC1400 difference raw21956; decide +kernel
    rw [ha]
    exact (canonical21956 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1400 + difference 1 5) (sourceB1400 + difference 5 1) sourceC1400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1602) := by
    have ha : (tripleCharges (sourceA1400 + difference 1 5) (sourceB1400 + difference 5 1) sourceC1400) = raw21957 := by
      apply Matrix.ext; unfold tripleCharges sourceA1400 sourceB1400 sourceC1400 difference raw21957; decide +kernel
    rw [ha]
    exact (canonical21957 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1400 + difference 2 0) (sourceB1400 + difference 0 2) sourceC1400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1489) := by
    have ha : (tripleCharges (sourceA1400 + difference 2 0) (sourceB1400 + difference 0 2) sourceC1400) = raw21958 := by
      apply Matrix.ext; unfold tripleCharges sourceA1400 sourceB1400 sourceC1400 difference raw21958; decide +kernel
    rw [ha]
    exact (canonical21958 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1400 + difference 2 1) (sourceB1400 + difference 1 2) sourceC1400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1586) := by
    have ha : (tripleCharges (sourceA1400 + difference 2 1) (sourceB1400 + difference 1 2) sourceC1400) = raw21959 := by
      apply Matrix.ext; unfold tripleCharges sourceA1400 sourceB1400 sourceC1400 difference raw21959; decide +kernel
    rw [ha]
    exact (canonical21959 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1400 + difference 2 3) (sourceB1400 + difference 3 2) sourceC1400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1557) := by
    have ha : (tripleCharges (sourceA1400 + difference 2 3) (sourceB1400 + difference 3 2) sourceC1400) = raw21960 := by
      apply Matrix.ext; unfold tripleCharges sourceA1400 sourceB1400 sourceC1400 difference raw21960; decide +kernel
    rw [ha]
    exact (canonical21960 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1400 + difference 2 4) (sourceB1400 + difference 4 2) sourceC1400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1599) := by
    have ha : (tripleCharges (sourceA1400 + difference 2 4) (sourceB1400 + difference 4 2) sourceC1400) = raw21961 := by
      apply Matrix.ext; unfold tripleCharges sourceA1400 sourceB1400 sourceC1400 difference raw21961; decide +kernel
    rw [ha]
    exact (canonical21961 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1400 + difference 2 5) (sourceB1400 + difference 5 2) sourceC1400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1602) := by
    have ha : (tripleCharges (sourceA1400 + difference 2 5) (sourceB1400 + difference 5 2) sourceC1400) = raw21962 := by
      apply Matrix.ext; unfold tripleCharges sourceA1400 sourceB1400 sourceC1400 difference raw21962; decide +kernel
    rw [ha]
    exact (canonical21962 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1400 + difference 3 0) (sourceB1400 + difference 0 3) sourceC1400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1499) := by
    have ha : (tripleCharges (sourceA1400 + difference 3 0) (sourceB1400 + difference 0 3) sourceC1400) = raw21963 := by
      apply Matrix.ext; unfold tripleCharges sourceA1400 sourceB1400 sourceC1400 difference raw21963; decide +kernel
    rw [ha]
    exact (canonical21963 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1400 + difference 3 1) (sourceB1400 + difference 1 3) sourceC1400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1633) := by
    have ha : (tripleCharges (sourceA1400 + difference 3 1) (sourceB1400 + difference 1 3) sourceC1400) = raw21964 := by
      apply Matrix.ext; unfold tripleCharges sourceA1400 sourceB1400 sourceC1400 difference raw21964; decide +kernel
    rw [ha]
    exact (canonical21964 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1400 + difference 3 2) (sourceB1400 + difference 2 3) sourceC1400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1633) := by
    have ha : (tripleCharges (sourceA1400 + difference 3 2) (sourceB1400 + difference 2 3) sourceC1400) = raw21965 := by
      apply Matrix.ext; unfold tripleCharges sourceA1400 sourceB1400 sourceC1400 difference raw21965; decide +kernel
    rw [ha]
    exact (canonical21965 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1400 + difference 3 4) (sourceB1400 + difference 4 3) sourceC1400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1647) := by
    have ha : (tripleCharges (sourceA1400 + difference 3 4) (sourceB1400 + difference 4 3) sourceC1400) = raw21966 := by
      apply Matrix.ext; unfold tripleCharges sourceA1400 sourceB1400 sourceC1400 difference raw21966; decide +kernel
    rw [ha]
    exact (canonical21966 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1400 + difference 3 5) (sourceB1400 + difference 5 3) sourceC1400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1650) := by
    have ha : (tripleCharges (sourceA1400 + difference 3 5) (sourceB1400 + difference 5 3) sourceC1400) = raw21967 := by
      apply Matrix.ext; unfold tripleCharges sourceA1400 sourceB1400 sourceC1400 difference raw21967; decide +kernel
    rw [ha]
    exact (canonical21967 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1400 + difference 4 0) (sourceB1400 + difference 0 4) sourceC1400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1495) := by
    have ha : (tripleCharges (sourceA1400 + difference 4 0) (sourceB1400 + difference 0 4) sourceC1400) = raw21968 := by
      apply Matrix.ext; unfold tripleCharges sourceA1400 sourceB1400 sourceC1400 difference raw21968; decide +kernel
    rw [ha]
    exact (canonical21968 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1400 + difference 4 1) (sourceB1400 + difference 1 4) sourceC1400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1590) := by
    have ha : (tripleCharges (sourceA1400 + difference 4 1) (sourceB1400 + difference 1 4) sourceC1400) = raw21969 := by
      apply Matrix.ext; unfold tripleCharges sourceA1400 sourceB1400 sourceC1400 difference raw21969; decide +kernel
    rw [ha]
    exact (canonical21969 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1400 + difference 4 2) (sourceB1400 + difference 2 4) sourceC1400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1590) := by
    have ha : (tripleCharges (sourceA1400 + difference 4 2) (sourceB1400 + difference 2 4) sourceC1400) = raw21970 := by
      apply Matrix.ext; unfold tripleCharges sourceA1400 sourceB1400 sourceC1400 difference raw21970; decide +kernel
    rw [ha]
    exact (canonical21970 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1400 + difference 4 3) (sourceB1400 + difference 3 4) sourceC1400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1576) := by
    have ha : (tripleCharges (sourceA1400 + difference 4 3) (sourceB1400 + difference 3 4) sourceC1400) = raw21971 := by
      apply Matrix.ext; unfold tripleCharges sourceA1400 sourceB1400 sourceC1400 difference raw21971; decide +kernel
    rw [ha]
    exact (canonical21971 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1400 + difference 4 5) (sourceB1400 + difference 5 4) sourceC1400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1627) := by
    have ha : (tripleCharges (sourceA1400 + difference 4 5) (sourceB1400 + difference 5 4) sourceC1400) = raw21972 := by
      apply Matrix.ext; unfold tripleCharges sourceA1400 sourceB1400 sourceC1400 difference raw21972; decide +kernel
    rw [ha]
    exact (canonical21972 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1400 + difference 5 0) (sourceB1400 + difference 0 5) sourceC1400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1494) := by
    have ha : (tripleCharges (sourceA1400 + difference 5 0) (sourceB1400 + difference 0 5) sourceC1400) = raw21973 := by
      apply Matrix.ext; unfold tripleCharges sourceA1400 sourceB1400 sourceC1400 difference raw21973; decide +kernel
    rw [ha]
    exact (canonical21973 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1400 + difference 5 1) (sourceB1400 + difference 1 5) sourceC1400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1555) := by
    have ha : (tripleCharges (sourceA1400 + difference 5 1) (sourceB1400 + difference 1 5) sourceC1400) = raw21974 := by
      apply Matrix.ext; unfold tripleCharges sourceA1400 sourceB1400 sourceC1400 difference raw21974; decide +kernel
    rw [ha]
    exact (canonical21974 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1400 + difference 5 2) (sourceB1400 + difference 2 5) sourceC1400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1555) := by
    have ha : (tripleCharges (sourceA1400 + difference 5 2) (sourceB1400 + difference 2 5) sourceC1400) = raw21975 := by
      apply Matrix.ext; unfold tripleCharges sourceA1400 sourceB1400 sourceC1400 difference raw21975; decide +kernel
    rw [ha]
    exact (canonical21975 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1400 + difference 5 3) (sourceB1400 + difference 3 5) sourceC1400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1574) := by
    have ha : (tripleCharges (sourceA1400 + difference 5 3) (sourceB1400 + difference 3 5) sourceC1400) = raw21976 := by
      apply Matrix.ext; unfold tripleCharges sourceA1400 sourceB1400 sourceC1400 difference raw21976; decide +kernel
    rw [ha]
    exact (canonical21976 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1400 + difference 5 4) (sourceB1400 + difference 4 5) sourceC1400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1620) := by
    have ha : (tripleCharges (sourceA1400 + difference 5 4) (sourceB1400 + difference 4 5) sourceC1400) = raw21977 := by
      apply Matrix.ext; unfold tripleCharges sourceA1400 sourceB1400 sourceC1400 difference raw21977; decide +kernel
    rw [ha]
    exact (canonical21977 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1400 sourceB1400 sourceC1400
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1400, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1401 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1401 : Charge := ![1, 0, 0, -1, 0, 0]
def sourceC1401 : Charge := ![3, 0, 0, 1, -1, -3]
def sourceForm1401 : Integer.Sparse Master := [(Sum.inr 867, 1), (Sum.inr 898, 1), (Sum.inr 902, 1), (Sum.inr 916, 1), (Sum.inr 1007, 1), (Sum.inr 1911, 1), (Sum.inr 4081, -1)]

theorem sourceEq1401 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1401 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1401 + difference 0 1) (sourceB1401 + difference 1 0) sourceC1401) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1911) := by
    have ha : (tripleCharges (sourceA1401 + difference 0 1) (sourceB1401 + difference 1 0) sourceC1401) = raw21978 := by
      apply Matrix.ext; unfold tripleCharges sourceA1401 sourceB1401 sourceC1401 difference raw21978; decide +kernel
    rw [ha]
    exact (canonical21978 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1401 + difference 1 1) (sourceB1401 + difference 1 1) sourceC1401) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1007) := by
    have ha : (tripleCharges (sourceA1401 + difference 1 1) (sourceB1401 + difference 1 1) sourceC1401) = raw21979 := by
      apply Matrix.ext; unfold tripleCharges sourceA1401 sourceB1401 sourceC1401 difference raw21979; decide +kernel
    rw [ha]
    exact (canonical21979 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1401 + difference 2 1) (sourceB1401 + difference 1 2) sourceC1401) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 898) := by
    have ha : (tripleCharges (sourceA1401 + difference 2 1) (sourceB1401 + difference 1 2) sourceC1401) = raw21980 := by
      apply Matrix.ext; unfold tripleCharges sourceA1401 sourceB1401 sourceC1401 difference raw21980; decide +kernel
    rw [ha]
    exact (canonical21980 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1401 + difference 3 1) (sourceB1401 + difference 1 3) sourceC1401) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 916) := by
    have ha : (tripleCharges (sourceA1401 + difference 3 1) (sourceB1401 + difference 1 3) sourceC1401) = raw21981 := by
      apply Matrix.ext; unfold tripleCharges sourceA1401 sourceB1401 sourceC1401 difference raw21981; decide +kernel
    rw [ha]
    exact (canonical21981 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1401 + difference 4 1) (sourceB1401 + difference 1 4) sourceC1401) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 902) := by
    have ha : (tripleCharges (sourceA1401 + difference 4 1) (sourceB1401 + difference 1 4) sourceC1401) = raw21982 := by
      apply Matrix.ext; unfold tripleCharges sourceA1401 sourceB1401 sourceC1401 difference raw21982; decide +kernel
    rw [ha]
    exact (canonical21982 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1401 + difference 5 1) (sourceB1401 + difference 1 5) sourceC1401) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 867) := by
    have ha : (tripleCharges (sourceA1401 + difference 5 1) (sourceB1401 + difference 1 5) sourceC1401) = raw21983 := by
      apply Matrix.ext; unfold tripleCharges sourceA1401 sourceB1401 sourceC1401 difference raw21983; decide +kernel
    rw [ha]
    exact (canonical21983 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1401 + sourceB1401) sourceC1401) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1401 + sourceB1401) sourceC1401) = raw21984 := by
      apply Matrix.ext; unfold doubleCharges sourceA1401 sourceB1401 sourceC1401 raw21984; decide +kernel
    rw [ha]
    exact (canonical21984 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1401 sourceB1401 sourceC1401
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1401, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1402 : Charge := ![1, 0, 0, -1, 0, 0]
def sourceB1402 : Charge := ![3, 0, 0, 1, -1, -3]
def sourceC1402 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1402 : Integer.Sparse Master := [(Sum.inr 4070, 1), (Sum.inr 4211, 2), (Sum.inr 4222, 1), (Sum.inr 4227, 1), (Sum.inr 4299, 2), (Sum.inr 4316, 1), (Sum.inr 4377, 2), (Sum.inr 4382, 1), (Sum.inr 4384, 2), (Sum.inr 4388, 2), (Sum.inr 4398, 2), (Sum.inr 4401, 2), (Sum.inr 4421, 1), (Sum.inr 4426, 2), (Sum.inr 4428, 1), (Sum.inr 4501, 1), (Sum.inr 4505, 1), (Sum.inr 4572, 1), (Sum.inr 4583, 2), (Sum.inr 4605, 1), (Sum.inr 4608, 1)]

theorem sourceEq1402 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1402 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1402 + difference 0 1) (sourceB1402 + difference 1 0) sourceC1402) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4583) := by
    have ha : (tripleCharges (sourceA1402 + difference 0 1) (sourceB1402 + difference 1 0) sourceC1402) = raw20809 := by
      apply Matrix.ext; unfold tripleCharges sourceA1402 sourceB1402 sourceC1402 difference raw20809; decide +kernel
    rw [ha]
    exact (canonical20809 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1402 + difference 0 2) (sourceB1402 + difference 2 0) sourceC1402) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4583) := by
    have ha : (tripleCharges (sourceA1402 + difference 0 2) (sourceB1402 + difference 2 0) sourceC1402) = raw20810 := by
      apply Matrix.ext; unfold tripleCharges sourceA1402 sourceB1402 sourceC1402 difference raw20810; decide +kernel
    rw [ha]
    exact (canonical20810 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1402 + difference 0 3) (sourceB1402 + difference 3 0) sourceC1402) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4572) := by
    have ha : (tripleCharges (sourceA1402 + difference 0 3) (sourceB1402 + difference 3 0) sourceC1402) = raw20811 := by
      apply Matrix.ext; unfold tripleCharges sourceA1402 sourceB1402 sourceC1402 difference raw20811; decide +kernel
    rw [ha]
    exact (canonical20811 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1402 + difference 0 4) (sourceB1402 + difference 4 0) sourceC1402) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4605) := by
    have ha : (tripleCharges (sourceA1402 + difference 0 4) (sourceB1402 + difference 4 0) sourceC1402) = raw20442 := by
      apply Matrix.ext; unfold tripleCharges sourceA1402 sourceB1402 sourceC1402 difference raw20442; decide +kernel
    rw [ha]
    exact (canonical20442 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1402 + difference 0 5) (sourceB1402 + difference 5 0) sourceC1402) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4608) := by
    have ha : (tripleCharges (sourceA1402 + difference 0 5) (sourceB1402 + difference 5 0) sourceC1402) = raw20437 := by
      apply Matrix.ext; unfold tripleCharges sourceA1402 sourceB1402 sourceC1402 difference raw20437; decide +kernel
    rw [ha]
    exact (canonical20437 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1402 + difference 1 0) (sourceB1402 + difference 0 1) sourceC1402) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4211) := by
    have ha : (tripleCharges (sourceA1402 + difference 1 0) (sourceB1402 + difference 0 1) sourceC1402) = raw21985 := by
      apply Matrix.ext; unfold tripleCharges sourceA1402 sourceB1402 sourceC1402 difference raw21985; decide +kernel
    rw [ha]
    exact (canonical21985 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1402 + difference 1 2) (sourceB1402 + difference 2 1) sourceC1402) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4384) := by
    have ha : (tripleCharges (sourceA1402 + difference 1 2) (sourceB1402 + difference 2 1) sourceC1402) = raw21986 := by
      apply Matrix.ext; unfold tripleCharges sourceA1402 sourceB1402 sourceC1402 difference raw21986; decide +kernel
    rw [ha]
    exact (canonical21986 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1402 + difference 1 3) (sourceB1402 + difference 3 1) sourceC1402) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4377) := by
    have ha : (tripleCharges (sourceA1402 + difference 1 3) (sourceB1402 + difference 3 1) sourceC1402) = raw21987 := by
      apply Matrix.ext; unfold tripleCharges sourceA1402 sourceB1402 sourceC1402 difference raw21987; decide +kernel
    rw [ha]
    exact (canonical21987 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1402 + difference 1 4) (sourceB1402 + difference 4 1) sourceC1402) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4398) := by
    have ha : (tripleCharges (sourceA1402 + difference 1 4) (sourceB1402 + difference 4 1) sourceC1402) = raw20967 := by
      apply Matrix.ext; unfold tripleCharges sourceA1402 sourceB1402 sourceC1402 difference raw20967; decide +kernel
    rw [ha]
    exact (canonical20967 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1402 + difference 1 5) (sourceB1402 + difference 5 1) sourceC1402) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4401) := by
    have ha : (tripleCharges (sourceA1402 + difference 1 5) (sourceB1402 + difference 5 1) sourceC1402) = raw20795 := by
      apply Matrix.ext; unfold tripleCharges sourceA1402 sourceB1402 sourceC1402 difference raw20795; decide +kernel
    rw [ha]
    exact (canonical20795 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1402 + difference 2 0) (sourceB1402 + difference 0 2) sourceC1402) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4211) := by
    have ha : (tripleCharges (sourceA1402 + difference 2 0) (sourceB1402 + difference 0 2) sourceC1402) = raw21988 := by
      apply Matrix.ext; unfold tripleCharges sourceA1402 sourceB1402 sourceC1402 difference raw21988; decide +kernel
    rw [ha]
    exact (canonical21988 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1402 + difference 2 1) (sourceB1402 + difference 1 2) sourceC1402) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4384) := by
    have ha : (tripleCharges (sourceA1402 + difference 2 1) (sourceB1402 + difference 1 2) sourceC1402) = raw21989 := by
      apply Matrix.ext; unfold tripleCharges sourceA1402 sourceB1402 sourceC1402 difference raw21989; decide +kernel
    rw [ha]
    exact (canonical21989 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1402 + difference 2 3) (sourceB1402 + difference 3 2) sourceC1402) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4377) := by
    have ha : (tripleCharges (sourceA1402 + difference 2 3) (sourceB1402 + difference 3 2) sourceC1402) = raw21990 := by
      apply Matrix.ext; unfold tripleCharges sourceA1402 sourceB1402 sourceC1402 difference raw21990; decide +kernel
    rw [ha]
    exact (canonical21990 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1402 + difference 2 4) (sourceB1402 + difference 4 2) sourceC1402) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4398) := by
    have ha : (tripleCharges (sourceA1402 + difference 2 4) (sourceB1402 + difference 4 2) sourceC1402) = raw20970 := by
      apply Matrix.ext; unfold tripleCharges sourceA1402 sourceB1402 sourceC1402 difference raw20970; decide +kernel
    rw [ha]
    exact (canonical20970 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1402 + difference 2 5) (sourceB1402 + difference 5 2) sourceC1402) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4401) := by
    have ha : (tripleCharges (sourceA1402 + difference 2 5) (sourceB1402 + difference 5 2) sourceC1402) = raw20799 := by
      apply Matrix.ext; unfold tripleCharges sourceA1402 sourceB1402 sourceC1402 difference raw20799; decide +kernel
    rw [ha]
    exact (canonical20799 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1402 + difference 3 0) (sourceB1402 + difference 0 3) sourceC1402) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (tripleCharges (sourceA1402 + difference 3 0) (sourceB1402 + difference 0 3) sourceC1402) = raw21991 := by
      apply Matrix.ext; unfold tripleCharges sourceA1402 sourceB1402 sourceC1402 difference raw21991; decide +kernel
    rw [ha]
    exact (canonical21991 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1402 + difference 3 1) (sourceB1402 + difference 1 3) sourceC1402) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4426) := by
    have ha : (tripleCharges (sourceA1402 + difference 3 1) (sourceB1402 + difference 1 3) sourceC1402) = raw21992 := by
      apply Matrix.ext; unfold tripleCharges sourceA1402 sourceB1402 sourceC1402 difference raw21992; decide +kernel
    rw [ha]
    exact (canonical21992 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1402 + difference 3 2) (sourceB1402 + difference 2 3) sourceC1402) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4426) := by
    have ha : (tripleCharges (sourceA1402 + difference 3 2) (sourceB1402 + difference 2 3) sourceC1402) = raw21993 := by
      apply Matrix.ext; unfold tripleCharges sourceA1402 sourceB1402 sourceC1402 difference raw21993; decide +kernel
    rw [ha]
    exact (canonical21993 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1402 + difference 3 4) (sourceB1402 + difference 4 3) sourceC1402) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4501) := by
    have ha : (tripleCharges (sourceA1402 + difference 3 4) (sourceB1402 + difference 4 3) sourceC1402) = raw20439 := by
      apply Matrix.ext; unfold tripleCharges sourceA1402 sourceB1402 sourceC1402 difference raw20439; decide +kernel
    rw [ha]
    exact (canonical20439 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1402 + difference 3 5) (sourceB1402 + difference 5 3) sourceC1402) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4505) := by
    have ha : (tripleCharges (sourceA1402 + difference 3 5) (sourceB1402 + difference 5 3) sourceC1402) = raw20434 := by
      apply Matrix.ext; unfold tripleCharges sourceA1402 sourceB1402 sourceC1402 difference raw20434; decide +kernel
    rw [ha]
    exact (canonical20434 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1402 + difference 4 0) (sourceB1402 + difference 0 4) sourceC1402) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4227) := by
    have ha : (tripleCharges (sourceA1402 + difference 4 0) (sourceB1402 + difference 0 4) sourceC1402) = raw21994 := by
      apply Matrix.ext; unfold tripleCharges sourceA1402 sourceB1402 sourceC1402 difference raw21994; decide +kernel
    rw [ha]
    exact (canonical21994 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1402 + difference 4 1) (sourceB1402 + difference 1 4) sourceC1402) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4388) := by
    have ha : (tripleCharges (sourceA1402 + difference 4 1) (sourceB1402 + difference 1 4) sourceC1402) = raw21995 := by
      apply Matrix.ext; unfold tripleCharges sourceA1402 sourceB1402 sourceC1402 difference raw21995; decide +kernel
    rw [ha]
    exact (canonical21995 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1402 + difference 4 2) (sourceB1402 + difference 2 4) sourceC1402) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4388) := by
    have ha : (tripleCharges (sourceA1402 + difference 4 2) (sourceB1402 + difference 2 4) sourceC1402) = raw21996 := by
      apply Matrix.ext; unfold tripleCharges sourceA1402 sourceB1402 sourceC1402 difference raw21996; decide +kernel
    rw [ha]
    exact (canonical21996 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1402 + difference 4 3) (sourceB1402 + difference 3 4) sourceC1402) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4382) := by
    have ha : (tripleCharges (sourceA1402 + difference 4 3) (sourceB1402 + difference 3 4) sourceC1402) = raw21997 := by
      apply Matrix.ext; unfold tripleCharges sourceA1402 sourceB1402 sourceC1402 difference raw21997; decide +kernel
    rw [ha]
    exact (canonical21997 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1402 + difference 4 5) (sourceB1402 + difference 5 4) sourceC1402) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4428) := by
    have ha : (tripleCharges (sourceA1402 + difference 4 5) (sourceB1402 + difference 5 4) sourceC1402) = raw20803 := by
      apply Matrix.ext; unfold tripleCharges sourceA1402 sourceB1402 sourceC1402 difference raw20803; decide +kernel
    rw [ha]
    exact (canonical20803 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1402 + difference 5 0) (sourceB1402 + difference 0 5) sourceC1402) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4222) := by
    have ha : (tripleCharges (sourceA1402 + difference 5 0) (sourceB1402 + difference 0 5) sourceC1402) = raw21998 := by
      apply Matrix.ext; unfold tripleCharges sourceA1402 sourceB1402 sourceC1402 difference raw21998; decide +kernel
    rw [ha]
    exact (canonical21998 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1402 + difference 5 1) (sourceB1402 + difference 1 5) sourceC1402) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4299) := by
    have ha : (tripleCharges (sourceA1402 + difference 5 1) (sourceB1402 + difference 1 5) sourceC1402) = raw21999 := by
      apply Matrix.ext; unfold tripleCharges sourceA1402 sourceB1402 sourceC1402 difference raw21999; decide +kernel
    rw [ha]
    exact (canonical21999 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1402 + difference 5 2) (sourceB1402 + difference 2 5) sourceC1402) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4299) := by
    have ha : (tripleCharges (sourceA1402 + difference 5 2) (sourceB1402 + difference 2 5) sourceC1402) = raw22000 := by
      apply Matrix.ext; unfold tripleCharges sourceA1402 sourceB1402 sourceC1402 difference raw22000; decide +kernel
    rw [ha]
    exact (canonical22000 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1402 + difference 5 3) (sourceB1402 + difference 3 5) sourceC1402) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4316) := by
    have ha : (tripleCharges (sourceA1402 + difference 5 3) (sourceB1402 + difference 3 5) sourceC1402) = raw22001 := by
      apply Matrix.ext; unfold tripleCharges sourceA1402 sourceB1402 sourceC1402 difference raw22001; decide +kernel
    rw [ha]
    exact (canonical22001 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1402 + difference 5 4) (sourceB1402 + difference 4 5) sourceC1402) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4421) := by
    have ha : (tripleCharges (sourceA1402 + difference 5 4) (sourceB1402 + difference 4 5) sourceC1402) = raw20973 := by
      apply Matrix.ext; unfold tripleCharges sourceA1402 sourceB1402 sourceC1402 difference raw20973; decide +kernel
    rw [ha]
    exact (canonical20973 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1402 sourceB1402 sourceC1402
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1402, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1403 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1403 : Charge := ![0, 2, 1, 0, 0, -3]
def sourceC1403 : Charge := ![4, -2, -1, 0, -1, 0]
def sourceForm1403 : Integer.Sparse Master := [(Sum.inr 793, 1), (Sum.inr 795, 1), (Sum.inr 796, 1), (Sum.inr 811, 1), (Sum.inr 827, 1), (Sum.inr 1715, 1), (Sum.inr 4069, -1)]

theorem sourceEq1403 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1403 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1403 + difference 0 5) (sourceB1403 + difference 5 0) sourceC1403) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1715) := by
    have ha : (tripleCharges (sourceA1403 + difference 0 5) (sourceB1403 + difference 5 0) sourceC1403) = raw22002 := by
      apply Matrix.ext; unfold tripleCharges sourceA1403 sourceB1403 sourceC1403 difference raw22002; decide +kernel
    rw [ha]
    exact (canonical22002 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1403 + difference 1 5) (sourceB1403 + difference 5 1) sourceC1403) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 811) := by
    have ha : (tripleCharges (sourceA1403 + difference 1 5) (sourceB1403 + difference 5 1) sourceC1403) = raw22003 := by
      apply Matrix.ext; unfold tripleCharges sourceA1403 sourceB1403 sourceC1403 difference raw22003; decide +kernel
    rw [ha]
    exact (canonical22003 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1403 + difference 2 5) (sourceB1403 + difference 5 2) sourceC1403) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 827) := by
    have ha : (tripleCharges (sourceA1403 + difference 2 5) (sourceB1403 + difference 5 2) sourceC1403) = raw22004 := by
      apply Matrix.ext; unfold tripleCharges sourceA1403 sourceB1403 sourceC1403 difference raw22004; decide +kernel
    rw [ha]
    exact (canonical22004 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1403 + difference 3 5) (sourceB1403 + difference 5 3) sourceC1403) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 793) := by
    have ha : (tripleCharges (sourceA1403 + difference 3 5) (sourceB1403 + difference 5 3) sourceC1403) = raw22005 := by
      apply Matrix.ext; unfold tripleCharges sourceA1403 sourceB1403 sourceC1403 difference raw22005; decide +kernel
    rw [ha]
    exact (canonical22005 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1403 + difference 4 5) (sourceB1403 + difference 5 4) sourceC1403) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 796) := by
    have ha : (tripleCharges (sourceA1403 + difference 4 5) (sourceB1403 + difference 5 4) sourceC1403) = raw22006 := by
      apply Matrix.ext; unfold tripleCharges sourceA1403 sourceB1403 sourceC1403 difference raw22006; decide +kernel
    rw [ha]
    exact (canonical22006 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1403 + difference 5 5) (sourceB1403 + difference 5 5) sourceC1403) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 795) := by
    have ha : (tripleCharges (sourceA1403 + difference 5 5) (sourceB1403 + difference 5 5) sourceC1403) = raw22007 := by
      apply Matrix.ext; unfold tripleCharges sourceA1403 sourceB1403 sourceC1403 difference raw22007; decide +kernel
    rw [ha]
    exact (canonical22007 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1403 + sourceB1403) sourceC1403) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1403 + sourceB1403) sourceC1403) = raw22008 := by
      apply Matrix.ext; unfold doubleCharges sourceA1403 sourceB1403 sourceC1403 raw22008; decide +kernel
    rw [ha]
    exact (canonical22008 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1403 sourceB1403 sourceC1403
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1403, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1404 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1404 : Charge := ![0, 2, 1, 0, -1, -2]
def sourceC1404 : Charge := ![4, -2, -1, 0, 0, -1]
def sourceForm1404 : Integer.Sparse Master := [(Sum.inr 792, 1), (Sum.inr 794, 1), (Sum.inr 796, 1), (Sum.inr 807, 1), (Sum.inr 824, 1), (Sum.inr 1714, 1), (Sum.inr 4069, -1)]

theorem sourceEq1404 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1404 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1404 + difference 0 5) (sourceB1404 + difference 5 0) sourceC1404) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1714) := by
    have ha : (tripleCharges (sourceA1404 + difference 0 5) (sourceB1404 + difference 5 0) sourceC1404) = raw22009 := by
      apply Matrix.ext; unfold tripleCharges sourceA1404 sourceB1404 sourceC1404 difference raw22009; decide +kernel
    rw [ha]
    exact (canonical22009 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1404 + difference 1 5) (sourceB1404 + difference 5 1) sourceC1404) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 807) := by
    have ha : (tripleCharges (sourceA1404 + difference 1 5) (sourceB1404 + difference 5 1) sourceC1404) = raw22010 := by
      apply Matrix.ext; unfold tripleCharges sourceA1404 sourceB1404 sourceC1404 difference raw22010; decide +kernel
    rw [ha]
    exact (canonical22010 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1404 + difference 2 5) (sourceB1404 + difference 5 2) sourceC1404) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 824) := by
    have ha : (tripleCharges (sourceA1404 + difference 2 5) (sourceB1404 + difference 5 2) sourceC1404) = raw22011 := by
      apply Matrix.ext; unfold tripleCharges sourceA1404 sourceB1404 sourceC1404 difference raw22011; decide +kernel
    rw [ha]
    exact (canonical22011 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1404 + difference 3 5) (sourceB1404 + difference 5 3) sourceC1404) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 792) := by
    have ha : (tripleCharges (sourceA1404 + difference 3 5) (sourceB1404 + difference 5 3) sourceC1404) = raw22012 := by
      apply Matrix.ext; unfold tripleCharges sourceA1404 sourceB1404 sourceC1404 difference raw22012; decide +kernel
    rw [ha]
    exact (canonical22012 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1404 + difference 4 5) (sourceB1404 + difference 5 4) sourceC1404) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 796) := by
    have ha : (tripleCharges (sourceA1404 + difference 4 5) (sourceB1404 + difference 5 4) sourceC1404) = raw22013 := by
      apply Matrix.ext; unfold tripleCharges sourceA1404 sourceB1404 sourceC1404 difference raw22013; decide +kernel
    rw [ha]
    exact (canonical22013 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1404 + difference 5 5) (sourceB1404 + difference 5 5) sourceC1404) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 794) := by
    have ha : (tripleCharges (sourceA1404 + difference 5 5) (sourceB1404 + difference 5 5) sourceC1404) = raw22014 := by
      apply Matrix.ext; unfold tripleCharges sourceA1404 sourceB1404 sourceC1404 difference raw22014; decide +kernel
    rw [ha]
    exact (canonical22014 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1404 + sourceB1404) sourceC1404) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1404 + sourceB1404) sourceC1404) = raw22015 := by
      apply Matrix.ext; unfold doubleCharges sourceA1404 sourceB1404 sourceC1404 raw22015; decide +kernel
    rw [ha]
    exact (canonical22015 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1404 sourceB1404 sourceC1404
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1404, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1405 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1405 : Charge := ![0, 2, 0, 0, 1, -3]
def sourceC1405 : Charge := ![4, -2, 0, 0, -2, 0]
def sourceForm1405 : Integer.Sparse Master := [(Sum.inr 825, 2), (Sum.inr 829, 1), (Sum.inr 830, 1), (Sum.inr 858, 1), (Sum.inr 1740, 1), (Sum.inr 4071, -1)]

theorem sourceEq1405 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1405 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1405 + difference 0 5) (sourceB1405 + difference 5 0) sourceC1405) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1740) := by
    have ha : (tripleCharges (sourceA1405 + difference 0 5) (sourceB1405 + difference 5 0) sourceC1405) = raw22016 := by
      apply Matrix.ext; unfold tripleCharges sourceA1405 sourceB1405 sourceC1405 difference raw22016; decide +kernel
    rw [ha]
    exact (canonical22016 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1405 + difference 1 5) (sourceB1405 + difference 5 1) sourceC1405) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 858) := by
    have ha : (tripleCharges (sourceA1405 + difference 1 5) (sourceB1405 + difference 5 1) sourceC1405) = raw22017 := by
      apply Matrix.ext; unfold tripleCharges sourceA1405 sourceB1405 sourceC1405 difference raw22017; decide +kernel
    rw [ha]
    exact (canonical22017 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1405 + difference 2 5) (sourceB1405 + difference 5 2) sourceC1405) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 825) := by
    have ha : (tripleCharges (sourceA1405 + difference 2 5) (sourceB1405 + difference 5 2) sourceC1405) = raw22018 := by
      apply Matrix.ext; unfold tripleCharges sourceA1405 sourceB1405 sourceC1405 difference raw22018; decide +kernel
    rw [ha]
    exact (canonical22018 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1405 + difference 3 5) (sourceB1405 + difference 5 3) sourceC1405) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 825) := by
    have ha : (tripleCharges (sourceA1405 + difference 3 5) (sourceB1405 + difference 5 3) sourceC1405) = raw22019 := by
      apply Matrix.ext; unfold tripleCharges sourceA1405 sourceB1405 sourceC1405 difference raw22019; decide +kernel
    rw [ha]
    exact (canonical22019 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1405 + difference 4 5) (sourceB1405 + difference 5 4) sourceC1405) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 830) := by
    have ha : (tripleCharges (sourceA1405 + difference 4 5) (sourceB1405 + difference 5 4) sourceC1405) = raw22020 := by
      apply Matrix.ext; unfold tripleCharges sourceA1405 sourceB1405 sourceC1405 difference raw22020; decide +kernel
    rw [ha]
    exact (canonical22020 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1405 + difference 5 5) (sourceB1405 + difference 5 5) sourceC1405) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 829) := by
    have ha : (tripleCharges (sourceA1405 + difference 5 5) (sourceB1405 + difference 5 5) sourceC1405) = raw22021 := by
      apply Matrix.ext; unfold tripleCharges sourceA1405 sourceB1405 sourceC1405 difference raw22021; decide +kernel
    rw [ha]
    exact (canonical22021 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1405 + sourceB1405) sourceC1405) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (doubleCharges (sourceA1405 + sourceB1405) sourceC1405) = raw22022 := by
      apply Matrix.ext; unfold doubleCharges sourceA1405 sourceB1405 sourceC1405 raw22022; decide +kernel
    rw [ha]
    exact (canonical22022 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1405 sourceB1405 sourceC1405
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1405, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1406 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1406 : Charge := ![0, 2, 0, 0, 0, -2]
def sourceC1406 : Charge := ![4, -2, 0, 0, -1, -1]
def sourceForm1406 : Integer.Sparse Master := [(Sum.inr 828, 1), (Sum.inr 1610, 2), (Sum.inr 1659, 1), (Sum.inr 1716, 1), (Sum.inr 1739, 1), (Sum.inr 4069, -1)]

theorem sourceEq1406 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1406 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1406 + difference 0 0) (sourceB1406 + difference 0 0) sourceC1406) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 828) := by
    have ha : (tripleCharges (sourceA1406 + difference 0 0) (sourceB1406 + difference 0 0) sourceC1406) = raw22023 := by
      apply Matrix.ext; unfold tripleCharges sourceA1406 sourceB1406 sourceC1406 difference raw22023; decide +kernel
    rw [ha]
    exact (canonical22023 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1406 + difference 0 1) (sourceB1406 + difference 1 0) sourceC1406) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1659) := by
    have ha : (tripleCharges (sourceA1406 + difference 0 1) (sourceB1406 + difference 1 0) sourceC1406) = raw22024 := by
      apply Matrix.ext; unfold tripleCharges sourceA1406 sourceB1406 sourceC1406 difference raw22024; decide +kernel
    rw [ha]
    exact (canonical22024 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1406 + difference 0 2) (sourceB1406 + difference 2 0) sourceC1406) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1610) := by
    have ha : (tripleCharges (sourceA1406 + difference 0 2) (sourceB1406 + difference 2 0) sourceC1406) = raw22025 := by
      apply Matrix.ext; unfold tripleCharges sourceA1406 sourceB1406 sourceC1406 difference raw22025; decide +kernel
    rw [ha]
    exact (canonical22025 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1406 + difference 0 3) (sourceB1406 + difference 3 0) sourceC1406) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1610) := by
    have ha : (tripleCharges (sourceA1406 + difference 0 3) (sourceB1406 + difference 3 0) sourceC1406) = raw22026 := by
      apply Matrix.ext; unfold tripleCharges sourceA1406 sourceB1406 sourceC1406 difference raw22026; decide +kernel
    rw [ha]
    exact (canonical22026 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1406 + difference 0 4) (sourceB1406 + difference 4 0) sourceC1406) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1716) := by
    have ha : (tripleCharges (sourceA1406 + difference 0 4) (sourceB1406 + difference 4 0) sourceC1406) = raw22027 := by
      apply Matrix.ext; unfold tripleCharges sourceA1406 sourceB1406 sourceC1406 difference raw22027; decide +kernel
    rw [ha]
    exact (canonical22027 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1406 + difference 0 5) (sourceB1406 + difference 5 0) sourceC1406) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1739) := by
    have ha : (tripleCharges (sourceA1406 + difference 0 5) (sourceB1406 + difference 5 0) sourceC1406) = raw22028 := by
      apply Matrix.ext; unfold tripleCharges sourceA1406 sourceB1406 sourceC1406 difference raw22028; decide +kernel
    rw [ha]
    exact (canonical22028 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1406 + sourceB1406) sourceC1406) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1406 + sourceB1406) sourceC1406) = raw22029 := by
      apply Matrix.ext; unfold doubleCharges sourceA1406 sourceB1406 sourceC1406 raw22029; decide +kernel
    rw [ha]
    exact (canonical22029 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1406 sourceB1406 sourceC1406
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1406, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1407 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1407 : Charge := ![0, 2, 0, 0, 0, -2]
def sourceC1407 : Charge := ![4, -2, 0, 0, -1, -1]
def sourceForm1407 : Integer.Sparse Master := [(Sum.inr 559, 1), (Sum.inr 720, 2), (Sum.inr 813, 1), (Sum.inr 828, 1), (Sum.inr 856, 1), (Sum.inr 4069, -1)]

theorem sourceEq1407 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1407 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1407 + difference 1 0) (sourceB1407 + difference 0 1) sourceC1407) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 559) := by
    have ha : (tripleCharges (sourceA1407 + difference 1 0) (sourceB1407 + difference 0 1) sourceC1407) = raw22030 := by
      apply Matrix.ext; unfold tripleCharges sourceA1407 sourceB1407 sourceC1407 difference raw22030; decide +kernel
    rw [ha]
    exact (canonical22030 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1407 + difference 1 1) (sourceB1407 + difference 1 1) sourceC1407) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 828) := by
    have ha : (tripleCharges (sourceA1407 + difference 1 1) (sourceB1407 + difference 1 1) sourceC1407) = raw22023 := by
      apply Matrix.ext; unfold tripleCharges sourceA1407 sourceB1407 sourceC1407 difference raw22023; decide +kernel
    rw [ha]
    exact (canonical22023 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1407 + difference 1 2) (sourceB1407 + difference 2 1) sourceC1407) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 720) := by
    have ha : (tripleCharges (sourceA1407 + difference 1 2) (sourceB1407 + difference 2 1) sourceC1407) = raw22031 := by
      apply Matrix.ext; unfold tripleCharges sourceA1407 sourceB1407 sourceC1407 difference raw22031; decide +kernel
    rw [ha]
    exact (canonical22031 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1407 + difference 1 3) (sourceB1407 + difference 3 1) sourceC1407) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 720) := by
    have ha : (tripleCharges (sourceA1407 + difference 1 3) (sourceB1407 + difference 3 1) sourceC1407) = raw22032 := by
      apply Matrix.ext; unfold tripleCharges sourceA1407 sourceB1407 sourceC1407 difference raw22032; decide +kernel
    rw [ha]
    exact (canonical22032 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1407 + difference 1 4) (sourceB1407 + difference 4 1) sourceC1407) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 813) := by
    have ha : (tripleCharges (sourceA1407 + difference 1 4) (sourceB1407 + difference 4 1) sourceC1407) = raw22033 := by
      apply Matrix.ext; unfold tripleCharges sourceA1407 sourceB1407 sourceC1407 difference raw22033; decide +kernel
    rw [ha]
    exact (canonical22033 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1407 + difference 1 5) (sourceB1407 + difference 5 1) sourceC1407) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 856) := by
    have ha : (tripleCharges (sourceA1407 + difference 1 5) (sourceB1407 + difference 5 1) sourceC1407) = raw22034 := by
      apply Matrix.ext; unfold tripleCharges sourceA1407 sourceB1407 sourceC1407 difference raw22034; decide +kernel
    rw [ha]
    exact (canonical22034 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1407 + sourceB1407) sourceC1407) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1407 + sourceB1407) sourceC1407) = raw22029 := by
      apply Matrix.ext; unfold doubleCharges sourceA1407 sourceB1407 sourceC1407 raw22029; decide +kernel
    rw [ha]
    exact (canonical22029 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1407 sourceB1407 sourceC1407
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1407, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
