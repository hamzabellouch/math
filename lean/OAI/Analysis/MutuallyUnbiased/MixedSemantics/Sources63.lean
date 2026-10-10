import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical133
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical143
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical153
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical160
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical161
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical162
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical163
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical198
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical215
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical216
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical217
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical218
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical222
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical223
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical224
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical225

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA2016 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2016 : Charge := ![1, 1, 1, 0, -3, 0]
def sourceC2016 : Charge := ![2, 0, -1, 0, 2, -3]
def sourceForm2016 : Integer.Sparse Master := [(Sum.inr 2117, 1), (Sum.inr 2119, 1), (Sum.inr 2122, 1), (Sum.inr 2128, 1), (Sum.inr 2215, 1), (Sum.inr 2681, 1), (Sum.inr 4082, -1)]

theorem sourceEq2016 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2016 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2016 + difference 0 0) (sourceB2016 + difference 0 0) sourceC2016) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2119) := by
    have ha : (tripleCharges (sourceA2016 + difference 0 0) (sourceB2016 + difference 0 0) sourceC2016) = raw28530 := by
      apply Matrix.ext; unfold tripleCharges sourceA2016 sourceB2016 sourceC2016 difference raw28530; decide +kernel
    rw [ha]
    exact (canonical28530 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2016 + difference 0 1) (sourceB2016 + difference 1 0) sourceC2016) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2122) := by
    have ha : (tripleCharges (sourceA2016 + difference 0 1) (sourceB2016 + difference 1 0) sourceC2016) = raw28531 := by
      apply Matrix.ext; unfold tripleCharges sourceA2016 sourceB2016 sourceC2016 difference raw28531; decide +kernel
    rw [ha]
    exact (canonical28531 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2016 + difference 0 2) (sourceB2016 + difference 2 0) sourceC2016) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2128) := by
    have ha : (tripleCharges (sourceA2016 + difference 0 2) (sourceB2016 + difference 2 0) sourceC2016) = raw28532 := by
      apply Matrix.ext; unfold tripleCharges sourceA2016 sourceB2016 sourceC2016 difference raw28532; decide +kernel
    rw [ha]
    exact (canonical28532 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2016 + difference 0 3) (sourceB2016 + difference 3 0) sourceC2016) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2117) := by
    have ha : (tripleCharges (sourceA2016 + difference 0 3) (sourceB2016 + difference 3 0) sourceC2016) = raw28533 := by
      apply Matrix.ext; unfold tripleCharges sourceA2016 sourceB2016 sourceC2016 difference raw28533; decide +kernel
    rw [ha]
    exact (canonical28533 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2016 + difference 0 4) (sourceB2016 + difference 4 0) sourceC2016) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2215) := by
    have ha : (tripleCharges (sourceA2016 + difference 0 4) (sourceB2016 + difference 4 0) sourceC2016) = raw28534 := by
      apply Matrix.ext; unfold tripleCharges sourceA2016 sourceB2016 sourceC2016 difference raw28534; decide +kernel
    rw [ha]
    exact (canonical28534 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2016 + difference 0 5) (sourceB2016 + difference 5 0) sourceC2016) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2681) := by
    have ha : (tripleCharges (sourceA2016 + difference 0 5) (sourceB2016 + difference 5 0) sourceC2016) = raw28535 := by
      apply Matrix.ext; unfold tripleCharges sourceA2016 sourceB2016 sourceC2016 difference raw28535; decide +kernel
    rw [ha]
    exact (canonical28535 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2016 + sourceB2016) sourceC2016) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2016 + sourceB2016) sourceC2016) = raw28536 := by
      apply Matrix.ext; unfold doubleCharges sourceA2016 sourceB2016 sourceC2016 raw28536; decide +kernel
    rw [ha]
    exact (canonical28536 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2016 sourceB2016 sourceC2016
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2016, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2017 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2017 : Charge := ![1, 1, 1, -1, -2, 0]
def sourceC2017 : Charge := ![2, 0, -1, 1, 1, -3]
def sourceForm2017 : Integer.Sparse Master := [(Sum.inr 2070, 1), (Sum.inr 2072, 1), (Sum.inr 2075, 1), (Sum.inr 2085, 1), (Sum.inr 2190, 1), (Sum.inr 3557, 1), (Sum.inr 4080, -1)]

theorem sourceEq2017 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2017 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2017 + difference 0 0) (sourceB2017 + difference 0 0) sourceC2017) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2070) := by
    have ha : (tripleCharges (sourceA2017 + difference 0 0) (sourceB2017 + difference 0 0) sourceC2017) = raw28537 := by
      apply Matrix.ext; unfold tripleCharges sourceA2017 sourceB2017 sourceC2017 difference raw28537; decide +kernel
    rw [ha]
    exact (canonical28537 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2017 + difference 0 1) (sourceB2017 + difference 1 0) sourceC2017) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2072) := by
    have ha : (tripleCharges (sourceA2017 + difference 0 1) (sourceB2017 + difference 1 0) sourceC2017) = raw28538 := by
      apply Matrix.ext; unfold tripleCharges sourceA2017 sourceB2017 sourceC2017 difference raw28538; decide +kernel
    rw [ha]
    exact (canonical28538 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2017 + difference 0 2) (sourceB2017 + difference 2 0) sourceC2017) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2085) := by
    have ha : (tripleCharges (sourceA2017 + difference 0 2) (sourceB2017 + difference 2 0) sourceC2017) = raw28539 := by
      apply Matrix.ext; unfold tripleCharges sourceA2017 sourceB2017 sourceC2017 difference raw28539; decide +kernel
    rw [ha]
    exact (canonical28539 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2017 + difference 0 3) (sourceB2017 + difference 3 0) sourceC2017) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2075) := by
    have ha : (tripleCharges (sourceA2017 + difference 0 3) (sourceB2017 + difference 3 0) sourceC2017) = raw28540 := by
      apply Matrix.ext; unfold tripleCharges sourceA2017 sourceB2017 sourceC2017 difference raw28540; decide +kernel
    rw [ha]
    exact (canonical28540 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2017 + difference 0 4) (sourceB2017 + difference 4 0) sourceC2017) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2190) := by
    have ha : (tripleCharges (sourceA2017 + difference 0 4) (sourceB2017 + difference 4 0) sourceC2017) = raw28541 := by
      apply Matrix.ext; unfold tripleCharges sourceA2017 sourceB2017 sourceC2017 difference raw28541; decide +kernel
    rw [ha]
    exact (canonical28541 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2017 + difference 0 5) (sourceB2017 + difference 5 0) sourceC2017) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3557) := by
    have ha : (tripleCharges (sourceA2017 + difference 0 5) (sourceB2017 + difference 5 0) sourceC2017) = raw28542 := by
      apply Matrix.ext; unfold tripleCharges sourceA2017 sourceB2017 sourceC2017 difference raw28542; decide +kernel
    rw [ha]
    exact (canonical28542 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2017 + sourceB2017) sourceC2017) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA2017 + sourceB2017) sourceC2017) = raw28543 := by
      apply Matrix.ext; unfold doubleCharges sourceA2017 sourceB2017 sourceC2017 raw28543; decide +kernel
    rw [ha]
    exact (canonical28543 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2017 sourceB2017 sourceC2017
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2017, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2018 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2018 : Charge := ![1, 1, 1, -2, 0, -1]
def sourceC2018 : Charge := ![2, 0, -1, 2, -1, -2]
def sourceForm2018 : Integer.Sparse Master := [(Sum.inr 2453, 1), (Sum.inr 2455, 1), (Sum.inr 2459, 1), (Sum.inr 2490, 1), (Sum.inr 2697, 1), (Sum.inr 3795, 1), (Sum.inr 4088, -1)]

theorem sourceEq2018 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2018 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2018 + difference 0 0) (sourceB2018 + difference 0 0) sourceC2018) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2453) := by
    have ha : (tripleCharges (sourceA2018 + difference 0 0) (sourceB2018 + difference 0 0) sourceC2018) = raw28544 := by
      apply Matrix.ext; unfold tripleCharges sourceA2018 sourceB2018 sourceC2018 difference raw28544; decide +kernel
    rw [ha]
    exact (canonical28544 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2018 + difference 0 1) (sourceB2018 + difference 1 0) sourceC2018) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2455) := by
    have ha : (tripleCharges (sourceA2018 + difference 0 1) (sourceB2018 + difference 1 0) sourceC2018) = raw28545 := by
      apply Matrix.ext; unfold tripleCharges sourceA2018 sourceB2018 sourceC2018 difference raw28545; decide +kernel
    rw [ha]
    exact (canonical28545 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2018 + difference 0 2) (sourceB2018 + difference 2 0) sourceC2018) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2490) := by
    have ha : (tripleCharges (sourceA2018 + difference 0 2) (sourceB2018 + difference 2 0) sourceC2018) = raw28546 := by
      apply Matrix.ext; unfold tripleCharges sourceA2018 sourceB2018 sourceC2018 difference raw28546; decide +kernel
    rw [ha]
    exact (canonical28546 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2018 + difference 0 3) (sourceB2018 + difference 3 0) sourceC2018) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2459) := by
    have ha : (tripleCharges (sourceA2018 + difference 0 3) (sourceB2018 + difference 3 0) sourceC2018) = raw28547 := by
      apply Matrix.ext; unfold tripleCharges sourceA2018 sourceB2018 sourceC2018 difference raw28547; decide +kernel
    rw [ha]
    exact (canonical28547 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2018 + difference 0 4) (sourceB2018 + difference 4 0) sourceC2018) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2697) := by
    have ha : (tripleCharges (sourceA2018 + difference 0 4) (sourceB2018 + difference 4 0) sourceC2018) = raw28548 := by
      apply Matrix.ext; unfold tripleCharges sourceA2018 sourceB2018 sourceC2018 difference raw28548; decide +kernel
    rw [ha]
    exact (canonical28548 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2018 + difference 0 5) (sourceB2018 + difference 5 0) sourceC2018) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3795) := by
    have ha : (tripleCharges (sourceA2018 + difference 0 5) (sourceB2018 + difference 5 0) sourceC2018) = raw28549 := by
      apply Matrix.ext; unfold tripleCharges sourceA2018 sourceB2018 sourceC2018 difference raw28549; decide +kernel
    rw [ha]
    exact (canonical28549 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2018 + sourceB2018) sourceC2018) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA2018 + sourceB2018) sourceC2018) = raw28550 := by
      apply Matrix.ext; unfold doubleCharges sourceA2018 sourceB2018 sourceC2018 raw28550; decide +kernel
    rw [ha]
    exact (canonical28550 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2018 sourceB2018 sourceC2018
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2018, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2019 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2019 : Charge := ![1, 1, 1, -2, 0, -1]
def sourceC2019 : Charge := ![2, 0, -1, 2, -1, -2]
def sourceForm2019 : Integer.Sparse Master := [(Sum.inr 2453, 1), (Sum.inr 2533, 1), (Sum.inr 2536, 1), (Sum.inr 2565, 1), (Sum.inr 2672, 1), (Sum.inr 3795, 1), (Sum.inr 4088, -1)]

theorem sourceEq2019 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2019 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2019 + difference 0 5) (sourceB2019 + difference 5 0) sourceC2019) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3795) := by
    have ha : (tripleCharges (sourceA2019 + difference 0 5) (sourceB2019 + difference 5 0) sourceC2019) = raw28549 := by
      apply Matrix.ext; unfold tripleCharges sourceA2019 sourceB2019 sourceC2019 difference raw28549; decide +kernel
    rw [ha]
    exact (canonical28549 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2019 + difference 1 5) (sourceB2019 + difference 5 1) sourceC2019) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2672) := by
    have ha : (tripleCharges (sourceA2019 + difference 1 5) (sourceB2019 + difference 5 1) sourceC2019) = raw28551 := by
      apply Matrix.ext; unfold tripleCharges sourceA2019 sourceB2019 sourceC2019 difference raw28551; decide +kernel
    rw [ha]
    exact (canonical28551 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2019 + difference 2 5) (sourceB2019 + difference 5 2) sourceC2019) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2536) := by
    have ha : (tripleCharges (sourceA2019 + difference 2 5) (sourceB2019 + difference 5 2) sourceC2019) = raw28552 := by
      apply Matrix.ext; unfold tripleCharges sourceA2019 sourceB2019 sourceC2019 difference raw28552; decide +kernel
    rw [ha]
    exact (canonical28552 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2019 + difference 3 5) (sourceB2019 + difference 5 3) sourceC2019) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2565) := by
    have ha : (tripleCharges (sourceA2019 + difference 3 5) (sourceB2019 + difference 5 3) sourceC2019) = raw28553 := by
      apply Matrix.ext; unfold tripleCharges sourceA2019 sourceB2019 sourceC2019 difference raw28553; decide +kernel
    rw [ha]
    exact (canonical28553 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2019 + difference 4 5) (sourceB2019 + difference 5 4) sourceC2019) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2533) := by
    have ha : (tripleCharges (sourceA2019 + difference 4 5) (sourceB2019 + difference 5 4) sourceC2019) = raw28554 := by
      apply Matrix.ext; unfold tripleCharges sourceA2019 sourceB2019 sourceC2019 difference raw28554; decide +kernel
    rw [ha]
    exact (canonical28554 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2019 + difference 5 5) (sourceB2019 + difference 5 5) sourceC2019) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2453) := by
    have ha : (tripleCharges (sourceA2019 + difference 5 5) (sourceB2019 + difference 5 5) sourceC2019) = raw28544 := by
      apply Matrix.ext; unfold tripleCharges sourceA2019 sourceB2019 sourceC2019 difference raw28544; decide +kernel
    rw [ha]
    exact (canonical28544 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2019 + sourceB2019) sourceC2019) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA2019 + sourceB2019) sourceC2019) = raw28550 := by
      apply Matrix.ext; unfold doubleCharges sourceA2019 sourceB2019 sourceC2019 raw28550; decide +kernel
    rw [ha]
    exact (canonical28550 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2019 sourceB2019 sourceC2019
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2019, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2020 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2020 : Charge := ![1, 1, 1, -2, -1, 0]
def sourceC2020 : Charge := ![2, 0, -1, 2, 0, -3]
def sourceForm2020 : Integer.Sparse Master := [(Sum.inr 1991, 1), (Sum.inr 1993, 1), (Sum.inr 1997, 1), (Sum.inr 2030, 1), (Sum.inr 2215, 1), (Sum.inr 3516, 1), (Sum.inr 4082, -1)]

theorem sourceEq2020 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2020 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2020 + difference 0 0) (sourceB2020 + difference 0 0) sourceC2020) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1991) := by
    have ha : (tripleCharges (sourceA2020 + difference 0 0) (sourceB2020 + difference 0 0) sourceC2020) = raw28555 := by
      apply Matrix.ext; unfold tripleCharges sourceA2020 sourceB2020 sourceC2020 difference raw28555; decide +kernel
    rw [ha]
    exact (canonical28555 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2020 + difference 0 1) (sourceB2020 + difference 1 0) sourceC2020) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1993) := by
    have ha : (tripleCharges (sourceA2020 + difference 0 1) (sourceB2020 + difference 1 0) sourceC2020) = raw28556 := by
      apply Matrix.ext; unfold tripleCharges sourceA2020 sourceB2020 sourceC2020 difference raw28556; decide +kernel
    rw [ha]
    exact (canonical28556 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2020 + difference 0 2) (sourceB2020 + difference 2 0) sourceC2020) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2030) := by
    have ha : (tripleCharges (sourceA2020 + difference 0 2) (sourceB2020 + difference 2 0) sourceC2020) = raw28557 := by
      apply Matrix.ext; unfold tripleCharges sourceA2020 sourceB2020 sourceC2020 difference raw28557; decide +kernel
    rw [ha]
    exact (canonical28557 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2020 + difference 0 3) (sourceB2020 + difference 3 0) sourceC2020) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1997) := by
    have ha : (tripleCharges (sourceA2020 + difference 0 3) (sourceB2020 + difference 3 0) sourceC2020) = raw28558 := by
      apply Matrix.ext; unfold tripleCharges sourceA2020 sourceB2020 sourceC2020 difference raw28558; decide +kernel
    rw [ha]
    exact (canonical28558 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2020 + difference 0 4) (sourceB2020 + difference 4 0) sourceC2020) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2215) := by
    have ha : (tripleCharges (sourceA2020 + difference 0 4) (sourceB2020 + difference 4 0) sourceC2020) = raw28559 := by
      apply Matrix.ext; unfold tripleCharges sourceA2020 sourceB2020 sourceC2020 difference raw28559; decide +kernel
    rw [ha]
    exact (canonical28559 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2020 + difference 0 5) (sourceB2020 + difference 5 0) sourceC2020) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3516) := by
    have ha : (tripleCharges (sourceA2020 + difference 0 5) (sourceB2020 + difference 5 0) sourceC2020) = raw28560 := by
      apply Matrix.ext; unfold tripleCharges sourceA2020 sourceB2020 sourceC2020 difference raw28560; decide +kernel
    rw [ha]
    exact (canonical28560 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2020 + sourceB2020) sourceC2020) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2020 + sourceB2020) sourceC2020) = raw28561 := by
      apply Matrix.ext; unfold doubleCharges sourceA2020 sourceB2020 sourceC2020 raw28561; decide +kernel
    rw [ha]
    exact (canonical28561 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2020 sourceB2020 sourceC2020
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2020, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2021 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2021 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC2021 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceForm2021 : Integer.Sparse Master := [(Sum.inr 4365, 2), (Sum.inr 4370, 1), (Sum.inr 4373, 1), (Sum.inr 4460, 1), (Sum.inr 4552, 2), (Sum.inr 4560, 1), (Sum.inr 4621, 1), (Sum.inr 4697, 2), (Sum.inr 4704, 1), (Sum.inr 4771, 2), (Sum.inr 4776, 2), (Sum.inr 4804, 2), (Sum.inr 4865, 2), (Sum.inr 4868, 2), (Sum.inr 4874, 1), (Sum.inr 4894, 1), (Sum.inr 4897, 1), (Sum.inr 5161, 2), (Sum.inr 5175, 1), (Sum.inr 5291, 1), (Sum.inr 5305, 1)]

theorem sourceEq2021 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2021 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2021 + difference 0 1) (sourceB2021 + difference 1 0) sourceC2021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4874) := by
    have ha : (tripleCharges (sourceA2021 + difference 0 1) (sourceB2021 + difference 1 0) sourceC2021) = raw28562 := by
      apply Matrix.ext; unfold tripleCharges sourceA2021 sourceB2021 sourceC2021 difference raw28562; decide +kernel
    rw [ha]
    exact (canonical28562 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2021 + difference 0 2) (sourceB2021 + difference 2 0) sourceC2021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4865) := by
    have ha : (tripleCharges (sourceA2021 + difference 0 2) (sourceB2021 + difference 2 0) sourceC2021) = raw28563 := by
      apply Matrix.ext; unfold tripleCharges sourceA2021 sourceB2021 sourceC2021 difference raw28563; decide +kernel
    rw [ha]
    exact (canonical28563 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2021 + difference 0 3) (sourceB2021 + difference 3 0) sourceC2021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4865) := by
    have ha : (tripleCharges (sourceA2021 + difference 0 3) (sourceB2021 + difference 3 0) sourceC2021) = raw28564 := by
      apply Matrix.ext; unfold tripleCharges sourceA2021 sourceB2021 sourceC2021 difference raw28564; decide +kernel
    rw [ha]
    exact (canonical28564 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2021 + difference 0 4) (sourceB2021 + difference 4 0) sourceC2021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4894) := by
    have ha : (tripleCharges (sourceA2021 + difference 0 4) (sourceB2021 + difference 4 0) sourceC2021) = raw5101 := by
      apply Matrix.ext; unfold tripleCharges sourceA2021 sourceB2021 sourceC2021 difference raw5101; decide +kernel
    rw [ha]
    exact (canonical5101 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2021 + difference 0 5) (sourceB2021 + difference 5 0) sourceC2021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5291) := by
    have ha : (tripleCharges (sourceA2021 + difference 0 5) (sourceB2021 + difference 5 0) sourceC2021) = raw10238 := by
      apply Matrix.ext; unfold tripleCharges sourceA2021 sourceB2021 sourceC2021 difference raw10238; decide +kernel
    rw [ha]
    exact (canonical10238 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2021 + difference 1 0) (sourceB2021 + difference 0 1) sourceC2021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4621) := by
    have ha : (tripleCharges (sourceA2021 + difference 1 0) (sourceB2021 + difference 0 1) sourceC2021) = raw5121 := by
      apply Matrix.ext; unfold tripleCharges sourceA2021 sourceB2021 sourceC2021 difference raw5121; decide +kernel
    rw [ha]
    exact (canonical5121 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2021 + difference 1 2) (sourceB2021 + difference 2 1) sourceC2021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4868) := by
    have ha : (tripleCharges (sourceA2021 + difference 1 2) (sourceB2021 + difference 2 1) sourceC2021) = raw5123 := by
      apply Matrix.ext; unfold tripleCharges sourceA2021 sourceB2021 sourceC2021 difference raw5123; decide +kernel
    rw [ha]
    exact (canonical5123 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2021 + difference 1 3) (sourceB2021 + difference 3 1) sourceC2021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4868) := by
    have ha : (tripleCharges (sourceA2021 + difference 1 3) (sourceB2021 + difference 3 1) sourceC2021) = raw5124 := by
      apply Matrix.ext; unfold tripleCharges sourceA2021 sourceB2021 sourceC2021 difference raw5124; decide +kernel
    rw [ha]
    exact (canonical5124 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2021 + difference 1 4) (sourceB2021 + difference 4 1) sourceC2021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4897) := by
    have ha : (tripleCharges (sourceA2021 + difference 1 4) (sourceB2021 + difference 4 1) sourceC2021) = raw10259 := by
      apply Matrix.ext; unfold tripleCharges sourceA2021 sourceB2021 sourceC2021 difference raw10259; decide +kernel
    rw [ha]
    exact (canonical10259 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2021 + difference 1 5) (sourceB2021 + difference 5 1) sourceC2021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5305) := by
    have ha : (tripleCharges (sourceA2021 + difference 1 5) (sourceB2021 + difference 5 1) sourceC2021) = raw5125 := by
      apply Matrix.ext; unfold tripleCharges sourceA2021 sourceB2021 sourceC2021 difference raw5125; decide +kernel
    rw [ha]
    exact (canonical5125 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2021 + difference 2 0) (sourceB2021 + difference 0 2) sourceC2021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4552) := by
    have ha : (tripleCharges (sourceA2021 + difference 2 0) (sourceB2021 + difference 0 2) sourceC2021) = raw20487 := by
      apply Matrix.ext; unfold tripleCharges sourceA2021 sourceB2021 sourceC2021 difference raw20487; decide +kernel
    rw [ha]
    exact (canonical20487 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2021 + difference 2 1) (sourceB2021 + difference 1 2) sourceC2021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4776) := by
    have ha : (tripleCharges (sourceA2021 + difference 2 1) (sourceB2021 + difference 1 2) sourceC2021) = raw28565 := by
      apply Matrix.ext; unfold tripleCharges sourceA2021 sourceB2021 sourceC2021 difference raw28565; decide +kernel
    rw [ha]
    exact (canonical28565 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2021 + difference 2 3) (sourceB2021 + difference 3 2) sourceC2021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4771) := by
    have ha : (tripleCharges (sourceA2021 + difference 2 3) (sourceB2021 + difference 3 2) sourceC2021) = raw28566 := by
      apply Matrix.ext; unfold tripleCharges sourceA2021 sourceB2021 sourceC2021 difference raw28566; decide +kernel
    rw [ha]
    exact (canonical28566 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2021 + difference 2 4) (sourceB2021 + difference 4 2) sourceC2021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA2021 + difference 2 4) (sourceB2021 + difference 4 2) sourceC2021) = raw5112 := by
      apply Matrix.ext; unfold tripleCharges sourceA2021 sourceB2021 sourceC2021 difference raw5112; decide +kernel
    rw [ha]
    exact (canonical5112 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2021 + difference 2 5) (sourceB2021 + difference 5 2) sourceC2021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5161) := by
    have ha : (tripleCharges (sourceA2021 + difference 2 5) (sourceB2021 + difference 5 2) sourceC2021) = raw10247 := by
      apply Matrix.ext; unfold tripleCharges sourceA2021 sourceB2021 sourceC2021 difference raw10247; decide +kernel
    rw [ha]
    exact (canonical10247 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2021 + difference 3 0) (sourceB2021 + difference 0 3) sourceC2021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4552) := by
    have ha : (tripleCharges (sourceA2021 + difference 3 0) (sourceB2021 + difference 0 3) sourceC2021) = raw20490 := by
      apply Matrix.ext; unfold tripleCharges sourceA2021 sourceB2021 sourceC2021 difference raw20490; decide +kernel
    rw [ha]
    exact (canonical20490 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2021 + difference 3 1) (sourceB2021 + difference 1 3) sourceC2021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4776) := by
    have ha : (tripleCharges (sourceA2021 + difference 3 1) (sourceB2021 + difference 1 3) sourceC2021) = raw28567 := by
      apply Matrix.ext; unfold tripleCharges sourceA2021 sourceB2021 sourceC2021 difference raw28567; decide +kernel
    rw [ha]
    exact (canonical28567 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2021 + difference 3 2) (sourceB2021 + difference 2 3) sourceC2021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4771) := by
    have ha : (tripleCharges (sourceA2021 + difference 3 2) (sourceB2021 + difference 2 3) sourceC2021) = raw28568 := by
      apply Matrix.ext; unfold tripleCharges sourceA2021 sourceB2021 sourceC2021 difference raw28568; decide +kernel
    rw [ha]
    exact (canonical28568 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2021 + difference 3 4) (sourceB2021 + difference 4 3) sourceC2021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA2021 + difference 3 4) (sourceB2021 + difference 4 3) sourceC2021) = raw5117 := by
      apply Matrix.ext; unfold tripleCharges sourceA2021 sourceB2021 sourceC2021 difference raw5117; decide +kernel
    rw [ha]
    exact (canonical5117 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2021 + difference 3 5) (sourceB2021 + difference 5 3) sourceC2021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5161) := by
    have ha : (tripleCharges (sourceA2021 + difference 3 5) (sourceB2021 + difference 5 3) sourceC2021) = raw10251 := by
      apply Matrix.ext; unfold tripleCharges sourceA2021 sourceB2021 sourceC2021 difference raw10251; decide +kernel
    rw [ha]
    exact (canonical10251 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2021 + difference 4 0) (sourceB2021 + difference 0 4) sourceC2021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4560) := by
    have ha : (tripleCharges (sourceA2021 + difference 4 0) (sourceB2021 + difference 0 4) sourceC2021) = raw20493 := by
      apply Matrix.ext; unfold tripleCharges sourceA2021 sourceB2021 sourceC2021 difference raw20493; decide +kernel
    rw [ha]
    exact (canonical20493 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2021 + difference 4 1) (sourceB2021 + difference 1 4) sourceC2021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4704) := by
    have ha : (tripleCharges (sourceA2021 + difference 4 1) (sourceB2021 + difference 1 4) sourceC2021) = raw28569 := by
      apply Matrix.ext; unfold tripleCharges sourceA2021 sourceB2021 sourceC2021 difference raw28569; decide +kernel
    rw [ha]
    exact (canonical28569 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2021 + difference 4 2) (sourceB2021 + difference 2 4) sourceC2021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4697) := by
    have ha : (tripleCharges (sourceA2021 + difference 4 2) (sourceB2021 + difference 2 4) sourceC2021) = raw28570 := by
      apply Matrix.ext; unfold tripleCharges sourceA2021 sourceB2021 sourceC2021 difference raw28570; decide +kernel
    rw [ha]
    exact (canonical28570 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2021 + difference 4 3) (sourceB2021 + difference 3 4) sourceC2021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4697) := by
    have ha : (tripleCharges (sourceA2021 + difference 4 3) (sourceB2021 + difference 3 4) sourceC2021) = raw28571 := by
      apply Matrix.ext; unfold tripleCharges sourceA2021 sourceB2021 sourceC2021 difference raw28571; decide +kernel
    rw [ha]
    exact (canonical28571 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2021 + difference 4 5) (sourceB2021 + difference 5 4) sourceC2021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5175) := by
    have ha : (tripleCharges (sourceA2021 + difference 4 5) (sourceB2021 + difference 5 4) sourceC2021) = raw10255 := by
      apply Matrix.ext; unfold tripleCharges sourceA2021 sourceB2021 sourceC2021 difference raw10255; decide +kernel
    rw [ha]
    exact (canonical10255 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2021 + difference 5 0) (sourceB2021 + difference 0 5) sourceC2021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4370) := by
    have ha : (tripleCharges (sourceA2021 + difference 5 0) (sourceB2021 + difference 0 5) sourceC2021) = raw19632 := by
      apply Matrix.ext; unfold tripleCharges sourceA2021 sourceB2021 sourceC2021 difference raw19632; decide +kernel
    rw [ha]
    exact (canonical19632 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2021 + difference 5 1) (sourceB2021 + difference 1 5) sourceC2021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4373) := by
    have ha : (tripleCharges (sourceA2021 + difference 5 1) (sourceB2021 + difference 1 5) sourceC2021) = raw28572 := by
      apply Matrix.ext; unfold tripleCharges sourceA2021 sourceB2021 sourceC2021 difference raw28572; decide +kernel
    rw [ha]
    exact (canonical28572 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2021 + difference 5 2) (sourceB2021 + difference 2 5) sourceC2021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4365) := by
    have ha : (tripleCharges (sourceA2021 + difference 5 2) (sourceB2021 + difference 2 5) sourceC2021) = raw28573 := by
      apply Matrix.ext; unfold tripleCharges sourceA2021 sourceB2021 sourceC2021 difference raw28573; decide +kernel
    rw [ha]
    exact (canonical28573 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2021 + difference 5 3) (sourceB2021 + difference 3 5) sourceC2021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4365) := by
    have ha : (tripleCharges (sourceA2021 + difference 5 3) (sourceB2021 + difference 3 5) sourceC2021) = raw28574 := by
      apply Matrix.ext; unfold tripleCharges sourceA2021 sourceB2021 sourceC2021 difference raw28574; decide +kernel
    rw [ha]
    exact (canonical28574 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2021 + difference 5 4) (sourceB2021 + difference 4 5) sourceC2021) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4460) := by
    have ha : (tripleCharges (sourceA2021 + difference 5 4) (sourceB2021 + difference 4 5) sourceC2021) = raw5127 := by
      apply Matrix.ext; unfold tripleCharges sourceA2021 sourceB2021 sourceC2021 difference raw5127; decide +kernel
    rw [ha]
    exact (canonical5127 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2021 sourceB2021 sourceC2021
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2021, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2022 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2022 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC2022 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceForm2022 : Integer.Sparse Master := [(Sum.inr 1137, 2), (Sum.inr 1142, 1), (Sum.inr 1146, 1), (Sum.inr 1308, 1), (Sum.inr 1320, 2), (Sum.inr 1325, 1), (Sum.inr 1416, 1), (Sum.inr 2816, 2), (Sum.inr 2821, 1), (Sum.inr 2895, 2), (Sum.inr 2899, 2), (Sum.inr 2941, 2), (Sum.inr 2964, 2), (Sum.inr 2966, 2), (Sum.inr 2967, 1), (Sum.inr 3103, 1), (Sum.inr 3114, 1), (Sum.inr 3125, 1), (Sum.inr 3185, 2), (Sum.inr 3187, 1), (Sum.inr 3230, 1)]

theorem sourceEq2022 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2022 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2022 + difference 0 1) (sourceB2022 + difference 1 0) sourceC2022) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3187) := by
    have ha : (tripleCharges (sourceA2022 + difference 0 1) (sourceB2022 + difference 1 0) sourceC2022) = raw28575 := by
      apply Matrix.ext; unfold tripleCharges sourceA2022 sourceB2022 sourceC2022 difference raw28575; decide +kernel
    rw [ha]
    exact (canonical28575 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2022 + difference 0 2) (sourceB2022 + difference 2 0) sourceC2022) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3185) := by
    have ha : (tripleCharges (sourceA2022 + difference 0 2) (sourceB2022 + difference 2 0) sourceC2022) = raw28576 := by
      apply Matrix.ext; unfold tripleCharges sourceA2022 sourceB2022 sourceC2022 difference raw28576; decide +kernel
    rw [ha]
    exact (canonical28576 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2022 + difference 0 3) (sourceB2022 + difference 3 0) sourceC2022) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3185) := by
    have ha : (tripleCharges (sourceA2022 + difference 0 3) (sourceB2022 + difference 3 0) sourceC2022) = raw28577 := by
      apply Matrix.ext; unfold tripleCharges sourceA2022 sourceB2022 sourceC2022 difference raw28577; decide +kernel
    rw [ha]
    exact (canonical28577 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2022 + difference 0 4) (sourceB2022 + difference 4 0) sourceC2022) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3230) := by
    have ha : (tripleCharges (sourceA2022 + difference 0 4) (sourceB2022 + difference 4 0) sourceC2022) = raw28578 := by
      apply Matrix.ext; unfold tripleCharges sourceA2022 sourceB2022 sourceC2022 difference raw28578; decide +kernel
    rw [ha]
    exact (canonical28578 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2022 + difference 0 5) (sourceB2022 + difference 5 0) sourceC2022) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3103) := by
    have ha : (tripleCharges (sourceA2022 + difference 0 5) (sourceB2022 + difference 5 0) sourceC2022) = raw10260 := by
      apply Matrix.ext; unfold tripleCharges sourceA2022 sourceB2022 sourceC2022 difference raw10260; decide +kernel
    rw [ha]
    exact (canonical10260 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2022 + difference 1 0) (sourceB2022 + difference 0 1) sourceC2022) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1308) := by
    have ha : (tripleCharges (sourceA2022 + difference 1 0) (sourceB2022 + difference 0 1) sourceC2022) = raw10285 := by
      apply Matrix.ext; unfold tripleCharges sourceA2022 sourceB2022 sourceC2022 difference raw10285; decide +kernel
    rw [ha]
    exact (canonical10285 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2022 + difference 1 2) (sourceB2022 + difference 2 1) sourceC2022) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2966) := by
    have ha : (tripleCharges (sourceA2022 + difference 1 2) (sourceB2022 + difference 2 1) sourceC2022) = raw10287 := by
      apply Matrix.ext; unfold tripleCharges sourceA2022 sourceB2022 sourceC2022 difference raw10287; decide +kernel
    rw [ha]
    exact (canonical10287 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2022 + difference 1 3) (sourceB2022 + difference 3 1) sourceC2022) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2966) := by
    have ha : (tripleCharges (sourceA2022 + difference 1 3) (sourceB2022 + difference 3 1) sourceC2022) = raw10288 := by
      apply Matrix.ext; unfold tripleCharges sourceA2022 sourceB2022 sourceC2022 difference raw10288; decide +kernel
    rw [ha]
    exact (canonical10288 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2022 + difference 1 4) (sourceB2022 + difference 4 1) sourceC2022) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3114) := by
    have ha : (tripleCharges (sourceA2022 + difference 1 4) (sourceB2022 + difference 4 1) sourceC2022) = raw10289 := by
      apply Matrix.ext; unfold tripleCharges sourceA2022 sourceB2022 sourceC2022 difference raw10289; decide +kernel
    rw [ha]
    exact (canonical10289 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2022 + difference 1 5) (sourceB2022 + difference 5 1) sourceC2022) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3125) := by
    have ha : (tripleCharges (sourceA2022 + difference 1 5) (sourceB2022 + difference 5 1) sourceC2022) = raw20496 := by
      apply Matrix.ext; unfold tripleCharges sourceA2022 sourceB2022 sourceC2022 difference raw20496; decide +kernel
    rw [ha]
    exact (canonical20496 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2022 + difference 2 0) (sourceB2022 + difference 0 2) sourceC2022) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1137) := by
    have ha : (tripleCharges (sourceA2022 + difference 2 0) (sourceB2022 + difference 0 2) sourceC2022) = raw20501 := by
      apply Matrix.ext; unfold tripleCharges sourceA2022 sourceB2022 sourceC2022 difference raw20501; decide +kernel
    rw [ha]
    exact (canonical20501 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2022 + difference 2 1) (sourceB2022 + difference 1 2) sourceC2022) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2816) := by
    have ha : (tripleCharges (sourceA2022 + difference 2 1) (sourceB2022 + difference 1 2) sourceC2022) = raw28579 := by
      apply Matrix.ext; unfold tripleCharges sourceA2022 sourceB2022 sourceC2022 difference raw28579; decide +kernel
    rw [ha]
    exact (canonical28579 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2022 + difference 2 3) (sourceB2022 + difference 3 2) sourceC2022) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2895) := by
    have ha : (tripleCharges (sourceA2022 + difference 2 3) (sourceB2022 + difference 3 2) sourceC2022) = raw28580 := by
      apply Matrix.ext; unfold tripleCharges sourceA2022 sourceB2022 sourceC2022 difference raw28580; decide +kernel
    rw [ha]
    exact (canonical28580 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2022 + difference 2 4) (sourceB2022 + difference 4 2) sourceC2022) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2941) := by
    have ha : (tripleCharges (sourceA2022 + difference 2 4) (sourceB2022 + difference 4 2) sourceC2022) = raw28581 := by
      apply Matrix.ext; unfold tripleCharges sourceA2022 sourceB2022 sourceC2022 difference raw28581; decide +kernel
    rw [ha]
    exact (canonical28581 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2022 + difference 2 5) (sourceB2022 + difference 5 2) sourceC2022) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2964) := by
    have ha : (tripleCharges (sourceA2022 + difference 2 5) (sourceB2022 + difference 5 2) sourceC2022) = raw10271 := by
      apply Matrix.ext; unfold tripleCharges sourceA2022 sourceB2022 sourceC2022 difference raw10271; decide +kernel
    rw [ha]
    exact (canonical10271 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2022 + difference 3 0) (sourceB2022 + difference 0 3) sourceC2022) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1137) := by
    have ha : (tripleCharges (sourceA2022 + difference 3 0) (sourceB2022 + difference 0 3) sourceC2022) = raw20504 := by
      apply Matrix.ext; unfold tripleCharges sourceA2022 sourceB2022 sourceC2022 difference raw20504; decide +kernel
    rw [ha]
    exact (canonical20504 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2022 + difference 3 1) (sourceB2022 + difference 1 3) sourceC2022) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2816) := by
    have ha : (tripleCharges (sourceA2022 + difference 3 1) (sourceB2022 + difference 1 3) sourceC2022) = raw28582 := by
      apply Matrix.ext; unfold tripleCharges sourceA2022 sourceB2022 sourceC2022 difference raw28582; decide +kernel
    rw [ha]
    exact (canonical28582 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2022 + difference 3 2) (sourceB2022 + difference 2 3) sourceC2022) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2895) := by
    have ha : (tripleCharges (sourceA2022 + difference 3 2) (sourceB2022 + difference 2 3) sourceC2022) = raw28583 := by
      apply Matrix.ext; unfold tripleCharges sourceA2022 sourceB2022 sourceC2022 difference raw28583; decide +kernel
    rw [ha]
    exact (canonical28583 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2022 + difference 3 4) (sourceB2022 + difference 4 3) sourceC2022) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2941) := by
    have ha : (tripleCharges (sourceA2022 + difference 3 4) (sourceB2022 + difference 4 3) sourceC2022) = raw28584 := by
      apply Matrix.ext; unfold tripleCharges sourceA2022 sourceB2022 sourceC2022 difference raw28584; decide +kernel
    rw [ha]
    exact (canonical28584 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2022 + difference 3 5) (sourceB2022 + difference 5 3) sourceC2022) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2964) := by
    have ha : (tripleCharges (sourceA2022 + difference 3 5) (sourceB2022 + difference 5 3) sourceC2022) = raw10276 := by
      apply Matrix.ext; unfold tripleCharges sourceA2022 sourceB2022 sourceC2022 difference raw10276; decide +kernel
    rw [ha]
    exact (canonical10276 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2022 + difference 4 0) (sourceB2022 + difference 0 4) sourceC2022) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1146) := by
    have ha : (tripleCharges (sourceA2022 + difference 4 0) (sourceB2022 + difference 0 4) sourceC2022) = raw20507 := by
      apply Matrix.ext; unfold tripleCharges sourceA2022 sourceB2022 sourceC2022 difference raw20507; decide +kernel
    rw [ha]
    exact (canonical20507 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2022 + difference 4 1) (sourceB2022 + difference 1 4) sourceC2022) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2821) := by
    have ha : (tripleCharges (sourceA2022 + difference 4 1) (sourceB2022 + difference 1 4) sourceC2022) = raw28585 := by
      apply Matrix.ext; unfold tripleCharges sourceA2022 sourceB2022 sourceC2022 difference raw28585; decide +kernel
    rw [ha]
    exact (canonical28585 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2022 + difference 4 2) (sourceB2022 + difference 2 4) sourceC2022) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2899) := by
    have ha : (tripleCharges (sourceA2022 + difference 4 2) (sourceB2022 + difference 2 4) sourceC2022) = raw28586 := by
      apply Matrix.ext; unfold tripleCharges sourceA2022 sourceB2022 sourceC2022 difference raw28586; decide +kernel
    rw [ha]
    exact (canonical28586 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2022 + difference 4 3) (sourceB2022 + difference 3 4) sourceC2022) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2899) := by
    have ha : (tripleCharges (sourceA2022 + difference 4 3) (sourceB2022 + difference 3 4) sourceC2022) = raw28587 := by
      apply Matrix.ext; unfold tripleCharges sourceA2022 sourceB2022 sourceC2022 difference raw28587; decide +kernel
    rw [ha]
    exact (canonical28587 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2022 + difference 4 5) (sourceB2022 + difference 5 4) sourceC2022) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2967) := by
    have ha : (tripleCharges (sourceA2022 + difference 4 5) (sourceB2022 + difference 5 4) sourceC2022) = raw10281 := by
      apply Matrix.ext; unfold tripleCharges sourceA2022 sourceB2022 sourceC2022 difference raw10281; decide +kernel
    rw [ha]
    exact (canonical10281 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2022 + difference 5 0) (sourceB2022 + difference 0 5) sourceC2022) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1142) := by
    have ha : (tripleCharges (sourceA2022 + difference 5 0) (sourceB2022 + difference 0 5) sourceC2022) = raw19660 := by
      apply Matrix.ext; unfold tripleCharges sourceA2022 sourceB2022 sourceC2022 difference raw19660; decide +kernel
    rw [ha]
    exact (canonical19660 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2022 + difference 5 1) (sourceB2022 + difference 1 5) sourceC2022) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1325) := by
    have ha : (tripleCharges (sourceA2022 + difference 5 1) (sourceB2022 + difference 1 5) sourceC2022) = raw28588 := by
      apply Matrix.ext; unfold tripleCharges sourceA2022 sourceB2022 sourceC2022 difference raw28588; decide +kernel
    rw [ha]
    exact (canonical28588 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2022 + difference 5 2) (sourceB2022 + difference 2 5) sourceC2022) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1320) := by
    have ha : (tripleCharges (sourceA2022 + difference 5 2) (sourceB2022 + difference 2 5) sourceC2022) = raw28589 := by
      apply Matrix.ext; unfold tripleCharges sourceA2022 sourceB2022 sourceC2022 difference raw28589; decide +kernel
    rw [ha]
    exact (canonical28589 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2022 + difference 5 3) (sourceB2022 + difference 3 5) sourceC2022) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1320) := by
    have ha : (tripleCharges (sourceA2022 + difference 5 3) (sourceB2022 + difference 3 5) sourceC2022) = raw28590 := by
      apply Matrix.ext; unfold tripleCharges sourceA2022 sourceB2022 sourceC2022 difference raw28590; decide +kernel
    rw [ha]
    exact (canonical28590 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2022 + difference 5 4) (sourceB2022 + difference 4 5) sourceC2022) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1416) := by
    have ha : (tripleCharges (sourceA2022 + difference 5 4) (sourceB2022 + difference 4 5) sourceC2022) = raw19640 := by
      apply Matrix.ext; unfold tripleCharges sourceA2022 sourceB2022 sourceC2022 difference raw19640; decide +kernel
    rw [ha]
    exact (canonical19640 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2022 sourceB2022 sourceC2022
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2022, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2023 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2023 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC2023 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceForm2023 : Integer.Sparse Master := [(Sum.inr 1704, 2), (Sum.inr 1722, 1), (Sum.inr 1725, 1), (Sum.inr 1735, 1), (Sum.inr 2189, 2), (Sum.inr 2200, 2), (Sum.inr 2203, 2), (Sum.inr 2212, 2), (Sum.inr 2239, 2), (Sum.inr 2242, 2), (Sum.inr 2258, 1), (Sum.inr 2261, 2), (Sum.inr 2264, 1), (Sum.inr 2273, 1), (Sum.inr 2276, 1), (Sum.inr 2289, 1), (Sum.inr 2292, 1), (Sum.inr 2719, 2), (Sum.inr 2761, 1), (Sum.inr 2765, 1), (Sum.inr 2783, 1)]

theorem sourceEq2023 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2023 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2023 + difference 0 1) (sourceB2023 + difference 1 0) sourceC2023) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2276) := by
    have ha : (tripleCharges (sourceA2023 + difference 0 1) (sourceB2023 + difference 1 0) sourceC2023) = raw28591 := by
      apply Matrix.ext; unfold tripleCharges sourceA2023 sourceB2023 sourceC2023 difference raw28591; decide +kernel
    rw [ha]
    exact (canonical28591 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2023 + difference 0 2) (sourceB2023 + difference 2 0) sourceC2023) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2242) := by
    have ha : (tripleCharges (sourceA2023 + difference 0 2) (sourceB2023 + difference 2 0) sourceC2023) = raw28592 := by
      apply Matrix.ext; unfold tripleCharges sourceA2023 sourceB2023 sourceC2023 difference raw28592; decide +kernel
    rw [ha]
    exact (canonical28592 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2023 + difference 0 3) (sourceB2023 + difference 3 0) sourceC2023) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2242) := by
    have ha : (tripleCharges (sourceA2023 + difference 0 3) (sourceB2023 + difference 3 0) sourceC2023) = raw28593 := by
      apply Matrix.ext; unfold tripleCharges sourceA2023 sourceB2023 sourceC2023 difference raw28593; decide +kernel
    rw [ha]
    exact (canonical28593 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2023 + difference 0 4) (sourceB2023 + difference 4 0) sourceC2023) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2264) := by
    have ha : (tripleCharges (sourceA2023 + difference 0 4) (sourceB2023 + difference 4 0) sourceC2023) = raw5131 := by
      apply Matrix.ext; unfold tripleCharges sourceA2023 sourceB2023 sourceC2023 difference raw5131; decide +kernel
    rw [ha]
    exact (canonical5131 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2023 + difference 0 5) (sourceB2023 + difference 5 0) sourceC2023) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2765) := by
    have ha : (tripleCharges (sourceA2023 + difference 0 5) (sourceB2023 + difference 5 0) sourceC2023) = raw10290 := by
      apply Matrix.ext; unfold tripleCharges sourceA2023 sourceB2023 sourceC2023 difference raw10290; decide +kernel
    rw [ha]
    exact (canonical10290 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2023 + difference 1 0) (sourceB2023 + difference 0 1) sourceC2023) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2289) := by
    have ha : (tripleCharges (sourceA2023 + difference 1 0) (sourceB2023 + difference 0 1) sourceC2023) = raw5151 := by
      apply Matrix.ext; unfold tripleCharges sourceA2023 sourceB2023 sourceC2023 difference raw5151; decide +kernel
    rw [ha]
    exact (canonical5151 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2023 + difference 1 2) (sourceB2023 + difference 2 1) sourceC2023) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2261) := by
    have ha : (tripleCharges (sourceA2023 + difference 1 2) (sourceB2023 + difference 2 1) sourceC2023) = raw5153 := by
      apply Matrix.ext; unfold tripleCharges sourceA2023 sourceB2023 sourceC2023 difference raw5153; decide +kernel
    rw [ha]
    exact (canonical5153 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2023 + difference 1 3) (sourceB2023 + difference 3 1) sourceC2023) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2261) := by
    have ha : (tripleCharges (sourceA2023 + difference 1 3) (sourceB2023 + difference 3 1) sourceC2023) = raw5154 := by
      apply Matrix.ext; unfold tripleCharges sourceA2023 sourceB2023 sourceC2023 difference raw5154; decide +kernel
    rw [ha]
    exact (canonical5154 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2023 + difference 1 4) (sourceB2023 + difference 4 1) sourceC2023) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2292) := by
    have ha : (tripleCharges (sourceA2023 + difference 1 4) (sourceB2023 + difference 4 1) sourceC2023) = raw10311 := by
      apply Matrix.ext; unfold tripleCharges sourceA2023 sourceB2023 sourceC2023 difference raw10311; decide +kernel
    rw [ha]
    exact (canonical10311 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2023 + difference 1 5) (sourceB2023 + difference 5 1) sourceC2023) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2783) := by
    have ha : (tripleCharges (sourceA2023 + difference 1 5) (sourceB2023 + difference 5 1) sourceC2023) = raw5155 := by
      apply Matrix.ext; unfold tripleCharges sourceA2023 sourceB2023 sourceC2023 difference raw5155; decide +kernel
    rw [ha]
    exact (canonical5155 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2023 + difference 2 0) (sourceB2023 + difference 0 2) sourceC2023) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2200) := by
    have ha : (tripleCharges (sourceA2023 + difference 2 0) (sourceB2023 + difference 0 2) sourceC2023) = raw20515 := by
      apply Matrix.ext; unfold tripleCharges sourceA2023 sourceB2023 sourceC2023 difference raw20515; decide +kernel
    rw [ha]
    exact (canonical20515 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2023 + difference 2 1) (sourceB2023 + difference 1 2) sourceC2023) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2212) := by
    have ha : (tripleCharges (sourceA2023 + difference 2 1) (sourceB2023 + difference 1 2) sourceC2023) = raw28594 := by
      apply Matrix.ext; unfold tripleCharges sourceA2023 sourceB2023 sourceC2023 difference raw28594; decide +kernel
    rw [ha]
    exact (canonical28594 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2023 + difference 2 3) (sourceB2023 + difference 3 2) sourceC2023) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2189) := by
    have ha : (tripleCharges (sourceA2023 + difference 2 3) (sourceB2023 + difference 3 2) sourceC2023) = raw28595 := by
      apply Matrix.ext; unfold tripleCharges sourceA2023 sourceB2023 sourceC2023 difference raw28595; decide +kernel
    rw [ha]
    exact (canonical28595 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2023 + difference 2 4) (sourceB2023 + difference 4 2) sourceC2023) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2203) := by
    have ha : (tripleCharges (sourceA2023 + difference 2 4) (sourceB2023 + difference 4 2) sourceC2023) = raw5142 := by
      apply Matrix.ext; unfold tripleCharges sourceA2023 sourceB2023 sourceC2023 difference raw5142; decide +kernel
    rw [ha]
    exact (canonical5142 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2023 + difference 2 5) (sourceB2023 + difference 5 2) sourceC2023) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2719) := by
    have ha : (tripleCharges (sourceA2023 + difference 2 5) (sourceB2023 + difference 5 2) sourceC2023) = raw10299 := by
      apply Matrix.ext; unfold tripleCharges sourceA2023 sourceB2023 sourceC2023 difference raw10299; decide +kernel
    rw [ha]
    exact (canonical10299 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2023 + difference 3 0) (sourceB2023 + difference 0 3) sourceC2023) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2200) := by
    have ha : (tripleCharges (sourceA2023 + difference 3 0) (sourceB2023 + difference 0 3) sourceC2023) = raw20518 := by
      apply Matrix.ext; unfold tripleCharges sourceA2023 sourceB2023 sourceC2023 difference raw20518; decide +kernel
    rw [ha]
    exact (canonical20518 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2023 + difference 3 1) (sourceB2023 + difference 1 3) sourceC2023) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2212) := by
    have ha : (tripleCharges (sourceA2023 + difference 3 1) (sourceB2023 + difference 1 3) sourceC2023) = raw28596 := by
      apply Matrix.ext; unfold tripleCharges sourceA2023 sourceB2023 sourceC2023 difference raw28596; decide +kernel
    rw [ha]
    exact (canonical28596 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2023 + difference 3 2) (sourceB2023 + difference 2 3) sourceC2023) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2189) := by
    have ha : (tripleCharges (sourceA2023 + difference 3 2) (sourceB2023 + difference 2 3) sourceC2023) = raw28597 := by
      apply Matrix.ext; unfold tripleCharges sourceA2023 sourceB2023 sourceC2023 difference raw28597; decide +kernel
    rw [ha]
    exact (canonical28597 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2023 + difference 3 4) (sourceB2023 + difference 4 3) sourceC2023) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2203) := by
    have ha : (tripleCharges (sourceA2023 + difference 3 4) (sourceB2023 + difference 4 3) sourceC2023) = raw5147 := by
      apply Matrix.ext; unfold tripleCharges sourceA2023 sourceB2023 sourceC2023 difference raw5147; decide +kernel
    rw [ha]
    exact (canonical5147 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2023 + difference 3 5) (sourceB2023 + difference 5 3) sourceC2023) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2719) := by
    have ha : (tripleCharges (sourceA2023 + difference 3 5) (sourceB2023 + difference 5 3) sourceC2023) = raw10303 := by
      apply Matrix.ext; unfold tripleCharges sourceA2023 sourceB2023 sourceC2023 difference raw10303; decide +kernel
    rw [ha]
    exact (canonical10303 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2023 + difference 4 0) (sourceB2023 + difference 0 4) sourceC2023) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2258) := by
    have ha : (tripleCharges (sourceA2023 + difference 4 0) (sourceB2023 + difference 0 4) sourceC2023) = raw20521 := by
      apply Matrix.ext; unfold tripleCharges sourceA2023 sourceB2023 sourceC2023 difference raw20521; decide +kernel
    rw [ha]
    exact (canonical20521 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2023 + difference 4 1) (sourceB2023 + difference 1 4) sourceC2023) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2273) := by
    have ha : (tripleCharges (sourceA2023 + difference 4 1) (sourceB2023 + difference 1 4) sourceC2023) = raw28598 := by
      apply Matrix.ext; unfold tripleCharges sourceA2023 sourceB2023 sourceC2023 difference raw28598; decide +kernel
    rw [ha]
    exact (canonical28598 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2023 + difference 4 2) (sourceB2023 + difference 2 4) sourceC2023) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2239) := by
    have ha : (tripleCharges (sourceA2023 + difference 4 2) (sourceB2023 + difference 2 4) sourceC2023) = raw28599 := by
      apply Matrix.ext; unfold tripleCharges sourceA2023 sourceB2023 sourceC2023 difference raw28599; decide +kernel
    rw [ha]
    exact (canonical28599 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2023 + difference 4 3) (sourceB2023 + difference 3 4) sourceC2023) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2239) := by
    have ha : (tripleCharges (sourceA2023 + difference 4 3) (sourceB2023 + difference 3 4) sourceC2023) = raw28600 := by
      apply Matrix.ext; unfold tripleCharges sourceA2023 sourceB2023 sourceC2023 difference raw28600; decide +kernel
    rw [ha]
    exact (canonical28600 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2023 + difference 4 5) (sourceB2023 + difference 5 4) sourceC2023) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2761) := by
    have ha : (tripleCharges (sourceA2023 + difference 4 5) (sourceB2023 + difference 5 4) sourceC2023) = raw10307 := by
      apply Matrix.ext; unfold tripleCharges sourceA2023 sourceB2023 sourceC2023 difference raw10307; decide +kernel
    rw [ha]
    exact (canonical10307 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2023 + difference 5 0) (sourceB2023 + difference 0 5) sourceC2023) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1722) := by
    have ha : (tripleCharges (sourceA2023 + difference 5 0) (sourceB2023 + difference 0 5) sourceC2023) = raw19681 := by
      apply Matrix.ext; unfold tripleCharges sourceA2023 sourceB2023 sourceC2023 difference raw19681; decide +kernel
    rw [ha]
    exact (canonical19681 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2023 + difference 5 1) (sourceB2023 + difference 1 5) sourceC2023) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1735) := by
    have ha : (tripleCharges (sourceA2023 + difference 5 1) (sourceB2023 + difference 1 5) sourceC2023) = raw28601 := by
      apply Matrix.ext; unfold tripleCharges sourceA2023 sourceB2023 sourceC2023 difference raw28601; decide +kernel
    rw [ha]
    exact (canonical28601 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2023 + difference 5 2) (sourceB2023 + difference 2 5) sourceC2023) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1704) := by
    have ha : (tripleCharges (sourceA2023 + difference 5 2) (sourceB2023 + difference 2 5) sourceC2023) = raw28602 := by
      apply Matrix.ext; unfold tripleCharges sourceA2023 sourceB2023 sourceC2023 difference raw28602; decide +kernel
    rw [ha]
    exact (canonical28602 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2023 + difference 5 3) (sourceB2023 + difference 3 5) sourceC2023) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1704) := by
    have ha : (tripleCharges (sourceA2023 + difference 5 3) (sourceB2023 + difference 3 5) sourceC2023) = raw28603 := by
      apply Matrix.ext; unfold tripleCharges sourceA2023 sourceB2023 sourceC2023 difference raw28603; decide +kernel
    rw [ha]
    exact (canonical28603 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2023 + difference 5 4) (sourceB2023 + difference 4 5) sourceC2023) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1725) := by
    have ha : (tripleCharges (sourceA2023 + difference 5 4) (sourceB2023 + difference 4 5) sourceC2023) = raw5157 := by
      apply Matrix.ext; unfold tripleCharges sourceA2023 sourceB2023 sourceC2023 difference raw5157; decide +kernel
    rw [ha]
    exact (canonical5157 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2023 sourceB2023 sourceC2023
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2023, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2024 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2024 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC2024 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceForm2024 : Integer.Sparse Master := [(Sum.inr 952, 1), (Sum.inr 1830, 1), (Sum.inr 1978, 2), (Sum.inr 2109, 1), (Sum.inr 2115, 1), (Sum.inr 4084, -1)]

theorem sourceEq2024 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2024 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2024 + difference 0 1) (sourceB2024 + difference 1 0) sourceC2024) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2115) := by
    have ha : (tripleCharges (sourceA2024 + difference 0 1) (sourceB2024 + difference 1 0) sourceC2024) = raw28604 := by
      apply Matrix.ext; unfold tripleCharges sourceA2024 sourceB2024 sourceC2024 difference raw28604; decide +kernel
    rw [ha]
    exact (canonical28604 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2024 + difference 1 1) (sourceB2024 + difference 1 1) sourceC2024) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2109) := by
    have ha : (tripleCharges (sourceA2024 + difference 1 1) (sourceB2024 + difference 1 1) sourceC2024) = raw5175 := by
      apply Matrix.ext; unfold tripleCharges sourceA2024 sourceB2024 sourceC2024 difference raw5175; decide +kernel
    rw [ha]
    exact (canonical5175 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2024 + difference 2 1) (sourceB2024 + difference 1 2) sourceC2024) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1978) := by
    have ha : (tripleCharges (sourceA2024 + difference 2 1) (sourceB2024 + difference 1 2) sourceC2024) = raw28605 := by
      apply Matrix.ext; unfold tripleCharges sourceA2024 sourceB2024 sourceC2024 difference raw28605; decide +kernel
    rw [ha]
    exact (canonical28605 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2024 + difference 3 1) (sourceB2024 + difference 1 3) sourceC2024) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1978) := by
    have ha : (tripleCharges (sourceA2024 + difference 3 1) (sourceB2024 + difference 1 3) sourceC2024) = raw28606 := by
      apply Matrix.ext; unfold tripleCharges sourceA2024 sourceB2024 sourceC2024 difference raw28606; decide +kernel
    rw [ha]
    exact (canonical28606 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2024 + difference 4 1) (sourceB2024 + difference 1 4) sourceC2024) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1830) := by
    have ha : (tripleCharges (sourceA2024 + difference 4 1) (sourceB2024 + difference 1 4) sourceC2024) = raw28607 := by
      apply Matrix.ext; unfold tripleCharges sourceA2024 sourceB2024 sourceC2024 difference raw28607; decide +kernel
    rw [ha]
    exact (canonical28607 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2024 + difference 5 1) (sourceB2024 + difference 1 5) sourceC2024) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 952) := by
    have ha : (tripleCharges (sourceA2024 + difference 5 1) (sourceB2024 + difference 1 5) sourceC2024) = raw28608 := by
      apply Matrix.ext; unfold tripleCharges sourceA2024 sourceB2024 sourceC2024 difference raw28608; decide +kernel
    rw [ha]
    exact (canonical28608 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2024 + sourceB2024) sourceC2024) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA2024 + sourceB2024) sourceC2024) = raw5167 := by
      apply Matrix.ext; unfold doubleCharges sourceA2024 sourceB2024 sourceC2024 raw5167; decide +kernel
    rw [ha]
    exact (canonical5167 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2024 sourceB2024 sourceC2024
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2024, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2025 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2025 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC2025 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceForm2025 : Integer.Sparse Master := [(Sum.inr 1157, 1), (Sum.inr 1972, 1), (Sum.inr 1978, 1), (Sum.inr 2022, 1), (Sum.inr 2109, 1), (Sum.inr 2588, 1), (Sum.inr 4084, -1)]

theorem sourceEq2025 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2025 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2025 + difference 2 0) (sourceB2025 + difference 0 2) sourceC2025) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1157) := by
    have ha : (tripleCharges (sourceA2025 + difference 2 0) (sourceB2025 + difference 0 2) sourceC2025) = raw20531 := by
      apply Matrix.ext; unfold tripleCharges sourceA2025 sourceB2025 sourceC2025 difference raw20531; decide +kernel
    rw [ha]
    exact (canonical20531 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2025 + difference 2 1) (sourceB2025 + difference 1 2) sourceC2025) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1978) := by
    have ha : (tripleCharges (sourceA2025 + difference 2 1) (sourceB2025 + difference 1 2) sourceC2025) = raw28605 := by
      apply Matrix.ext; unfold tripleCharges sourceA2025 sourceB2025 sourceC2025 difference raw28605; decide +kernel
    rw [ha]
    exact (canonical28605 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2025 + difference 2 2) (sourceB2025 + difference 2 2) sourceC2025) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2109) := by
    have ha : (tripleCharges (sourceA2025 + difference 2 2) (sourceB2025 + difference 2 2) sourceC2025) = raw5175 := by
      apply Matrix.ext; unfold tripleCharges sourceA2025 sourceB2025 sourceC2025 difference raw5175; decide +kernel
    rw [ha]
    exact (canonical5175 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2025 + difference 2 3) (sourceB2025 + difference 3 2) sourceC2025) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1972) := by
    have ha : (tripleCharges (sourceA2025 + difference 2 3) (sourceB2025 + difference 3 2) sourceC2025) = raw28609 := by
      apply Matrix.ext; unfold tripleCharges sourceA2025 sourceB2025 sourceC2025 difference raw28609; decide +kernel
    rw [ha]
    exact (canonical28609 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2025 + difference 2 4) (sourceB2025 + difference 4 2) sourceC2025) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2022) := by
    have ha : (tripleCharges (sourceA2025 + difference 2 4) (sourceB2025 + difference 4 2) sourceC2025) = raw5173 := by
      apply Matrix.ext; unfold tripleCharges sourceA2025 sourceB2025 sourceC2025 difference raw5173; decide +kernel
    rw [ha]
    exact (canonical5173 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2025 + difference 2 5) (sourceB2025 + difference 5 2) sourceC2025) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2588) := by
    have ha : (tripleCharges (sourceA2025 + difference 2 5) (sourceB2025 + difference 5 2) sourceC2025) = raw28610 := by
      apply Matrix.ext; unfold tripleCharges sourceA2025 sourceB2025 sourceC2025 difference raw28610; decide +kernel
    rw [ha]
    exact (canonical28610 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2025 + sourceB2025) sourceC2025) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA2025 + sourceB2025) sourceC2025) = raw5167 := by
      apply Matrix.ext; unfold doubleCharges sourceA2025 sourceB2025 sourceC2025 raw5167; decide +kernel
    rw [ha]
    exact (canonical5167 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2025 sourceB2025 sourceC2025
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2025, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2026 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2026 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC2026 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceForm2026 : Integer.Sparse Master := [(Sum.inr 943, 1), (Sum.inr 1823, 1), (Sum.inr 1972, 1), (Sum.inr 2106, 1), (Sum.inr 2109, 2), (Sum.inr 4084, -1)]

theorem sourceEq2026 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2026 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2026 + difference 0 2) (sourceB2026 + difference 2 0) sourceC2026) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2106) := by
    have ha : (tripleCharges (sourceA2026 + difference 0 2) (sourceB2026 + difference 2 0) sourceC2026) = raw28611 := by
      apply Matrix.ext; unfold tripleCharges sourceA2026 sourceB2026 sourceC2026 difference raw28611; decide +kernel
    rw [ha]
    exact (canonical28611 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2026 + difference 1 2) (sourceB2026 + difference 2 1) sourceC2026) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2109) := by
    have ha : (tripleCharges (sourceA2026 + difference 1 2) (sourceB2026 + difference 2 1) sourceC2026) = raw5177 := by
      apply Matrix.ext; unfold tripleCharges sourceA2026 sourceB2026 sourceC2026 difference raw5177; decide +kernel
    rw [ha]
    exact (canonical5177 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2026 + difference 2 2) (sourceB2026 + difference 2 2) sourceC2026) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2109) := by
    have ha : (tripleCharges (sourceA2026 + difference 2 2) (sourceB2026 + difference 2 2) sourceC2026) = raw5175 := by
      apply Matrix.ext; unfold tripleCharges sourceA2026 sourceB2026 sourceC2026 difference raw5175; decide +kernel
    rw [ha]
    exact (canonical5175 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2026 + difference 3 2) (sourceB2026 + difference 2 3) sourceC2026) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1972) := by
    have ha : (tripleCharges (sourceA2026 + difference 3 2) (sourceB2026 + difference 2 3) sourceC2026) = raw28612 := by
      apply Matrix.ext; unfold tripleCharges sourceA2026 sourceB2026 sourceC2026 difference raw28612; decide +kernel
    rw [ha]
    exact (canonical28612 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2026 + difference 4 2) (sourceB2026 + difference 2 4) sourceC2026) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1823) := by
    have ha : (tripleCharges (sourceA2026 + difference 4 2) (sourceB2026 + difference 2 4) sourceC2026) = raw28613 := by
      apply Matrix.ext; unfold tripleCharges sourceA2026 sourceB2026 sourceC2026 difference raw28613; decide +kernel
    rw [ha]
    exact (canonical28613 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2026 + difference 5 2) (sourceB2026 + difference 2 5) sourceC2026) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 943) := by
    have ha : (tripleCharges (sourceA2026 + difference 5 2) (sourceB2026 + difference 2 5) sourceC2026) = raw28614 := by
      apply Matrix.ext; unfold tripleCharges sourceA2026 sourceB2026 sourceC2026 difference raw28614; decide +kernel
    rw [ha]
    exact (canonical28614 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2026 + sourceB2026) sourceC2026) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA2026 + sourceB2026) sourceC2026) = raw5167 := by
      apply Matrix.ext; unfold doubleCharges sourceA2026 sourceB2026 sourceC2026 raw5167; decide +kernel
    rw [ha]
    exact (canonical5167 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2026 sourceB2026 sourceC2026
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2026, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2027 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2027 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceC2027 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceForm2027 : Integer.Sparse Master := [(Sum.inr 4233, 2), (Sum.inr 4235, 1), (Sum.inr 4242, 1), (Sum.inr 4272, 1), (Sum.inr 4338, 2), (Sum.inr 4359, 1), (Sum.inr 4454, 1), (Sum.inr 4681, 2), (Sum.inr 4692, 1), (Sum.inr 4721, 2), (Sum.inr 4726, 2), (Sum.inr 4744, 2), (Sum.inr 4827, 2), (Sum.inr 4845, 1), (Sum.inr 4866, 2), (Sum.inr 4875, 1), (Sum.inr 4896, 1), (Sum.inr 5163, 2), (Sum.inr 5176, 1), (Sum.inr 5291, 1), (Sum.inr 5451, 1)]

theorem sourceEq2027 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2027 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2027 + difference 0 1) (sourceB2027 + difference 1 0) sourceC2027) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4875) := by
    have ha : (tripleCharges (sourceA2027 + difference 0 1) (sourceB2027 + difference 1 0) sourceC2027) = raw28615 := by
      apply Matrix.ext; unfold tripleCharges sourceA2027 sourceB2027 sourceC2027 difference raw28615; decide +kernel
    rw [ha]
    exact (canonical28615 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2027 + difference 0 2) (sourceB2027 + difference 2 0) sourceC2027) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA2027 + difference 0 2) (sourceB2027 + difference 2 0) sourceC2027) = raw28616 := by
      apply Matrix.ext; unfold tripleCharges sourceA2027 sourceB2027 sourceC2027 difference raw28616; decide +kernel
    rw [ha]
    exact (canonical28616 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2027 + difference 0 3) (sourceB2027 + difference 3 0) sourceC2027) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA2027 + difference 0 3) (sourceB2027 + difference 3 0) sourceC2027) = raw28617 := by
      apply Matrix.ext; unfold tripleCharges sourceA2027 sourceB2027 sourceC2027 difference raw28617; decide +kernel
    rw [ha]
    exact (canonical28617 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2027 + difference 0 4) (sourceB2027 + difference 4 0) sourceC2027) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4896) := by
    have ha : (tripleCharges (sourceA2027 + difference 0 4) (sourceB2027 + difference 4 0) sourceC2027) = raw28618 := by
      apply Matrix.ext; unfold tripleCharges sourceA2027 sourceB2027 sourceC2027 difference raw28618; decide +kernel
    rw [ha]
    exact (canonical28618 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2027 + difference 0 5) (sourceB2027 + difference 5 0) sourceC2027) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA2027 + difference 0 5) (sourceB2027 + difference 5 0) sourceC2027) = raw9592 := by
      apply Matrix.ext; unfold tripleCharges sourceA2027 sourceB2027 sourceC2027 difference raw9592; decide +kernel
    rw [ha]
    exact (canonical9592 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2027 + difference 1 0) (sourceB2027 + difference 0 1) sourceC2027) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4454) := by
    have ha : (tripleCharges (sourceA2027 + difference 1 0) (sourceB2027 + difference 0 1) sourceC2027) = raw9617 := by
      apply Matrix.ext; unfold tripleCharges sourceA2027 sourceB2027 sourceC2027 difference raw9617; decide +kernel
    rw [ha]
    exact (canonical9617 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2027 + difference 1 2) (sourceB2027 + difference 2 1) sourceC2027) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4827) := by
    have ha : (tripleCharges (sourceA2027 + difference 1 2) (sourceB2027 + difference 2 1) sourceC2027) = raw9619 := by
      apply Matrix.ext; unfold tripleCharges sourceA2027 sourceB2027 sourceC2027 difference raw9619; decide +kernel
    rw [ha]
    exact (canonical9619 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2027 + difference 1 3) (sourceB2027 + difference 3 1) sourceC2027) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4827) := by
    have ha : (tripleCharges (sourceA2027 + difference 1 3) (sourceB2027 + difference 3 1) sourceC2027) = raw9620 := by
      apply Matrix.ext; unfold tripleCharges sourceA2027 sourceB2027 sourceC2027 difference raw9620; decide +kernel
    rw [ha]
    exact (canonical9620 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2027 + difference 1 4) (sourceB2027 + difference 4 1) sourceC2027) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4845) := by
    have ha : (tripleCharges (sourceA2027 + difference 1 4) (sourceB2027 + difference 4 1) sourceC2027) = raw9621 := by
      apply Matrix.ext; unfold tripleCharges sourceA2027 sourceB2027 sourceC2027 difference raw9621; decide +kernel
    rw [ha]
    exact (canonical9621 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2027 + difference 1 5) (sourceB2027 + difference 5 1) sourceC2027) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5291) := by
    have ha : (tripleCharges (sourceA2027 + difference 1 5) (sourceB2027 + difference 5 1) sourceC2027) = raw28619 := by
      apply Matrix.ext; unfold tripleCharges sourceA2027 sourceB2027 sourceC2027 difference raw28619; decide +kernel
    rw [ha]
    exact (canonical28619 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2027 + difference 2 0) (sourceB2027 + difference 0 2) sourceC2027) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4338) := by
    have ha : (tripleCharges (sourceA2027 + difference 2 0) (sourceB2027 + difference 0 2) sourceC2027) = raw28620 := by
      apply Matrix.ext; unfold tripleCharges sourceA2027 sourceB2027 sourceC2027 difference raw28620; decide +kernel
    rw [ha]
    exact (canonical28620 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2027 + difference 2 1) (sourceB2027 + difference 1 2) sourceC2027) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4726) := by
    have ha : (tripleCharges (sourceA2027 + difference 2 1) (sourceB2027 + difference 1 2) sourceC2027) = raw28621 := by
      apply Matrix.ext; unfold tripleCharges sourceA2027 sourceB2027 sourceC2027 difference raw28621; decide +kernel
    rw [ha]
    exact (canonical28621 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2027 + difference 2 3) (sourceB2027 + difference 3 2) sourceC2027) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4721) := by
    have ha : (tripleCharges (sourceA2027 + difference 2 3) (sourceB2027 + difference 3 2) sourceC2027) = raw28622 := by
      apply Matrix.ext; unfold tripleCharges sourceA2027 sourceB2027 sourceC2027 difference raw28622; decide +kernel
    rw [ha]
    exact (canonical28622 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2027 + difference 2 4) (sourceB2027 + difference 4 2) sourceC2027) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4744) := by
    have ha : (tripleCharges (sourceA2027 + difference 2 4) (sourceB2027 + difference 4 2) sourceC2027) = raw28623 := by
      apply Matrix.ext; unfold tripleCharges sourceA2027 sourceB2027 sourceC2027 difference raw28623; decide +kernel
    rw [ha]
    exact (canonical28623 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2027 + difference 2 5) (sourceB2027 + difference 5 2) sourceC2027) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5163) := by
    have ha : (tripleCharges (sourceA2027 + difference 2 5) (sourceB2027 + difference 5 2) sourceC2027) = raw9603 := by
      apply Matrix.ext; unfold tripleCharges sourceA2027 sourceB2027 sourceC2027 difference raw9603; decide +kernel
    rw [ha]
    exact (canonical9603 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2027 + difference 3 0) (sourceB2027 + difference 0 3) sourceC2027) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4338) := by
    have ha : (tripleCharges (sourceA2027 + difference 3 0) (sourceB2027 + difference 0 3) sourceC2027) = raw28624 := by
      apply Matrix.ext; unfold tripleCharges sourceA2027 sourceB2027 sourceC2027 difference raw28624; decide +kernel
    rw [ha]
    exact (canonical28624 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2027 + difference 3 1) (sourceB2027 + difference 1 3) sourceC2027) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4726) := by
    have ha : (tripleCharges (sourceA2027 + difference 3 1) (sourceB2027 + difference 1 3) sourceC2027) = raw28625 := by
      apply Matrix.ext; unfold tripleCharges sourceA2027 sourceB2027 sourceC2027 difference raw28625; decide +kernel
    rw [ha]
    exact (canonical28625 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2027 + difference 3 2) (sourceB2027 + difference 2 3) sourceC2027) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4721) := by
    have ha : (tripleCharges (sourceA2027 + difference 3 2) (sourceB2027 + difference 2 3) sourceC2027) = raw28626 := by
      apply Matrix.ext; unfold tripleCharges sourceA2027 sourceB2027 sourceC2027 difference raw28626; decide +kernel
    rw [ha]
    exact (canonical28626 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2027 + difference 3 4) (sourceB2027 + difference 4 3) sourceC2027) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4744) := by
    have ha : (tripleCharges (sourceA2027 + difference 3 4) (sourceB2027 + difference 4 3) sourceC2027) = raw28627 := by
      apply Matrix.ext; unfold tripleCharges sourceA2027 sourceB2027 sourceC2027 difference raw28627; decide +kernel
    rw [ha]
    exact (canonical28627 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2027 + difference 3 5) (sourceB2027 + difference 5 3) sourceC2027) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5163) := by
    have ha : (tripleCharges (sourceA2027 + difference 3 5) (sourceB2027 + difference 5 3) sourceC2027) = raw9608 := by
      apply Matrix.ext; unfold tripleCharges sourceA2027 sourceB2027 sourceC2027 difference raw9608; decide +kernel
    rw [ha]
    exact (canonical9608 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2027 + difference 4 0) (sourceB2027 + difference 0 4) sourceC2027) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4359) := by
    have ha : (tripleCharges (sourceA2027 + difference 4 0) (sourceB2027 + difference 0 4) sourceC2027) = raw28628 := by
      apply Matrix.ext; unfold tripleCharges sourceA2027 sourceB2027 sourceC2027 difference raw28628; decide +kernel
    rw [ha]
    exact (canonical28628 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2027 + difference 4 1) (sourceB2027 + difference 1 4) sourceC2027) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4692) := by
    have ha : (tripleCharges (sourceA2027 + difference 4 1) (sourceB2027 + difference 1 4) sourceC2027) = raw28629 := by
      apply Matrix.ext; unfold tripleCharges sourceA2027 sourceB2027 sourceC2027 difference raw28629; decide +kernel
    rw [ha]
    exact (canonical28629 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2027 + difference 4 2) (sourceB2027 + difference 2 4) sourceC2027) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4681) := by
    have ha : (tripleCharges (sourceA2027 + difference 4 2) (sourceB2027 + difference 2 4) sourceC2027) = raw28630 := by
      apply Matrix.ext; unfold tripleCharges sourceA2027 sourceB2027 sourceC2027 difference raw28630; decide +kernel
    rw [ha]
    exact (canonical28630 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2027 + difference 4 3) (sourceB2027 + difference 3 4) sourceC2027) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4681) := by
    have ha : (tripleCharges (sourceA2027 + difference 4 3) (sourceB2027 + difference 3 4) sourceC2027) = raw28631 := by
      apply Matrix.ext; unfold tripleCharges sourceA2027 sourceB2027 sourceC2027 difference raw28631; decide +kernel
    rw [ha]
    exact (canonical28631 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2027 + difference 4 5) (sourceB2027 + difference 5 4) sourceC2027) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5176) := by
    have ha : (tripleCharges (sourceA2027 + difference 4 5) (sourceB2027 + difference 5 4) sourceC2027) = raw9613 := by
      apply Matrix.ext; unfold tripleCharges sourceA2027 sourceB2027 sourceC2027 difference raw9613; decide +kernel
    rw [ha]
    exact (canonical9613 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2027 + difference 5 0) (sourceB2027 + difference 0 5) sourceC2027) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4235) := by
    have ha : (tripleCharges (sourceA2027 + difference 5 0) (sourceB2027 + difference 0 5) sourceC2027) = raw28632 := by
      apply Matrix.ext; unfold tripleCharges sourceA2027 sourceB2027 sourceC2027 difference raw28632; decide +kernel
    rw [ha]
    exact (canonical28632 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2027 + difference 5 1) (sourceB2027 + difference 1 5) sourceC2027) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4242) := by
    have ha : (tripleCharges (sourceA2027 + difference 5 1) (sourceB2027 + difference 1 5) sourceC2027) = raw28633 := by
      apply Matrix.ext; unfold tripleCharges sourceA2027 sourceB2027 sourceC2027 difference raw28633; decide +kernel
    rw [ha]
    exact (canonical28633 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2027 + difference 5 2) (sourceB2027 + difference 2 5) sourceC2027) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4233) := by
    have ha : (tripleCharges (sourceA2027 + difference 5 2) (sourceB2027 + difference 2 5) sourceC2027) = raw28634 := by
      apply Matrix.ext; unfold tripleCharges sourceA2027 sourceB2027 sourceC2027 difference raw28634; decide +kernel
    rw [ha]
    exact (canonical28634 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2027 + difference 5 3) (sourceB2027 + difference 3 5) sourceC2027) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4233) := by
    have ha : (tripleCharges (sourceA2027 + difference 5 3) (sourceB2027 + difference 3 5) sourceC2027) = raw28635 := by
      apply Matrix.ext; unfold tripleCharges sourceA2027 sourceB2027 sourceC2027 difference raw28635; decide +kernel
    rw [ha]
    exact (canonical28635 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2027 + difference 5 4) (sourceB2027 + difference 4 5) sourceC2027) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4272) := by
    have ha : (tripleCharges (sourceA2027 + difference 5 4) (sourceB2027 + difference 4 5) sourceC2027) = raw28636 := by
      apply Matrix.ext; unfold tripleCharges sourceA2027 sourceB2027 sourceC2027 difference raw28636; decide +kernel
    rw [ha]
    exact (canonical28636 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2027 sourceB2027 sourceC2027
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2027, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2028 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2028 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceC2028 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceForm2028 : Integer.Sparse Master := [(Sum.inr 733, 2), (Sum.inr 735, 1), (Sum.inr 742, 1), (Sum.inr 826, 1), (Sum.inr 916, 2), (Sum.inr 937, 1), (Sum.inr 1037, 1), (Sum.inr 1807, 2), (Sum.inr 1818, 1), (Sum.inr 1875, 2), (Sum.inr 1880, 2), (Sum.inr 1924, 2), (Sum.inr 2079, 2), (Sum.inr 2107, 2), (Sum.inr 2116, 1), (Sum.inr 2218, 1), (Sum.inr 2278, 1), (Sum.inr 2590, 2), (Sum.inr 2604, 1), (Sum.inr 2765, 1), (Sum.inr 3888, 1)]

theorem sourceEq2028 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2028 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2028 + difference 0 1) (sourceB2028 + difference 1 0) sourceC2028) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2116) := by
    have ha : (tripleCharges (sourceA2028 + difference 0 1) (sourceB2028 + difference 1 0) sourceC2028) = raw28637 := by
      apply Matrix.ext; unfold tripleCharges sourceA2028 sourceB2028 sourceC2028 difference raw28637; decide +kernel
    rw [ha]
    exact (canonical28637 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2028 + difference 0 2) (sourceB2028 + difference 2 0) sourceC2028) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2107) := by
    have ha : (tripleCharges (sourceA2028 + difference 0 2) (sourceB2028 + difference 2 0) sourceC2028) = raw28638 := by
      apply Matrix.ext; unfold tripleCharges sourceA2028 sourceB2028 sourceC2028 difference raw28638; decide +kernel
    rw [ha]
    exact (canonical28638 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2028 + difference 0 3) (sourceB2028 + difference 3 0) sourceC2028) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2107) := by
    have ha : (tripleCharges (sourceA2028 + difference 0 3) (sourceB2028 + difference 3 0) sourceC2028) = raw28639 := by
      apply Matrix.ext; unfold tripleCharges sourceA2028 sourceB2028 sourceC2028 difference raw28639; decide +kernel
    rw [ha]
    exact (canonical28639 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2028 + difference 0 4) (sourceB2028 + difference 4 0) sourceC2028) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2278) := by
    have ha : (tripleCharges (sourceA2028 + difference 0 4) (sourceB2028 + difference 4 0) sourceC2028) = raw28640 := by
      apply Matrix.ext; unfold tripleCharges sourceA2028 sourceB2028 sourceC2028 difference raw28640; decide +kernel
    rw [ha]
    exact (canonical28640 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2028 + difference 0 5) (sourceB2028 + difference 5 0) sourceC2028) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3888) := by
    have ha : (tripleCharges (sourceA2028 + difference 0 5) (sourceB2028 + difference 5 0) sourceC2028) = raw9622 := by
      apply Matrix.ext; unfold tripleCharges sourceA2028 sourceB2028 sourceC2028 difference raw9622; decide +kernel
    rw [ha]
    exact (canonical9622 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2028 + difference 1 0) (sourceB2028 + difference 0 1) sourceC2028) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1037) := by
    have ha : (tripleCharges (sourceA2028 + difference 1 0) (sourceB2028 + difference 0 1) sourceC2028) = raw9647 := by
      apply Matrix.ext; unfold tripleCharges sourceA2028 sourceB2028 sourceC2028 difference raw9647; decide +kernel
    rw [ha]
    exact (canonical9647 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2028 + difference 1 2) (sourceB2028 + difference 2 1) sourceC2028) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2079) := by
    have ha : (tripleCharges (sourceA2028 + difference 1 2) (sourceB2028 + difference 2 1) sourceC2028) = raw9649 := by
      apply Matrix.ext; unfold tripleCharges sourceA2028 sourceB2028 sourceC2028 difference raw9649; decide +kernel
    rw [ha]
    exact (canonical9649 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2028 + difference 1 3) (sourceB2028 + difference 3 1) sourceC2028) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2079) := by
    have ha : (tripleCharges (sourceA2028 + difference 1 3) (sourceB2028 + difference 3 1) sourceC2028) = raw9650 := by
      apply Matrix.ext; unfold tripleCharges sourceA2028 sourceB2028 sourceC2028 difference raw9650; decide +kernel
    rw [ha]
    exact (canonical9650 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2028 + difference 1 4) (sourceB2028 + difference 4 1) sourceC2028) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2218) := by
    have ha : (tripleCharges (sourceA2028 + difference 1 4) (sourceB2028 + difference 4 1) sourceC2028) = raw9651 := by
      apply Matrix.ext; unfold tripleCharges sourceA2028 sourceB2028 sourceC2028 difference raw9651; decide +kernel
    rw [ha]
    exact (canonical9651 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2028 + difference 1 5) (sourceB2028 + difference 5 1) sourceC2028) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2765) := by
    have ha : (tripleCharges (sourceA2028 + difference 1 5) (sourceB2028 + difference 5 1) sourceC2028) = raw28641 := by
      apply Matrix.ext; unfold tripleCharges sourceA2028 sourceB2028 sourceC2028 difference raw28641; decide +kernel
    rw [ha]
    exact (canonical28641 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2028 + difference 2 0) (sourceB2028 + difference 0 2) sourceC2028) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 916) := by
    have ha : (tripleCharges (sourceA2028 + difference 2 0) (sourceB2028 + difference 0 2) sourceC2028) = raw28642 := by
      apply Matrix.ext; unfold tripleCharges sourceA2028 sourceB2028 sourceC2028 difference raw28642; decide +kernel
    rw [ha]
    exact (canonical28642 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2028 + difference 2 1) (sourceB2028 + difference 1 2) sourceC2028) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1880) := by
    have ha : (tripleCharges (sourceA2028 + difference 2 1) (sourceB2028 + difference 1 2) sourceC2028) = raw28643 := by
      apply Matrix.ext; unfold tripleCharges sourceA2028 sourceB2028 sourceC2028 difference raw28643; decide +kernel
    rw [ha]
    exact (canonical28643 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2028 + difference 2 3) (sourceB2028 + difference 3 2) sourceC2028) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1875) := by
    have ha : (tripleCharges (sourceA2028 + difference 2 3) (sourceB2028 + difference 3 2) sourceC2028) = raw28644 := by
      apply Matrix.ext; unfold tripleCharges sourceA2028 sourceB2028 sourceC2028 difference raw28644; decide +kernel
    rw [ha]
    exact (canonical28644 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2028 + difference 2 4) (sourceB2028 + difference 4 2) sourceC2028) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1924) := by
    have ha : (tripleCharges (sourceA2028 + difference 2 4) (sourceB2028 + difference 4 2) sourceC2028) = raw28645 := by
      apply Matrix.ext; unfold tripleCharges sourceA2028 sourceB2028 sourceC2028 difference raw28645; decide +kernel
    rw [ha]
    exact (canonical28645 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2028 + difference 2 5) (sourceB2028 + difference 5 2) sourceC2028) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2590) := by
    have ha : (tripleCharges (sourceA2028 + difference 2 5) (sourceB2028 + difference 5 2) sourceC2028) = raw9633 := by
      apply Matrix.ext; unfold tripleCharges sourceA2028 sourceB2028 sourceC2028 difference raw9633; decide +kernel
    rw [ha]
    exact (canonical9633 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2028 + difference 3 0) (sourceB2028 + difference 0 3) sourceC2028) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 916) := by
    have ha : (tripleCharges (sourceA2028 + difference 3 0) (sourceB2028 + difference 0 3) sourceC2028) = raw28646 := by
      apply Matrix.ext; unfold tripleCharges sourceA2028 sourceB2028 sourceC2028 difference raw28646; decide +kernel
    rw [ha]
    exact (canonical28646 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2028 + difference 3 1) (sourceB2028 + difference 1 3) sourceC2028) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1880) := by
    have ha : (tripleCharges (sourceA2028 + difference 3 1) (sourceB2028 + difference 1 3) sourceC2028) = raw28647 := by
      apply Matrix.ext; unfold tripleCharges sourceA2028 sourceB2028 sourceC2028 difference raw28647; decide +kernel
    rw [ha]
    exact (canonical28647 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2028 + difference 3 2) (sourceB2028 + difference 2 3) sourceC2028) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1875) := by
    have ha : (tripleCharges (sourceA2028 + difference 3 2) (sourceB2028 + difference 2 3) sourceC2028) = raw28648 := by
      apply Matrix.ext; unfold tripleCharges sourceA2028 sourceB2028 sourceC2028 difference raw28648; decide +kernel
    rw [ha]
    exact (canonical28648 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2028 + difference 3 4) (sourceB2028 + difference 4 3) sourceC2028) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1924) := by
    have ha : (tripleCharges (sourceA2028 + difference 3 4) (sourceB2028 + difference 4 3) sourceC2028) = raw28649 := by
      apply Matrix.ext; unfold tripleCharges sourceA2028 sourceB2028 sourceC2028 difference raw28649; decide +kernel
    rw [ha]
    exact (canonical28649 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2028 + difference 3 5) (sourceB2028 + difference 5 3) sourceC2028) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2590) := by
    have ha : (tripleCharges (sourceA2028 + difference 3 5) (sourceB2028 + difference 5 3) sourceC2028) = raw9638 := by
      apply Matrix.ext; unfold tripleCharges sourceA2028 sourceB2028 sourceC2028 difference raw9638; decide +kernel
    rw [ha]
    exact (canonical9638 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2028 + difference 4 0) (sourceB2028 + difference 0 4) sourceC2028) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 937) := by
    have ha : (tripleCharges (sourceA2028 + difference 4 0) (sourceB2028 + difference 0 4) sourceC2028) = raw28650 := by
      apply Matrix.ext; unfold tripleCharges sourceA2028 sourceB2028 sourceC2028 difference raw28650; decide +kernel
    rw [ha]
    exact (canonical28650 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2028 + difference 4 1) (sourceB2028 + difference 1 4) sourceC2028) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1818) := by
    have ha : (tripleCharges (sourceA2028 + difference 4 1) (sourceB2028 + difference 1 4) sourceC2028) = raw28651 := by
      apply Matrix.ext; unfold tripleCharges sourceA2028 sourceB2028 sourceC2028 difference raw28651; decide +kernel
    rw [ha]
    exact (canonical28651 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2028 + difference 4 2) (sourceB2028 + difference 2 4) sourceC2028) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1807) := by
    have ha : (tripleCharges (sourceA2028 + difference 4 2) (sourceB2028 + difference 2 4) sourceC2028) = raw28652 := by
      apply Matrix.ext; unfold tripleCharges sourceA2028 sourceB2028 sourceC2028 difference raw28652; decide +kernel
    rw [ha]
    exact (canonical28652 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2028 + difference 4 3) (sourceB2028 + difference 3 4) sourceC2028) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1807) := by
    have ha : (tripleCharges (sourceA2028 + difference 4 3) (sourceB2028 + difference 3 4) sourceC2028) = raw28653 := by
      apply Matrix.ext; unfold tripleCharges sourceA2028 sourceB2028 sourceC2028 difference raw28653; decide +kernel
    rw [ha]
    exact (canonical28653 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2028 + difference 4 5) (sourceB2028 + difference 5 4) sourceC2028) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2604) := by
    have ha : (tripleCharges (sourceA2028 + difference 4 5) (sourceB2028 + difference 5 4) sourceC2028) = raw9643 := by
      apply Matrix.ext; unfold tripleCharges sourceA2028 sourceB2028 sourceC2028 difference raw9643; decide +kernel
    rw [ha]
    exact (canonical9643 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2028 + difference 5 0) (sourceB2028 + difference 0 5) sourceC2028) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 735) := by
    have ha : (tripleCharges (sourceA2028 + difference 5 0) (sourceB2028 + difference 0 5) sourceC2028) = raw28654 := by
      apply Matrix.ext; unfold tripleCharges sourceA2028 sourceB2028 sourceC2028 difference raw28654; decide +kernel
    rw [ha]
    exact (canonical28654 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2028 + difference 5 1) (sourceB2028 + difference 1 5) sourceC2028) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 742) := by
    have ha : (tripleCharges (sourceA2028 + difference 5 1) (sourceB2028 + difference 1 5) sourceC2028) = raw28655 := by
      apply Matrix.ext; unfold tripleCharges sourceA2028 sourceB2028 sourceC2028 difference raw28655; decide +kernel
    rw [ha]
    exact (canonical28655 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2028 + difference 5 2) (sourceB2028 + difference 2 5) sourceC2028) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 733) := by
    have ha : (tripleCharges (sourceA2028 + difference 5 2) (sourceB2028 + difference 2 5) sourceC2028) = raw28656 := by
      apply Matrix.ext; unfold tripleCharges sourceA2028 sourceB2028 sourceC2028 difference raw28656; decide +kernel
    rw [ha]
    exact (canonical28656 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2028 + difference 5 3) (sourceB2028 + difference 3 5) sourceC2028) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 733) := by
    have ha : (tripleCharges (sourceA2028 + difference 5 3) (sourceB2028 + difference 3 5) sourceC2028) = raw28657 := by
      apply Matrix.ext; unfold tripleCharges sourceA2028 sourceB2028 sourceC2028 difference raw28657; decide +kernel
    rw [ha]
    exact (canonical28657 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2028 + difference 5 4) (sourceB2028 + difference 4 5) sourceC2028) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 826) := by
    have ha : (tripleCharges (sourceA2028 + difference 5 4) (sourceB2028 + difference 4 5) sourceC2028) = raw28658 := by
      apply Matrix.ext; unfold tripleCharges sourceA2028 sourceB2028 sourceC2028 difference raw28658; decide +kernel
    rw [ha]
    exact (canonical28658 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2028 sourceB2028 sourceC2028
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2028, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2029 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceB2029 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceC2029 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceForm2029 : Integer.Sparse Master := [(Sum.inr 4450, 2), (Sum.inr 4454, 1), (Sum.inr 4465, 1), (Sum.inr 4490, 1), (Sum.inr 4797, 2), (Sum.inr 4800, 2), (Sum.inr 4804, 2), (Sum.inr 4809, 2), (Sum.inr 4827, 2), (Sum.inr 4837, 1), (Sum.inr 4841, 1), (Sum.inr 4850, 2), (Sum.inr 4853, 2), (Sum.inr 4862, 1), (Sum.inr 4871, 1), (Sum.inr 4873, 1), (Sum.inr 4881, 1), (Sum.inr 5109, 1), (Sum.inr 5147, 2), (Sum.inr 5171, 1), (Sum.inr 5201, 1)]

theorem sourceEq2029 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2029 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2029 + difference 0 1) (sourceB2029 + difference 1 0) sourceC2029) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4871) := by
    have ha : (tripleCharges (sourceA2029 + difference 0 1) (sourceB2029 + difference 1 0) sourceC2029) = raw28659 := by
      apply Matrix.ext; unfold tripleCharges sourceA2029 sourceB2029 sourceC2029 difference raw28659; decide +kernel
    rw [ha]
    exact (canonical28659 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2029 + difference 0 2) (sourceB2029 + difference 2 0) sourceC2029) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4853) := by
    have ha : (tripleCharges (sourceA2029 + difference 0 2) (sourceB2029 + difference 2 0) sourceC2029) = raw28660 := by
      apply Matrix.ext; unfold tripleCharges sourceA2029 sourceB2029 sourceC2029 difference raw28660; decide +kernel
    rw [ha]
    exact (canonical28660 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2029 + difference 0 3) (sourceB2029 + difference 3 0) sourceC2029) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4853) := by
    have ha : (tripleCharges (sourceA2029 + difference 0 3) (sourceB2029 + difference 3 0) sourceC2029) = raw28661 := by
      apply Matrix.ext; unfold tripleCharges sourceA2029 sourceB2029 sourceC2029 difference raw28661; decide +kernel
    rw [ha]
    exact (canonical28661 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2029 + difference 0 4) (sourceB2029 + difference 4 0) sourceC2029) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4881) := by
    have ha : (tripleCharges (sourceA2029 + difference 0 4) (sourceB2029 + difference 4 0) sourceC2029) = raw28662 := by
      apply Matrix.ext; unfold tripleCharges sourceA2029 sourceB2029 sourceC2029 difference raw28662; decide +kernel
    rw [ha]
    exact (canonical28662 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2029 + difference 0 5) (sourceB2029 + difference 5 0) sourceC2029) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5109) := by
    have ha : (tripleCharges (sourceA2029 + difference 0 5) (sourceB2029 + difference 5 0) sourceC2029) = raw28663 := by
      apply Matrix.ext; unfold tripleCharges sourceA2029 sourceB2029 sourceC2029 difference raw28663; decide +kernel
    rw [ha]
    exact (canonical28663 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2029 + difference 1 0) (sourceB2029 + difference 0 1) sourceC2029) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4862) := by
    have ha : (tripleCharges (sourceA2029 + difference 1 0) (sourceB2029 + difference 0 1) sourceC2029) = raw28664 := by
      apply Matrix.ext; unfold tripleCharges sourceA2029 sourceB2029 sourceC2029 difference raw28664; decide +kernel
    rw [ha]
    exact (canonical28664 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2029 + difference 1 2) (sourceB2029 + difference 2 1) sourceC2029) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4850) := by
    have ha : (tripleCharges (sourceA2029 + difference 1 2) (sourceB2029 + difference 2 1) sourceC2029) = raw28665 := by
      apply Matrix.ext; unfold tripleCharges sourceA2029 sourceB2029 sourceC2029 difference raw28665; decide +kernel
    rw [ha]
    exact (canonical28665 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2029 + difference 1 3) (sourceB2029 + difference 3 1) sourceC2029) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4850) := by
    have ha : (tripleCharges (sourceA2029 + difference 1 3) (sourceB2029 + difference 3 1) sourceC2029) = raw28666 := by
      apply Matrix.ext; unfold tripleCharges sourceA2029 sourceB2029 sourceC2029 difference raw28666; decide +kernel
    rw [ha]
    exact (canonical28666 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2029 + difference 1 4) (sourceB2029 + difference 4 1) sourceC2029) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4873) := by
    have ha : (tripleCharges (sourceA2029 + difference 1 4) (sourceB2029 + difference 4 1) sourceC2029) = raw28667 := by
      apply Matrix.ext; unfold tripleCharges sourceA2029 sourceB2029 sourceC2029 difference raw28667; decide +kernel
    rw [ha]
    exact (canonical28667 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2029 + difference 1 5) (sourceB2029 + difference 5 1) sourceC2029) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5201) := by
    have ha : (tripleCharges (sourceA2029 + difference 1 5) (sourceB2029 + difference 5 1) sourceC2029) = raw28668 := by
      apply Matrix.ext; unfold tripleCharges sourceA2029 sourceB2029 sourceC2029 difference raw28668; decide +kernel
    rw [ha]
    exact (canonical28668 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2029 + difference 2 0) (sourceB2029 + difference 0 2) sourceC2029) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4800) := by
    have ha : (tripleCharges (sourceA2029 + difference 2 0) (sourceB2029 + difference 0 2) sourceC2029) = raw28669 := by
      apply Matrix.ext; unfold tripleCharges sourceA2029 sourceB2029 sourceC2029 difference raw28669; decide +kernel
    rw [ha]
    exact (canonical28669 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2029 + difference 2 1) (sourceB2029 + difference 1 2) sourceC2029) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4827) := by
    have ha : (tripleCharges (sourceA2029 + difference 2 1) (sourceB2029 + difference 1 2) sourceC2029) = raw28670 := by
      apply Matrix.ext; unfold tripleCharges sourceA2029 sourceB2029 sourceC2029 difference raw28670; decide +kernel
    rw [ha]
    exact (canonical28670 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2029 + difference 2 3) (sourceB2029 + difference 3 2) sourceC2029) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4797) := by
    have ha : (tripleCharges (sourceA2029 + difference 2 3) (sourceB2029 + difference 3 2) sourceC2029) = raw28671 := by
      apply Matrix.ext; unfold tripleCharges sourceA2029 sourceB2029 sourceC2029 difference raw28671; decide +kernel
    rw [ha]
    exact (canonical28671 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2029 + difference 2 4) (sourceB2029 + difference 4 2) sourceC2029) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4809) := by
    have ha : (tripleCharges (sourceA2029 + difference 2 4) (sourceB2029 + difference 4 2) sourceC2029) = raw28672 := by
      apply Matrix.ext; unfold tripleCharges sourceA2029 sourceB2029 sourceC2029 difference raw28672; decide +kernel
    rw [ha]
    exact (canonical28672 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2029 + difference 2 5) (sourceB2029 + difference 5 2) sourceC2029) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5147) := by
    have ha : (tripleCharges (sourceA2029 + difference 2 5) (sourceB2029 + difference 5 2) sourceC2029) = raw28673 := by
      apply Matrix.ext; unfold tripleCharges sourceA2029 sourceB2029 sourceC2029 difference raw28673; decide +kernel
    rw [ha]
    exact (canonical28673 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2029 + difference 3 0) (sourceB2029 + difference 0 3) sourceC2029) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4800) := by
    have ha : (tripleCharges (sourceA2029 + difference 3 0) (sourceB2029 + difference 0 3) sourceC2029) = raw28674 := by
      apply Matrix.ext; unfold tripleCharges sourceA2029 sourceB2029 sourceC2029 difference raw28674; decide +kernel
    rw [ha]
    exact (canonical28674 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2029 + difference 3 1) (sourceB2029 + difference 1 3) sourceC2029) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4827) := by
    have ha : (tripleCharges (sourceA2029 + difference 3 1) (sourceB2029 + difference 1 3) sourceC2029) = raw28675 := by
      apply Matrix.ext; unfold tripleCharges sourceA2029 sourceB2029 sourceC2029 difference raw28675; decide +kernel
    rw [ha]
    exact (canonical28675 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2029 + difference 3 2) (sourceB2029 + difference 2 3) sourceC2029) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4797) := by
    have ha : (tripleCharges (sourceA2029 + difference 3 2) (sourceB2029 + difference 2 3) sourceC2029) = raw28676 := by
      apply Matrix.ext; unfold tripleCharges sourceA2029 sourceB2029 sourceC2029 difference raw28676; decide +kernel
    rw [ha]
    exact (canonical28676 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2029 + difference 3 4) (sourceB2029 + difference 4 3) sourceC2029) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4809) := by
    have ha : (tripleCharges (sourceA2029 + difference 3 4) (sourceB2029 + difference 4 3) sourceC2029) = raw28677 := by
      apply Matrix.ext; unfold tripleCharges sourceA2029 sourceB2029 sourceC2029 difference raw28677; decide +kernel
    rw [ha]
    exact (canonical28677 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2029 + difference 3 5) (sourceB2029 + difference 5 3) sourceC2029) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5147) := by
    have ha : (tripleCharges (sourceA2029 + difference 3 5) (sourceB2029 + difference 5 3) sourceC2029) = raw27971 := by
      apply Matrix.ext; unfold tripleCharges sourceA2029 sourceB2029 sourceC2029 difference raw27971; decide +kernel
    rw [ha]
    exact (canonical27971 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2029 + difference 4 0) (sourceB2029 + difference 0 4) sourceC2029) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4837) := by
    have ha : (tripleCharges (sourceA2029 + difference 4 0) (sourceB2029 + difference 0 4) sourceC2029) = raw28678 := by
      apply Matrix.ext; unfold tripleCharges sourceA2029 sourceB2029 sourceC2029 difference raw28678; decide +kernel
    rw [ha]
    exact (canonical28678 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2029 + difference 4 1) (sourceB2029 + difference 1 4) sourceC2029) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4841) := by
    have ha : (tripleCharges (sourceA2029 + difference 4 1) (sourceB2029 + difference 1 4) sourceC2029) = raw28679 := by
      apply Matrix.ext; unfold tripleCharges sourceA2029 sourceB2029 sourceC2029 difference raw28679; decide +kernel
    rw [ha]
    exact (canonical28679 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2029 + difference 4 2) (sourceB2029 + difference 2 4) sourceC2029) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA2029 + difference 4 2) (sourceB2029 + difference 2 4) sourceC2029) = raw28680 := by
      apply Matrix.ext; unfold tripleCharges sourceA2029 sourceB2029 sourceC2029 difference raw28680; decide +kernel
    rw [ha]
    exact (canonical28680 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2029 + difference 4 3) (sourceB2029 + difference 3 4) sourceC2029) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA2029 + difference 4 3) (sourceB2029 + difference 3 4) sourceC2029) = raw28681 := by
      apply Matrix.ext; unfold tripleCharges sourceA2029 sourceB2029 sourceC2029 difference raw28681; decide +kernel
    rw [ha]
    exact (canonical28681 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2029 + difference 4 5) (sourceB2029 + difference 5 4) sourceC2029) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5171) := by
    have ha : (tripleCharges (sourceA2029 + difference 4 5) (sourceB2029 + difference 5 4) sourceC2029) = raw27667 := by
      apply Matrix.ext; unfold tripleCharges sourceA2029 sourceB2029 sourceC2029 difference raw27667; decide +kernel
    rw [ha]
    exact (canonical27667 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2029 + difference 5 0) (sourceB2029 + difference 0 5) sourceC2029) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4454) := by
    have ha : (tripleCharges (sourceA2029 + difference 5 0) (sourceB2029 + difference 0 5) sourceC2029) = raw28682 := by
      apply Matrix.ext; unfold tripleCharges sourceA2029 sourceB2029 sourceC2029 difference raw28682; decide +kernel
    rw [ha]
    exact (canonical28682 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2029 + difference 5 1) (sourceB2029 + difference 1 5) sourceC2029) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4490) := by
    have ha : (tripleCharges (sourceA2029 + difference 5 1) (sourceB2029 + difference 1 5) sourceC2029) = raw28683 := by
      apply Matrix.ext; unfold tripleCharges sourceA2029 sourceB2029 sourceC2029 difference raw28683; decide +kernel
    rw [ha]
    exact (canonical28683 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2029 + difference 5 2) (sourceB2029 + difference 2 5) sourceC2029) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4450) := by
    have ha : (tripleCharges (sourceA2029 + difference 5 2) (sourceB2029 + difference 2 5) sourceC2029) = raw28684 := by
      apply Matrix.ext; unfold tripleCharges sourceA2029 sourceB2029 sourceC2029 difference raw28684; decide +kernel
    rw [ha]
    exact (canonical28684 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2029 + difference 5 3) (sourceB2029 + difference 3 5) sourceC2029) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4450) := by
    have ha : (tripleCharges (sourceA2029 + difference 5 3) (sourceB2029 + difference 3 5) sourceC2029) = raw28685 := by
      apply Matrix.ext; unfold tripleCharges sourceA2029 sourceB2029 sourceC2029 difference raw28685; decide +kernel
    rw [ha]
    exact (canonical28685 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2029 + difference 5 4) (sourceB2029 + difference 4 5) sourceC2029) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4465) := by
    have ha : (tripleCharges (sourceA2029 + difference 5 4) (sourceB2029 + difference 4 5) sourceC2029) = raw28686 := by
      apply Matrix.ext; unfold tripleCharges sourceA2029 sourceB2029 sourceC2029 difference raw28686; decide +kernel
    rw [ha]
    exact (canonical28686 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2029 sourceB2029 sourceC2029
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2029, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2030 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceB2030 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceC2030 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceForm2030 : Integer.Sparse Master := [(Sum.inr 1415, 2), (Sum.inr 1417, 1), (Sum.inr 1418, 1), (Sum.inr 1449, 1), (Sum.inr 2486, 2), (Sum.inr 2519, 1), (Sum.inr 2520, 1), (Sum.inr 2602, 1), (Sum.inr 2865, 2), (Sum.inr 2866, 2), (Sum.inr 2886, 1), (Sum.inr 2887, 1), (Sum.inr 2915, 2), (Sum.inr 2929, 2), (Sum.inr 2941, 2), (Sum.inr 2965, 1), (Sum.inr 2989, 2), (Sum.inr 3004, 1), (Sum.inr 3177, 2), (Sum.inr 3186, 1), (Sum.inr 3215, 1)]

theorem sourceEq2030 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2030 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2030 + difference 0 1) (sourceB2030 + difference 1 0) sourceC2030) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2602) := by
    have ha : (tripleCharges (sourceA2030 + difference 0 1) (sourceB2030 + difference 1 0) sourceC2030) = raw28687 := by
      apply Matrix.ext; unfold tripleCharges sourceA2030 sourceB2030 sourceC2030 difference raw28687; decide +kernel
    rw [ha]
    exact (canonical28687 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2030 + difference 0 2) (sourceB2030 + difference 2 0) sourceC2030) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2486) := by
    have ha : (tripleCharges (sourceA2030 + difference 0 2) (sourceB2030 + difference 2 0) sourceC2030) = raw28688 := by
      apply Matrix.ext; unfold tripleCharges sourceA2030 sourceB2030 sourceC2030 difference raw28688; decide +kernel
    rw [ha]
    exact (canonical28688 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2030 + difference 0 3) (sourceB2030 + difference 3 0) sourceC2030) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2486) := by
    have ha : (tripleCharges (sourceA2030 + difference 0 3) (sourceB2030 + difference 3 0) sourceC2030) = raw28689 := by
      apply Matrix.ext; unfold tripleCharges sourceA2030 sourceB2030 sourceC2030 difference raw28689; decide +kernel
    rw [ha]
    exact (canonical28689 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2030 + difference 0 4) (sourceB2030 + difference 4 0) sourceC2030) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2520) := by
    have ha : (tripleCharges (sourceA2030 + difference 0 4) (sourceB2030 + difference 4 0) sourceC2030) = raw28690 := by
      apply Matrix.ext; unfold tripleCharges sourceA2030 sourceB2030 sourceC2030 difference raw28690; decide +kernel
    rw [ha]
    exact (canonical28690 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2030 + difference 0 5) (sourceB2030 + difference 5 0) sourceC2030) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2519) := by
    have ha : (tripleCharges (sourceA2030 + difference 0 5) (sourceB2030 + difference 5 0) sourceC2030) = raw28691 := by
      apply Matrix.ext; unfold tripleCharges sourceA2030 sourceB2030 sourceC2030 difference raw28691; decide +kernel
    rw [ha]
    exact (canonical28691 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2030 + difference 1 0) (sourceB2030 + difference 0 1) sourceC2030) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3186) := by
    have ha : (tripleCharges (sourceA2030 + difference 1 0) (sourceB2030 + difference 0 1) sourceC2030) = raw28692 := by
      apply Matrix.ext; unfold tripleCharges sourceA2030 sourceB2030 sourceC2030 difference raw28692; decide +kernel
    rw [ha]
    exact (canonical28692 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2030 + difference 1 2) (sourceB2030 + difference 2 1) sourceC2030) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2866) := by
    have ha : (tripleCharges (sourceA2030 + difference 1 2) (sourceB2030 + difference 2 1) sourceC2030) = raw28693 := by
      apply Matrix.ext; unfold tripleCharges sourceA2030 sourceB2030 sourceC2030 difference raw28693; decide +kernel
    rw [ha]
    exact (canonical28693 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2030 + difference 1 3) (sourceB2030 + difference 3 1) sourceC2030) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2866) := by
    have ha : (tripleCharges (sourceA2030 + difference 1 3) (sourceB2030 + difference 3 1) sourceC2030) = raw28694 := by
      apply Matrix.ext; unfold tripleCharges sourceA2030 sourceB2030 sourceC2030 difference raw28694; decide +kernel
    rw [ha]
    exact (canonical28694 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2030 + difference 1 4) (sourceB2030 + difference 4 1) sourceC2030) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2887) := by
    have ha : (tripleCharges (sourceA2030 + difference 1 4) (sourceB2030 + difference 4 1) sourceC2030) = raw28695 := by
      apply Matrix.ext; unfold tripleCharges sourceA2030 sourceB2030 sourceC2030 difference raw28695; decide +kernel
    rw [ha]
    exact (canonical28695 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2030 + difference 1 5) (sourceB2030 + difference 5 1) sourceC2030) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2886) := by
    have ha : (tripleCharges (sourceA2030 + difference 1 5) (sourceB2030 + difference 5 1) sourceC2030) = raw28696 := by
      apply Matrix.ext; unfold tripleCharges sourceA2030 sourceB2030 sourceC2030 difference raw28696; decide +kernel
    rw [ha]
    exact (canonical28696 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2030 + difference 2 0) (sourceB2030 + difference 0 2) sourceC2030) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3177) := by
    have ha : (tripleCharges (sourceA2030 + difference 2 0) (sourceB2030 + difference 0 2) sourceC2030) = raw28697 := by
      apply Matrix.ext; unfold tripleCharges sourceA2030 sourceB2030 sourceC2030 difference raw28697; decide +kernel
    rw [ha]
    exact (canonical28697 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2030 + difference 2 1) (sourceB2030 + difference 1 2) sourceC2030) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2989) := by
    have ha : (tripleCharges (sourceA2030 + difference 2 1) (sourceB2030 + difference 1 2) sourceC2030) = raw28698 := by
      apply Matrix.ext; unfold tripleCharges sourceA2030 sourceB2030 sourceC2030 difference raw28698; decide +kernel
    rw [ha]
    exact (canonical28698 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2030 + difference 2 3) (sourceB2030 + difference 3 2) sourceC2030) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2915) := by
    have ha : (tripleCharges (sourceA2030 + difference 2 3) (sourceB2030 + difference 3 2) sourceC2030) = raw28699 := by
      apply Matrix.ext; unfold tripleCharges sourceA2030 sourceB2030 sourceC2030 difference raw28699; decide +kernel
    rw [ha]
    exact (canonical28699 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2030 + difference 2 4) (sourceB2030 + difference 4 2) sourceC2030) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2929) := by
    have ha : (tripleCharges (sourceA2030 + difference 2 4) (sourceB2030 + difference 4 2) sourceC2030) = raw28700 := by
      apply Matrix.ext; unfold tripleCharges sourceA2030 sourceB2030 sourceC2030 difference raw28700; decide +kernel
    rw [ha]
    exact (canonical28700 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2030 + difference 2 5) (sourceB2030 + difference 5 2) sourceC2030) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2865) := by
    have ha : (tripleCharges (sourceA2030 + difference 2 5) (sourceB2030 + difference 5 2) sourceC2030) = raw28701 := by
      apply Matrix.ext; unfold tripleCharges sourceA2030 sourceB2030 sourceC2030 difference raw28701; decide +kernel
    rw [ha]
    exact (canonical28701 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2030 + difference 3 0) (sourceB2030 + difference 0 3) sourceC2030) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3177) := by
    have ha : (tripleCharges (sourceA2030 + difference 3 0) (sourceB2030 + difference 0 3) sourceC2030) = raw28702 := by
      apply Matrix.ext; unfold tripleCharges sourceA2030 sourceB2030 sourceC2030 difference raw28702; decide +kernel
    rw [ha]
    exact (canonical28702 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2030 + difference 3 1) (sourceB2030 + difference 1 3) sourceC2030) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2989) := by
    have ha : (tripleCharges (sourceA2030 + difference 3 1) (sourceB2030 + difference 1 3) sourceC2030) = raw28703 := by
      apply Matrix.ext; unfold tripleCharges sourceA2030 sourceB2030 sourceC2030 difference raw28703; decide +kernel
    rw [ha]
    exact (canonical28703 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2030 + difference 3 2) (sourceB2030 + difference 2 3) sourceC2030) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2915) := by
    have ha : (tripleCharges (sourceA2030 + difference 3 2) (sourceB2030 + difference 2 3) sourceC2030) = raw28704 := by
      apply Matrix.ext; unfold tripleCharges sourceA2030 sourceB2030 sourceC2030 difference raw28704; decide +kernel
    rw [ha]
    exact (canonical28704 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2030 + difference 3 4) (sourceB2030 + difference 4 3) sourceC2030) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2929) := by
    have ha : (tripleCharges (sourceA2030 + difference 3 4) (sourceB2030 + difference 4 3) sourceC2030) = raw28705 := by
      apply Matrix.ext; unfold tripleCharges sourceA2030 sourceB2030 sourceC2030 difference raw28705; decide +kernel
    rw [ha]
    exact (canonical28705 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2030 + difference 3 5) (sourceB2030 + difference 5 3) sourceC2030) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2865) := by
    have ha : (tripleCharges (sourceA2030 + difference 3 5) (sourceB2030 + difference 5 3) sourceC2030) = raw27999 := by
      apply Matrix.ext; unfold tripleCharges sourceA2030 sourceB2030 sourceC2030 difference raw27999; decide +kernel
    rw [ha]
    exact (canonical27999 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2030 + difference 4 0) (sourceB2030 + difference 0 4) sourceC2030) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3215) := by
    have ha : (tripleCharges (sourceA2030 + difference 4 0) (sourceB2030 + difference 0 4) sourceC2030) = raw28706 := by
      apply Matrix.ext; unfold tripleCharges sourceA2030 sourceB2030 sourceC2030 difference raw28706; decide +kernel
    rw [ha]
    exact (canonical28706 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2030 + difference 4 1) (sourceB2030 + difference 1 4) sourceC2030) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3004) := by
    have ha : (tripleCharges (sourceA2030 + difference 4 1) (sourceB2030 + difference 1 4) sourceC2030) = raw28707 := by
      apply Matrix.ext; unfold tripleCharges sourceA2030 sourceB2030 sourceC2030 difference raw28707; decide +kernel
    rw [ha]
    exact (canonical28707 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2030 + difference 4 2) (sourceB2030 + difference 2 4) sourceC2030) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2941) := by
    have ha : (tripleCharges (sourceA2030 + difference 4 2) (sourceB2030 + difference 2 4) sourceC2030) = raw28708 := by
      apply Matrix.ext; unfold tripleCharges sourceA2030 sourceB2030 sourceC2030 difference raw28708; decide +kernel
    rw [ha]
    exact (canonical28708 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2030 + difference 4 3) (sourceB2030 + difference 3 4) sourceC2030) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2941) := by
    have ha : (tripleCharges (sourceA2030 + difference 4 3) (sourceB2030 + difference 3 4) sourceC2030) = raw28709 := by
      apply Matrix.ext; unfold tripleCharges sourceA2030 sourceB2030 sourceC2030 difference raw28709; decide +kernel
    rw [ha]
    exact (canonical28709 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2030 + difference 4 5) (sourceB2030 + difference 5 4) sourceC2030) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2965) := by
    have ha : (tripleCharges (sourceA2030 + difference 4 5) (sourceB2030 + difference 5 4) sourceC2030) = raw27998 := by
      apply Matrix.ext; unfold tripleCharges sourceA2030 sourceB2030 sourceC2030 difference raw27998; decide +kernel
    rw [ha]
    exact (canonical27998 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2030 + difference 5 0) (sourceB2030 + difference 0 5) sourceC2030) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1417) := by
    have ha : (tripleCharges (sourceA2030 + difference 5 0) (sourceB2030 + difference 0 5) sourceC2030) = raw28710 := by
      apply Matrix.ext; unfold tripleCharges sourceA2030 sourceB2030 sourceC2030 difference raw28710; decide +kernel
    rw [ha]
    exact (canonical28710 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2030 + difference 5 1) (sourceB2030 + difference 1 5) sourceC2030) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1449) := by
    have ha : (tripleCharges (sourceA2030 + difference 5 1) (sourceB2030 + difference 1 5) sourceC2030) = raw28711 := by
      apply Matrix.ext; unfold tripleCharges sourceA2030 sourceB2030 sourceC2030 difference raw28711; decide +kernel
    rw [ha]
    exact (canonical28711 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2030 + difference 5 2) (sourceB2030 + difference 2 5) sourceC2030) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1415) := by
    have ha : (tripleCharges (sourceA2030 + difference 5 2) (sourceB2030 + difference 2 5) sourceC2030) = raw28712 := by
      apply Matrix.ext; unfold tripleCharges sourceA2030 sourceB2030 sourceC2030 difference raw28712; decide +kernel
    rw [ha]
    exact (canonical28712 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2030 + difference 5 3) (sourceB2030 + difference 3 5) sourceC2030) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1415) := by
    have ha : (tripleCharges (sourceA2030 + difference 5 3) (sourceB2030 + difference 3 5) sourceC2030) = raw28713 := by
      apply Matrix.ext; unfold tripleCharges sourceA2030 sourceB2030 sourceC2030 difference raw28713; decide +kernel
    rw [ha]
    exact (canonical28713 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2030 + difference 5 4) (sourceB2030 + difference 4 5) sourceC2030) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1418) := by
    have ha : (tripleCharges (sourceA2030 + difference 5 4) (sourceB2030 + difference 4 5) sourceC2030) = raw28714 := by
      apply Matrix.ext; unfold tripleCharges sourceA2030 sourceB2030 sourceC2030 difference raw28714; decide +kernel
    rw [ha]
    exact (canonical28714 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2030 sourceB2030 sourceC2030
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2030, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2031 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2031 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC2031 : Charge := ![2, 0, 0, 1, -1, -2]
def sourceForm2031 : Integer.Sparse Master := [(Sum.inr 4527, 1), (Sum.inr 4528, 1), (Sum.inr 4531, 1), (Sum.inr 4534, 1), (Sum.inr 4535, 1), (Sum.inr 4546, 1), (Sum.inr 4547, 1), (Sum.inr 4591, 1), (Sum.inr 4608, 1), (Sum.inr 4929, 1), (Sum.inr 4934, 1), (Sum.inr 4943, 1), (Sum.inr 4954, 1), (Sum.inr 4965, 1), (Sum.inr 5033, 1), (Sum.inr 5041, 1), (Sum.inr 5072, 1), (Sum.inr 5075, 1), (Sum.inr 5080, 1), (Sum.inr 5101, 1), (Sum.inr 5107, 1), (Sum.inr 5127, 1), (Sum.inr 5134, 1), (Sum.inr 5141, 1), (Sum.inr 5147, 1), (Sum.inr 5163, 1), (Sum.inr 5258, 1), (Sum.inr 5261, 1), (Sum.inr 5274, 1), (Sum.inr 5409, 1)]

theorem sourceEq2031 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2031 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2031 + difference 0 1) (sourceB2031 + difference 1 0) sourceC2031) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5080) := by
    have ha : (tripleCharges (sourceA2031 + difference 0 1) (sourceB2031 + difference 1 0) sourceC2031) = raw18331 := by
      apply Matrix.ext; unfold tripleCharges sourceA2031 sourceB2031 sourceC2031 difference raw18331; decide +kernel
    rw [ha]
    exact (canonical18331 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2031 + difference 0 2) (sourceB2031 + difference 2 0) sourceC2031) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5072) := by
    have ha : (tripleCharges (sourceA2031 + difference 0 2) (sourceB2031 + difference 2 0) sourceC2031) = raw18332 := by
      apply Matrix.ext; unfold tripleCharges sourceA2031 sourceB2031 sourceC2031 difference raw18332; decide +kernel
    rw [ha]
    exact (canonical18332 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2031 + difference 0 3) (sourceB2031 + difference 3 0) sourceC2031) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5101) := by
    have ha : (tripleCharges (sourceA2031 + difference 0 3) (sourceB2031 + difference 3 0) sourceC2031) = raw18333 := by
      apply Matrix.ext; unfold tripleCharges sourceA2031 sourceB2031 sourceC2031 difference raw18333; decide +kernel
    rw [ha]
    exact (canonical18333 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2031 + difference 0 4) (sourceB2031 + difference 4 0) sourceC2031) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA2031 + difference 0 4) (sourceB2031 + difference 4 0) sourceC2031) = raw18334 := by
      apply Matrix.ext; unfold tripleCharges sourceA2031 sourceB2031 sourceC2031 difference raw18334; decide +kernel
    rw [ha]
    exact (canonical18334 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2031 + difference 0 5) (sourceB2031 + difference 5 0) sourceC2031) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5409) := by
    have ha : (tripleCharges (sourceA2031 + difference 0 5) (sourceB2031 + difference 5 0) sourceC2031) = raw10539 := by
      apply Matrix.ext; unfold tripleCharges sourceA2031 sourceB2031 sourceC2031 difference raw10539; decide +kernel
    rw [ha]
    exact (canonical10539 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2031 + difference 1 0) (sourceB2031 + difference 0 1) sourceC2031) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4608) := by
    have ha : (tripleCharges (sourceA2031 + difference 1 0) (sourceB2031 + difference 0 1) sourceC2031) = raw10564 := by
      apply Matrix.ext; unfold tripleCharges sourceA2031 sourceB2031 sourceC2031 difference raw10564; decide +kernel
    rw [ha]
    exact (canonical10564 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2031 + difference 1 2) (sourceB2031 + difference 2 1) sourceC2031) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA2031 + difference 1 2) (sourceB2031 + difference 2 1) sourceC2031) = raw10566 := by
      apply Matrix.ext; unfold tripleCharges sourceA2031 sourceB2031 sourceC2031 difference raw10566; decide +kernel
    rw [ha]
    exact (canonical10566 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2031 + difference 1 3) (sourceB2031 + difference 3 1) sourceC2031) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5107) := by
    have ha : (tripleCharges (sourceA2031 + difference 1 3) (sourceB2031 + difference 3 1) sourceC2031) = raw10567 := by
      apply Matrix.ext; unfold tripleCharges sourceA2031 sourceB2031 sourceC2031 difference raw10567; decide +kernel
    rw [ha]
    exact (canonical10567 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2031 + difference 1 4) (sourceB2031 + difference 4 1) sourceC2031) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5261) := by
    have ha : (tripleCharges (sourceA2031 + difference 1 4) (sourceB2031 + difference 4 1) sourceC2031) = raw10568 := by
      apply Matrix.ext; unfold tripleCharges sourceA2031 sourceB2031 sourceC2031 difference raw10568; decide +kernel
    rw [ha]
    exact (canonical10568 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2031 + difference 1 5) (sourceB2031 + difference 5 1) sourceC2031) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5274) := by
    have ha : (tripleCharges (sourceA2031 + difference 1 5) (sourceB2031 + difference 5 1) sourceC2031) = raw18318 := by
      apply Matrix.ext; unfold tripleCharges sourceA2031 sourceB2031 sourceC2031 difference raw18318; decide +kernel
    rw [ha]
    exact (canonical18318 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2031 + difference 2 0) (sourceB2031 + difference 0 2) sourceC2031) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4528) := by
    have ha : (tripleCharges (sourceA2031 + difference 2 0) (sourceB2031 + difference 0 2) sourceC2031) = raw20656 := by
      apply Matrix.ext; unfold tripleCharges sourceA2031 sourceB2031 sourceC2031 difference raw20656; decide +kernel
    rw [ha]
    exact (canonical20656 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2031 + difference 2 1) (sourceB2031 + difference 1 2) sourceC2031) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4954) := by
    have ha : (tripleCharges (sourceA2031 + difference 2 1) (sourceB2031 + difference 1 2) sourceC2031) = raw28715 := by
      apply Matrix.ext; unfold tripleCharges sourceA2031 sourceB2031 sourceC2031 difference raw28715; decide +kernel
    rw [ha]
    exact (canonical28715 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2031 + difference 2 3) (sourceB2031 + difference 3 2) sourceC2031) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5033) := by
    have ha : (tripleCharges (sourceA2031 + difference 2 3) (sourceB2031 + difference 3 2) sourceC2031) = raw28716 := by
      apply Matrix.ext; unfold tripleCharges sourceA2031 sourceB2031 sourceC2031 difference raw28716; decide +kernel
    rw [ha]
    exact (canonical28716 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2031 + difference 2 4) (sourceB2031 + difference 4 2) sourceC2031) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5127) := by
    have ha : (tripleCharges (sourceA2031 + difference 2 4) (sourceB2031 + difference 4 2) sourceC2031) = raw28717 := by
      apply Matrix.ext; unfold tripleCharges sourceA2031 sourceB2031 sourceC2031 difference raw28717; decide +kernel
    rw [ha]
    exact (canonical28717 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2031 + difference 2 5) (sourceB2031 + difference 5 2) sourceC2031) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5134) := by
    have ha : (tripleCharges (sourceA2031 + difference 2 5) (sourceB2031 + difference 5 2) sourceC2031) = raw10550 := by
      apply Matrix.ext; unfold tripleCharges sourceA2031 sourceB2031 sourceC2031 difference raw10550; decide +kernel
    rw [ha]
    exact (canonical10550 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2031 + difference 3 0) (sourceB2031 + difference 0 3) sourceC2031) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4547) := by
    have ha : (tripleCharges (sourceA2031 + difference 3 0) (sourceB2031 + difference 0 3) sourceC2031) = raw20660 := by
      apply Matrix.ext; unfold tripleCharges sourceA2031 sourceB2031 sourceC2031 difference raw20660; decide +kernel
    rw [ha]
    exact (canonical20660 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2031 + difference 3 1) (sourceB2031 + difference 1 3) sourceC2031) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4965) := by
    have ha : (tripleCharges (sourceA2031 + difference 3 1) (sourceB2031 + difference 1 3) sourceC2031) = raw28718 := by
      apply Matrix.ext; unfold tripleCharges sourceA2031 sourceB2031 sourceC2031 difference raw28718; decide +kernel
    rw [ha]
    exact (canonical28718 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2031 + difference 3 2) (sourceB2031 + difference 2 3) sourceC2031) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5041) := by
    have ha : (tripleCharges (sourceA2031 + difference 3 2) (sourceB2031 + difference 2 3) sourceC2031) = raw28719 := by
      apply Matrix.ext; unfold tripleCharges sourceA2031 sourceB2031 sourceC2031 difference raw28719; decide +kernel
    rw [ha]
    exact (canonical28719 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2031 + difference 3 4) (sourceB2031 + difference 4 3) sourceC2031) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5147) := by
    have ha : (tripleCharges (sourceA2031 + difference 3 4) (sourceB2031 + difference 4 3) sourceC2031) = raw28720 := by
      apply Matrix.ext; unfold tripleCharges sourceA2031 sourceB2031 sourceC2031 difference raw28720; decide +kernel
    rw [ha]
    exact (canonical28720 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2031 + difference 3 5) (sourceB2031 + difference 5 3) sourceC2031) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5163) := by
    have ha : (tripleCharges (sourceA2031 + difference 3 5) (sourceB2031 + difference 5 3) sourceC2031) = raw10555 := by
      apply Matrix.ext; unfold tripleCharges sourceA2031 sourceB2031 sourceC2031 difference raw10555; decide +kernel
    rw [ha]
    exact (canonical10555 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2031 + difference 4 0) (sourceB2031 + difference 0 4) sourceC2031) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4535) := by
    have ha : (tripleCharges (sourceA2031 + difference 4 0) (sourceB2031 + difference 0 4) sourceC2031) = raw20664 := by
      apply Matrix.ext; unfold tripleCharges sourceA2031 sourceB2031 sourceC2031 difference raw20664; decide +kernel
    rw [ha]
    exact (canonical20664 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2031 + difference 4 1) (sourceB2031 + difference 1 4) sourceC2031) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4934) := by
    have ha : (tripleCharges (sourceA2031 + difference 4 1) (sourceB2031 + difference 1 4) sourceC2031) = raw28721 := by
      apply Matrix.ext; unfold tripleCharges sourceA2031 sourceB2031 sourceC2031 difference raw28721; decide +kernel
    rw [ha]
    exact (canonical28721 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2031 + difference 4 2) (sourceB2031 + difference 2 4) sourceC2031) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4929) := by
    have ha : (tripleCharges (sourceA2031 + difference 4 2) (sourceB2031 + difference 2 4) sourceC2031) = raw28722 := by
      apply Matrix.ext; unfold tripleCharges sourceA2031 sourceB2031 sourceC2031 difference raw28722; decide +kernel
    rw [ha]
    exact (canonical28722 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2031 + difference 4 3) (sourceB2031 + difference 3 4) sourceC2031) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4943) := by
    have ha : (tripleCharges (sourceA2031 + difference 4 3) (sourceB2031 + difference 3 4) sourceC2031) = raw28723 := by
      apply Matrix.ext; unfold tripleCharges sourceA2031 sourceB2031 sourceC2031 difference raw28723; decide +kernel
    rw [ha]
    exact (canonical28723 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2031 + difference 4 5) (sourceB2031 + difference 5 4) sourceC2031) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA2031 + difference 4 5) (sourceB2031 + difference 5 4) sourceC2031) = raw10560 := by
      apply Matrix.ext; unfold tripleCharges sourceA2031 sourceB2031 sourceC2031 difference raw10560; decide +kernel
    rw [ha]
    exact (canonical10560 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2031 + difference 5 0) (sourceB2031 + difference 0 5) sourceC2031) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4531) := by
    have ha : (tripleCharges (sourceA2031 + difference 5 0) (sourceB2031 + difference 0 5) sourceC2031) = raw20668 := by
      apply Matrix.ext; unfold tripleCharges sourceA2031 sourceB2031 sourceC2031 difference raw20668; decide +kernel
    rw [ha]
    exact (canonical20668 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2031 + difference 5 1) (sourceB2031 + difference 1 5) sourceC2031) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4534) := by
    have ha : (tripleCharges (sourceA2031 + difference 5 1) (sourceB2031 + difference 1 5) sourceC2031) = raw28724 := by
      apply Matrix.ext; unfold tripleCharges sourceA2031 sourceB2031 sourceC2031 difference raw28724; decide +kernel
    rw [ha]
    exact (canonical28724 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2031 + difference 5 2) (sourceB2031 + difference 2 5) sourceC2031) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4527) := by
    have ha : (tripleCharges (sourceA2031 + difference 5 2) (sourceB2031 + difference 2 5) sourceC2031) = raw28725 := by
      apply Matrix.ext; unfold tripleCharges sourceA2031 sourceB2031 sourceC2031 difference raw28725; decide +kernel
    rw [ha]
    exact (canonical28725 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2031 + difference 5 3) (sourceB2031 + difference 3 5) sourceC2031) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4546) := by
    have ha : (tripleCharges (sourceA2031 + difference 5 3) (sourceB2031 + difference 3 5) sourceC2031) = raw28726 := by
      apply Matrix.ext; unfold tripleCharges sourceA2031 sourceB2031 sourceC2031 difference raw28726; decide +kernel
    rw [ha]
    exact (canonical28726 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2031 + difference 5 4) (sourceB2031 + difference 4 5) sourceC2031) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4591) := by
    have ha : (tripleCharges (sourceA2031 + difference 5 4) (sourceB2031 + difference 4 5) sourceC2031) = raw28727 := by
      apply Matrix.ext; unfold tripleCharges sourceA2031 sourceB2031 sourceC2031 difference raw28727; decide +kernel
    rw [ha]
    exact (canonical28727 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2031 sourceB2031 sourceC2031
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2031, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2032 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2032 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC2032 : Charge := ![2, 0, 0, 1, -1, -2]
def sourceForm2032 : Integer.Sparse Master := [(Sum.inr 3255, 1), (Sum.inr 3260, 1), (Sum.inr 3262, 1), (Sum.inr 3264, 1), (Sum.inr 3266, 1), (Sum.inr 3268, 1), (Sum.inr 3272, 1), (Sum.inr 3291, 1), (Sum.inr 3300, 1), (Sum.inr 3403, 1), (Sum.inr 3411, 1), (Sum.inr 3415, 1), (Sum.inr 3449, 1), (Sum.inr 3452, 1), (Sum.inr 3458, 1), (Sum.inr 3459, 1), (Sum.inr 3468, 1), (Sum.inr 3470, 1), (Sum.inr 3475, 1), (Sum.inr 3478, 1), (Sum.inr 3484, 1), (Sum.inr 3513, 1), (Sum.inr 3514, 1), (Sum.inr 3522, 1), (Sum.inr 3530, 1), (Sum.inr 3533, 1), (Sum.inr 3545, 1), (Sum.inr 3547, 1), (Sum.inr 3564, 1), (Sum.inr 3807, 1)]

theorem sourceEq2032 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2032 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2032 + difference 0 1) (sourceB2032 + difference 1 0) sourceC2032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3478) := by
    have ha : (tripleCharges (sourceA2032 + difference 0 1) (sourceB2032 + difference 1 0) sourceC2032) = raw28728 := by
      apply Matrix.ext; unfold tripleCharges sourceA2032 sourceB2032 sourceC2032 difference raw28728; decide +kernel
    rw [ha]
    exact (canonical28728 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2032 + difference 0 2) (sourceB2032 + difference 2 0) sourceC2032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3459) := by
    have ha : (tripleCharges (sourceA2032 + difference 0 2) (sourceB2032 + difference 2 0) sourceC2032) = raw28729 := by
      apply Matrix.ext; unfold tripleCharges sourceA2032 sourceB2032 sourceC2032 difference raw28729; decide +kernel
    rw [ha]
    exact (canonical28729 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2032 + difference 0 3) (sourceB2032 + difference 3 0) sourceC2032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3470) := by
    have ha : (tripleCharges (sourceA2032 + difference 0 3) (sourceB2032 + difference 3 0) sourceC2032) = raw28730 := by
      apply Matrix.ext; unfold tripleCharges sourceA2032 sourceB2032 sourceC2032 difference raw28730; decide +kernel
    rw [ha]
    exact (canonical28730 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2032 + difference 0 4) (sourceB2032 + difference 4 0) sourceC2032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3533) := by
    have ha : (tripleCharges (sourceA2032 + difference 0 4) (sourceB2032 + difference 4 0) sourceC2032) = raw28731 := by
      apply Matrix.ext; unfold tripleCharges sourceA2032 sourceB2032 sourceC2032 difference raw28731; decide +kernel
    rw [ha]
    exact (canonical28731 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2032 + difference 0 5) (sourceB2032 + difference 5 0) sourceC2032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3807) := by
    have ha : (tripleCharges (sourceA2032 + difference 0 5) (sourceB2032 + difference 5 0) sourceC2032) = raw28732 := by
      apply Matrix.ext; unfold tripleCharges sourceA2032 sourceB2032 sourceC2032 difference raw28732; decide +kernel
    rw [ha]
    exact (canonical28732 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2032 + difference 1 0) (sourceB2032 + difference 0 1) sourceC2032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3300) := by
    have ha : (tripleCharges (sourceA2032 + difference 1 0) (sourceB2032 + difference 0 1) sourceC2032) = raw28733 := by
      apply Matrix.ext; unfold tripleCharges sourceA2032 sourceB2032 sourceC2032 difference raw28733; decide +kernel
    rw [ha]
    exact (canonical28733 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2032 + difference 1 2) (sourceB2032 + difference 2 1) sourceC2032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3468) := by
    have ha : (tripleCharges (sourceA2032 + difference 1 2) (sourceB2032 + difference 2 1) sourceC2032) = raw20703 := by
      apply Matrix.ext; unfold tripleCharges sourceA2032 sourceB2032 sourceC2032 difference raw20703; decide +kernel
    rw [ha]
    exact (canonical20703 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2032 + difference 1 3) (sourceB2032 + difference 3 1) sourceC2032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3484) := by
    have ha : (tripleCharges (sourceA2032 + difference 1 3) (sourceB2032 + difference 3 1) sourceC2032) = raw20704 := by
      apply Matrix.ext; unfold tripleCharges sourceA2032 sourceB2032 sourceC2032 difference raw20704; decide +kernel
    rw [ha]
    exact (canonical20704 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2032 + difference 1 4) (sourceB2032 + difference 4 1) sourceC2032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3545) := by
    have ha : (tripleCharges (sourceA2032 + difference 1 4) (sourceB2032 + difference 4 1) sourceC2032) = raw20705 := by
      apply Matrix.ext; unfold tripleCharges sourceA2032 sourceB2032 sourceC2032 difference raw20705; decide +kernel
    rw [ha]
    exact (canonical20705 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2032 + difference 1 5) (sourceB2032 + difference 5 1) sourceC2032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3547) := by
    have ha : (tripleCharges (sourceA2032 + difference 1 5) (sourceB2032 + difference 5 1) sourceC2032) = raw20706 := by
      apply Matrix.ext; unfold tripleCharges sourceA2032 sourceB2032 sourceC2032 difference raw20706; decide +kernel
    rw [ha]
    exact (canonical20706 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2032 + difference 2 0) (sourceB2032 + difference 0 2) sourceC2032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3260) := by
    have ha : (tripleCharges (sourceA2032 + difference 2 0) (sourceB2032 + difference 0 2) sourceC2032) = raw20713 := by
      apply Matrix.ext; unfold tripleCharges sourceA2032 sourceB2032 sourceC2032 difference raw20713; decide +kernel
    rw [ha]
    exact (canonical20713 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2032 + difference 2 1) (sourceB2032 + difference 1 2) sourceC2032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3452) := by
    have ha : (tripleCharges (sourceA2032 + difference 2 1) (sourceB2032 + difference 1 2) sourceC2032) = raw28734 := by
      apply Matrix.ext; unfold tripleCharges sourceA2032 sourceB2032 sourceC2032 difference raw28734; decide +kernel
    rw [ha]
    exact (canonical28734 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2032 + difference 2 3) (sourceB2032 + difference 3 2) sourceC2032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3449) := by
    have ha : (tripleCharges (sourceA2032 + difference 2 3) (sourceB2032 + difference 3 2) sourceC2032) = raw28735 := by
      apply Matrix.ext; unfold tripleCharges sourceA2032 sourceB2032 sourceC2032 difference raw28735; decide +kernel
    rw [ha]
    exact (canonical28735 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2032 + difference 2 4) (sourceB2032 + difference 4 2) sourceC2032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3513) := by
    have ha : (tripleCharges (sourceA2032 + difference 2 4) (sourceB2032 + difference 4 2) sourceC2032) = raw28736 := by
      apply Matrix.ext; unfold tripleCharges sourceA2032 sourceB2032 sourceC2032 difference raw28736; decide +kernel
    rw [ha]
    exact (canonical28736 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2032 + difference 2 5) (sourceB2032 + difference 5 2) sourceC2032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3514) := by
    have ha : (tripleCharges (sourceA2032 + difference 2 5) (sourceB2032 + difference 5 2) sourceC2032) = raw28737 := by
      apply Matrix.ext; unfold tripleCharges sourceA2032 sourceB2032 sourceC2032 difference raw28737; decide +kernel
    rw [ha]
    exact (canonical28737 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2032 + difference 3 0) (sourceB2032 + difference 0 3) sourceC2032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3266) := by
    have ha : (tripleCharges (sourceA2032 + difference 3 0) (sourceB2032 + difference 0 3) sourceC2032) = raw20718 := by
      apply Matrix.ext; unfold tripleCharges sourceA2032 sourceB2032 sourceC2032 difference raw20718; decide +kernel
    rw [ha]
    exact (canonical20718 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2032 + difference 3 1) (sourceB2032 + difference 1 3) sourceC2032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3475) := by
    have ha : (tripleCharges (sourceA2032 + difference 3 1) (sourceB2032 + difference 1 3) sourceC2032) = raw28738 := by
      apply Matrix.ext; unfold tripleCharges sourceA2032 sourceB2032 sourceC2032 difference raw28738; decide +kernel
    rw [ha]
    exact (canonical28738 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2032 + difference 3 2) (sourceB2032 + difference 2 3) sourceC2032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3458) := by
    have ha : (tripleCharges (sourceA2032 + difference 3 2) (sourceB2032 + difference 2 3) sourceC2032) = raw28739 := by
      apply Matrix.ext; unfold tripleCharges sourceA2032 sourceB2032 sourceC2032 difference raw28739; decide +kernel
    rw [ha]
    exact (canonical28739 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2032 + difference 3 4) (sourceB2032 + difference 4 3) sourceC2032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3530) := by
    have ha : (tripleCharges (sourceA2032 + difference 3 4) (sourceB2032 + difference 4 3) sourceC2032) = raw28740 := by
      apply Matrix.ext; unfold tripleCharges sourceA2032 sourceB2032 sourceC2032 difference raw28740; decide +kernel
    rw [ha]
    exact (canonical28740 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2032 + difference 3 5) (sourceB2032 + difference 5 3) sourceC2032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3564) := by
    have ha : (tripleCharges (sourceA2032 + difference 3 5) (sourceB2032 + difference 5 3) sourceC2032) = raw28741 := by
      apply Matrix.ext; unfold tripleCharges sourceA2032 sourceB2032 sourceC2032 difference raw28741; decide +kernel
    rw [ha]
    exact (canonical28741 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2032 + difference 4 0) (sourceB2032 + difference 0 4) sourceC2032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3272) := by
    have ha : (tripleCharges (sourceA2032 + difference 4 0) (sourceB2032 + difference 0 4) sourceC2032) = raw20723 := by
      apply Matrix.ext; unfold tripleCharges sourceA2032 sourceB2032 sourceC2032 difference raw20723; decide +kernel
    rw [ha]
    exact (canonical20723 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2032 + difference 4 1) (sourceB2032 + difference 1 4) sourceC2032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3415) := by
    have ha : (tripleCharges (sourceA2032 + difference 4 1) (sourceB2032 + difference 1 4) sourceC2032) = raw28742 := by
      apply Matrix.ext; unfold tripleCharges sourceA2032 sourceB2032 sourceC2032 difference raw28742; decide +kernel
    rw [ha]
    exact (canonical28742 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2032 + difference 4 2) (sourceB2032 + difference 2 4) sourceC2032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3403) := by
    have ha : (tripleCharges (sourceA2032 + difference 4 2) (sourceB2032 + difference 2 4) sourceC2032) = raw28743 := by
      apply Matrix.ext; unfold tripleCharges sourceA2032 sourceB2032 sourceC2032 difference raw28743; decide +kernel
    rw [ha]
    exact (canonical28743 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2032 + difference 4 3) (sourceB2032 + difference 3 4) sourceC2032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3411) := by
    have ha : (tripleCharges (sourceA2032 + difference 4 3) (sourceB2032 + difference 3 4) sourceC2032) = raw28744 := by
      apply Matrix.ext; unfold tripleCharges sourceA2032 sourceB2032 sourceC2032 difference raw28744; decide +kernel
    rw [ha]
    exact (canonical28744 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2032 + difference 4 5) (sourceB2032 + difference 5 4) sourceC2032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3522) := by
    have ha : (tripleCharges (sourceA2032 + difference 4 5) (sourceB2032 + difference 5 4) sourceC2032) = raw28745 := by
      apply Matrix.ext; unfold tripleCharges sourceA2032 sourceB2032 sourceC2032 difference raw28745; decide +kernel
    rw [ha]
    exact (canonical28745 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2032 + difference 5 0) (sourceB2032 + difference 0 5) sourceC2032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3262) := by
    have ha : (tripleCharges (sourceA2032 + difference 5 0) (sourceB2032 + difference 0 5) sourceC2032) = raw20728 := by
      apply Matrix.ext; unfold tripleCharges sourceA2032 sourceB2032 sourceC2032 difference raw20728; decide +kernel
    rw [ha]
    exact (canonical20728 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2032 + difference 5 1) (sourceB2032 + difference 1 5) sourceC2032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3268) := by
    have ha : (tripleCharges (sourceA2032 + difference 5 1) (sourceB2032 + difference 1 5) sourceC2032) = raw28746 := by
      apply Matrix.ext; unfold tripleCharges sourceA2032 sourceB2032 sourceC2032 difference raw28746; decide +kernel
    rw [ha]
    exact (canonical28746 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2032 + difference 5 2) (sourceB2032 + difference 2 5) sourceC2032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3255) := by
    have ha : (tripleCharges (sourceA2032 + difference 5 2) (sourceB2032 + difference 2 5) sourceC2032) = raw28747 := by
      apply Matrix.ext; unfold tripleCharges sourceA2032 sourceB2032 sourceC2032 difference raw28747; decide +kernel
    rw [ha]
    exact (canonical28747 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2032 + difference 5 3) (sourceB2032 + difference 3 5) sourceC2032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3264) := by
    have ha : (tripleCharges (sourceA2032 + difference 5 3) (sourceB2032 + difference 3 5) sourceC2032) = raw28748 := by
      apply Matrix.ext; unfold tripleCharges sourceA2032 sourceB2032 sourceC2032 difference raw28748; decide +kernel
    rw [ha]
    exact (canonical28748 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2032 + difference 5 4) (sourceB2032 + difference 4 5) sourceC2032) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3291) := by
    have ha : (tripleCharges (sourceA2032 + difference 5 4) (sourceB2032 + difference 4 5) sourceC2032) = raw28749 := by
      apply Matrix.ext; unfold tripleCharges sourceA2032 sourceB2032 sourceC2032 difference raw28749; decide +kernel
    rw [ha]
    exact (canonical28749 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2032 sourceB2032 sourceC2032
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2032, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2033 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2033 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC2033 : Charge := ![2, 0, 0, 1, -1, -2]
def sourceForm2033 : Integer.Sparse Master := [(Sum.inr 1119, 1), (Sum.inr 2325, 1), (Sum.inr 2347, 1), (Sum.inr 2355, 1), (Sum.inr 2482, 1), (Sum.inr 2488, 1), (Sum.inr 4092, -1)]

theorem sourceEq2033 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2033 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2033 + difference 0 1) (sourceB2033 + difference 1 0) sourceC2033) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2488) := by
    have ha : (tripleCharges (sourceA2033 + difference 0 1) (sourceB2033 + difference 1 0) sourceC2033) = raw28750 := by
      apply Matrix.ext; unfold tripleCharges sourceA2033 sourceB2033 sourceC2033 difference raw28750; decide +kernel
    rw [ha]
    exact (canonical28750 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2033 + difference 1 1) (sourceB2033 + difference 1 1) sourceC2033) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2482) := by
    have ha : (tripleCharges (sourceA2033 + difference 1 1) (sourceB2033 + difference 1 1) sourceC2033) = raw20739 := by
      apply Matrix.ext; unfold tripleCharges sourceA2033 sourceB2033 sourceC2033 difference raw20739; decide +kernel
    rw [ha]
    exact (canonical20739 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2033 + difference 2 1) (sourceB2033 + difference 1 2) sourceC2033) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2347) := by
    have ha : (tripleCharges (sourceA2033 + difference 2 1) (sourceB2033 + difference 1 2) sourceC2033) = raw28751 := by
      apply Matrix.ext; unfold tripleCharges sourceA2033 sourceB2033 sourceC2033 difference raw28751; decide +kernel
    rw [ha]
    exact (canonical28751 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2033 + difference 3 1) (sourceB2033 + difference 1 3) sourceC2033) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2355) := by
    have ha : (tripleCharges (sourceA2033 + difference 3 1) (sourceB2033 + difference 1 3) sourceC2033) = raw28752 := by
      apply Matrix.ext; unfold tripleCharges sourceA2033 sourceB2033 sourceC2033 difference raw28752; decide +kernel
    rw [ha]
    exact (canonical28752 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2033 + difference 4 1) (sourceB2033 + difference 1 4) sourceC2033) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2325) := by
    have ha : (tripleCharges (sourceA2033 + difference 4 1) (sourceB2033 + difference 1 4) sourceC2033) = raw28753 := by
      apply Matrix.ext; unfold tripleCharges sourceA2033 sourceB2033 sourceC2033 difference raw28753; decide +kernel
    rw [ha]
    exact (canonical28753 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2033 + difference 5 1) (sourceB2033 + difference 1 5) sourceC2033) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1119) := by
    have ha : (tripleCharges (sourceA2033 + difference 5 1) (sourceB2033 + difference 1 5) sourceC2033) = raw28754 := by
      apply Matrix.ext; unfold tripleCharges sourceA2033 sourceB2033 sourceC2033 difference raw28754; decide +kernel
    rw [ha]
    exact (canonical28754 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2033 + sourceB2033) sourceC2033) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2033 + sourceB2033) sourceC2033) = raw20738 := by
      apply Matrix.ext; unfold doubleCharges sourceA2033 sourceB2033 sourceC2033 raw20738; decide +kernel
    rw [ha]
    exact (canonical20738 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2033 sourceB2033 sourceC2033
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2033, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2034 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2034 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC2034 : Charge := ![2, 0, 0, 1, -1, -2]
def sourceForm2034 : Integer.Sparse Master := [(Sum.inr 1111, 1), (Sum.inr 2319, 1), (Sum.inr 2436, 1), (Sum.inr 2479, 1), (Sum.inr 2482, 2), (Sum.inr 4092, -1)]

theorem sourceEq2034 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2034 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2034 + difference 0 2) (sourceB2034 + difference 2 0) sourceC2034) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2479) := by
    have ha : (tripleCharges (sourceA2034 + difference 0 2) (sourceB2034 + difference 2 0) sourceC2034) = raw28755 := by
      apply Matrix.ext; unfold tripleCharges sourceA2034 sourceB2034 sourceC2034 difference raw28755; decide +kernel
    rw [ha]
    exact (canonical28755 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2034 + difference 1 2) (sourceB2034 + difference 2 1) sourceC2034) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2482) := by
    have ha : (tripleCharges (sourceA2034 + difference 1 2) (sourceB2034 + difference 2 1) sourceC2034) = raw28756 := by
      apply Matrix.ext; unfold tripleCharges sourceA2034 sourceB2034 sourceC2034 difference raw28756; decide +kernel
    rw [ha]
    exact (canonical28756 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2034 + difference 2 2) (sourceB2034 + difference 2 2) sourceC2034) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2482) := by
    have ha : (tripleCharges (sourceA2034 + difference 2 2) (sourceB2034 + difference 2 2) sourceC2034) = raw20739 := by
      apply Matrix.ext; unfold tripleCharges sourceA2034 sourceB2034 sourceC2034 difference raw20739; decide +kernel
    rw [ha]
    exact (canonical20739 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2034 + difference 3 2) (sourceB2034 + difference 2 3) sourceC2034) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2436) := by
    have ha : (tripleCharges (sourceA2034 + difference 3 2) (sourceB2034 + difference 2 3) sourceC2034) = raw28757 := by
      apply Matrix.ext; unfold tripleCharges sourceA2034 sourceB2034 sourceC2034 difference raw28757; decide +kernel
    rw [ha]
    exact (canonical28757 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2034 + difference 4 2) (sourceB2034 + difference 2 4) sourceC2034) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2319) := by
    have ha : (tripleCharges (sourceA2034 + difference 4 2) (sourceB2034 + difference 2 4) sourceC2034) = raw28758 := by
      apply Matrix.ext; unfold tripleCharges sourceA2034 sourceB2034 sourceC2034 difference raw28758; decide +kernel
    rw [ha]
    exact (canonical28758 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2034 + difference 5 2) (sourceB2034 + difference 2 5) sourceC2034) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1111) := by
    have ha : (tripleCharges (sourceA2034 + difference 5 2) (sourceB2034 + difference 2 5) sourceC2034) = raw28759 := by
      apply Matrix.ext; unfold tripleCharges sourceA2034 sourceB2034 sourceC2034 difference raw28759; decide +kernel
    rw [ha]
    exact (canonical28759 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2034 + sourceB2034) sourceC2034) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2034 + sourceB2034) sourceC2034) = raw20738 := by
      apply Matrix.ext; unfold doubleCharges sourceA2034 sourceB2034 sourceC2034 raw20738; decide +kernel
    rw [ha]
    exact (canonical20738 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2034 sourceB2034 sourceC2034
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2034, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2035 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2035 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC2035 : Charge := ![2, 0, 0, 1, -1, -2]
def sourceForm2035 : Integer.Sparse Master := [(Sum.inr 1131, 1), (Sum.inr 2334, 1), (Sum.inr 2425, 1), (Sum.inr 2482, 1), (Sum.inr 2511, 1), (Sum.inr 2517, 1), (Sum.inr 4092, -1)]

theorem sourceEq2035 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2035 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2035 + difference 0 3) (sourceB2035 + difference 3 0) sourceC2035) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2511) := by
    have ha : (tripleCharges (sourceA2035 + difference 0 3) (sourceB2035 + difference 3 0) sourceC2035) = raw28760 := by
      apply Matrix.ext; unfold tripleCharges sourceA2035 sourceB2035 sourceC2035 difference raw28760; decide +kernel
    rw [ha]
    exact (canonical28760 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2035 + difference 1 3) (sourceB2035 + difference 3 1) sourceC2035) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2517) := by
    have ha : (tripleCharges (sourceA2035 + difference 1 3) (sourceB2035 + difference 3 1) sourceC2035) = raw20744 := by
      apply Matrix.ext; unfold tripleCharges sourceA2035 sourceB2035 sourceC2035 difference raw20744; decide +kernel
    rw [ha]
    exact (canonical20744 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2035 + difference 2 3) (sourceB2035 + difference 3 2) sourceC2035) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2425) := by
    have ha : (tripleCharges (sourceA2035 + difference 2 3) (sourceB2035 + difference 3 2) sourceC2035) = raw28761 := by
      apply Matrix.ext; unfold tripleCharges sourceA2035 sourceB2035 sourceC2035 difference raw28761; decide +kernel
    rw [ha]
    exact (canonical28761 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2035 + difference 3 3) (sourceB2035 + difference 3 3) sourceC2035) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2482) := by
    have ha : (tripleCharges (sourceA2035 + difference 3 3) (sourceB2035 + difference 3 3) sourceC2035) = raw20739 := by
      apply Matrix.ext; unfold tripleCharges sourceA2035 sourceB2035 sourceC2035 difference raw20739; decide +kernel
    rw [ha]
    exact (canonical20739 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2035 + difference 4 3) (sourceB2035 + difference 3 4) sourceC2035) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2334) := by
    have ha : (tripleCharges (sourceA2035 + difference 4 3) (sourceB2035 + difference 3 4) sourceC2035) = raw28762 := by
      apply Matrix.ext; unfold tripleCharges sourceA2035 sourceB2035 sourceC2035 difference raw28762; decide +kernel
    rw [ha]
    exact (canonical28762 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2035 + difference 5 3) (sourceB2035 + difference 3 5) sourceC2035) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1131) := by
    have ha : (tripleCharges (sourceA2035 + difference 5 3) (sourceB2035 + difference 3 5) sourceC2035) = raw28763 := by
      apply Matrix.ext; unfold tripleCharges sourceA2035 sourceB2035 sourceC2035 difference raw28763; decide +kernel
    rw [ha]
    exact (canonical28763 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2035 + sourceB2035) sourceC2035) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2035 + sourceB2035) sourceC2035) = raw20738 := by
      apply Matrix.ext; unfold doubleCharges sourceA2035 sourceB2035 sourceC2035 raw20738; decide +kernel
    rw [ha]
    exact (canonical20738 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2035 sourceB2035 sourceC2035
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2035, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2036 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2036 : Charge := ![2, 0, 0, 1, -1, -2]
def sourceC2036 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceForm2036 : Integer.Sparse Master := [(Sum.inr 4287, 1), (Sum.inr 4289, 1), (Sum.inr 4295, 1), (Sum.inr 4303, 1), (Sum.inr 4322, 1), (Sum.inr 4325, 1), (Sum.inr 4346, 1), (Sum.inr 4401, 1), (Sum.inr 4460, 1), (Sum.inr 4902, 1), (Sum.inr 4907, 1), (Sum.inr 4913, 1), (Sum.inr 4927, 1), (Sum.inr 4943, 1), (Sum.inr 4986, 1), (Sum.inr 5000, 1), (Sum.inr 5033, 1), (Sum.inr 5047, 1), (Sum.inr 5073, 1), (Sum.inr 5075, 1), (Sum.inr 5081, 1), (Sum.inr 5102, 1), (Sum.inr 5137, 1), (Sum.inr 5141, 1), (Sum.inr 5169, 1), (Sum.inr 5171, 1), (Sum.inr 5259, 1), (Sum.inr 5261, 1), (Sum.inr 5293, 1), (Sum.inr 5483, 1)]

theorem sourceEq2036 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2036 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2036 + difference 0 1) (sourceB2036 + difference 1 0) sourceC2036) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5081) := by
    have ha : (tripleCharges (sourceA2036 + difference 0 1) (sourceB2036 + difference 1 0) sourceC2036) = raw17099 := by
      apply Matrix.ext; unfold tripleCharges sourceA2036 sourceB2036 sourceC2036 difference raw17099; decide +kernel
    rw [ha]
    exact (canonical17099 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2036 + difference 0 2) (sourceB2036 + difference 2 0) sourceC2036) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5073) := by
    have ha : (tripleCharges (sourceA2036 + difference 0 2) (sourceB2036 + difference 2 0) sourceC2036) = raw17100 := by
      apply Matrix.ext; unfold tripleCharges sourceA2036 sourceB2036 sourceC2036 difference raw17100; decide +kernel
    rw [ha]
    exact (canonical17100 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2036 + difference 0 3) (sourceB2036 + difference 3 0) sourceC2036) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5102) := by
    have ha : (tripleCharges (sourceA2036 + difference 0 3) (sourceB2036 + difference 3 0) sourceC2036) = raw17101 := by
      apply Matrix.ext; unfold tripleCharges sourceA2036 sourceB2036 sourceC2036 difference raw17101; decide +kernel
    rw [ha]
    exact (canonical17101 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2036 + difference 0 4) (sourceB2036 + difference 4 0) sourceC2036) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA2036 + difference 0 4) (sourceB2036 + difference 4 0) sourceC2036) = raw17102 := by
      apply Matrix.ext; unfold tripleCharges sourceA2036 sourceB2036 sourceC2036 difference raw17102; decide +kernel
    rw [ha]
    exact (canonical17102 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2036 + difference 0 5) (sourceB2036 + difference 5 0) sourceC2036) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA2036 + difference 0 5) (sourceB2036 + difference 5 0) sourceC2036) = raw3145 := by
      apply Matrix.ext; unfold tripleCharges sourceA2036 sourceB2036 sourceC2036 difference raw3145; decide +kernel
    rw [ha]
    exact (canonical3145 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2036 + difference 1 0) (sourceB2036 + difference 0 1) sourceC2036) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4401) := by
    have ha : (tripleCharges (sourceA2036 + difference 1 0) (sourceB2036 + difference 0 1) sourceC2036) = raw9864 := by
      apply Matrix.ext; unfold tripleCharges sourceA2036 sourceB2036 sourceC2036 difference raw9864; decide +kernel
    rw [ha]
    exact (canonical9864 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2036 + difference 1 2) (sourceB2036 + difference 2 1) sourceC2036) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5047) := by
    have ha : (tripleCharges (sourceA2036 + difference 1 2) (sourceB2036 + difference 2 1) sourceC2036) = raw9866 := by
      apply Matrix.ext; unfold tripleCharges sourceA2036 sourceB2036 sourceC2036 difference raw9866; decide +kernel
    rw [ha]
    exact (canonical9866 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2036 + difference 1 3) (sourceB2036 + difference 3 1) sourceC2036) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5000) := by
    have ha : (tripleCharges (sourceA2036 + difference 1 3) (sourceB2036 + difference 3 1) sourceC2036) = raw9867 := by
      apply Matrix.ext; unfold tripleCharges sourceA2036 sourceB2036 sourceC2036 difference raw9867; decide +kernel
    rw [ha]
    exact (canonical9867 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2036 + difference 1 4) (sourceB2036 + difference 4 1) sourceC2036) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5261) := by
    have ha : (tripleCharges (sourceA2036 + difference 1 4) (sourceB2036 + difference 4 1) sourceC2036) = raw9868 := by
      apply Matrix.ext; unfold tripleCharges sourceA2036 sourceB2036 sourceC2036 difference raw9868; decide +kernel
    rw [ha]
    exact (canonical9868 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2036 + difference 1 5) (sourceB2036 + difference 5 1) sourceC2036) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA2036 + difference 1 5) (sourceB2036 + difference 5 1) sourceC2036) = raw3144 := by
      apply Matrix.ext; unfold tripleCharges sourceA2036 sourceB2036 sourceC2036 difference raw3144; decide +kernel
    rw [ha]
    exact (canonical3144 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2036 + difference 2 0) (sourceB2036 + difference 0 2) sourceC2036) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4322) := by
    have ha : (tripleCharges (sourceA2036 + difference 2 0) (sourceB2036 + difference 0 2) sourceC2036) = raw28764 := by
      apply Matrix.ext; unfold tripleCharges sourceA2036 sourceB2036 sourceC2036 difference raw28764; decide +kernel
    rw [ha]
    exact (canonical28764 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2036 + difference 2 1) (sourceB2036 + difference 1 2) sourceC2036) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4927) := by
    have ha : (tripleCharges (sourceA2036 + difference 2 1) (sourceB2036 + difference 1 2) sourceC2036) = raw28765 := by
      apply Matrix.ext; unfold tripleCharges sourceA2036 sourceB2036 sourceC2036 difference raw28765; decide +kernel
    rw [ha]
    exact (canonical28765 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2036 + difference 2 3) (sourceB2036 + difference 3 2) sourceC2036) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4986) := by
    have ha : (tripleCharges (sourceA2036 + difference 2 3) (sourceB2036 + difference 3 2) sourceC2036) = raw28766 := by
      apply Matrix.ext; unfold tripleCharges sourceA2036 sourceB2036 sourceC2036 difference raw28766; decide +kernel
    rw [ha]
    exact (canonical28766 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2036 + difference 2 4) (sourceB2036 + difference 4 2) sourceC2036) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA2036 + difference 2 4) (sourceB2036 + difference 4 2) sourceC2036) = raw28767 := by
      apply Matrix.ext; unfold tripleCharges sourceA2036 sourceB2036 sourceC2036 difference raw28767; decide +kernel
    rw [ha]
    exact (canonical28767 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2036 + difference 2 5) (sourceB2036 + difference 5 2) sourceC2036) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5137) := by
    have ha : (tripleCharges (sourceA2036 + difference 2 5) (sourceB2036 + difference 5 2) sourceC2036) = raw9853 := by
      apply Matrix.ext; unfold tripleCharges sourceA2036 sourceB2036 sourceC2036 difference raw9853; decide +kernel
    rw [ha]
    exact (canonical9853 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2036 + difference 3 0) (sourceB2036 + difference 0 3) sourceC2036) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4346) := by
    have ha : (tripleCharges (sourceA2036 + difference 3 0) (sourceB2036 + difference 0 3) sourceC2036) = raw28768 := by
      apply Matrix.ext; unfold tripleCharges sourceA2036 sourceB2036 sourceC2036 difference raw28768; decide +kernel
    rw [ha]
    exact (canonical28768 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2036 + difference 3 1) (sourceB2036 + difference 1 3) sourceC2036) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4943) := by
    have ha : (tripleCharges (sourceA2036 + difference 3 1) (sourceB2036 + difference 1 3) sourceC2036) = raw28769 := by
      apply Matrix.ext; unfold tripleCharges sourceA2036 sourceB2036 sourceC2036 difference raw28769; decide +kernel
    rw [ha]
    exact (canonical28769 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2036 + difference 3 2) (sourceB2036 + difference 2 3) sourceC2036) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5033) := by
    have ha : (tripleCharges (sourceA2036 + difference 3 2) (sourceB2036 + difference 2 3) sourceC2036) = raw28770 := by
      apply Matrix.ext; unfold tripleCharges sourceA2036 sourceB2036 sourceC2036 difference raw28770; decide +kernel
    rw [ha]
    exact (canonical28770 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2036 + difference 3 4) (sourceB2036 + difference 4 3) sourceC2036) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5171) := by
    have ha : (tripleCharges (sourceA2036 + difference 3 4) (sourceB2036 + difference 4 3) sourceC2036) = raw28771 := by
      apply Matrix.ext; unfold tripleCharges sourceA2036 sourceB2036 sourceC2036 difference raw28771; decide +kernel
    rw [ha]
    exact (canonical28771 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2036 + difference 3 5) (sourceB2036 + difference 5 3) sourceC2036) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA2036 + difference 3 5) (sourceB2036 + difference 5 3) sourceC2036) = raw9857 := by
      apply Matrix.ext; unfold tripleCharges sourceA2036 sourceB2036 sourceC2036 difference raw9857; decide +kernel
    rw [ha]
    exact (canonical9857 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2036 + difference 4 0) (sourceB2036 + difference 0 4) sourceC2036) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4325) := by
    have ha : (tripleCharges (sourceA2036 + difference 4 0) (sourceB2036 + difference 0 4) sourceC2036) = raw28772 := by
      apply Matrix.ext; unfold tripleCharges sourceA2036 sourceB2036 sourceC2036 difference raw28772; decide +kernel
    rw [ha]
    exact (canonical28772 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2036 + difference 4 1) (sourceB2036 + difference 1 4) sourceC2036) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4907) := by
    have ha : (tripleCharges (sourceA2036 + difference 4 1) (sourceB2036 + difference 1 4) sourceC2036) = raw28773 := by
      apply Matrix.ext; unfold tripleCharges sourceA2036 sourceB2036 sourceC2036 difference raw28773; decide +kernel
    rw [ha]
    exact (canonical28773 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2036 + difference 4 2) (sourceB2036 + difference 2 4) sourceC2036) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4902) := by
    have ha : (tripleCharges (sourceA2036 + difference 4 2) (sourceB2036 + difference 2 4) sourceC2036) = raw28774 := by
      apply Matrix.ext; unfold tripleCharges sourceA2036 sourceB2036 sourceC2036 difference raw28774; decide +kernel
    rw [ha]
    exact (canonical28774 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2036 + difference 4 3) (sourceB2036 + difference 3 4) sourceC2036) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4913) := by
    have ha : (tripleCharges (sourceA2036 + difference 4 3) (sourceB2036 + difference 3 4) sourceC2036) = raw28775 := by
      apply Matrix.ext; unfold tripleCharges sourceA2036 sourceB2036 sourceC2036 difference raw28775; decide +kernel
    rw [ha]
    exact (canonical28775 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2036 + difference 4 5) (sourceB2036 + difference 5 4) sourceC2036) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA2036 + difference 4 5) (sourceB2036 + difference 5 4) sourceC2036) = raw9861 := by
      apply Matrix.ext; unfold tripleCharges sourceA2036 sourceB2036 sourceC2036 difference raw9861; decide +kernel
    rw [ha]
    exact (canonical9861 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2036 + difference 5 0) (sourceB2036 + difference 0 5) sourceC2036) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4289) := by
    have ha : (tripleCharges (sourceA2036 + difference 5 0) (sourceB2036 + difference 0 5) sourceC2036) = raw28776 := by
      apply Matrix.ext; unfold tripleCharges sourceA2036 sourceB2036 sourceC2036 difference raw28776; decide +kernel
    rw [ha]
    exact (canonical28776 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2036 + difference 5 1) (sourceB2036 + difference 1 5) sourceC2036) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4295) := by
    have ha : (tripleCharges (sourceA2036 + difference 5 1) (sourceB2036 + difference 1 5) sourceC2036) = raw28777 := by
      apply Matrix.ext; unfold tripleCharges sourceA2036 sourceB2036 sourceC2036 difference raw28777; decide +kernel
    rw [ha]
    exact (canonical28777 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2036 + difference 5 2) (sourceB2036 + difference 2 5) sourceC2036) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4287) := by
    have ha : (tripleCharges (sourceA2036 + difference 5 2) (sourceB2036 + difference 2 5) sourceC2036) = raw28778 := by
      apply Matrix.ext; unfold tripleCharges sourceA2036 sourceB2036 sourceC2036 difference raw28778; decide +kernel
    rw [ha]
    exact (canonical28778 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2036 + difference 5 3) (sourceB2036 + difference 3 5) sourceC2036) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4303) := by
    have ha : (tripleCharges (sourceA2036 + difference 5 3) (sourceB2036 + difference 3 5) sourceC2036) = raw28779 := by
      apply Matrix.ext; unfold tripleCharges sourceA2036 sourceB2036 sourceC2036 difference raw28779; decide +kernel
    rw [ha]
    exact (canonical28779 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2036 + difference 5 4) (sourceB2036 + difference 4 5) sourceC2036) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4460) := by
    have ha : (tripleCharges (sourceA2036 + difference 5 4) (sourceB2036 + difference 4 5) sourceC2036) = raw28780 := by
      apply Matrix.ext; unfold tripleCharges sourceA2036 sourceB2036 sourceC2036 difference raw28780; decide +kernel
    rw [ha]
    exact (canonical28780 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2036 sourceB2036 sourceC2036
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2036, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2037 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2037 : Charge := ![2, 0, 0, 1, -1, -2]
def sourceC2037 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceForm2037 : Integer.Sparse Master := [(Sum.inr 865, 1), (Sum.inr 867, 1), (Sum.inr 873, 1), (Sum.inr 881, 1), (Sum.inr 900, 1), (Sum.inr 903, 1), (Sum.inr 924, 1), (Sum.inr 982, 1), (Sum.inr 1043, 1), (Sum.inr 2295, 1), (Sum.inr 2300, 1), (Sum.inr 2306, 1), (Sum.inr 2317, 1), (Sum.inr 2334, 1), (Sum.inr 2371, 1), (Sum.inr 2385, 1), (Sum.inr 2425, 1), (Sum.inr 2449, 1), (Sum.inr 2480, 1), (Sum.inr 2482, 1), (Sum.inr 2489, 1), (Sum.inr 2512, 1), (Sum.inr 2556, 1), (Sum.inr 2561, 1), (Sum.inr 2595, 1), (Sum.inr 2598, 1), (Sum.inr 2723, 1), (Sum.inr 2726, 1), (Sum.inr 2767, 1), (Sum.inr 3981, 1)]

theorem sourceEq2037 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2037 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2037 + difference 0 1) (sourceB2037 + difference 1 0) sourceC2037) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2489) := by
    have ha : (tripleCharges (sourceA2037 + difference 0 1) (sourceB2037 + difference 1 0) sourceC2037) = raw17116 := by
      apply Matrix.ext; unfold tripleCharges sourceA2037 sourceB2037 sourceC2037 difference raw17116; decide +kernel
    rw [ha]
    exact (canonical17116 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2037 + difference 0 2) (sourceB2037 + difference 2 0) sourceC2037) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2480) := by
    have ha : (tripleCharges (sourceA2037 + difference 0 2) (sourceB2037 + difference 2 0) sourceC2037) = raw17117 := by
      apply Matrix.ext; unfold tripleCharges sourceA2037 sourceB2037 sourceC2037 difference raw17117; decide +kernel
    rw [ha]
    exact (canonical17117 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2037 + difference 0 3) (sourceB2037 + difference 3 0) sourceC2037) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2512) := by
    have ha : (tripleCharges (sourceA2037 + difference 0 3) (sourceB2037 + difference 3 0) sourceC2037) = raw17118 := by
      apply Matrix.ext; unfold tripleCharges sourceA2037 sourceB2037 sourceC2037 difference raw17118; decide +kernel
    rw [ha]
    exact (canonical17118 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2037 + difference 0 4) (sourceB2037 + difference 4 0) sourceC2037) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2767) := by
    have ha : (tripleCharges (sourceA2037 + difference 0 4) (sourceB2037 + difference 4 0) sourceC2037) = raw17119 := by
      apply Matrix.ext; unfold tripleCharges sourceA2037 sourceB2037 sourceC2037 difference raw17119; decide +kernel
    rw [ha]
    exact (canonical17119 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2037 + difference 0 5) (sourceB2037 + difference 5 0) sourceC2037) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3981) := by
    have ha : (tripleCharges (sourceA2037 + difference 0 5) (sourceB2037 + difference 5 0) sourceC2037) = raw3175 := by
      apply Matrix.ext; unfold tripleCharges sourceA2037 sourceB2037 sourceC2037 difference raw3175; decide +kernel
    rw [ha]
    exact (canonical3175 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2037 + difference 1 0) (sourceB2037 + difference 0 1) sourceC2037) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 982) := by
    have ha : (tripleCharges (sourceA2037 + difference 1 0) (sourceB2037 + difference 0 1) sourceC2037) = raw9886 := by
      apply Matrix.ext; unfold tripleCharges sourceA2037 sourceB2037 sourceC2037 difference raw9886; decide +kernel
    rw [ha]
    exact (canonical9886 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2037 + difference 1 2) (sourceB2037 + difference 2 1) sourceC2037) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2449) := by
    have ha : (tripleCharges (sourceA2037 + difference 1 2) (sourceB2037 + difference 2 1) sourceC2037) = raw9888 := by
      apply Matrix.ext; unfold tripleCharges sourceA2037 sourceB2037 sourceC2037 difference raw9888; decide +kernel
    rw [ha]
    exact (canonical9888 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2037 + difference 1 3) (sourceB2037 + difference 3 1) sourceC2037) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2385) := by
    have ha : (tripleCharges (sourceA2037 + difference 1 3) (sourceB2037 + difference 3 1) sourceC2037) = raw9889 := by
      apply Matrix.ext; unfold tripleCharges sourceA2037 sourceB2037 sourceC2037 difference raw9889; decide +kernel
    rw [ha]
    exact (canonical9889 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2037 + difference 1 4) (sourceB2037 + difference 4 1) sourceC2037) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2726) := by
    have ha : (tripleCharges (sourceA2037 + difference 1 4) (sourceB2037 + difference 4 1) sourceC2037) = raw9890 := by
      apply Matrix.ext; unfold tripleCharges sourceA2037 sourceB2037 sourceC2037 difference raw9890; decide +kernel
    rw [ha]
    exact (canonical9890 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2037 + difference 1 5) (sourceB2037 + difference 5 1) sourceC2037) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA2037 + difference 1 5) (sourceB2037 + difference 5 1) sourceC2037) = raw3174 := by
      apply Matrix.ext; unfold tripleCharges sourceA2037 sourceB2037 sourceC2037 difference raw3174; decide +kernel
    rw [ha]
    exact (canonical3174 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2037 + difference 2 0) (sourceB2037 + difference 0 2) sourceC2037) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 900) := by
    have ha : (tripleCharges (sourceA2037 + difference 2 0) (sourceB2037 + difference 0 2) sourceC2037) = raw28781 := by
      apply Matrix.ext; unfold tripleCharges sourceA2037 sourceB2037 sourceC2037 difference raw28781; decide +kernel
    rw [ha]
    exact (canonical28781 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2037 + difference 2 1) (sourceB2037 + difference 1 2) sourceC2037) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2317) := by
    have ha : (tripleCharges (sourceA2037 + difference 2 1) (sourceB2037 + difference 1 2) sourceC2037) = raw28782 := by
      apply Matrix.ext; unfold tripleCharges sourceA2037 sourceB2037 sourceC2037 difference raw28782; decide +kernel
    rw [ha]
    exact (canonical28782 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2037 + difference 2 3) (sourceB2037 + difference 3 2) sourceC2037) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2371) := by
    have ha : (tripleCharges (sourceA2037 + difference 2 3) (sourceB2037 + difference 3 2) sourceC2037) = raw28783 := by
      apply Matrix.ext; unfold tripleCharges sourceA2037 sourceB2037 sourceC2037 difference raw28783; decide +kernel
    rw [ha]
    exact (canonical28783 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2037 + difference 2 4) (sourceB2037 + difference 4 2) sourceC2037) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2482) := by
    have ha : (tripleCharges (sourceA2037 + difference 2 4) (sourceB2037 + difference 4 2) sourceC2037) = raw28784 := by
      apply Matrix.ext; unfold tripleCharges sourceA2037 sourceB2037 sourceC2037 difference raw28784; decide +kernel
    rw [ha]
    exact (canonical28784 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2037 + difference 2 5) (sourceB2037 + difference 5 2) sourceC2037) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2556) := by
    have ha : (tripleCharges (sourceA2037 + difference 2 5) (sourceB2037 + difference 5 2) sourceC2037) = raw9875 := by
      apply Matrix.ext; unfold tripleCharges sourceA2037 sourceB2037 sourceC2037 difference raw9875; decide +kernel
    rw [ha]
    exact (canonical9875 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2037 + difference 3 0) (sourceB2037 + difference 0 3) sourceC2037) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 924) := by
    have ha : (tripleCharges (sourceA2037 + difference 3 0) (sourceB2037 + difference 0 3) sourceC2037) = raw28785 := by
      apply Matrix.ext; unfold tripleCharges sourceA2037 sourceB2037 sourceC2037 difference raw28785; decide +kernel
    rw [ha]
    exact (canonical28785 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2037 + difference 3 1) (sourceB2037 + difference 1 3) sourceC2037) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2334) := by
    have ha : (tripleCharges (sourceA2037 + difference 3 1) (sourceB2037 + difference 1 3) sourceC2037) = raw28786 := by
      apply Matrix.ext; unfold tripleCharges sourceA2037 sourceB2037 sourceC2037 difference raw28786; decide +kernel
    rw [ha]
    exact (canonical28786 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2037 + difference 3 2) (sourceB2037 + difference 2 3) sourceC2037) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2425) := by
    have ha : (tripleCharges (sourceA2037 + difference 3 2) (sourceB2037 + difference 2 3) sourceC2037) = raw28787 := by
      apply Matrix.ext; unfold tripleCharges sourceA2037 sourceB2037 sourceC2037 difference raw28787; decide +kernel
    rw [ha]
    exact (canonical28787 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2037 + difference 3 4) (sourceB2037 + difference 4 3) sourceC2037) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2598) := by
    have ha : (tripleCharges (sourceA2037 + difference 3 4) (sourceB2037 + difference 4 3) sourceC2037) = raw28788 := by
      apply Matrix.ext; unfold tripleCharges sourceA2037 sourceB2037 sourceC2037 difference raw28788; decide +kernel
    rw [ha]
    exact (canonical28788 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2037 + difference 3 5) (sourceB2037 + difference 5 3) sourceC2037) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2595) := by
    have ha : (tripleCharges (sourceA2037 + difference 3 5) (sourceB2037 + difference 5 3) sourceC2037) = raw9879 := by
      apply Matrix.ext; unfold tripleCharges sourceA2037 sourceB2037 sourceC2037 difference raw9879; decide +kernel
    rw [ha]
    exact (canonical9879 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2037 + difference 4 0) (sourceB2037 + difference 0 4) sourceC2037) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 903) := by
    have ha : (tripleCharges (sourceA2037 + difference 4 0) (sourceB2037 + difference 0 4) sourceC2037) = raw28789 := by
      apply Matrix.ext; unfold tripleCharges sourceA2037 sourceB2037 sourceC2037 difference raw28789; decide +kernel
    rw [ha]
    exact (canonical28789 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2037 + difference 4 1) (sourceB2037 + difference 1 4) sourceC2037) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2300) := by
    have ha : (tripleCharges (sourceA2037 + difference 4 1) (sourceB2037 + difference 1 4) sourceC2037) = raw28790 := by
      apply Matrix.ext; unfold tripleCharges sourceA2037 sourceB2037 sourceC2037 difference raw28790; decide +kernel
    rw [ha]
    exact (canonical28790 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2037 + difference 4 2) (sourceB2037 + difference 2 4) sourceC2037) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2295) := by
    have ha : (tripleCharges (sourceA2037 + difference 4 2) (sourceB2037 + difference 2 4) sourceC2037) = raw28791 := by
      apply Matrix.ext; unfold tripleCharges sourceA2037 sourceB2037 sourceC2037 difference raw28791; decide +kernel
    rw [ha]
    exact (canonical28791 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2037 + difference 4 3) (sourceB2037 + difference 3 4) sourceC2037) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2306) := by
    have ha : (tripleCharges (sourceA2037 + difference 4 3) (sourceB2037 + difference 3 4) sourceC2037) = raw28792 := by
      apply Matrix.ext; unfold tripleCharges sourceA2037 sourceB2037 sourceC2037 difference raw28792; decide +kernel
    rw [ha]
    exact (canonical28792 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2037 + difference 4 5) (sourceB2037 + difference 5 4) sourceC2037) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2561) := by
    have ha : (tripleCharges (sourceA2037 + difference 4 5) (sourceB2037 + difference 5 4) sourceC2037) = raw9883 := by
      apply Matrix.ext; unfold tripleCharges sourceA2037 sourceB2037 sourceC2037 difference raw9883; decide +kernel
    rw [ha]
    exact (canonical9883 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2037 + difference 5 0) (sourceB2037 + difference 0 5) sourceC2037) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 867) := by
    have ha : (tripleCharges (sourceA2037 + difference 5 0) (sourceB2037 + difference 0 5) sourceC2037) = raw28793 := by
      apply Matrix.ext; unfold tripleCharges sourceA2037 sourceB2037 sourceC2037 difference raw28793; decide +kernel
    rw [ha]
    exact (canonical28793 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2037 + difference 5 1) (sourceB2037 + difference 1 5) sourceC2037) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 873) := by
    have ha : (tripleCharges (sourceA2037 + difference 5 1) (sourceB2037 + difference 1 5) sourceC2037) = raw28794 := by
      apply Matrix.ext; unfold tripleCharges sourceA2037 sourceB2037 sourceC2037 difference raw28794; decide +kernel
    rw [ha]
    exact (canonical28794 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2037 + difference 5 2) (sourceB2037 + difference 2 5) sourceC2037) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 865) := by
    have ha : (tripleCharges (sourceA2037 + difference 5 2) (sourceB2037 + difference 2 5) sourceC2037) = raw28795 := by
      apply Matrix.ext; unfold tripleCharges sourceA2037 sourceB2037 sourceC2037 difference raw28795; decide +kernel
    rw [ha]
    exact (canonical28795 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2037 + difference 5 3) (sourceB2037 + difference 3 5) sourceC2037) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 881) := by
    have ha : (tripleCharges (sourceA2037 + difference 5 3) (sourceB2037 + difference 3 5) sourceC2037) = raw28796 := by
      apply Matrix.ext; unfold tripleCharges sourceA2037 sourceB2037 sourceC2037 difference raw28796; decide +kernel
    rw [ha]
    exact (canonical28796 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2037 + difference 5 4) (sourceB2037 + difference 4 5) sourceC2037) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1043) := by
    have ha : (tripleCharges (sourceA2037 + difference 5 4) (sourceB2037 + difference 4 5) sourceC2037) = raw28797 := by
      apply Matrix.ext; unfold tripleCharges sourceA2037 sourceB2037 sourceC2037 difference raw28797; decide +kernel
    rw [ha]
    exact (canonical28797 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2037 sourceB2037 sourceC2037
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2037, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2038 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceB2038 : Charge := ![2, 0, 0, 1, -1, -2]
def sourceC2038 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceForm2038 : Integer.Sparse Master := [(Sum.inr 4728, 1), (Sum.inr 4738, 1), (Sum.inr 4741, 1), (Sum.inr 4744, 1), (Sum.inr 4779, 1), (Sum.inr 4788, 1), (Sum.inr 4804, 1), (Sum.inr 4827, 1), (Sum.inr 4841, 1), (Sum.inr 4991, 1), (Sum.inr 5000, 1), (Sum.inr 5006, 1), (Sum.inr 5047, 1), (Sum.inr 5051, 1), (Sum.inr 5064, 1), (Sum.inr 5065, 1), (Sum.inr 5075, 2), (Sum.inr 5078, 2), (Sum.inr 5084, 1), (Sum.inr 5087, 1), (Sum.inr 5107, 1), (Sum.inr 5127, 1), (Sum.inr 5128, 1), (Sum.inr 5139, 2), (Sum.inr 5147, 1), (Sum.inr 5171, 1), (Sum.inr 5174, 1)]

theorem sourceEq2038 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2038 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2038 + difference 0 1) (sourceB2038 + difference 1 0) sourceC2038) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5078) := by
    have ha : (tripleCharges (sourceA2038 + difference 0 1) (sourceB2038 + difference 1 0) sourceC2038) = raw28798 := by
      apply Matrix.ext; unfold tripleCharges sourceA2038 sourceB2038 sourceC2038 difference raw28798; decide +kernel
    rw [ha]
    exact (canonical28798 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2038 + difference 0 2) (sourceB2038 + difference 2 0) sourceC2038) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5065) := by
    have ha : (tripleCharges (sourceA2038 + difference 0 2) (sourceB2038 + difference 2 0) sourceC2038) = raw28799 := by
      apply Matrix.ext; unfold tripleCharges sourceA2038 sourceB2038 sourceC2038 difference raw28799; decide +kernel
    rw [ha]
    exact (canonical28799 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2038 + difference 0 3) (sourceB2038 + difference 3 0) sourceC2038) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5087) := by
    have ha : (tripleCharges (sourceA2038 + difference 0 3) (sourceB2038 + difference 3 0) sourceC2038) = raw28800 := by
      apply Matrix.ext; unfold tripleCharges sourceA2038 sourceB2038 sourceC2038 difference raw28800; decide +kernel
    rw [ha]
    exact (canonical28800 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2038 + difference 0 4) (sourceB2038 + difference 4 0) sourceC2038) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5078) := by
    have ha : (tripleCharges (sourceA2038 + difference 0 4) (sourceB2038 + difference 4 0) sourceC2038) = raw28801 := by
      apply Matrix.ext; unfold tripleCharges sourceA2038 sourceB2038 sourceC2038 difference raw28801; decide +kernel
    rw [ha]
    exact (canonical28801 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2038 + difference 0 5) (sourceB2038 + difference 5 0) sourceC2038) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA2038 + difference 0 5) (sourceB2038 + difference 5 0) sourceC2038) = raw27640 := by
      apply Matrix.ext; unfold tripleCharges sourceA2038 sourceB2038 sourceC2038 difference raw27640; decide +kernel
    rw [ha]
    exact (canonical27640 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2038 + difference 1 0) (sourceB2038 + difference 0 1) sourceC2038) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4827) := by
    have ha : (tripleCharges (sourceA2038 + difference 1 0) (sourceB2038 + difference 0 1) sourceC2038) = raw28802 := by
      apply Matrix.ext; unfold tripleCharges sourceA2038 sourceB2038 sourceC2038 difference raw28802; decide +kernel
    rw [ha]
    exact (canonical28802 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2038 + difference 1 2) (sourceB2038 + difference 2 1) sourceC2038) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5064) := by
    have ha : (tripleCharges (sourceA2038 + difference 1 2) (sourceB2038 + difference 2 1) sourceC2038) = raw28803 := by
      apply Matrix.ext; unfold tripleCharges sourceA2038 sourceB2038 sourceC2038 difference raw28803; decide +kernel
    rw [ha]
    exact (canonical28803 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2038 + difference 1 3) (sourceB2038 + difference 3 1) sourceC2038) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5084) := by
    have ha : (tripleCharges (sourceA2038 + difference 1 3) (sourceB2038 + difference 3 1) sourceC2038) = raw28804 := by
      apply Matrix.ext; unfold tripleCharges sourceA2038 sourceB2038 sourceC2038 difference raw28804; decide +kernel
    rw [ha]
    exact (canonical28804 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2038 + difference 1 4) (sourceB2038 + difference 4 1) sourceC2038) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5147) := by
    have ha : (tripleCharges (sourceA2038 + difference 1 4) (sourceB2038 + difference 4 1) sourceC2038) = raw28805 := by
      apply Matrix.ext; unfold tripleCharges sourceA2038 sourceB2038 sourceC2038 difference raw28805; decide +kernel
    rw [ha]
    exact (canonical28805 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2038 + difference 1 5) (sourceB2038 + difference 5 1) sourceC2038) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5139) := by
    have ha : (tripleCharges (sourceA2038 + difference 1 5) (sourceB2038 + difference 5 1) sourceC2038) = raw27645 := by
      apply Matrix.ext; unfold tripleCharges sourceA2038 sourceB2038 sourceC2038 difference raw27645; decide +kernel
    rw [ha]
    exact (canonical27645 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2038 + difference 2 0) (sourceB2038 + difference 0 2) sourceC2038) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4779) := by
    have ha : (tripleCharges (sourceA2038 + difference 2 0) (sourceB2038 + difference 0 2) sourceC2038) = raw28806 := by
      apply Matrix.ext; unfold tripleCharges sourceA2038 sourceB2038 sourceC2038 difference raw28806; decide +kernel
    rw [ha]
    exact (canonical28806 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2038 + difference 2 1) (sourceB2038 + difference 1 2) sourceC2038) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5047) := by
    have ha : (tripleCharges (sourceA2038 + difference 2 1) (sourceB2038 + difference 1 2) sourceC2038) = raw28807 := by
      apply Matrix.ext; unfold tripleCharges sourceA2038 sourceB2038 sourceC2038 difference raw28807; decide +kernel
    rw [ha]
    exact (canonical28807 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2038 + difference 2 3) (sourceB2038 + difference 3 2) sourceC2038) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5051) := by
    have ha : (tripleCharges (sourceA2038 + difference 2 3) (sourceB2038 + difference 3 2) sourceC2038) = raw28808 := by
      apply Matrix.ext; unfold tripleCharges sourceA2038 sourceB2038 sourceC2038 difference raw28808; decide +kernel
    rw [ha]
    exact (canonical28808 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2038 + difference 2 4) (sourceB2038 + difference 4 2) sourceC2038) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5127) := by
    have ha : (tripleCharges (sourceA2038 + difference 2 4) (sourceB2038 + difference 4 2) sourceC2038) = raw28809 := by
      apply Matrix.ext; unfold tripleCharges sourceA2038 sourceB2038 sourceC2038 difference raw28809; decide +kernel
    rw [ha]
    exact (canonical28809 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2038 + difference 2 5) (sourceB2038 + difference 5 2) sourceC2038) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5128) := by
    have ha : (tripleCharges (sourceA2038 + difference 2 5) (sourceB2038 + difference 5 2) sourceC2038) = raw27650 := by
      apply Matrix.ext; unfold tripleCharges sourceA2038 sourceB2038 sourceC2038 difference raw27650; decide +kernel
    rw [ha]
    exact (canonical27650 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2038 + difference 3 0) (sourceB2038 + difference 0 3) sourceC2038) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4841) := by
    have ha : (tripleCharges (sourceA2038 + difference 3 0) (sourceB2038 + difference 0 3) sourceC2038) = raw27663 := by
      apply Matrix.ext; unfold tripleCharges sourceA2038 sourceB2038 sourceC2038 difference raw27663; decide +kernel
    rw [ha]
    exact (canonical27663 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2038 + difference 3 1) (sourceB2038 + difference 1 3) sourceC2038) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5107) := by
    have ha : (tripleCharges (sourceA2038 + difference 3 1) (sourceB2038 + difference 1 3) sourceC2038) = raw27664 := by
      apply Matrix.ext; unfold tripleCharges sourceA2038 sourceB2038 sourceC2038 difference raw27664; decide +kernel
    rw [ha]
    exact (canonical27664 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2038 + difference 3 2) (sourceB2038 + difference 2 3) sourceC2038) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA2038 + difference 3 2) (sourceB2038 + difference 2 3) sourceC2038) = raw27665 := by
      apply Matrix.ext; unfold tripleCharges sourceA2038 sourceB2038 sourceC2038 difference raw27665; decide +kernel
    rw [ha]
    exact (canonical27665 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2038 + difference 3 4) (sourceB2038 + difference 4 3) sourceC2038) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5171) := by
    have ha : (tripleCharges (sourceA2038 + difference 3 4) (sourceB2038 + difference 4 3) sourceC2038) = raw27667 := by
      apply Matrix.ext; unfold tripleCharges sourceA2038 sourceB2038 sourceC2038 difference raw27667; decide +kernel
    rw [ha]
    exact (canonical27667 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2038 + difference 3 5) (sourceB2038 + difference 5 3) sourceC2038) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5174) := by
    have ha : (tripleCharges (sourceA2038 + difference 3 5) (sourceB2038 + difference 5 3) sourceC2038) = raw27780 := by
      apply Matrix.ext; unfold tripleCharges sourceA2038 sourceB2038 sourceC2038 difference raw27780; decide +kernel
    rw [ha]
    exact (canonical27780 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2038 + difference 4 0) (sourceB2038 + difference 0 4) sourceC2038) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4788) := by
    have ha : (tripleCharges (sourceA2038 + difference 4 0) (sourceB2038 + difference 0 4) sourceC2038) = raw28810 := by
      apply Matrix.ext; unfold tripleCharges sourceA2038 sourceB2038 sourceC2038 difference raw28810; decide +kernel
    rw [ha]
    exact (canonical28810 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2038 + difference 4 1) (sourceB2038 + difference 1 4) sourceC2038) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5000) := by
    have ha : (tripleCharges (sourceA2038 + difference 4 1) (sourceB2038 + difference 1 4) sourceC2038) = raw28811 := by
      apply Matrix.ext; unfold tripleCharges sourceA2038 sourceB2038 sourceC2038 difference raw28811; decide +kernel
    rw [ha]
    exact (canonical28811 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2038 + difference 4 2) (sourceB2038 + difference 2 4) sourceC2038) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4991) := by
    have ha : (tripleCharges (sourceA2038 + difference 4 2) (sourceB2038 + difference 2 4) sourceC2038) = raw28812 := by
      apply Matrix.ext; unfold tripleCharges sourceA2038 sourceB2038 sourceC2038 difference raw28812; decide +kernel
    rw [ha]
    exact (canonical28812 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2038 + difference 4 3) (sourceB2038 + difference 3 4) sourceC2038) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5006) := by
    have ha : (tripleCharges (sourceA2038 + difference 4 3) (sourceB2038 + difference 3 4) sourceC2038) = raw28813 := by
      apply Matrix.ext; unfold tripleCharges sourceA2038 sourceB2038 sourceC2038 difference raw28813; decide +kernel
    rw [ha]
    exact (canonical28813 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2038 + difference 4 5) (sourceB2038 + difference 5 4) sourceC2038) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5139) := by
    have ha : (tripleCharges (sourceA2038 + difference 4 5) (sourceB2038 + difference 5 4) sourceC2038) = raw27661 := by
      apply Matrix.ext; unfold tripleCharges sourceA2038 sourceB2038 sourceC2038 difference raw27661; decide +kernel
    rw [ha]
    exact (canonical27661 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2038 + difference 5 0) (sourceB2038 + difference 0 5) sourceC2038) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4738) := by
    have ha : (tripleCharges (sourceA2038 + difference 5 0) (sourceB2038 + difference 0 5) sourceC2038) = raw28814 := by
      apply Matrix.ext; unfold tripleCharges sourceA2038 sourceB2038 sourceC2038 difference raw28814; decide +kernel
    rw [ha]
    exact (canonical28814 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2038 + difference 5 1) (sourceB2038 + difference 1 5) sourceC2038) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4741) := by
    have ha : (tripleCharges (sourceA2038 + difference 5 1) (sourceB2038 + difference 1 5) sourceC2038) = raw28815 := by
      apply Matrix.ext; unfold tripleCharges sourceA2038 sourceB2038 sourceC2038 difference raw28815; decide +kernel
    rw [ha]
    exact (canonical28815 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2038 + difference 5 2) (sourceB2038 + difference 2 5) sourceC2038) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4728) := by
    have ha : (tripleCharges (sourceA2038 + difference 5 2) (sourceB2038 + difference 2 5) sourceC2038) = raw28816 := by
      apply Matrix.ext; unfold tripleCharges sourceA2038 sourceB2038 sourceC2038 difference raw28816; decide +kernel
    rw [ha]
    exact (canonical28816 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2038 + difference 5 3) (sourceB2038 + difference 3 5) sourceC2038) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4744) := by
    have ha : (tripleCharges (sourceA2038 + difference 5 3) (sourceB2038 + difference 3 5) sourceC2038) = raw28817 := by
      apply Matrix.ext; unfold tripleCharges sourceA2038 sourceB2038 sourceC2038 difference raw28817; decide +kernel
    rw [ha]
    exact (canonical28817 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2038 + difference 5 4) (sourceB2038 + difference 4 5) sourceC2038) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA2038 + difference 5 4) (sourceB2038 + difference 4 5) sourceC2038) = raw28681 := by
      apply Matrix.ext; unfold tripleCharges sourceA2038 sourceB2038 sourceC2038 difference raw28681; decide +kernel
    rw [ha]
    exact (canonical28681 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2038 sourceB2038 sourceC2038
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2038, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2039 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2039 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC2039 : Charge := ![2, 0, 0, 1, 0, -3]
def sourceForm2039 : Integer.Sparse Master := [(Sum.inr 4326, 1), (Sum.inr 4330, 1), (Sum.inr 4334, 1), (Sum.inr 4346, 1), (Sum.inr 4460, 1), (Sum.inr 4532, 1), (Sum.inr 4536, 1), (Sum.inr 4552, 1), (Sum.inr 4605, 1), (Sum.inr 4663, 1), (Sum.inr 4669, 1), (Sum.inr 4681, 1), (Sum.inr 4756, 1), (Sum.inr 4760, 1), (Sum.inr 4771, 1), (Sum.inr 4776, 1), (Sum.inr 4801, 1), (Sum.inr 4804, 2), (Sum.inr 4810, 1), (Sum.inr 4834, 1), (Sum.inr 4841, 1), (Sum.inr 4868, 1), (Sum.inr 4894, 1), (Sum.inr 4897, 1), (Sum.inr 5133, 1), (Sum.inr 5140, 1), (Sum.inr 5161, 1), (Sum.inr 5258, 1), (Sum.inr 5272, 1)]

theorem sourceEq2039 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2039 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2039 + difference 0 1) (sourceB2039 + difference 1 0) sourceC2039) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4810) := by
    have ha : (tripleCharges (sourceA2039 + difference 0 1) (sourceB2039 + difference 1 0) sourceC2039) = raw28818 := by
      apply Matrix.ext; unfold tripleCharges sourceA2039 sourceB2039 sourceC2039 difference raw28818; decide +kernel
    rw [ha]
    exact (canonical28818 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2039 + difference 0 2) (sourceB2039 + difference 2 0) sourceC2039) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4801) := by
    have ha : (tripleCharges (sourceA2039 + difference 0 2) (sourceB2039 + difference 2 0) sourceC2039) = raw28819 := by
      apply Matrix.ext; unfold tripleCharges sourceA2039 sourceB2039 sourceC2039 difference raw28819; decide +kernel
    rw [ha]
    exact (canonical28819 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2039 + difference 0 3) (sourceB2039 + difference 3 0) sourceC2039) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4834) := by
    have ha : (tripleCharges (sourceA2039 + difference 0 3) (sourceB2039 + difference 3 0) sourceC2039) = raw28820 := by
      apply Matrix.ext; unfold tripleCharges sourceA2039 sourceB2039 sourceC2039 difference raw28820; decide +kernel
    rw [ha]
    exact (canonical28820 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2039 + difference 0 4) (sourceB2039 + difference 4 0) sourceC2039) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4894) := by
    have ha : (tripleCharges (sourceA2039 + difference 0 4) (sourceB2039 + difference 4 0) sourceC2039) = raw28821 := by
      apply Matrix.ext; unfold tripleCharges sourceA2039 sourceB2039 sourceC2039 difference raw28821; decide +kernel
    rw [ha]
    exact (canonical28821 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2039 + difference 0 5) (sourceB2039 + difference 5 0) sourceC2039) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA2039 + difference 0 5) (sourceB2039 + difference 5 0) sourceC2039) = raw10582 := by
      apply Matrix.ext; unfold tripleCharges sourceA2039 sourceB2039 sourceC2039 difference raw10582; decide +kernel
    rw [ha]
    exact (canonical10582 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2039 + difference 1 0) (sourceB2039 + difference 0 1) sourceC2039) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4605) := by
    have ha : (tripleCharges (sourceA2039 + difference 1 0) (sourceB2039 + difference 0 1) sourceC2039) = raw10607 := by
      apply Matrix.ext; unfold tripleCharges sourceA2039 sourceB2039 sourceC2039 difference raw10607; decide +kernel
    rw [ha]
    exact (canonical10607 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2039 + difference 1 2) (sourceB2039 + difference 2 1) sourceC2039) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA2039 + difference 1 2) (sourceB2039 + difference 2 1) sourceC2039) = raw10609 := by
      apply Matrix.ext; unfold tripleCharges sourceA2039 sourceB2039 sourceC2039 difference raw10609; decide +kernel
    rw [ha]
    exact (canonical10609 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2039 + difference 1 3) (sourceB2039 + difference 3 1) sourceC2039) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4841) := by
    have ha : (tripleCharges (sourceA2039 + difference 1 3) (sourceB2039 + difference 3 1) sourceC2039) = raw10610 := by
      apply Matrix.ext; unfold tripleCharges sourceA2039 sourceB2039 sourceC2039 difference raw10610; decide +kernel
    rw [ha]
    exact (canonical10610 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2039 + difference 1 4) (sourceB2039 + difference 4 1) sourceC2039) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4897) := by
    have ha : (tripleCharges (sourceA2039 + difference 1 4) (sourceB2039 + difference 4 1) sourceC2039) = raw10611 := by
      apply Matrix.ext; unfold tripleCharges sourceA2039 sourceB2039 sourceC2039 difference raw10611; decide +kernel
    rw [ha]
    exact (canonical10611 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2039 + difference 1 5) (sourceB2039 + difference 5 1) sourceC2039) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5272) := by
    have ha : (tripleCharges (sourceA2039 + difference 1 5) (sourceB2039 + difference 5 1) sourceC2039) = raw20844 := by
      apply Matrix.ext; unfold tripleCharges sourceA2039 sourceB2039 sourceC2039 difference raw20844; decide +kernel
    rw [ha]
    exact (canonical20844 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2039 + difference 2 0) (sourceB2039 + difference 0 2) sourceC2039) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4532) := by
    have ha : (tripleCharges (sourceA2039 + difference 2 0) (sourceB2039 + difference 0 2) sourceC2039) = raw20850 := by
      apply Matrix.ext; unfold tripleCharges sourceA2039 sourceB2039 sourceC2039 difference raw20850; decide +kernel
    rw [ha]
    exact (canonical20850 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2039 + difference 2 1) (sourceB2039 + difference 1 2) sourceC2039) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4756) := by
    have ha : (tripleCharges (sourceA2039 + difference 2 1) (sourceB2039 + difference 1 2) sourceC2039) = raw28822 := by
      apply Matrix.ext; unfold tripleCharges sourceA2039 sourceB2039 sourceC2039 difference raw28822; decide +kernel
    rw [ha]
    exact (canonical28822 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2039 + difference 2 3) (sourceB2039 + difference 3 2) sourceC2039) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4760) := by
    have ha : (tripleCharges (sourceA2039 + difference 2 3) (sourceB2039 + difference 3 2) sourceC2039) = raw28823 := by
      apply Matrix.ext; unfold tripleCharges sourceA2039 sourceB2039 sourceC2039 difference raw28823; decide +kernel
    rw [ha]
    exact (canonical28823 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2039 + difference 2 4) (sourceB2039 + difference 4 2) sourceC2039) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA2039 + difference 2 4) (sourceB2039 + difference 4 2) sourceC2039) = raw28824 := by
      apply Matrix.ext; unfold tripleCharges sourceA2039 sourceB2039 sourceC2039 difference raw28824; decide +kernel
    rw [ha]
    exact (canonical28824 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2039 + difference 2 5) (sourceB2039 + difference 5 2) sourceC2039) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5133) := by
    have ha : (tripleCharges (sourceA2039 + difference 2 5) (sourceB2039 + difference 5 2) sourceC2039) = raw10593 := by
      apply Matrix.ext; unfold tripleCharges sourceA2039 sourceB2039 sourceC2039 difference raw10593; decide +kernel
    rw [ha]
    exact (canonical10593 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2039 + difference 3 0) (sourceB2039 + difference 0 3) sourceC2039) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4552) := by
    have ha : (tripleCharges (sourceA2039 + difference 3 0) (sourceB2039 + difference 0 3) sourceC2039) = raw20854 := by
      apply Matrix.ext; unfold tripleCharges sourceA2039 sourceB2039 sourceC2039 difference raw20854; decide +kernel
    rw [ha]
    exact (canonical20854 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2039 + difference 3 1) (sourceB2039 + difference 1 3) sourceC2039) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4776) := by
    have ha : (tripleCharges (sourceA2039 + difference 3 1) (sourceB2039 + difference 1 3) sourceC2039) = raw28825 := by
      apply Matrix.ext; unfold tripleCharges sourceA2039 sourceB2039 sourceC2039 difference raw28825; decide +kernel
    rw [ha]
    exact (canonical28825 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2039 + difference 3 2) (sourceB2039 + difference 2 3) sourceC2039) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4771) := by
    have ha : (tripleCharges (sourceA2039 + difference 3 2) (sourceB2039 + difference 2 3) sourceC2039) = raw28826 := by
      apply Matrix.ext; unfold tripleCharges sourceA2039 sourceB2039 sourceC2039 difference raw28826; decide +kernel
    rw [ha]
    exact (canonical28826 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2039 + difference 3 4) (sourceB2039 + difference 4 3) sourceC2039) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4868) := by
    have ha : (tripleCharges (sourceA2039 + difference 3 4) (sourceB2039 + difference 4 3) sourceC2039) = raw28827 := by
      apply Matrix.ext; unfold tripleCharges sourceA2039 sourceB2039 sourceC2039 difference raw28827; decide +kernel
    rw [ha]
    exact (canonical28827 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2039 + difference 3 5) (sourceB2039 + difference 5 3) sourceC2039) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5161) := by
    have ha : (tripleCharges (sourceA2039 + difference 3 5) (sourceB2039 + difference 5 3) sourceC2039) = raw10598 := by
      apply Matrix.ext; unfold tripleCharges sourceA2039 sourceB2039 sourceC2039 difference raw10598; decide +kernel
    rw [ha]
    exact (canonical10598 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2039 + difference 4 0) (sourceB2039 + difference 0 4) sourceC2039) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4536) := by
    have ha : (tripleCharges (sourceA2039 + difference 4 0) (sourceB2039 + difference 0 4) sourceC2039) = raw20858 := by
      apply Matrix.ext; unfold tripleCharges sourceA2039 sourceB2039 sourceC2039 difference raw20858; decide +kernel
    rw [ha]
    exact (canonical20858 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2039 + difference 4 1) (sourceB2039 + difference 1 4) sourceC2039) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4669) := by
    have ha : (tripleCharges (sourceA2039 + difference 4 1) (sourceB2039 + difference 1 4) sourceC2039) = raw28828 := by
      apply Matrix.ext; unfold tripleCharges sourceA2039 sourceB2039 sourceC2039 difference raw28828; decide +kernel
    rw [ha]
    exact (canonical28828 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2039 + difference 4 2) (sourceB2039 + difference 2 4) sourceC2039) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4663) := by
    have ha : (tripleCharges (sourceA2039 + difference 4 2) (sourceB2039 + difference 2 4) sourceC2039) = raw28829 := by
      apply Matrix.ext; unfold tripleCharges sourceA2039 sourceB2039 sourceC2039 difference raw28829; decide +kernel
    rw [ha]
    exact (canonical28829 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2039 + difference 4 3) (sourceB2039 + difference 3 4) sourceC2039) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4681) := by
    have ha : (tripleCharges (sourceA2039 + difference 4 3) (sourceB2039 + difference 3 4) sourceC2039) = raw28830 := by
      apply Matrix.ext; unfold tripleCharges sourceA2039 sourceB2039 sourceC2039 difference raw28830; decide +kernel
    rw [ha]
    exact (canonical28830 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2039 + difference 4 5) (sourceB2039 + difference 5 4) sourceC2039) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5140) := by
    have ha : (tripleCharges (sourceA2039 + difference 4 5) (sourceB2039 + difference 5 4) sourceC2039) = raw10603 := by
      apply Matrix.ext; unfold tripleCharges sourceA2039 sourceB2039 sourceC2039 difference raw10603; decide +kernel
    rw [ha]
    exact (canonical10603 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2039 + difference 5 0) (sourceB2039 + difference 0 5) sourceC2039) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4330) := by
    have ha : (tripleCharges (sourceA2039 + difference 5 0) (sourceB2039 + difference 0 5) sourceC2039) = raw20862 := by
      apply Matrix.ext; unfold tripleCharges sourceA2039 sourceB2039 sourceC2039 difference raw20862; decide +kernel
    rw [ha]
    exact (canonical20862 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2039 + difference 5 1) (sourceB2039 + difference 1 5) sourceC2039) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4334) := by
    have ha : (tripleCharges (sourceA2039 + difference 5 1) (sourceB2039 + difference 1 5) sourceC2039) = raw28831 := by
      apply Matrix.ext; unfold tripleCharges sourceA2039 sourceB2039 sourceC2039 difference raw28831; decide +kernel
    rw [ha]
    exact (canonical28831 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2039 + difference 5 2) (sourceB2039 + difference 2 5) sourceC2039) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4326) := by
    have ha : (tripleCharges (sourceA2039 + difference 5 2) (sourceB2039 + difference 2 5) sourceC2039) = raw28832 := by
      apply Matrix.ext; unfold tripleCharges sourceA2039 sourceB2039 sourceC2039 difference raw28832; decide +kernel
    rw [ha]
    exact (canonical28832 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2039 + difference 5 3) (sourceB2039 + difference 3 5) sourceC2039) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4346) := by
    have ha : (tripleCharges (sourceA2039 + difference 5 3) (sourceB2039 + difference 3 5) sourceC2039) = raw28833 := by
      apply Matrix.ext; unfold tripleCharges sourceA2039 sourceB2039 sourceC2039 difference raw28833; decide +kernel
    rw [ha]
    exact (canonical28833 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2039 + difference 5 4) (sourceB2039 + difference 4 5) sourceC2039) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4460) := by
    have ha : (tripleCharges (sourceA2039 + difference 5 4) (sourceB2039 + difference 4 5) sourceC2039) = raw28834 := by
      apply Matrix.ext; unfold tripleCharges sourceA2039 sourceB2039 sourceC2039 difference raw28834; decide +kernel
    rw [ha]
    exact (canonical28834 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2039 sourceB2039 sourceC2039
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2039, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2040 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2040 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC2040 : Charge := ![2, 0, 0, 1, 0, -3]
def sourceForm2040 : Integer.Sparse Master := [(Sum.inr 1116, 1), (Sum.inr 1118, 1), (Sum.inr 1121, 1), (Sum.inr 1137, 1), (Sum.inr 1271, 1), (Sum.inr 1329, 1), (Sum.inr 1334, 1), (Sum.inr 1342, 1), (Sum.inr 1416, 1), (Sum.inr 2800, 1), (Sum.inr 2803, 1), (Sum.inr 2816, 1), (Sum.inr 2890, 1), (Sum.inr 2895, 1), (Sum.inr 2901, 1), (Sum.inr 2904, 1), (Sum.inr 2940, 1), (Sum.inr 2941, 2), (Sum.inr 2942, 1), (Sum.inr 2964, 1), (Sum.inr 2966, 1), (Sum.inr 3004, 1), (Sum.inr 3089, 1), (Sum.inr 3113, 1), (Sum.inr 3114, 1), (Sum.inr 3205, 1), (Sum.inr 3206, 1), (Sum.inr 3214, 1), (Sum.inr 3230, 1)]

theorem sourceEq2040 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2040 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2040 + difference 0 1) (sourceB2040 + difference 1 0) sourceC2040) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3206) := by
    have ha : (tripleCharges (sourceA2040 + difference 0 1) (sourceB2040 + difference 1 0) sourceC2040) = raw28835 := by
      apply Matrix.ext; unfold tripleCharges sourceA2040 sourceB2040 sourceC2040 difference raw28835; decide +kernel
    rw [ha]
    exact (canonical28835 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2040 + difference 0 2) (sourceB2040 + difference 2 0) sourceC2040) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3205) := by
    have ha : (tripleCharges (sourceA2040 + difference 0 2) (sourceB2040 + difference 2 0) sourceC2040) = raw28836 := by
      apply Matrix.ext; unfold tripleCharges sourceA2040 sourceB2040 sourceC2040 difference raw28836; decide +kernel
    rw [ha]
    exact (canonical28836 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2040 + difference 0 3) (sourceB2040 + difference 3 0) sourceC2040) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3214) := by
    have ha : (tripleCharges (sourceA2040 + difference 0 3) (sourceB2040 + difference 3 0) sourceC2040) = raw28837 := by
      apply Matrix.ext; unfold tripleCharges sourceA2040 sourceB2040 sourceC2040 difference raw28837; decide +kernel
    rw [ha]
    exact (canonical28837 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2040 + difference 0 4) (sourceB2040 + difference 4 0) sourceC2040) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3230) := by
    have ha : (tripleCharges (sourceA2040 + difference 0 4) (sourceB2040 + difference 4 0) sourceC2040) = raw28838 := by
      apply Matrix.ext; unfold tripleCharges sourceA2040 sourceB2040 sourceC2040 difference raw28838; decide +kernel
    rw [ha]
    exact (canonical28838 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2040 + difference 0 5) (sourceB2040 + difference 5 0) sourceC2040) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3089) := by
    have ha : (tripleCharges (sourceA2040 + difference 0 5) (sourceB2040 + difference 5 0) sourceC2040) = raw10612 := by
      apply Matrix.ext; unfold tripleCharges sourceA2040 sourceB2040 sourceC2040 difference raw10612; decide +kernel
    rw [ha]
    exact (canonical10612 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2040 + difference 1 0) (sourceB2040 + difference 0 1) sourceC2040) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1271) := by
    have ha : (tripleCharges (sourceA2040 + difference 1 0) (sourceB2040 + difference 0 1) sourceC2040) = raw10637 := by
      apply Matrix.ext; unfold tripleCharges sourceA2040 sourceB2040 sourceC2040 difference raw10637; decide +kernel
    rw [ha]
    exact (canonical10637 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2040 + difference 1 2) (sourceB2040 + difference 2 1) sourceC2040) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2941) := by
    have ha : (tripleCharges (sourceA2040 + difference 1 2) (sourceB2040 + difference 2 1) sourceC2040) = raw10639 := by
      apply Matrix.ext; unfold tripleCharges sourceA2040 sourceB2040 sourceC2040 difference raw10639; decide +kernel
    rw [ha]
    exact (canonical10639 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2040 + difference 1 3) (sourceB2040 + difference 3 1) sourceC2040) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3004) := by
    have ha : (tripleCharges (sourceA2040 + difference 1 3) (sourceB2040 + difference 3 1) sourceC2040) = raw10640 := by
      apply Matrix.ext; unfold tripleCharges sourceA2040 sourceB2040 sourceC2040 difference raw10640; decide +kernel
    rw [ha]
    exact (canonical10640 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2040 + difference 1 4) (sourceB2040 + difference 4 1) sourceC2040) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3114) := by
    have ha : (tripleCharges (sourceA2040 + difference 1 4) (sourceB2040 + difference 4 1) sourceC2040) = raw10641 := by
      apply Matrix.ext; unfold tripleCharges sourceA2040 sourceB2040 sourceC2040 difference raw10641; decide +kernel
    rw [ha]
    exact (canonical10641 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2040 + difference 1 5) (sourceB2040 + difference 5 1) sourceC2040) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3113) := by
    have ha : (tripleCharges (sourceA2040 + difference 1 5) (sourceB2040 + difference 5 1) sourceC2040) = raw20866 := by
      apply Matrix.ext; unfold tripleCharges sourceA2040 sourceB2040 sourceC2040 difference raw20866; decide +kernel
    rw [ha]
    exact (canonical20866 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2040 + difference 2 0) (sourceB2040 + difference 0 2) sourceC2040) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1116) := by
    have ha : (tripleCharges (sourceA2040 + difference 2 0) (sourceB2040 + difference 0 2) sourceC2040) = raw20872 := by
      apply Matrix.ext; unfold tripleCharges sourceA2040 sourceB2040 sourceC2040 difference raw20872; decide +kernel
    rw [ha]
    exact (canonical20872 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2040 + difference 2 1) (sourceB2040 + difference 1 2) sourceC2040) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2800) := by
    have ha : (tripleCharges (sourceA2040 + difference 2 1) (sourceB2040 + difference 1 2) sourceC2040) = raw28839 := by
      apply Matrix.ext; unfold tripleCharges sourceA2040 sourceB2040 sourceC2040 difference raw28839; decide +kernel
    rw [ha]
    exact (canonical28839 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2040 + difference 2 3) (sourceB2040 + difference 3 2) sourceC2040) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2901) := by
    have ha : (tripleCharges (sourceA2040 + difference 2 3) (sourceB2040 + difference 3 2) sourceC2040) = raw28840 := by
      apply Matrix.ext; unfold tripleCharges sourceA2040 sourceB2040 sourceC2040 difference raw28840; decide +kernel
    rw [ha]
    exact (canonical28840 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2040 + difference 2 4) (sourceB2040 + difference 4 2) sourceC2040) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2941) := by
    have ha : (tripleCharges (sourceA2040 + difference 2 4) (sourceB2040 + difference 4 2) sourceC2040) = raw28841 := by
      apply Matrix.ext; unfold tripleCharges sourceA2040 sourceB2040 sourceC2040 difference raw28841; decide +kernel
    rw [ha]
    exact (canonical28841 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2040 + difference 2 5) (sourceB2040 + difference 5 2) sourceC2040) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2940) := by
    have ha : (tripleCharges (sourceA2040 + difference 2 5) (sourceB2040 + difference 5 2) sourceC2040) = raw10623 := by
      apply Matrix.ext; unfold tripleCharges sourceA2040 sourceB2040 sourceC2040 difference raw10623; decide +kernel
    rw [ha]
    exact (canonical10623 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2040 + difference 3 0) (sourceB2040 + difference 0 3) sourceC2040) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1137) := by
    have ha : (tripleCharges (sourceA2040 + difference 3 0) (sourceB2040 + difference 0 3) sourceC2040) = raw20876 := by
      apply Matrix.ext; unfold tripleCharges sourceA2040 sourceB2040 sourceC2040 difference raw20876; decide +kernel
    rw [ha]
    exact (canonical20876 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2040 + difference 3 1) (sourceB2040 + difference 1 3) sourceC2040) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2816) := by
    have ha : (tripleCharges (sourceA2040 + difference 3 1) (sourceB2040 + difference 1 3) sourceC2040) = raw28842 := by
      apply Matrix.ext; unfold tripleCharges sourceA2040 sourceB2040 sourceC2040 difference raw28842; decide +kernel
    rw [ha]
    exact (canonical28842 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2040 + difference 3 2) (sourceB2040 + difference 2 3) sourceC2040) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2895) := by
    have ha : (tripleCharges (sourceA2040 + difference 3 2) (sourceB2040 + difference 2 3) sourceC2040) = raw28843 := by
      apply Matrix.ext; unfold tripleCharges sourceA2040 sourceB2040 sourceC2040 difference raw28843; decide +kernel
    rw [ha]
    exact (canonical28843 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2040 + difference 3 4) (sourceB2040 + difference 4 3) sourceC2040) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2966) := by
    have ha : (tripleCharges (sourceA2040 + difference 3 4) (sourceB2040 + difference 4 3) sourceC2040) = raw28844 := by
      apply Matrix.ext; unfold tripleCharges sourceA2040 sourceB2040 sourceC2040 difference raw28844; decide +kernel
    rw [ha]
    exact (canonical28844 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2040 + difference 3 5) (sourceB2040 + difference 5 3) sourceC2040) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2964) := by
    have ha : (tripleCharges (sourceA2040 + difference 3 5) (sourceB2040 + difference 5 3) sourceC2040) = raw10628 := by
      apply Matrix.ext; unfold tripleCharges sourceA2040 sourceB2040 sourceC2040 difference raw10628; decide +kernel
    rw [ha]
    exact (canonical10628 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2040 + difference 4 0) (sourceB2040 + difference 0 4) sourceC2040) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1121) := by
    have ha : (tripleCharges (sourceA2040 + difference 4 0) (sourceB2040 + difference 0 4) sourceC2040) = raw20880 := by
      apply Matrix.ext; unfold tripleCharges sourceA2040 sourceB2040 sourceC2040 difference raw20880; decide +kernel
    rw [ha]
    exact (canonical20880 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2040 + difference 4 1) (sourceB2040 + difference 1 4) sourceC2040) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2803) := by
    have ha : (tripleCharges (sourceA2040 + difference 4 1) (sourceB2040 + difference 1 4) sourceC2040) = raw28845 := by
      apply Matrix.ext; unfold tripleCharges sourceA2040 sourceB2040 sourceC2040 difference raw28845; decide +kernel
    rw [ha]
    exact (canonical28845 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2040 + difference 4 2) (sourceB2040 + difference 2 4) sourceC2040) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2890) := by
    have ha : (tripleCharges (sourceA2040 + difference 4 2) (sourceB2040 + difference 2 4) sourceC2040) = raw28846 := by
      apply Matrix.ext; unfold tripleCharges sourceA2040 sourceB2040 sourceC2040 difference raw28846; decide +kernel
    rw [ha]
    exact (canonical28846 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2040 + difference 4 3) (sourceB2040 + difference 3 4) sourceC2040) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2904) := by
    have ha : (tripleCharges (sourceA2040 + difference 4 3) (sourceB2040 + difference 3 4) sourceC2040) = raw28847 := by
      apply Matrix.ext; unfold tripleCharges sourceA2040 sourceB2040 sourceC2040 difference raw28847; decide +kernel
    rw [ha]
    exact (canonical28847 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2040 + difference 4 5) (sourceB2040 + difference 5 4) sourceC2040) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2942) := by
    have ha : (tripleCharges (sourceA2040 + difference 4 5) (sourceB2040 + difference 5 4) sourceC2040) = raw10633 := by
      apply Matrix.ext; unfold tripleCharges sourceA2040 sourceB2040 sourceC2040 difference raw10633; decide +kernel
    rw [ha]
    exact (canonical10633 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2040 + difference 5 0) (sourceB2040 + difference 0 5) sourceC2040) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1118) := by
    have ha : (tripleCharges (sourceA2040 + difference 5 0) (sourceB2040 + difference 0 5) sourceC2040) = raw20884 := by
      apply Matrix.ext; unfold tripleCharges sourceA2040 sourceB2040 sourceC2040 difference raw20884; decide +kernel
    rw [ha]
    exact (canonical20884 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2040 + difference 5 1) (sourceB2040 + difference 1 5) sourceC2040) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1334) := by
    have ha : (tripleCharges (sourceA2040 + difference 5 1) (sourceB2040 + difference 1 5) sourceC2040) = raw28848 := by
      apply Matrix.ext; unfold tripleCharges sourceA2040 sourceB2040 sourceC2040 difference raw28848; decide +kernel
    rw [ha]
    exact (canonical28848 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2040 + difference 5 2) (sourceB2040 + difference 2 5) sourceC2040) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1329) := by
    have ha : (tripleCharges (sourceA2040 + difference 5 2) (sourceB2040 + difference 2 5) sourceC2040) = raw28849 := by
      apply Matrix.ext; unfold tripleCharges sourceA2040 sourceB2040 sourceC2040 difference raw28849; decide +kernel
    rw [ha]
    exact (canonical28849 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2040 + difference 5 3) (sourceB2040 + difference 3 5) sourceC2040) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1342) := by
    have ha : (tripleCharges (sourceA2040 + difference 5 3) (sourceB2040 + difference 3 5) sourceC2040) = raw28850 := by
      apply Matrix.ext; unfold tripleCharges sourceA2040 sourceB2040 sourceC2040 difference raw28850; decide +kernel
    rw [ha]
    exact (canonical28850 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2040 + difference 5 4) (sourceB2040 + difference 4 5) sourceC2040) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1416) := by
    have ha : (tripleCharges (sourceA2040 + difference 5 4) (sourceB2040 + difference 4 5) sourceC2040) = raw28851 := by
      apply Matrix.ext; unfold tripleCharges sourceA2040 sourceB2040 sourceC2040 difference raw28851; decide +kernel
    rw [ha]
    exact (canonical28851 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2040 sourceB2040 sourceC2040
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2040, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2041 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2041 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC2041 : Charge := ![2, 0, 0, 1, 0, -3]
def sourceForm2041 : Integer.Sparse Master := [(Sum.inr 1663, 1), (Sum.inr 1672, 1), (Sum.inr 1674, 1), (Sum.inr 1679, 1), (Sum.inr 1725, 1), (Sum.inr 2140, 1), (Sum.inr 2149, 1), (Sum.inr 2151, 1), (Sum.inr 2155, 1), (Sum.inr 2172, 1), (Sum.inr 2173, 1), (Sum.inr 2176, 1), (Sum.inr 2189, 1), (Sum.inr 2190, 1), (Sum.inr 2200, 1), (Sum.inr 2203, 2), (Sum.inr 2205, 1), (Sum.inr 2212, 1), (Sum.inr 2215, 1), (Sum.inr 2226, 1), (Sum.inr 2228, 1), (Sum.inr 2261, 1), (Sum.inr 2264, 1), (Sum.inr 2292, 1), (Sum.inr 2670, 1), (Sum.inr 2693, 1), (Sum.inr 2719, 1), (Sum.inr 2722, 1), (Sum.inr 2740, 1)]

theorem sourceEq2041 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2041 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2041 + difference 0 1) (sourceB2041 + difference 1 0) sourceC2041) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2215) := by
    have ha : (tripleCharges (sourceA2041 + difference 0 1) (sourceB2041 + difference 1 0) sourceC2041) = raw28852 := by
      apply Matrix.ext; unfold tripleCharges sourceA2041 sourceB2041 sourceC2041 difference raw28852; decide +kernel
    rw [ha]
    exact (canonical28852 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2041 + difference 0 2) (sourceB2041 + difference 2 0) sourceC2041) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2190) := by
    have ha : (tripleCharges (sourceA2041 + difference 0 2) (sourceB2041 + difference 2 0) sourceC2041) = raw28853 := by
      apply Matrix.ext; unfold tripleCharges sourceA2041 sourceB2041 sourceC2041 difference raw28853; decide +kernel
    rw [ha]
    exact (canonical28853 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2041 + difference 0 3) (sourceB2041 + difference 3 0) sourceC2041) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2205) := by
    have ha : (tripleCharges (sourceA2041 + difference 0 3) (sourceB2041 + difference 3 0) sourceC2041) = raw28854 := by
      apply Matrix.ext; unfold tripleCharges sourceA2041 sourceB2041 sourceC2041 difference raw28854; decide +kernel
    rw [ha]
    exact (canonical28854 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2041 + difference 0 4) (sourceB2041 + difference 4 0) sourceC2041) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2264) := by
    have ha : (tripleCharges (sourceA2041 + difference 0 4) (sourceB2041 + difference 4 0) sourceC2041) = raw28855 := by
      apply Matrix.ext; unfold tripleCharges sourceA2041 sourceB2041 sourceC2041 difference raw28855; decide +kernel
    rw [ha]
    exact (canonical28855 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2041 + difference 0 5) (sourceB2041 + difference 5 0) sourceC2041) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA2041 + difference 0 5) (sourceB2041 + difference 5 0) sourceC2041) = raw10642 := by
      apply Matrix.ext; unfold tripleCharges sourceA2041 sourceB2041 sourceC2041 difference raw10642; decide +kernel
    rw [ha]
    exact (canonical10642 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2041 + difference 1 0) (sourceB2041 + difference 0 1) sourceC2041) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2226) := by
    have ha : (tripleCharges (sourceA2041 + difference 1 0) (sourceB2041 + difference 0 1) sourceC2041) = raw10667 := by
      apply Matrix.ext; unfold tripleCharges sourceA2041 sourceB2041 sourceC2041 difference raw10667; decide +kernel
    rw [ha]
    exact (canonical10667 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2041 + difference 1 2) (sourceB2041 + difference 2 1) sourceC2041) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2203) := by
    have ha : (tripleCharges (sourceA2041 + difference 1 2) (sourceB2041 + difference 2 1) sourceC2041) = raw10669 := by
      apply Matrix.ext; unfold tripleCharges sourceA2041 sourceB2041 sourceC2041 difference raw10669; decide +kernel
    rw [ha]
    exact (canonical10669 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2041 + difference 1 3) (sourceB2041 + difference 3 1) sourceC2041) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2228) := by
    have ha : (tripleCharges (sourceA2041 + difference 1 3) (sourceB2041 + difference 3 1) sourceC2041) = raw10670 := by
      apply Matrix.ext; unfold tripleCharges sourceA2041 sourceB2041 sourceC2041 difference raw10670; decide +kernel
    rw [ha]
    exact (canonical10670 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2041 + difference 1 4) (sourceB2041 + difference 4 1) sourceC2041) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2292) := by
    have ha : (tripleCharges (sourceA2041 + difference 1 4) (sourceB2041 + difference 4 1) sourceC2041) = raw10671 := by
      apply Matrix.ext; unfold tripleCharges sourceA2041 sourceB2041 sourceC2041 difference raw10671; decide +kernel
    rw [ha]
    exact (canonical10671 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2041 + difference 1 5) (sourceB2041 + difference 5 1) sourceC2041) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2740) := by
    have ha : (tripleCharges (sourceA2041 + difference 1 5) (sourceB2041 + difference 5 1) sourceC2041) = raw20888 := by
      apply Matrix.ext; unfold tripleCharges sourceA2041 sourceB2041 sourceC2041 difference raw20888; decide +kernel
    rw [ha]
    exact (canonical20888 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2041 + difference 2 0) (sourceB2041 + difference 0 2) sourceC2041) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2172) := by
    have ha : (tripleCharges (sourceA2041 + difference 2 0) (sourceB2041 + difference 0 2) sourceC2041) = raw20894 := by
      apply Matrix.ext; unfold tripleCharges sourceA2041 sourceB2041 sourceC2041 difference raw20894; decide +kernel
    rw [ha]
    exact (canonical20894 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2041 + difference 2 1) (sourceB2041 + difference 1 2) sourceC2041) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2176) := by
    have ha : (tripleCharges (sourceA2041 + difference 2 1) (sourceB2041 + difference 1 2) sourceC2041) = raw28856 := by
      apply Matrix.ext; unfold tripleCharges sourceA2041 sourceB2041 sourceC2041 difference raw28856; decide +kernel
    rw [ha]
    exact (canonical28856 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2041 + difference 2 3) (sourceB2041 + difference 3 2) sourceC2041) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2173) := by
    have ha : (tripleCharges (sourceA2041 + difference 2 3) (sourceB2041 + difference 3 2) sourceC2041) = raw28857 := by
      apply Matrix.ext; unfold tripleCharges sourceA2041 sourceB2041 sourceC2041 difference raw28857; decide +kernel
    rw [ha]
    exact (canonical28857 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2041 + difference 2 4) (sourceB2041 + difference 4 2) sourceC2041) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2203) := by
    have ha : (tripleCharges (sourceA2041 + difference 2 4) (sourceB2041 + difference 4 2) sourceC2041) = raw28858 := by
      apply Matrix.ext; unfold tripleCharges sourceA2041 sourceB2041 sourceC2041 difference raw28858; decide +kernel
    rw [ha]
    exact (canonical28858 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2041 + difference 2 5) (sourceB2041 + difference 5 2) sourceC2041) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2693) := by
    have ha : (tripleCharges (sourceA2041 + difference 2 5) (sourceB2041 + difference 5 2) sourceC2041) = raw10653 := by
      apply Matrix.ext; unfold tripleCharges sourceA2041 sourceB2041 sourceC2041 difference raw10653; decide +kernel
    rw [ha]
    exact (canonical10653 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2041 + difference 3 0) (sourceB2041 + difference 0 3) sourceC2041) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2200) := by
    have ha : (tripleCharges (sourceA2041 + difference 3 0) (sourceB2041 + difference 0 3) sourceC2041) = raw20898 := by
      apply Matrix.ext; unfold tripleCharges sourceA2041 sourceB2041 sourceC2041 difference raw20898; decide +kernel
    rw [ha]
    exact (canonical20898 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2041 + difference 3 1) (sourceB2041 + difference 1 3) sourceC2041) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2212) := by
    have ha : (tripleCharges (sourceA2041 + difference 3 1) (sourceB2041 + difference 1 3) sourceC2041) = raw28859 := by
      apply Matrix.ext; unfold tripleCharges sourceA2041 sourceB2041 sourceC2041 difference raw28859; decide +kernel
    rw [ha]
    exact (canonical28859 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2041 + difference 3 2) (sourceB2041 + difference 2 3) sourceC2041) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2189) := by
    have ha : (tripleCharges (sourceA2041 + difference 3 2) (sourceB2041 + difference 2 3) sourceC2041) = raw28860 := by
      apply Matrix.ext; unfold tripleCharges sourceA2041 sourceB2041 sourceC2041 difference raw28860; decide +kernel
    rw [ha]
    exact (canonical28860 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2041 + difference 3 4) (sourceB2041 + difference 4 3) sourceC2041) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2261) := by
    have ha : (tripleCharges (sourceA2041 + difference 3 4) (sourceB2041 + difference 4 3) sourceC2041) = raw28861 := by
      apply Matrix.ext; unfold tripleCharges sourceA2041 sourceB2041 sourceC2041 difference raw28861; decide +kernel
    rw [ha]
    exact (canonical28861 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2041 + difference 3 5) (sourceB2041 + difference 5 3) sourceC2041) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2719) := by
    have ha : (tripleCharges (sourceA2041 + difference 3 5) (sourceB2041 + difference 5 3) sourceC2041) = raw10658 := by
      apply Matrix.ext; unfold tripleCharges sourceA2041 sourceB2041 sourceC2041 difference raw10658; decide +kernel
    rw [ha]
    exact (canonical10658 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2041 + difference 4 0) (sourceB2041 + difference 0 4) sourceC2041) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2149) := by
    have ha : (tripleCharges (sourceA2041 + difference 4 0) (sourceB2041 + difference 0 4) sourceC2041) = raw20902 := by
      apply Matrix.ext; unfold tripleCharges sourceA2041 sourceB2041 sourceC2041 difference raw20902; decide +kernel
    rw [ha]
    exact (canonical20902 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2041 + difference 4 1) (sourceB2041 + difference 1 4) sourceC2041) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2155) := by
    have ha : (tripleCharges (sourceA2041 + difference 4 1) (sourceB2041 + difference 1 4) sourceC2041) = raw28862 := by
      apply Matrix.ext; unfold tripleCharges sourceA2041 sourceB2041 sourceC2041 difference raw28862; decide +kernel
    rw [ha]
    exact (canonical28862 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2041 + difference 4 2) (sourceB2041 + difference 2 4) sourceC2041) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2140) := by
    have ha : (tripleCharges (sourceA2041 + difference 4 2) (sourceB2041 + difference 2 4) sourceC2041) = raw28863 := by
      apply Matrix.ext; unfold tripleCharges sourceA2041 sourceB2041 sourceC2041 difference raw28863; decide +kernel
    rw [ha]
    exact (canonical28863 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2041 + difference 4 3) (sourceB2041 + difference 3 4) sourceC2041) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2151) := by
    have ha : (tripleCharges (sourceA2041 + difference 4 3) (sourceB2041 + difference 3 4) sourceC2041) = raw28864 := by
      apply Matrix.ext; unfold tripleCharges sourceA2041 sourceB2041 sourceC2041 difference raw28864; decide +kernel
    rw [ha]
    exact (canonical28864 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2041 + difference 4 5) (sourceB2041 + difference 5 4) sourceC2041) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2670) := by
    have ha : (tripleCharges (sourceA2041 + difference 4 5) (sourceB2041 + difference 5 4) sourceC2041) = raw10663 := by
      apply Matrix.ext; unfold tripleCharges sourceA2041 sourceB2041 sourceC2041 difference raw10663; decide +kernel
    rw [ha]
    exact (canonical10663 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2041 + difference 5 0) (sourceB2041 + difference 0 5) sourceC2041) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1672) := by
    have ha : (tripleCharges (sourceA2041 + difference 5 0) (sourceB2041 + difference 0 5) sourceC2041) = raw20906 := by
      apply Matrix.ext; unfold tripleCharges sourceA2041 sourceB2041 sourceC2041 difference raw20906; decide +kernel
    rw [ha]
    exact (canonical20906 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2041 + difference 5 1) (sourceB2041 + difference 1 5) sourceC2041) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1679) := by
    have ha : (tripleCharges (sourceA2041 + difference 5 1) (sourceB2041 + difference 1 5) sourceC2041) = raw28865 := by
      apply Matrix.ext; unfold tripleCharges sourceA2041 sourceB2041 sourceC2041 difference raw28865; decide +kernel
    rw [ha]
    exact (canonical28865 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2041 + difference 5 2) (sourceB2041 + difference 2 5) sourceC2041) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1663) := by
    have ha : (tripleCharges (sourceA2041 + difference 5 2) (sourceB2041 + difference 2 5) sourceC2041) = raw28866 := by
      apply Matrix.ext; unfold tripleCharges sourceA2041 sourceB2041 sourceC2041 difference raw28866; decide +kernel
    rw [ha]
    exact (canonical28866 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2041 + difference 5 3) (sourceB2041 + difference 3 5) sourceC2041) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1674) := by
    have ha : (tripleCharges (sourceA2041 + difference 5 3) (sourceB2041 + difference 3 5) sourceC2041) = raw28867 := by
      apply Matrix.ext; unfold tripleCharges sourceA2041 sourceB2041 sourceC2041 difference raw28867; decide +kernel
    rw [ha]
    exact (canonical28867 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2041 + difference 5 4) (sourceB2041 + difference 4 5) sourceC2041) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1725) := by
    have ha : (tripleCharges (sourceA2041 + difference 5 4) (sourceB2041 + difference 4 5) sourceC2041) = raw28868 := by
      apply Matrix.ext; unfold tripleCharges sourceA2041 sourceB2041 sourceC2041 difference raw28868; decide +kernel
    rw [ha]
    exact (canonical28868 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2041 sourceB2041 sourceC2041
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2041, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2042 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2042 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC2042 : Charge := ![2, 0, 0, 1, 0, -3]
def sourceForm2042 : Integer.Sparse Master := [(Sum.inr 912, 1), (Sum.inr 1795, 1), (Sum.inr 1955, 1), (Sum.inr 1978, 1), (Sum.inr 2022, 1), (Sum.inr 2028, 1), (Sum.inr 4084, -1)]

theorem sourceEq2042 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2042 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2042 + difference 0 1) (sourceB2042 + difference 1 0) sourceC2042) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2028) := by
    have ha : (tripleCharges (sourceA2042 + difference 0 1) (sourceB2042 + difference 1 0) sourceC2042) = raw28869 := by
      apply Matrix.ext; unfold tripleCharges sourceA2042 sourceB2042 sourceC2042 difference raw28869; decide +kernel
    rw [ha]
    exact (canonical28869 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2042 + difference 1 1) (sourceB2042 + difference 1 1) sourceC2042) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2022) := by
    have ha : (tripleCharges (sourceA2042 + difference 1 1) (sourceB2042 + difference 1 1) sourceC2042) = raw20921 := by
      apply Matrix.ext; unfold tripleCharges sourceA2042 sourceB2042 sourceC2042 difference raw20921; decide +kernel
    rw [ha]
    exact (canonical20921 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2042 + difference 2 1) (sourceB2042 + difference 1 2) sourceC2042) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1955) := by
    have ha : (tripleCharges (sourceA2042 + difference 2 1) (sourceB2042 + difference 1 2) sourceC2042) = raw28870 := by
      apply Matrix.ext; unfold tripleCharges sourceA2042 sourceB2042 sourceC2042 difference raw28870; decide +kernel
    rw [ha]
    exact (canonical28870 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2042 + difference 3 1) (sourceB2042 + difference 1 3) sourceC2042) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1978) := by
    have ha : (tripleCharges (sourceA2042 + difference 3 1) (sourceB2042 + difference 1 3) sourceC2042) = raw28871 := by
      apply Matrix.ext; unfold tripleCharges sourceA2042 sourceB2042 sourceC2042 difference raw28871; decide +kernel
    rw [ha]
    exact (canonical28871 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2042 + difference 4 1) (sourceB2042 + difference 1 4) sourceC2042) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1795) := by
    have ha : (tripleCharges (sourceA2042 + difference 4 1) (sourceB2042 + difference 1 4) sourceC2042) = raw28872 := by
      apply Matrix.ext; unfold tripleCharges sourceA2042 sourceB2042 sourceC2042 difference raw28872; decide +kernel
    rw [ha]
    exact (canonical28872 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2042 + difference 5 1) (sourceB2042 + difference 1 5) sourceC2042) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 912) := by
    have ha : (tripleCharges (sourceA2042 + difference 5 1) (sourceB2042 + difference 1 5) sourceC2042) = raw28873 := by
      apply Matrix.ext; unfold tripleCharges sourceA2042 sourceB2042 sourceC2042 difference raw28873; decide +kernel
    rw [ha]
    exact (canonical28873 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2042 + sourceB2042) sourceC2042) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA2042 + sourceB2042) sourceC2042) = raw20916 := by
      apply Matrix.ext; unfold doubleCharges sourceA2042 sourceB2042 sourceC2042 raw20916; decide +kernel
    rw [ha]
    exact (canonical20916 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2042 sourceB2042 sourceC2042
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2042, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2043 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2043 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC2043 : Charge := ![2, 0, 0, 1, 0, -3]
def sourceForm2043 : Integer.Sparse Master := [(Sum.inr 1147, 1), (Sum.inr 1955, 1), (Sum.inr 1960, 1), (Sum.inr 2022, 2), (Sum.inr 2552, 1), (Sum.inr 4084, -1)]

theorem sourceEq2043 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2043 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2043 + difference 2 0) (sourceB2043 + difference 0 2) sourceC2043) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1147) := by
    have ha : (tripleCharges (sourceA2043 + difference 2 0) (sourceB2043 + difference 0 2) sourceC2043) = raw20922 := by
      apply Matrix.ext; unfold tripleCharges sourceA2043 sourceB2043 sourceC2043 difference raw20922; decide +kernel
    rw [ha]
    exact (canonical20922 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2043 + difference 2 1) (sourceB2043 + difference 1 2) sourceC2043) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1955) := by
    have ha : (tripleCharges (sourceA2043 + difference 2 1) (sourceB2043 + difference 1 2) sourceC2043) = raw28870 := by
      apply Matrix.ext; unfold tripleCharges sourceA2043 sourceB2043 sourceC2043 difference raw28870; decide +kernel
    rw [ha]
    exact (canonical28870 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2043 + difference 2 2) (sourceB2043 + difference 2 2) sourceC2043) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2022) := by
    have ha : (tripleCharges (sourceA2043 + difference 2 2) (sourceB2043 + difference 2 2) sourceC2043) = raw20921 := by
      apply Matrix.ext; unfold tripleCharges sourceA2043 sourceB2043 sourceC2043 difference raw20921; decide +kernel
    rw [ha]
    exact (canonical20921 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2043 + difference 2 3) (sourceB2043 + difference 3 2) sourceC2043) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1960) := by
    have ha : (tripleCharges (sourceA2043 + difference 2 3) (sourceB2043 + difference 3 2) sourceC2043) = raw28874 := by
      apply Matrix.ext; unfold tripleCharges sourceA2043 sourceB2043 sourceC2043 difference raw28874; decide +kernel
    rw [ha]
    exact (canonical28874 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2043 + difference 2 4) (sourceB2043 + difference 4 2) sourceC2043) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2022) := by
    have ha : (tripleCharges (sourceA2043 + difference 2 4) (sourceB2043 + difference 4 2) sourceC2043) = raw28875 := by
      apply Matrix.ext; unfold tripleCharges sourceA2043 sourceB2043 sourceC2043 difference raw28875; decide +kernel
    rw [ha]
    exact (canonical28875 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2043 + difference 2 5) (sourceB2043 + difference 5 2) sourceC2043) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2552) := by
    have ha : (tripleCharges (sourceA2043 + difference 2 5) (sourceB2043 + difference 5 2) sourceC2043) = raw28876 := by
      apply Matrix.ext; unfold tripleCharges sourceA2043 sourceB2043 sourceC2043 difference raw28876; decide +kernel
    rw [ha]
    exact (canonical28876 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2043 + sourceB2043) sourceC2043) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA2043 + sourceB2043) sourceC2043) = raw20916 := by
      apply Matrix.ext; unfold doubleCharges sourceA2043 sourceB2043 sourceC2043 raw20916; decide +kernel
    rw [ha]
    exact (canonical20916 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2043 sourceB2043 sourceC2043
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2043, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2044 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2044 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC2044 : Charge := ![2, 0, 0, 1, 0, -3]
def sourceForm2044 : Integer.Sparse Master := [(Sum.inr 904, 1), (Sum.inr 1789, 1), (Sum.inr 1972, 1), (Sum.inr 2019, 1), (Sum.inr 2022, 2), (Sum.inr 4084, -1)]

theorem sourceEq2044 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2044 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2044 + difference 0 2) (sourceB2044 + difference 2 0) sourceC2044) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2019) := by
    have ha : (tripleCharges (sourceA2044 + difference 0 2) (sourceB2044 + difference 2 0) sourceC2044) = raw28877 := by
      apply Matrix.ext; unfold tripleCharges sourceA2044 sourceB2044 sourceC2044 difference raw28877; decide +kernel
    rw [ha]
    exact (canonical28877 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2044 + difference 1 2) (sourceB2044 + difference 2 1) sourceC2044) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2022) := by
    have ha : (tripleCharges (sourceA2044 + difference 1 2) (sourceB2044 + difference 2 1) sourceC2044) = raw28878 := by
      apply Matrix.ext; unfold tripleCharges sourceA2044 sourceB2044 sourceC2044 difference raw28878; decide +kernel
    rw [ha]
    exact (canonical28878 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2044 + difference 2 2) (sourceB2044 + difference 2 2) sourceC2044) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2022) := by
    have ha : (tripleCharges (sourceA2044 + difference 2 2) (sourceB2044 + difference 2 2) sourceC2044) = raw20921 := by
      apply Matrix.ext; unfold tripleCharges sourceA2044 sourceB2044 sourceC2044 difference raw20921; decide +kernel
    rw [ha]
    exact (canonical20921 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2044 + difference 3 2) (sourceB2044 + difference 2 3) sourceC2044) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1972) := by
    have ha : (tripleCharges (sourceA2044 + difference 3 2) (sourceB2044 + difference 2 3) sourceC2044) = raw28879 := by
      apply Matrix.ext; unfold tripleCharges sourceA2044 sourceB2044 sourceC2044 difference raw28879; decide +kernel
    rw [ha]
    exact (canonical28879 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2044 + difference 4 2) (sourceB2044 + difference 2 4) sourceC2044) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1789) := by
    have ha : (tripleCharges (sourceA2044 + difference 4 2) (sourceB2044 + difference 2 4) sourceC2044) = raw28880 := by
      apply Matrix.ext; unfold tripleCharges sourceA2044 sourceB2044 sourceC2044 difference raw28880; decide +kernel
    rw [ha]
    exact (canonical28880 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2044 + difference 5 2) (sourceB2044 + difference 2 5) sourceC2044) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 904) := by
    have ha : (tripleCharges (sourceA2044 + difference 5 2) (sourceB2044 + difference 2 5) sourceC2044) = raw28881 := by
      apply Matrix.ext; unfold tripleCharges sourceA2044 sourceB2044 sourceC2044 difference raw28881; decide +kernel
    rw [ha]
    exact (canonical28881 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2044 + sourceB2044) sourceC2044) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA2044 + sourceB2044) sourceC2044) = raw20916 := by
      apply Matrix.ext; unfold doubleCharges sourceA2044 sourceB2044 sourceC2044 raw20916; decide +kernel
    rw [ha]
    exact (canonical20916 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2044 sourceB2044 sourceC2044
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2044, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2045 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2045 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC2045 : Charge := ![2, 0, 0, 1, 0, -3]
def sourceForm2045 : Integer.Sparse Master := [(Sum.inr 924, 1), (Sum.inr 1807, 1), (Sum.inr 1960, 1), (Sum.inr 2022, 1), (Sum.inr 2053, 1), (Sum.inr 2060, 1), (Sum.inr 4084, -1)]

theorem sourceEq2045 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2045 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2045 + difference 0 3) (sourceB2045 + difference 3 0) sourceC2045) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2053) := by
    have ha : (tripleCharges (sourceA2045 + difference 0 3) (sourceB2045 + difference 3 0) sourceC2045) = raw28882 := by
      apply Matrix.ext; unfold tripleCharges sourceA2045 sourceB2045 sourceC2045 difference raw28882; decide +kernel
    rw [ha]
    exact (canonical28882 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2045 + difference 1 3) (sourceB2045 + difference 3 1) sourceC2045) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2060) := by
    have ha : (tripleCharges (sourceA2045 + difference 1 3) (sourceB2045 + difference 3 1) sourceC2045) = raw20926 := by
      apply Matrix.ext; unfold tripleCharges sourceA2045 sourceB2045 sourceC2045 difference raw20926; decide +kernel
    rw [ha]
    exact (canonical20926 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2045 + difference 2 3) (sourceB2045 + difference 3 2) sourceC2045) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1960) := by
    have ha : (tripleCharges (sourceA2045 + difference 2 3) (sourceB2045 + difference 3 2) sourceC2045) = raw28874 := by
      apply Matrix.ext; unfold tripleCharges sourceA2045 sourceB2045 sourceC2045 difference raw28874; decide +kernel
    rw [ha]
    exact (canonical28874 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2045 + difference 3 3) (sourceB2045 + difference 3 3) sourceC2045) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2022) := by
    have ha : (tripleCharges (sourceA2045 + difference 3 3) (sourceB2045 + difference 3 3) sourceC2045) = raw20921 := by
      apply Matrix.ext; unfold tripleCharges sourceA2045 sourceB2045 sourceC2045 difference raw20921; decide +kernel
    rw [ha]
    exact (canonical20921 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2045 + difference 4 3) (sourceB2045 + difference 3 4) sourceC2045) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1807) := by
    have ha : (tripleCharges (sourceA2045 + difference 4 3) (sourceB2045 + difference 3 4) sourceC2045) = raw28883 := by
      apply Matrix.ext; unfold tripleCharges sourceA2045 sourceB2045 sourceC2045 difference raw28883; decide +kernel
    rw [ha]
    exact (canonical28883 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2045 + difference 5 3) (sourceB2045 + difference 3 5) sourceC2045) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 924) := by
    have ha : (tripleCharges (sourceA2045 + difference 5 3) (sourceB2045 + difference 3 5) sourceC2045) = raw28884 := by
      apply Matrix.ext; unfold tripleCharges sourceA2045 sourceB2045 sourceC2045 difference raw28884; decide +kernel
    rw [ha]
    exact (canonical28884 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2045 + sourceB2045) sourceC2045) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA2045 + sourceB2045) sourceC2045) = raw20916 := by
      apply Matrix.ext; unfold doubleCharges sourceA2045 sourceB2045 sourceC2045 raw20916; decide +kernel
    rw [ha]
    exact (canonical20916 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2045 sourceB2045 sourceC2045
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2045, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2046 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2046 : Charge := ![2, 0, 0, 1, 0, -3]
def sourceC2046 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceForm2046 : Integer.Sparse Master := [(Sum.inr 4196, 1), (Sum.inr 4198, 1), (Sum.inr 4204, 1), (Sum.inr 4212, 1), (Sum.inr 4251, 1), (Sum.inr 4320, 1), (Sum.inr 4324, 1), (Sum.inr 4343, 1), (Sum.inr 4398, 1), (Sum.inr 4631, 1), (Sum.inr 4637, 1), (Sum.inr 4644, 1), (Sum.inr 4706, 1), (Sum.inr 4709, 1), (Sum.inr 4728, 1), (Sum.inr 4760, 1), (Sum.inr 4769, 1), (Sum.inr 4779, 1), (Sum.inr 4788, 1), (Sum.inr 4802, 1), (Sum.inr 4804, 1), (Sum.inr 4811, 1), (Sum.inr 4832, 1), (Sum.inr 4835, 1), (Sum.inr 4888, 1), (Sum.inr 5134, 1), (Sum.inr 5141, 1), (Sum.inr 5168, 1), (Sum.inr 5258, 1), (Sum.inr 5434, 1)]

theorem sourceEq2046 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2046 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2046 + difference 0 1) (sourceB2046 + difference 1 0) sourceC2046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4811) := by
    have ha : (tripleCharges (sourceA2046 + difference 0 1) (sourceB2046 + difference 1 0) sourceC2046) = raw28885 := by
      apply Matrix.ext; unfold tripleCharges sourceA2046 sourceB2046 sourceC2046 difference raw28885; decide +kernel
    rw [ha]
    exact (canonical28885 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2046 + difference 0 2) (sourceB2046 + difference 2 0) sourceC2046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA2046 + difference 0 2) (sourceB2046 + difference 2 0) sourceC2046) = raw28886 := by
      apply Matrix.ext; unfold tripleCharges sourceA2046 sourceB2046 sourceC2046 difference raw28886; decide +kernel
    rw [ha]
    exact (canonical28886 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2046 + difference 0 3) (sourceB2046 + difference 3 0) sourceC2046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4835) := by
    have ha : (tripleCharges (sourceA2046 + difference 0 3) (sourceB2046 + difference 3 0) sourceC2046) = raw28887 := by
      apply Matrix.ext; unfold tripleCharges sourceA2046 sourceB2046 sourceC2046 difference raw28887; decide +kernel
    rw [ha]
    exact (canonical28887 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2046 + difference 0 4) (sourceB2046 + difference 4 0) sourceC2046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA2046 + difference 0 4) (sourceB2046 + difference 4 0) sourceC2046) = raw28888 := by
      apply Matrix.ext; unfold tripleCharges sourceA2046 sourceB2046 sourceC2046 difference raw28888; decide +kernel
    rw [ha]
    exact (canonical28888 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2046 + difference 0 5) (sourceB2046 + difference 5 0) sourceC2046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA2046 + difference 0 5) (sourceB2046 + difference 5 0) sourceC2046) = raw10085 := by
      apply Matrix.ext; unfold tripleCharges sourceA2046 sourceB2046 sourceC2046 difference raw10085; decide +kernel
    rw [ha]
    exact (canonical10085 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2046 + difference 1 0) (sourceB2046 + difference 0 1) sourceC2046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4398) := by
    have ha : (tripleCharges (sourceA2046 + difference 1 0) (sourceB2046 + difference 0 1) sourceC2046) = raw10110 := by
      apply Matrix.ext; unfold tripleCharges sourceA2046 sourceB2046 sourceC2046 difference raw10110; decide +kernel
    rw [ha]
    exact (canonical10110 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2046 + difference 1 2) (sourceB2046 + difference 2 1) sourceC2046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4779) := by
    have ha : (tripleCharges (sourceA2046 + difference 1 2) (sourceB2046 + difference 2 1) sourceC2046) = raw10112 := by
      apply Matrix.ext; unfold tripleCharges sourceA2046 sourceB2046 sourceC2046 difference raw10112; decide +kernel
    rw [ha]
    exact (canonical10112 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2046 + difference 1 3) (sourceB2046 + difference 3 1) sourceC2046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4788) := by
    have ha : (tripleCharges (sourceA2046 + difference 1 3) (sourceB2046 + difference 3 1) sourceC2046) = raw10113 := by
      apply Matrix.ext; unfold tripleCharges sourceA2046 sourceB2046 sourceC2046 difference raw10113; decide +kernel
    rw [ha]
    exact (canonical10113 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2046 + difference 1 4) (sourceB2046 + difference 4 1) sourceC2046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4832) := by
    have ha : (tripleCharges (sourceA2046 + difference 1 4) (sourceB2046 + difference 4 1) sourceC2046) = raw10114 := by
      apply Matrix.ext; unfold tripleCharges sourceA2046 sourceB2046 sourceC2046 difference raw10114; decide +kernel
    rw [ha]
    exact (canonical10114 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2046 + difference 1 5) (sourceB2046 + difference 5 1) sourceC2046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA2046 + difference 1 5) (sourceB2046 + difference 5 1) sourceC2046) = raw25427 := by
      apply Matrix.ext; unfold tripleCharges sourceA2046 sourceB2046 sourceC2046 difference raw25427; decide +kernel
    rw [ha]
    exact (canonical25427 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2046 + difference 2 0) (sourceB2046 + difference 0 2) sourceC2046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4320) := by
    have ha : (tripleCharges (sourceA2046 + difference 2 0) (sourceB2046 + difference 0 2) sourceC2046) = raw28889 := by
      apply Matrix.ext; unfold tripleCharges sourceA2046 sourceB2046 sourceC2046 difference raw28889; decide +kernel
    rw [ha]
    exact (canonical28889 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2046 + difference 2 1) (sourceB2046 + difference 1 2) sourceC2046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4706) := by
    have ha : (tripleCharges (sourceA2046 + difference 2 1) (sourceB2046 + difference 1 2) sourceC2046) = raw28890 := by
      apply Matrix.ext; unfold tripleCharges sourceA2046 sourceB2046 sourceC2046 difference raw28890; decide +kernel
    rw [ha]
    exact (canonical28890 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2046 + difference 2 3) (sourceB2046 + difference 3 2) sourceC2046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4709) := by
    have ha : (tripleCharges (sourceA2046 + difference 2 3) (sourceB2046 + difference 3 2) sourceC2046) = raw28891 := by
      apply Matrix.ext; unfold tripleCharges sourceA2046 sourceB2046 sourceC2046 difference raw28891; decide +kernel
    rw [ha]
    exact (canonical28891 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2046 + difference 2 4) (sourceB2046 + difference 4 2) sourceC2046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4728) := by
    have ha : (tripleCharges (sourceA2046 + difference 2 4) (sourceB2046 + difference 4 2) sourceC2046) = raw28892 := by
      apply Matrix.ext; unfold tripleCharges sourceA2046 sourceB2046 sourceC2046 difference raw28892; decide +kernel
    rw [ha]
    exact (canonical28892 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2046 + difference 2 5) (sourceB2046 + difference 5 2) sourceC2046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5134) := by
    have ha : (tripleCharges (sourceA2046 + difference 2 5) (sourceB2046 + difference 5 2) sourceC2046) = raw10096 := by
      apply Matrix.ext; unfold tripleCharges sourceA2046 sourceB2046 sourceC2046 difference raw10096; decide +kernel
    rw [ha]
    exact (canonical10096 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2046 + difference 3 0) (sourceB2046 + difference 0 3) sourceC2046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4343) := by
    have ha : (tripleCharges (sourceA2046 + difference 3 0) (sourceB2046 + difference 0 3) sourceC2046) = raw25446 := by
      apply Matrix.ext; unfold tripleCharges sourceA2046 sourceB2046 sourceC2046 difference raw25446; decide +kernel
    rw [ha]
    exact (canonical25446 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2046 + difference 3 1) (sourceB2046 + difference 1 3) sourceC2046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4769) := by
    have ha : (tripleCharges (sourceA2046 + difference 3 1) (sourceB2046 + difference 1 3) sourceC2046) = raw28893 := by
      apply Matrix.ext; unfold tripleCharges sourceA2046 sourceB2046 sourceC2046 difference raw28893; decide +kernel
    rw [ha]
    exact (canonical28893 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2046 + difference 3 2) (sourceB2046 + difference 2 3) sourceC2046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4760) := by
    have ha : (tripleCharges (sourceA2046 + difference 3 2) (sourceB2046 + difference 2 3) sourceC2046) = raw28894 := by
      apply Matrix.ext; unfold tripleCharges sourceA2046 sourceB2046 sourceC2046 difference raw28894; decide +kernel
    rw [ha]
    exact (canonical28894 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2046 + difference 3 4) (sourceB2046 + difference 4 3) sourceC2046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA2046 + difference 3 4) (sourceB2046 + difference 4 3) sourceC2046) = raw28895 := by
      apply Matrix.ext; unfold tripleCharges sourceA2046 sourceB2046 sourceC2046 difference raw28895; decide +kernel
    rw [ha]
    exact (canonical28895 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2046 + difference 3 5) (sourceB2046 + difference 5 3) sourceC2046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5168) := by
    have ha : (tripleCharges (sourceA2046 + difference 3 5) (sourceB2046 + difference 5 3) sourceC2046) = raw10101 := by
      apply Matrix.ext; unfold tripleCharges sourceA2046 sourceB2046 sourceC2046 difference raw10101; decide +kernel
    rw [ha]
    exact (canonical10101 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2046 + difference 4 0) (sourceB2046 + difference 0 4) sourceC2046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4324) := by
    have ha : (tripleCharges (sourceA2046 + difference 4 0) (sourceB2046 + difference 0 4) sourceC2046) = raw28896 := by
      apply Matrix.ext; unfold tripleCharges sourceA2046 sourceB2046 sourceC2046 difference raw28896; decide +kernel
    rw [ha]
    exact (canonical28896 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2046 + difference 4 1) (sourceB2046 + difference 1 4) sourceC2046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4637) := by
    have ha : (tripleCharges (sourceA2046 + difference 4 1) (sourceB2046 + difference 1 4) sourceC2046) = raw28897 := by
      apply Matrix.ext; unfold tripleCharges sourceA2046 sourceB2046 sourceC2046 difference raw28897; decide +kernel
    rw [ha]
    exact (canonical28897 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2046 + difference 4 2) (sourceB2046 + difference 2 4) sourceC2046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4631) := by
    have ha : (tripleCharges (sourceA2046 + difference 4 2) (sourceB2046 + difference 2 4) sourceC2046) = raw28898 := by
      apply Matrix.ext; unfold tripleCharges sourceA2046 sourceB2046 sourceC2046 difference raw28898; decide +kernel
    rw [ha]
    exact (canonical28898 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2046 + difference 4 3) (sourceB2046 + difference 3 4) sourceC2046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4644) := by
    have ha : (tripleCharges (sourceA2046 + difference 4 3) (sourceB2046 + difference 3 4) sourceC2046) = raw28899 := by
      apply Matrix.ext; unfold tripleCharges sourceA2046 sourceB2046 sourceC2046 difference raw28899; decide +kernel
    rw [ha]
    exact (canonical28899 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2046 + difference 4 5) (sourceB2046 + difference 5 4) sourceC2046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA2046 + difference 4 5) (sourceB2046 + difference 5 4) sourceC2046) = raw10106 := by
      apply Matrix.ext; unfold tripleCharges sourceA2046 sourceB2046 sourceC2046 difference raw10106; decide +kernel
    rw [ha]
    exact (canonical10106 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2046 + difference 5 0) (sourceB2046 + difference 0 5) sourceC2046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4198) := by
    have ha : (tripleCharges (sourceA2046 + difference 5 0) (sourceB2046 + difference 0 5) sourceC2046) = raw28900 := by
      apply Matrix.ext; unfold tripleCharges sourceA2046 sourceB2046 sourceC2046 difference raw28900; decide +kernel
    rw [ha]
    exact (canonical28900 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2046 + difference 5 1) (sourceB2046 + difference 1 5) sourceC2046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4204) := by
    have ha : (tripleCharges (sourceA2046 + difference 5 1) (sourceB2046 + difference 1 5) sourceC2046) = raw28901 := by
      apply Matrix.ext; unfold tripleCharges sourceA2046 sourceB2046 sourceC2046 difference raw28901; decide +kernel
    rw [ha]
    exact (canonical28901 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2046 + difference 5 2) (sourceB2046 + difference 2 5) sourceC2046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4196) := by
    have ha : (tripleCharges (sourceA2046 + difference 5 2) (sourceB2046 + difference 2 5) sourceC2046) = raw28902 := by
      apply Matrix.ext; unfold tripleCharges sourceA2046 sourceB2046 sourceC2046 difference raw28902; decide +kernel
    rw [ha]
    exact (canonical28902 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2046 + difference 5 3) (sourceB2046 + difference 3 5) sourceC2046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4212) := by
    have ha : (tripleCharges (sourceA2046 + difference 5 3) (sourceB2046 + difference 3 5) sourceC2046) = raw28903 := by
      apply Matrix.ext; unfold tripleCharges sourceA2046 sourceB2046 sourceC2046 difference raw28903; decide +kernel
    rw [ha]
    exact (canonical28903 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2046 + difference 5 4) (sourceB2046 + difference 4 5) sourceC2046) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4251) := by
    have ha : (tripleCharges (sourceA2046 + difference 5 4) (sourceB2046 + difference 4 5) sourceC2046) = raw28904 := by
      apply Matrix.ext; unfold tripleCharges sourceA2046 sourceB2046 sourceC2046 difference raw28904; decide +kernel
    rw [ha]
    exact (canonical28904 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2046 sourceB2046 sourceC2046
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2046, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2047 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2047 : Charge := ![2, 0, 0, 1, 0, -3]
def sourceC2047 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceForm2047 : Integer.Sparse Master := [(Sum.inr 699, 1), (Sum.inr 701, 1), (Sum.inr 707, 1), (Sum.inr 715, 1), (Sum.inr 785, 1), (Sum.inr 898, 1), (Sum.inr 902, 1), (Sum.inr 921, 1), (Sum.inr 979, 1), (Sum.inr 1760, 1), (Sum.inr 1766, 1), (Sum.inr 1773, 1), (Sum.inr 1860, 1), (Sum.inr 1863, 1), (Sum.inr 1897, 1), (Sum.inr 1960, 1), (Sum.inr 1969, 1), (Sum.inr 1987, 1), (Sum.inr 2003, 1), (Sum.inr 2020, 1), (Sum.inr 2022, 1), (Sum.inr 2029, 1), (Sum.inr 2054, 1), (Sum.inr 2193, 1), (Sum.inr 2244, 1), (Sum.inr 2553, 1), (Sum.inr 2561, 1), (Sum.inr 2594, 1), (Sum.inr 2722, 1), (Sum.inr 3852, 1)]

theorem sourceEq2047 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2047 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2047 + difference 0 1) (sourceB2047 + difference 1 0) sourceC2047) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2029) := by
    have ha : (tripleCharges (sourceA2047 + difference 0 1) (sourceB2047 + difference 1 0) sourceC2047) = raw28905 := by
      apply Matrix.ext; unfold tripleCharges sourceA2047 sourceB2047 sourceC2047 difference raw28905; decide +kernel
    rw [ha]
    exact (canonical28905 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2047 + difference 0 2) (sourceB2047 + difference 2 0) sourceC2047) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2020) := by
    have ha : (tripleCharges (sourceA2047 + difference 0 2) (sourceB2047 + difference 2 0) sourceC2047) = raw28906 := by
      apply Matrix.ext; unfold tripleCharges sourceA2047 sourceB2047 sourceC2047 difference raw28906; decide +kernel
    rw [ha]
    exact (canonical28906 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2047 + difference 0 3) (sourceB2047 + difference 3 0) sourceC2047) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2054) := by
    have ha : (tripleCharges (sourceA2047 + difference 0 3) (sourceB2047 + difference 3 0) sourceC2047) = raw28907 := by
      apply Matrix.ext; unfold tripleCharges sourceA2047 sourceB2047 sourceC2047 difference raw28907; decide +kernel
    rw [ha]
    exact (canonical28907 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2047 + difference 0 4) (sourceB2047 + difference 4 0) sourceC2047) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2244) := by
    have ha : (tripleCharges (sourceA2047 + difference 0 4) (sourceB2047 + difference 4 0) sourceC2047) = raw28908 := by
      apply Matrix.ext; unfold tripleCharges sourceA2047 sourceB2047 sourceC2047 difference raw28908; decide +kernel
    rw [ha]
    exact (canonical28908 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2047 + difference 0 5) (sourceB2047 + difference 5 0) sourceC2047) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3852) := by
    have ha : (tripleCharges (sourceA2047 + difference 0 5) (sourceB2047 + difference 5 0) sourceC2047) = raw10115 := by
      apply Matrix.ext; unfold tripleCharges sourceA2047 sourceB2047 sourceC2047 difference raw10115; decide +kernel
    rw [ha]
    exact (canonical10115 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2047 + difference 1 0) (sourceB2047 + difference 0 1) sourceC2047) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 979) := by
    have ha : (tripleCharges (sourceA2047 + difference 1 0) (sourceB2047 + difference 0 1) sourceC2047) = raw10140 := by
      apply Matrix.ext; unfold tripleCharges sourceA2047 sourceB2047 sourceC2047 difference raw10140; decide +kernel
    rw [ha]
    exact (canonical10140 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2047 + difference 1 2) (sourceB2047 + difference 2 1) sourceC2047) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1987) := by
    have ha : (tripleCharges (sourceA2047 + difference 1 2) (sourceB2047 + difference 2 1) sourceC2047) = raw10142 := by
      apply Matrix.ext; unfold tripleCharges sourceA2047 sourceB2047 sourceC2047 difference raw10142; decide +kernel
    rw [ha]
    exact (canonical10142 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2047 + difference 1 3) (sourceB2047 + difference 3 1) sourceC2047) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2003) := by
    have ha : (tripleCharges (sourceA2047 + difference 1 3) (sourceB2047 + difference 3 1) sourceC2047) = raw10143 := by
      apply Matrix.ext; unfold tripleCharges sourceA2047 sourceB2047 sourceC2047 difference raw10143; decide +kernel
    rw [ha]
    exact (canonical10143 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2047 + difference 1 4) (sourceB2047 + difference 4 1) sourceC2047) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2193) := by
    have ha : (tripleCharges (sourceA2047 + difference 1 4) (sourceB2047 + difference 4 1) sourceC2047) = raw10144 := by
      apply Matrix.ext; unfold tripleCharges sourceA2047 sourceB2047 sourceC2047 difference raw10144; decide +kernel
    rw [ha]
    exact (canonical10144 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2047 + difference 1 5) (sourceB2047 + difference 5 1) sourceC2047) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA2047 + difference 1 5) (sourceB2047 + difference 5 1) sourceC2047) = raw25449 := by
      apply Matrix.ext; unfold tripleCharges sourceA2047 sourceB2047 sourceC2047 difference raw25449; decide +kernel
    rw [ha]
    exact (canonical25449 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2047 + difference 2 0) (sourceB2047 + difference 0 2) sourceC2047) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 898) := by
    have ha : (tripleCharges (sourceA2047 + difference 2 0) (sourceB2047 + difference 0 2) sourceC2047) = raw28909 := by
      apply Matrix.ext; unfold tripleCharges sourceA2047 sourceB2047 sourceC2047 difference raw28909; decide +kernel
    rw [ha]
    exact (canonical28909 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2047 + difference 2 1) (sourceB2047 + difference 1 2) sourceC2047) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1860) := by
    have ha : (tripleCharges (sourceA2047 + difference 2 1) (sourceB2047 + difference 1 2) sourceC2047) = raw28910 := by
      apply Matrix.ext; unfold tripleCharges sourceA2047 sourceB2047 sourceC2047 difference raw28910; decide +kernel
    rw [ha]
    exact (canonical28910 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2047 + difference 2 3) (sourceB2047 + difference 3 2) sourceC2047) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1863) := by
    have ha : (tripleCharges (sourceA2047 + difference 2 3) (sourceB2047 + difference 3 2) sourceC2047) = raw28911 := by
      apply Matrix.ext; unfold tripleCharges sourceA2047 sourceB2047 sourceC2047 difference raw28911; decide +kernel
    rw [ha]
    exact (canonical28911 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2047 + difference 2 4) (sourceB2047 + difference 4 2) sourceC2047) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1897) := by
    have ha : (tripleCharges (sourceA2047 + difference 2 4) (sourceB2047 + difference 4 2) sourceC2047) = raw28912 := by
      apply Matrix.ext; unfold tripleCharges sourceA2047 sourceB2047 sourceC2047 difference raw28912; decide +kernel
    rw [ha]
    exact (canonical28912 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2047 + difference 2 5) (sourceB2047 + difference 5 2) sourceC2047) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2553) := by
    have ha : (tripleCharges (sourceA2047 + difference 2 5) (sourceB2047 + difference 5 2) sourceC2047) = raw10126 := by
      apply Matrix.ext; unfold tripleCharges sourceA2047 sourceB2047 sourceC2047 difference raw10126; decide +kernel
    rw [ha]
    exact (canonical10126 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2047 + difference 3 0) (sourceB2047 + difference 0 3) sourceC2047) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 921) := by
    have ha : (tripleCharges (sourceA2047 + difference 3 0) (sourceB2047 + difference 0 3) sourceC2047) = raw25468 := by
      apply Matrix.ext; unfold tripleCharges sourceA2047 sourceB2047 sourceC2047 difference raw25468; decide +kernel
    rw [ha]
    exact (canonical25468 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2047 + difference 3 1) (sourceB2047 + difference 1 3) sourceC2047) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1969) := by
    have ha : (tripleCharges (sourceA2047 + difference 3 1) (sourceB2047 + difference 1 3) sourceC2047) = raw28913 := by
      apply Matrix.ext; unfold tripleCharges sourceA2047 sourceB2047 sourceC2047 difference raw28913; decide +kernel
    rw [ha]
    exact (canonical28913 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2047 + difference 3 2) (sourceB2047 + difference 2 3) sourceC2047) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1960) := by
    have ha : (tripleCharges (sourceA2047 + difference 3 2) (sourceB2047 + difference 2 3) sourceC2047) = raw28914 := by
      apply Matrix.ext; unfold tripleCharges sourceA2047 sourceB2047 sourceC2047 difference raw28914; decide +kernel
    rw [ha]
    exact (canonical28914 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2047 + difference 3 4) (sourceB2047 + difference 4 3) sourceC2047) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2022) := by
    have ha : (tripleCharges (sourceA2047 + difference 3 4) (sourceB2047 + difference 4 3) sourceC2047) = raw28915 := by
      apply Matrix.ext; unfold tripleCharges sourceA2047 sourceB2047 sourceC2047 difference raw28915; decide +kernel
    rw [ha]
    exact (canonical28915 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2047 + difference 3 5) (sourceB2047 + difference 5 3) sourceC2047) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2594) := by
    have ha : (tripleCharges (sourceA2047 + difference 3 5) (sourceB2047 + difference 5 3) sourceC2047) = raw10131 := by
      apply Matrix.ext; unfold tripleCharges sourceA2047 sourceB2047 sourceC2047 difference raw10131; decide +kernel
    rw [ha]
    exact (canonical10131 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2047 + difference 4 0) (sourceB2047 + difference 0 4) sourceC2047) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 902) := by
    have ha : (tripleCharges (sourceA2047 + difference 4 0) (sourceB2047 + difference 0 4) sourceC2047) = raw28916 := by
      apply Matrix.ext; unfold tripleCharges sourceA2047 sourceB2047 sourceC2047 difference raw28916; decide +kernel
    rw [ha]
    exact (canonical28916 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2047 + difference 4 1) (sourceB2047 + difference 1 4) sourceC2047) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1766) := by
    have ha : (tripleCharges (sourceA2047 + difference 4 1) (sourceB2047 + difference 1 4) sourceC2047) = raw28917 := by
      apply Matrix.ext; unfold tripleCharges sourceA2047 sourceB2047 sourceC2047 difference raw28917; decide +kernel
    rw [ha]
    exact (canonical28917 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2047 + difference 4 2) (sourceB2047 + difference 2 4) sourceC2047) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1760) := by
    have ha : (tripleCharges (sourceA2047 + difference 4 2) (sourceB2047 + difference 2 4) sourceC2047) = raw28918 := by
      apply Matrix.ext; unfold tripleCharges sourceA2047 sourceB2047 sourceC2047 difference raw28918; decide +kernel
    rw [ha]
    exact (canonical28918 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2047 + difference 4 3) (sourceB2047 + difference 3 4) sourceC2047) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1773) := by
    have ha : (tripleCharges (sourceA2047 + difference 4 3) (sourceB2047 + difference 3 4) sourceC2047) = raw28919 := by
      apply Matrix.ext; unfold tripleCharges sourceA2047 sourceB2047 sourceC2047 difference raw28919; decide +kernel
    rw [ha]
    exact (canonical28919 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2047 + difference 4 5) (sourceB2047 + difference 5 4) sourceC2047) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2561) := by
    have ha : (tripleCharges (sourceA2047 + difference 4 5) (sourceB2047 + difference 5 4) sourceC2047) = raw10136 := by
      apply Matrix.ext; unfold tripleCharges sourceA2047 sourceB2047 sourceC2047 difference raw10136; decide +kernel
    rw [ha]
    exact (canonical10136 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2047 + difference 5 0) (sourceB2047 + difference 0 5) sourceC2047) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 701) := by
    have ha : (tripleCharges (sourceA2047 + difference 5 0) (sourceB2047 + difference 0 5) sourceC2047) = raw28920 := by
      apply Matrix.ext; unfold tripleCharges sourceA2047 sourceB2047 sourceC2047 difference raw28920; decide +kernel
    rw [ha]
    exact (canonical28920 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2047 + difference 5 1) (sourceB2047 + difference 1 5) sourceC2047) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 707) := by
    have ha : (tripleCharges (sourceA2047 + difference 5 1) (sourceB2047 + difference 1 5) sourceC2047) = raw28921 := by
      apply Matrix.ext; unfold tripleCharges sourceA2047 sourceB2047 sourceC2047 difference raw28921; decide +kernel
    rw [ha]
    exact (canonical28921 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2047 + difference 5 2) (sourceB2047 + difference 2 5) sourceC2047) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 699) := by
    have ha : (tripleCharges (sourceA2047 + difference 5 2) (sourceB2047 + difference 2 5) sourceC2047) = raw28922 := by
      apply Matrix.ext; unfold tripleCharges sourceA2047 sourceB2047 sourceC2047 difference raw28922; decide +kernel
    rw [ha]
    exact (canonical28922 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2047 + difference 5 3) (sourceB2047 + difference 3 5) sourceC2047) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 715) := by
    have ha : (tripleCharges (sourceA2047 + difference 5 3) (sourceB2047 + difference 3 5) sourceC2047) = raw28923 := by
      apply Matrix.ext; unfold tripleCharges sourceA2047 sourceB2047 sourceC2047 difference raw28923; decide +kernel
    rw [ha]
    exact (canonical28923 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2047 + difference 5 4) (sourceB2047 + difference 4 5) sourceC2047) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 785) := by
    have ha : (tripleCharges (sourceA2047 + difference 5 4) (sourceB2047 + difference 4 5) sourceC2047) = raw28924 := by
      apply Matrix.ext; unfold tripleCharges sourceA2047 sourceB2047 sourceC2047 difference raw28924; decide +kernel
    rw [ha]
    exact (canonical28924 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2047 sourceB2047 sourceC2047
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2047, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
