import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA608 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceB608 : Charge := ![2, -1, 0, 1, 0, -2]
def sourceC608 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm608 : Integer.Sparse Master := [(Sum.inr 2019, 1), (Sum.inr 2022, 1), (Sum.inr 2028, 1), (Sum.inr 2053, 1), (Sum.inr 2264, 1), (Sum.inr 3533, 1), (Sum.inr 4084, -1)]

theorem sourceEq608 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm608 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA608 + difference 0 0) (sourceB608 + difference 0 0) sourceC608) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3533) := by
    have ha : (tripleCharges (sourceA608 + difference 0 0) (sourceB608 + difference 0 0) sourceC608) = raw10190 := by
      apply Matrix.ext; unfold tripleCharges sourceA608 sourceB608 sourceC608 difference raw10190; decide +kernel
    rw [ha]
    exact (canonical10190 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA608 + difference 1 0) (sourceB608 + difference 0 1) sourceC608) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2028) := by
    have ha : (tripleCharges (sourceA608 + difference 1 0) (sourceB608 + difference 0 1) sourceC608) = raw10191 := by
      apply Matrix.ext; unfold tripleCharges sourceA608 sourceB608 sourceC608 difference raw10191; decide +kernel
    rw [ha]
    exact (canonical10191 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA608 + difference 2 0) (sourceB608 + difference 0 2) sourceC608) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2019) := by
    have ha : (tripleCharges (sourceA608 + difference 2 0) (sourceB608 + difference 0 2) sourceC608) = raw10192 := by
      apply Matrix.ext; unfold tripleCharges sourceA608 sourceB608 sourceC608 difference raw10192; decide +kernel
    rw [ha]
    exact (canonical10192 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA608 + difference 3 0) (sourceB608 + difference 0 3) sourceC608) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2264) := by
    have ha : (tripleCharges (sourceA608 + difference 3 0) (sourceB608 + difference 0 3) sourceC608) = raw9728 := by
      apply Matrix.ext; unfold tripleCharges sourceA608 sourceB608 sourceC608 difference raw9728; decide +kernel
    rw [ha]
    exact (canonical9728 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA608 + difference 4 0) (sourceB608 + difference 0 4) sourceC608) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2053) := by
    have ha : (tripleCharges (sourceA608 + difference 4 0) (sourceB608 + difference 0 4) sourceC608) = raw9968 := by
      apply Matrix.ext; unfold tripleCharges sourceA608 sourceB608 sourceC608 difference raw9968; decide +kernel
    rw [ha]
    exact (canonical9968 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA608 + difference 5 0) (sourceB608 + difference 0 5) sourceC608) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2022) := by
    have ha : (tripleCharges (sourceA608 + difference 5 0) (sourceB608 + difference 0 5) sourceC608) = raw10193 := by
      apply Matrix.ext; unfold tripleCharges sourceA608 sourceB608 sourceC608 difference raw10193; decide +kernel
    rw [ha]
    exact (canonical10193 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA608 + sourceB608) sourceC608) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA608 + sourceB608) sourceC608) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA608 sourceB608 sourceC608 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA608 sourceB608 sourceC608
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm608, Integer.Sparse.eval]
  linarith only [hs]

def sourceA609 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB609 : Charge := ![1, 0, 0, 0, 0, -1]
def sourceC609 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceForm609 : Integer.Sparse Master := [(Sum.inr 4093, 1), (Sum.inr 4624, 3), (Sum.inr 4625, 1), (Sum.inr 4628, 1), (Sum.inr 5169, 6), (Sum.inr 5174, 3), (Sum.inr 5177, 3), (Sum.inr 5293, 3), (Sum.inr 5296, 1), (Sum.inr 5307, 3), (Sum.inr 5309, 1), (Sum.inr 5442, 3), (Sum.inr 5455, 1)]

theorem sourceEq609 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm609 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA609 + difference 0 1) (sourceB609 + difference 1 0) sourceC609) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5442) := by
    have ha : (tripleCharges (sourceA609 + difference 0 1) (sourceB609 + difference 1 0) sourceC609) = raw10194 := by
      apply Matrix.ext; unfold tripleCharges sourceA609 sourceB609 sourceC609 difference raw10194; decide +kernel
    rw [ha]
    exact (canonical10194 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA609 + difference 0 2) (sourceB609 + difference 2 0) sourceC609) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5442) := by
    have ha : (tripleCharges (sourceA609 + difference 0 2) (sourceB609 + difference 2 0) sourceC609) = raw10195 := by
      apply Matrix.ext; unfold tripleCharges sourceA609 sourceB609 sourceC609 difference raw10195; decide +kernel
    rw [ha]
    exact (canonical10195 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA609 + difference 0 3) (sourceB609 + difference 3 0) sourceC609) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5442) := by
    have ha : (tripleCharges (sourceA609 + difference 0 3) (sourceB609 + difference 3 0) sourceC609) = raw10196 := by
      apply Matrix.ext; unfold tripleCharges sourceA609 sourceB609 sourceC609 difference raw10196; decide +kernel
    rw [ha]
    exact (canonical10196 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA609 + difference 0 4) (sourceB609 + difference 4 0) sourceC609) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5455) := by
    have ha : (tripleCharges (sourceA609 + difference 0 4) (sourceB609 + difference 4 0) sourceC609) = raw4286 := by
      apply Matrix.ext; unfold tripleCharges sourceA609 sourceB609 sourceC609 difference raw4286; decide +kernel
    rw [ha]
    exact (canonical4286 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA609 + difference 0 5) (sourceB609 + difference 5 0) sourceC609) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4093) := by
    have ha : (tripleCharges (sourceA609 + difference 0 5) (sourceB609 + difference 5 0) sourceC609) = raw10197 := by
      apply Matrix.ext; unfold tripleCharges sourceA609 sourceB609 sourceC609 difference raw10197; decide +kernel
    rw [ha]
    exact (canonical10197 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA609 + difference 1 0) (sourceB609 + difference 0 1) sourceC609) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4624) := by
    have ha : (tripleCharges (sourceA609 + difference 1 0) (sourceB609 + difference 0 1) sourceC609) = raw10198 := by
      apply Matrix.ext; unfold tripleCharges sourceA609 sourceB609 sourceC609 difference raw10198; decide +kernel
    rw [ha]
    exact (canonical10198 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA609 + difference 1 2) (sourceB609 + difference 2 1) sourceC609) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA609 + difference 1 2) (sourceB609 + difference 2 1) sourceC609) = raw10199 := by
      apply Matrix.ext; unfold tripleCharges sourceA609 sourceB609 sourceC609 difference raw10199; decide +kernel
    rw [ha]
    exact (canonical10199 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA609 + difference 1 3) (sourceB609 + difference 3 1) sourceC609) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA609 + difference 1 3) (sourceB609 + difference 3 1) sourceC609) = raw10200 := by
      apply Matrix.ext; unfold tripleCharges sourceA609 sourceB609 sourceC609 difference raw10200; decide +kernel
    rw [ha]
    exact (canonical10200 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA609 + difference 1 4) (sourceB609 + difference 4 1) sourceC609) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA609 + difference 1 4) (sourceB609 + difference 4 1) sourceC609) = raw4291 := by
      apply Matrix.ext; unfold tripleCharges sourceA609 sourceB609 sourceC609 difference raw4291; decide +kernel
    rw [ha]
    exact (canonical4291 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA609 + difference 1 5) (sourceB609 + difference 5 1) sourceC609) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5307) := by
    have ha : (tripleCharges (sourceA609 + difference 1 5) (sourceB609 + difference 5 1) sourceC609) = raw10201 := by
      apply Matrix.ext; unfold tripleCharges sourceA609 sourceB609 sourceC609 difference raw10201; decide +kernel
    rw [ha]
    exact (canonical10201 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA609 + difference 2 0) (sourceB609 + difference 0 2) sourceC609) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4624) := by
    have ha : (tripleCharges (sourceA609 + difference 2 0) (sourceB609 + difference 0 2) sourceC609) = raw10202 := by
      apply Matrix.ext; unfold tripleCharges sourceA609 sourceB609 sourceC609 difference raw10202; decide +kernel
    rw [ha]
    exact (canonical10202 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA609 + difference 2 1) (sourceB609 + difference 1 2) sourceC609) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA609 + difference 2 1) (sourceB609 + difference 1 2) sourceC609) = raw10203 := by
      apply Matrix.ext; unfold tripleCharges sourceA609 sourceB609 sourceC609 difference raw10203; decide +kernel
    rw [ha]
    exact (canonical10203 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA609 + difference 2 3) (sourceB609 + difference 3 2) sourceC609) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA609 + difference 2 3) (sourceB609 + difference 3 2) sourceC609) = raw10204 := by
      apply Matrix.ext; unfold tripleCharges sourceA609 sourceB609 sourceC609 difference raw10204; decide +kernel
    rw [ha]
    exact (canonical10204 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA609 + difference 2 4) (sourceB609 + difference 4 2) sourceC609) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA609 + difference 2 4) (sourceB609 + difference 4 2) sourceC609) = raw4296 := by
      apply Matrix.ext; unfold tripleCharges sourceA609 sourceB609 sourceC609 difference raw4296; decide +kernel
    rw [ha]
    exact (canonical4296 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA609 + difference 2 5) (sourceB609 + difference 5 2) sourceC609) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5307) := by
    have ha : (tripleCharges (sourceA609 + difference 2 5) (sourceB609 + difference 5 2) sourceC609) = raw10205 := by
      apply Matrix.ext; unfold tripleCharges sourceA609 sourceB609 sourceC609 difference raw10205; decide +kernel
    rw [ha]
    exact (canonical10205 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA609 + difference 3 0) (sourceB609 + difference 0 3) sourceC609) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4624) := by
    have ha : (tripleCharges (sourceA609 + difference 3 0) (sourceB609 + difference 0 3) sourceC609) = raw10206 := by
      apply Matrix.ext; unfold tripleCharges sourceA609 sourceB609 sourceC609 difference raw10206; decide +kernel
    rw [ha]
    exact (canonical10206 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA609 + difference 3 1) (sourceB609 + difference 1 3) sourceC609) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA609 + difference 3 1) (sourceB609 + difference 1 3) sourceC609) = raw10207 := by
      apply Matrix.ext; unfold tripleCharges sourceA609 sourceB609 sourceC609 difference raw10207; decide +kernel
    rw [ha]
    exact (canonical10207 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA609 + difference 3 2) (sourceB609 + difference 2 3) sourceC609) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA609 + difference 3 2) (sourceB609 + difference 2 3) sourceC609) = raw10208 := by
      apply Matrix.ext; unfold tripleCharges sourceA609 sourceB609 sourceC609 difference raw10208; decide +kernel
    rw [ha]
    exact (canonical10208 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA609 + difference 3 4) (sourceB609 + difference 4 3) sourceC609) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA609 + difference 3 4) (sourceB609 + difference 4 3) sourceC609) = raw4301 := by
      apply Matrix.ext; unfold tripleCharges sourceA609 sourceB609 sourceC609 difference raw4301; decide +kernel
    rw [ha]
    exact (canonical4301 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA609 + difference 3 5) (sourceB609 + difference 5 3) sourceC609) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5307) := by
    have ha : (tripleCharges (sourceA609 + difference 3 5) (sourceB609 + difference 5 3) sourceC609) = raw10209 := by
      apply Matrix.ext; unfold tripleCharges sourceA609 sourceB609 sourceC609 difference raw10209; decide +kernel
    rw [ha]
    exact (canonical10209 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA609 + difference 4 0) (sourceB609 + difference 0 4) sourceC609) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4628) := by
    have ha : (tripleCharges (sourceA609 + difference 4 0) (sourceB609 + difference 0 4) sourceC609) = raw10210 := by
      apply Matrix.ext; unfold tripleCharges sourceA609 sourceB609 sourceC609 difference raw10210; decide +kernel
    rw [ha]
    exact (canonical10210 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA609 + difference 4 1) (sourceB609 + difference 1 4) sourceC609) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5177) := by
    have ha : (tripleCharges (sourceA609 + difference 4 1) (sourceB609 + difference 1 4) sourceC609) = raw10211 := by
      apply Matrix.ext; unfold tripleCharges sourceA609 sourceB609 sourceC609 difference raw10211; decide +kernel
    rw [ha]
    exact (canonical10211 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA609 + difference 4 2) (sourceB609 + difference 2 4) sourceC609) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5177) := by
    have ha : (tripleCharges (sourceA609 + difference 4 2) (sourceB609 + difference 2 4) sourceC609) = raw10212 := by
      apply Matrix.ext; unfold tripleCharges sourceA609 sourceB609 sourceC609 difference raw10212; decide +kernel
    rw [ha]
    exact (canonical10212 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA609 + difference 4 3) (sourceB609 + difference 3 4) sourceC609) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5177) := by
    have ha : (tripleCharges (sourceA609 + difference 4 3) (sourceB609 + difference 3 4) sourceC609) = raw10213 := by
      apply Matrix.ext; unfold tripleCharges sourceA609 sourceB609 sourceC609 difference raw10213; decide +kernel
    rw [ha]
    exact (canonical10213 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA609 + difference 4 5) (sourceB609 + difference 5 4) sourceC609) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5309) := by
    have ha : (tripleCharges (sourceA609 + difference 4 5) (sourceB609 + difference 5 4) sourceC609) = raw10214 := by
      apply Matrix.ext; unfold tripleCharges sourceA609 sourceB609 sourceC609 difference raw10214; decide +kernel
    rw [ha]
    exact (canonical10214 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA609 + difference 5 0) (sourceB609 + difference 0 5) sourceC609) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4625) := by
    have ha : (tripleCharges (sourceA609 + difference 5 0) (sourceB609 + difference 0 5) sourceC609) = raw4302 := by
      apply Matrix.ext; unfold tripleCharges sourceA609 sourceB609 sourceC609 difference raw4302; decide +kernel
    rw [ha]
    exact (canonical4302 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA609 + difference 5 1) (sourceB609 + difference 1 5) sourceC609) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5174) := by
    have ha : (tripleCharges (sourceA609 + difference 5 1) (sourceB609 + difference 1 5) sourceC609) = raw4303 := by
      apply Matrix.ext; unfold tripleCharges sourceA609 sourceB609 sourceC609 difference raw4303; decide +kernel
    rw [ha]
    exact (canonical4303 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA609 + difference 5 2) (sourceB609 + difference 2 5) sourceC609) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5174) := by
    have ha : (tripleCharges (sourceA609 + difference 5 2) (sourceB609 + difference 2 5) sourceC609) = raw4304 := by
      apply Matrix.ext; unfold tripleCharges sourceA609 sourceB609 sourceC609 difference raw4304; decide +kernel
    rw [ha]
    exact (canonical4304 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA609 + difference 5 3) (sourceB609 + difference 3 5) sourceC609) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5174) := by
    have ha : (tripleCharges (sourceA609 + difference 5 3) (sourceB609 + difference 3 5) sourceC609) = raw4305 := by
      apply Matrix.ext; unfold tripleCharges sourceA609 sourceB609 sourceC609 difference raw4305; decide +kernel
    rw [ha]
    exact (canonical4305 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA609 + difference 5 4) (sourceB609 + difference 4 5) sourceC609) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5296) := by
    have ha : (tripleCharges (sourceA609 + difference 5 4) (sourceB609 + difference 4 5) sourceC609) = raw10215 := by
      apply Matrix.ext; unfold tripleCharges sourceA609 sourceB609 sourceC609 difference raw10215; decide +kernel
    rw [ha]
    exact (canonical10215 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA609 sourceB609 sourceC609
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm609, Integer.Sparse.eval]
  linarith only [hs]

def sourceA610 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB610 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceC610 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceForm610 : Integer.Sparse Master := [(Sum.inr 4094, 1), (Sum.inr 4623, 3), (Sum.inr 4625, 1), (Sum.inr 4627, 1), (Sum.inr 5168, 6), (Sum.inr 5171, 3), (Sum.inr 5176, 3), (Sum.inr 5306, 3), (Sum.inr 5308, 3), (Sum.inr 5310, 1), (Sum.inr 5312, 1), (Sum.inr 5441, 3), (Sum.inr 5455, 1)]

theorem sourceEq610 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm610 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA610 + difference 0 1) (sourceB610 + difference 1 0) sourceC610) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5441) := by
    have ha : (tripleCharges (sourceA610 + difference 0 1) (sourceB610 + difference 1 0) sourceC610) = raw10216 := by
      apply Matrix.ext; unfold tripleCharges sourceA610 sourceB610 sourceC610 difference raw10216; decide +kernel
    rw [ha]
    exact (canonical10216 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA610 + difference 0 2) (sourceB610 + difference 2 0) sourceC610) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5441) := by
    have ha : (tripleCharges (sourceA610 + difference 0 2) (sourceB610 + difference 2 0) sourceC610) = raw10217 := by
      apply Matrix.ext; unfold tripleCharges sourceA610 sourceB610 sourceC610 difference raw10217; decide +kernel
    rw [ha]
    exact (canonical10217 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA610 + difference 0 3) (sourceB610 + difference 3 0) sourceC610) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5441) := by
    have ha : (tripleCharges (sourceA610 + difference 0 3) (sourceB610 + difference 3 0) sourceC610) = raw10218 := by
      apply Matrix.ext; unfold tripleCharges sourceA610 sourceB610 sourceC610 difference raw10218; decide +kernel
    rw [ha]
    exact (canonical10218 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA610 + difference 0 4) (sourceB610 + difference 4 0) sourceC610) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4094) := by
    have ha : (tripleCharges (sourceA610 + difference 0 4) (sourceB610 + difference 4 0) sourceC610) = raw5062 := by
      apply Matrix.ext; unfold tripleCharges sourceA610 sourceB610 sourceC610 difference raw5062; decide +kernel
    rw [ha]
    exact (canonical5062 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA610 + difference 0 5) (sourceB610 + difference 5 0) sourceC610) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5455) := by
    have ha : (tripleCharges (sourceA610 + difference 0 5) (sourceB610 + difference 5 0) sourceC610) = raw10219 := by
      apply Matrix.ext; unfold tripleCharges sourceA610 sourceB610 sourceC610 difference raw10219; decide +kernel
    rw [ha]
    exact (canonical10219 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA610 + difference 1 0) (sourceB610 + difference 0 1) sourceC610) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4623) := by
    have ha : (tripleCharges (sourceA610 + difference 1 0) (sourceB610 + difference 0 1) sourceC610) = raw10220 := by
      apply Matrix.ext; unfold tripleCharges sourceA610 sourceB610 sourceC610 difference raw10220; decide +kernel
    rw [ha]
    exact (canonical10220 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA610 + difference 1 2) (sourceB610 + difference 2 1) sourceC610) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5168) := by
    have ha : (tripleCharges (sourceA610 + difference 1 2) (sourceB610 + difference 2 1) sourceC610) = raw10221 := by
      apply Matrix.ext; unfold tripleCharges sourceA610 sourceB610 sourceC610 difference raw10221; decide +kernel
    rw [ha]
    exact (canonical10221 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA610 + difference 1 3) (sourceB610 + difference 3 1) sourceC610) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5168) := by
    have ha : (tripleCharges (sourceA610 + difference 1 3) (sourceB610 + difference 3 1) sourceC610) = raw10222 := by
      apply Matrix.ext; unfold tripleCharges sourceA610 sourceB610 sourceC610 difference raw10222; decide +kernel
    rw [ha]
    exact (canonical10222 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA610 + difference 1 4) (sourceB610 + difference 4 1) sourceC610) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5308) := by
    have ha : (tripleCharges (sourceA610 + difference 1 4) (sourceB610 + difference 4 1) sourceC610) = raw5067 := by
      apply Matrix.ext; unfold tripleCharges sourceA610 sourceB610 sourceC610 difference raw5067; decide +kernel
    rw [ha]
    exact (canonical5067 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA610 + difference 1 5) (sourceB610 + difference 5 1) sourceC610) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5306) := by
    have ha : (tripleCharges (sourceA610 + difference 1 5) (sourceB610 + difference 5 1) sourceC610) = raw10223 := by
      apply Matrix.ext; unfold tripleCharges sourceA610 sourceB610 sourceC610 difference raw10223; decide +kernel
    rw [ha]
    exact (canonical10223 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA610 + difference 2 0) (sourceB610 + difference 0 2) sourceC610) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4623) := by
    have ha : (tripleCharges (sourceA610 + difference 2 0) (sourceB610 + difference 0 2) sourceC610) = raw10224 := by
      apply Matrix.ext; unfold tripleCharges sourceA610 sourceB610 sourceC610 difference raw10224; decide +kernel
    rw [ha]
    exact (canonical10224 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA610 + difference 2 1) (sourceB610 + difference 1 2) sourceC610) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5168) := by
    have ha : (tripleCharges (sourceA610 + difference 2 1) (sourceB610 + difference 1 2) sourceC610) = raw10225 := by
      apply Matrix.ext; unfold tripleCharges sourceA610 sourceB610 sourceC610 difference raw10225; decide +kernel
    rw [ha]
    exact (canonical10225 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA610 + difference 2 3) (sourceB610 + difference 3 2) sourceC610) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5168) := by
    have ha : (tripleCharges (sourceA610 + difference 2 3) (sourceB610 + difference 3 2) sourceC610) = raw10226 := by
      apply Matrix.ext; unfold tripleCharges sourceA610 sourceB610 sourceC610 difference raw10226; decide +kernel
    rw [ha]
    exact (canonical10226 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA610 + difference 2 4) (sourceB610 + difference 4 2) sourceC610) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5308) := by
    have ha : (tripleCharges (sourceA610 + difference 2 4) (sourceB610 + difference 4 2) sourceC610) = raw5072 := by
      apply Matrix.ext; unfold tripleCharges sourceA610 sourceB610 sourceC610 difference raw5072; decide +kernel
    rw [ha]
    exact (canonical5072 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA610 + difference 2 5) (sourceB610 + difference 5 2) sourceC610) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5306) := by
    have ha : (tripleCharges (sourceA610 + difference 2 5) (sourceB610 + difference 5 2) sourceC610) = raw10227 := by
      apply Matrix.ext; unfold tripleCharges sourceA610 sourceB610 sourceC610 difference raw10227; decide +kernel
    rw [ha]
    exact (canonical10227 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA610 + difference 3 0) (sourceB610 + difference 0 3) sourceC610) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4623) := by
    have ha : (tripleCharges (sourceA610 + difference 3 0) (sourceB610 + difference 0 3) sourceC610) = raw10228 := by
      apply Matrix.ext; unfold tripleCharges sourceA610 sourceB610 sourceC610 difference raw10228; decide +kernel
    rw [ha]
    exact (canonical10228 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA610 + difference 3 1) (sourceB610 + difference 1 3) sourceC610) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5168) := by
    have ha : (tripleCharges (sourceA610 + difference 3 1) (sourceB610 + difference 1 3) sourceC610) = raw10229 := by
      apply Matrix.ext; unfold tripleCharges sourceA610 sourceB610 sourceC610 difference raw10229; decide +kernel
    rw [ha]
    exact (canonical10229 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA610 + difference 3 2) (sourceB610 + difference 2 3) sourceC610) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5168) := by
    have ha : (tripleCharges (sourceA610 + difference 3 2) (sourceB610 + difference 2 3) sourceC610) = raw10230 := by
      apply Matrix.ext; unfold tripleCharges sourceA610 sourceB610 sourceC610 difference raw10230; decide +kernel
    rw [ha]
    exact (canonical10230 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA610 + difference 3 4) (sourceB610 + difference 4 3) sourceC610) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5308) := by
    have ha : (tripleCharges (sourceA610 + difference 3 4) (sourceB610 + difference 4 3) sourceC610) = raw5077 := by
      apply Matrix.ext; unfold tripleCharges sourceA610 sourceB610 sourceC610 difference raw5077; decide +kernel
    rw [ha]
    exact (canonical5077 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA610 + difference 3 5) (sourceB610 + difference 5 3) sourceC610) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5306) := by
    have ha : (tripleCharges (sourceA610 + difference 3 5) (sourceB610 + difference 5 3) sourceC610) = raw10231 := by
      apply Matrix.ext; unfold tripleCharges sourceA610 sourceB610 sourceC610 difference raw10231; decide +kernel
    rw [ha]
    exact (canonical10231 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA610 + difference 4 0) (sourceB610 + difference 0 4) sourceC610) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4627) := by
    have ha : (tripleCharges (sourceA610 + difference 4 0) (sourceB610 + difference 0 4) sourceC610) = raw10232 := by
      apply Matrix.ext; unfold tripleCharges sourceA610 sourceB610 sourceC610 difference raw10232; decide +kernel
    rw [ha]
    exact (canonical10232 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA610 + difference 4 1) (sourceB610 + difference 1 4) sourceC610) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5176) := by
    have ha : (tripleCharges (sourceA610 + difference 4 1) (sourceB610 + difference 1 4) sourceC610) = raw10233 := by
      apply Matrix.ext; unfold tripleCharges sourceA610 sourceB610 sourceC610 difference raw10233; decide +kernel
    rw [ha]
    exact (canonical10233 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA610 + difference 4 2) (sourceB610 + difference 2 4) sourceC610) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5176) := by
    have ha : (tripleCharges (sourceA610 + difference 4 2) (sourceB610 + difference 2 4) sourceC610) = raw10234 := by
      apply Matrix.ext; unfold tripleCharges sourceA610 sourceB610 sourceC610 difference raw10234; decide +kernel
    rw [ha]
    exact (canonical10234 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA610 + difference 4 3) (sourceB610 + difference 3 4) sourceC610) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5176) := by
    have ha : (tripleCharges (sourceA610 + difference 4 3) (sourceB610 + difference 3 4) sourceC610) = raw10235 := by
      apply Matrix.ext; unfold tripleCharges sourceA610 sourceB610 sourceC610 difference raw10235; decide +kernel
    rw [ha]
    exact (canonical10235 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA610 + difference 4 5) (sourceB610 + difference 5 4) sourceC610) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5310) := by
    have ha : (tripleCharges (sourceA610 + difference 4 5) (sourceB610 + difference 5 4) sourceC610) = raw10236 := by
      apply Matrix.ext; unfold tripleCharges sourceA610 sourceB610 sourceC610 difference raw10236; decide +kernel
    rw [ha]
    exact (canonical10236 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA610 + difference 5 0) (sourceB610 + difference 0 5) sourceC610) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4625) := by
    have ha : (tripleCharges (sourceA610 + difference 5 0) (sourceB610 + difference 0 5) sourceC610) = raw5078 := by
      apply Matrix.ext; unfold tripleCharges sourceA610 sourceB610 sourceC610 difference raw5078; decide +kernel
    rw [ha]
    exact (canonical5078 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA610 + difference 5 1) (sourceB610 + difference 1 5) sourceC610) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5171) := by
    have ha : (tripleCharges (sourceA610 + difference 5 1) (sourceB610 + difference 1 5) sourceC610) = raw5079 := by
      apply Matrix.ext; unfold tripleCharges sourceA610 sourceB610 sourceC610 difference raw5079; decide +kernel
    rw [ha]
    exact (canonical5079 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA610 + difference 5 2) (sourceB610 + difference 2 5) sourceC610) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5171) := by
    have ha : (tripleCharges (sourceA610 + difference 5 2) (sourceB610 + difference 2 5) sourceC610) = raw5080 := by
      apply Matrix.ext; unfold tripleCharges sourceA610 sourceB610 sourceC610 difference raw5080; decide +kernel
    rw [ha]
    exact (canonical5080 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA610 + difference 5 3) (sourceB610 + difference 3 5) sourceC610) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5171) := by
    have ha : (tripleCharges (sourceA610 + difference 5 3) (sourceB610 + difference 3 5) sourceC610) = raw5081 := by
      apply Matrix.ext; unfold tripleCharges sourceA610 sourceB610 sourceC610 difference raw5081; decide +kernel
    rw [ha]
    exact (canonical5081 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA610 + difference 5 4) (sourceB610 + difference 4 5) sourceC610) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5312) := by
    have ha : (tripleCharges (sourceA610 + difference 5 4) (sourceB610 + difference 4 5) sourceC610) = raw10237 := by
      apply Matrix.ext; unfold tripleCharges sourceA610 sourceB610 sourceC610 difference raw10237; decide +kernel
    rw [ha]
    exact (canonical10237 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA610 sourceB610 sourceC610
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm610, Integer.Sparse.eval]
  linarith only [hs]

def sourceA611 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB611 : Charge := ![1, 0, 0, 0, -2, 1]
def sourceC611 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceForm611 : Integer.Sparse Master := [(Sum.inr 4617, 3), (Sum.inr 4621, 1), (Sum.inr 4626, 1), (Sum.inr 4868, 3), (Sum.inr 4897, 1), (Sum.inr 5161, 6), (Sum.inr 5175, 3), (Sum.inr 5272, 3), (Sum.inr 5291, 3), (Sum.inr 5295, 3), (Sum.inr 5308, 1), (Sum.inr 5310, 1), (Sum.inr 5311, 1)]

theorem sourceEq611 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm611 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA611 + difference 0 1) (sourceB611 + difference 1 0) sourceC611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5291) := by
    have ha : (tripleCharges (sourceA611 + difference 0 1) (sourceB611 + difference 1 0) sourceC611) = raw10238 := by
      apply Matrix.ext; unfold tripleCharges sourceA611 sourceB611 sourceC611 difference raw10238; decide +kernel
    rw [ha]
    exact (canonical10238 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA611 + difference 0 2) (sourceB611 + difference 2 0) sourceC611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5291) := by
    have ha : (tripleCharges (sourceA611 + difference 0 2) (sourceB611 + difference 2 0) sourceC611) = raw10239 := by
      apply Matrix.ext; unfold tripleCharges sourceA611 sourceB611 sourceC611 difference raw10239; decide +kernel
    rw [ha]
    exact (canonical10239 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA611 + difference 0 3) (sourceB611 + difference 3 0) sourceC611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5291) := by
    have ha : (tripleCharges (sourceA611 + difference 0 3) (sourceB611 + difference 3 0) sourceC611) = raw10240 := by
      apply Matrix.ext; unfold tripleCharges sourceA611 sourceB611 sourceC611 difference raw10240; decide +kernel
    rw [ha]
    exact (canonical10240 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA611 + difference 0 4) (sourceB611 + difference 4 0) sourceC611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5308) := by
    have ha : (tripleCharges (sourceA611 + difference 0 4) (sourceB611 + difference 4 0) sourceC611) = raw5105 := by
      apply Matrix.ext; unfold tripleCharges sourceA611 sourceB611 sourceC611 difference raw5105; decide +kernel
    rw [ha]
    exact (canonical5105 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA611 + difference 0 5) (sourceB611 + difference 5 0) sourceC611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5310) := by
    have ha : (tripleCharges (sourceA611 + difference 0 5) (sourceB611 + difference 5 0) sourceC611) = raw10241 := by
      apply Matrix.ext; unfold tripleCharges sourceA611 sourceB611 sourceC611 difference raw10241; decide +kernel
    rw [ha]
    exact (canonical10241 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA611 + difference 1 0) (sourceB611 + difference 0 1) sourceC611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4617) := by
    have ha : (tripleCharges (sourceA611 + difference 1 0) (sourceB611 + difference 0 1) sourceC611) = raw10242 := by
      apply Matrix.ext; unfold tripleCharges sourceA611 sourceB611 sourceC611 difference raw10242; decide +kernel
    rw [ha]
    exact (canonical10242 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA611 + difference 1 2) (sourceB611 + difference 2 1) sourceC611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5161) := by
    have ha : (tripleCharges (sourceA611 + difference 1 2) (sourceB611 + difference 2 1) sourceC611) = raw10243 := by
      apply Matrix.ext; unfold tripleCharges sourceA611 sourceB611 sourceC611 difference raw10243; decide +kernel
    rw [ha]
    exact (canonical10243 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA611 + difference 1 3) (sourceB611 + difference 3 1) sourceC611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5161) := by
    have ha : (tripleCharges (sourceA611 + difference 1 3) (sourceB611 + difference 3 1) sourceC611) = raw10244 := by
      apply Matrix.ext; unfold tripleCharges sourceA611 sourceB611 sourceC611 difference raw10244; decide +kernel
    rw [ha]
    exact (canonical10244 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA611 + difference 1 4) (sourceB611 + difference 4 1) sourceC611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5272) := by
    have ha : (tripleCharges (sourceA611 + difference 1 4) (sourceB611 + difference 4 1) sourceC611) = raw5110 := by
      apply Matrix.ext; unfold tripleCharges sourceA611 sourceB611 sourceC611 difference raw5110; decide +kernel
    rw [ha]
    exact (canonical5110 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA611 + difference 1 5) (sourceB611 + difference 5 1) sourceC611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5295) := by
    have ha : (tripleCharges (sourceA611 + difference 1 5) (sourceB611 + difference 5 1) sourceC611) = raw10245 := by
      apply Matrix.ext; unfold tripleCharges sourceA611 sourceB611 sourceC611 difference raw10245; decide +kernel
    rw [ha]
    exact (canonical10245 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA611 + difference 2 0) (sourceB611 + difference 0 2) sourceC611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4617) := by
    have ha : (tripleCharges (sourceA611 + difference 2 0) (sourceB611 + difference 0 2) sourceC611) = raw10246 := by
      apply Matrix.ext; unfold tripleCharges sourceA611 sourceB611 sourceC611 difference raw10246; decide +kernel
    rw [ha]
    exact (canonical10246 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA611 + difference 2 1) (sourceB611 + difference 1 2) sourceC611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5161) := by
    have ha : (tripleCharges (sourceA611 + difference 2 1) (sourceB611 + difference 1 2) sourceC611) = raw10247 := by
      apply Matrix.ext; unfold tripleCharges sourceA611 sourceB611 sourceC611 difference raw10247; decide +kernel
    rw [ha]
    exact (canonical10247 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA611 + difference 2 3) (sourceB611 + difference 3 2) sourceC611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5161) := by
    have ha : (tripleCharges (sourceA611 + difference 2 3) (sourceB611 + difference 3 2) sourceC611) = raw10248 := by
      apply Matrix.ext; unfold tripleCharges sourceA611 sourceB611 sourceC611 difference raw10248; decide +kernel
    rw [ha]
    exact (canonical10248 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA611 + difference 2 4) (sourceB611 + difference 4 2) sourceC611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5272) := by
    have ha : (tripleCharges (sourceA611 + difference 2 4) (sourceB611 + difference 4 2) sourceC611) = raw5115 := by
      apply Matrix.ext; unfold tripleCharges sourceA611 sourceB611 sourceC611 difference raw5115; decide +kernel
    rw [ha]
    exact (canonical5115 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA611 + difference 2 5) (sourceB611 + difference 5 2) sourceC611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5295) := by
    have ha : (tripleCharges (sourceA611 + difference 2 5) (sourceB611 + difference 5 2) sourceC611) = raw10249 := by
      apply Matrix.ext; unfold tripleCharges sourceA611 sourceB611 sourceC611 difference raw10249; decide +kernel
    rw [ha]
    exact (canonical10249 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA611 + difference 3 0) (sourceB611 + difference 0 3) sourceC611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4617) := by
    have ha : (tripleCharges (sourceA611 + difference 3 0) (sourceB611 + difference 0 3) sourceC611) = raw10250 := by
      apply Matrix.ext; unfold tripleCharges sourceA611 sourceB611 sourceC611 difference raw10250; decide +kernel
    rw [ha]
    exact (canonical10250 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA611 + difference 3 1) (sourceB611 + difference 1 3) sourceC611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5161) := by
    have ha : (tripleCharges (sourceA611 + difference 3 1) (sourceB611 + difference 1 3) sourceC611) = raw10251 := by
      apply Matrix.ext; unfold tripleCharges sourceA611 sourceB611 sourceC611 difference raw10251; decide +kernel
    rw [ha]
    exact (canonical10251 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA611 + difference 3 2) (sourceB611 + difference 2 3) sourceC611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5161) := by
    have ha : (tripleCharges (sourceA611 + difference 3 2) (sourceB611 + difference 2 3) sourceC611) = raw10252 := by
      apply Matrix.ext; unfold tripleCharges sourceA611 sourceB611 sourceC611 difference raw10252; decide +kernel
    rw [ha]
    exact (canonical10252 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA611 + difference 3 4) (sourceB611 + difference 4 3) sourceC611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5272) := by
    have ha : (tripleCharges (sourceA611 + difference 3 4) (sourceB611 + difference 4 3) sourceC611) = raw5120 := by
      apply Matrix.ext; unfold tripleCharges sourceA611 sourceB611 sourceC611 difference raw5120; decide +kernel
    rw [ha]
    exact (canonical5120 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA611 + difference 3 5) (sourceB611 + difference 5 3) sourceC611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5295) := by
    have ha : (tripleCharges (sourceA611 + difference 3 5) (sourceB611 + difference 5 3) sourceC611) = raw10253 := by
      apply Matrix.ext; unfold tripleCharges sourceA611 sourceB611 sourceC611 difference raw10253; decide +kernel
    rw [ha]
    exact (canonical10253 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA611 + difference 4 0) (sourceB611 + difference 0 4) sourceC611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4626) := by
    have ha : (tripleCharges (sourceA611 + difference 4 0) (sourceB611 + difference 0 4) sourceC611) = raw10254 := by
      apply Matrix.ext; unfold tripleCharges sourceA611 sourceB611 sourceC611 difference raw10254; decide +kernel
    rw [ha]
    exact (canonical10254 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA611 + difference 4 1) (sourceB611 + difference 1 4) sourceC611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5175) := by
    have ha : (tripleCharges (sourceA611 + difference 4 1) (sourceB611 + difference 1 4) sourceC611) = raw10255 := by
      apply Matrix.ext; unfold tripleCharges sourceA611 sourceB611 sourceC611 difference raw10255; decide +kernel
    rw [ha]
    exact (canonical10255 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA611 + difference 4 2) (sourceB611 + difference 2 4) sourceC611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5175) := by
    have ha : (tripleCharges (sourceA611 + difference 4 2) (sourceB611 + difference 2 4) sourceC611) = raw10256 := by
      apply Matrix.ext; unfold tripleCharges sourceA611 sourceB611 sourceC611 difference raw10256; decide +kernel
    rw [ha]
    exact (canonical10256 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA611 + difference 4 3) (sourceB611 + difference 3 4) sourceC611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5175) := by
    have ha : (tripleCharges (sourceA611 + difference 4 3) (sourceB611 + difference 3 4) sourceC611) = raw10257 := by
      apply Matrix.ext; unfold tripleCharges sourceA611 sourceB611 sourceC611 difference raw10257; decide +kernel
    rw [ha]
    exact (canonical10257 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA611 + difference 4 5) (sourceB611 + difference 5 4) sourceC611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5311) := by
    have ha : (tripleCharges (sourceA611 + difference 4 5) (sourceB611 + difference 5 4) sourceC611) = raw10258 := by
      apply Matrix.ext; unfold tripleCharges sourceA611 sourceB611 sourceC611 difference raw10258; decide +kernel
    rw [ha]
    exact (canonical10258 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA611 + difference 5 0) (sourceB611 + difference 0 5) sourceC611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4621) := by
    have ha : (tripleCharges (sourceA611 + difference 5 0) (sourceB611 + difference 0 5) sourceC611) = raw5121 := by
      apply Matrix.ext; unfold tripleCharges sourceA611 sourceB611 sourceC611 difference raw5121; decide +kernel
    rw [ha]
    exact (canonical5121 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA611 + difference 5 1) (sourceB611 + difference 1 5) sourceC611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4868) := by
    have ha : (tripleCharges (sourceA611 + difference 5 1) (sourceB611 + difference 1 5) sourceC611) = raw5122 := by
      apply Matrix.ext; unfold tripleCharges sourceA611 sourceB611 sourceC611 difference raw5122; decide +kernel
    rw [ha]
    exact (canonical5122 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA611 + difference 5 2) (sourceB611 + difference 2 5) sourceC611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4868) := by
    have ha : (tripleCharges (sourceA611 + difference 5 2) (sourceB611 + difference 2 5) sourceC611) = raw5123 := by
      apply Matrix.ext; unfold tripleCharges sourceA611 sourceB611 sourceC611 difference raw5123; decide +kernel
    rw [ha]
    exact (canonical5123 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA611 + difference 5 3) (sourceB611 + difference 3 5) sourceC611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4868) := by
    have ha : (tripleCharges (sourceA611 + difference 5 3) (sourceB611 + difference 3 5) sourceC611) = raw5124 := by
      apply Matrix.ext; unfold tripleCharges sourceA611 sourceB611 sourceC611 difference raw5124; decide +kernel
    rw [ha]
    exact (canonical5124 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA611 + difference 5 4) (sourceB611 + difference 4 5) sourceC611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4897) := by
    have ha : (tripleCharges (sourceA611 + difference 5 4) (sourceB611 + difference 4 5) sourceC611) = raw10259 := by
      apply Matrix.ext; unfold tripleCharges sourceA611 sourceB611 sourceC611 difference raw10259; decide +kernel
    rw [ha]
    exact (canonical10259 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA611 sourceB611 sourceC611
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm611, Integer.Sparse.eval]
  linarith only [hs]

def sourceA612 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB612 : Charge := ![1, 0, 0, 0, -2, 1]
def sourceC612 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceForm612 : Integer.Sparse Master := [(Sum.inr 1306, 3), (Sum.inr 1308, 1), (Sum.inr 1310, 1), (Sum.inr 2769, 3), (Sum.inr 2788, 1), (Sum.inr 2789, 1), (Sum.inr 2964, 6), (Sum.inr 2966, 3), (Sum.inr 2967, 3), (Sum.inr 3103, 3), (Sum.inr 3113, 3), (Sum.inr 3114, 1), (Sum.inr 3124, 1)]

theorem sourceEq612 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm612 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA612 + difference 0 1) (sourceB612 + difference 1 0) sourceC612) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3103) := by
    have ha : (tripleCharges (sourceA612 + difference 0 1) (sourceB612 + difference 1 0) sourceC612) = raw10260 := by
      apply Matrix.ext; unfold tripleCharges sourceA612 sourceB612 sourceC612 difference raw10260; decide +kernel
    rw [ha]
    exact (canonical10260 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA612 + difference 0 2) (sourceB612 + difference 2 0) sourceC612) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3103) := by
    have ha : (tripleCharges (sourceA612 + difference 0 2) (sourceB612 + difference 2 0) sourceC612) = raw10261 := by
      apply Matrix.ext; unfold tripleCharges sourceA612 sourceB612 sourceC612 difference raw10261; decide +kernel
    rw [ha]
    exact (canonical10261 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA612 + difference 0 3) (sourceB612 + difference 3 0) sourceC612) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3103) := by
    have ha : (tripleCharges (sourceA612 + difference 0 3) (sourceB612 + difference 3 0) sourceC612) = raw10262 := by
      apply Matrix.ext; unfold tripleCharges sourceA612 sourceB612 sourceC612 difference raw10262; decide +kernel
    rw [ha]
    exact (canonical10262 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA612 + difference 0 4) (sourceB612 + difference 4 0) sourceC612) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3124) := by
    have ha : (tripleCharges (sourceA612 + difference 0 4) (sourceB612 + difference 4 0) sourceC612) = raw10263 := by
      apply Matrix.ext; unfold tripleCharges sourceA612 sourceB612 sourceC612 difference raw10263; decide +kernel
    rw [ha]
    exact (canonical10263 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA612 + difference 0 5) (sourceB612 + difference 5 0) sourceC612) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2788) := by
    have ha : (tripleCharges (sourceA612 + difference 0 5) (sourceB612 + difference 5 0) sourceC612) = raw10264 := by
      apply Matrix.ext; unfold tripleCharges sourceA612 sourceB612 sourceC612 difference raw10264; decide +kernel
    rw [ha]
    exact (canonical10264 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA612 + difference 1 0) (sourceB612 + difference 0 1) sourceC612) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1306) := by
    have ha : (tripleCharges (sourceA612 + difference 1 0) (sourceB612 + difference 0 1) sourceC612) = raw10265 := by
      apply Matrix.ext; unfold tripleCharges sourceA612 sourceB612 sourceC612 difference raw10265; decide +kernel
    rw [ha]
    exact (canonical10265 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA612 + difference 1 2) (sourceB612 + difference 2 1) sourceC612) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2964) := by
    have ha : (tripleCharges (sourceA612 + difference 1 2) (sourceB612 + difference 2 1) sourceC612) = raw10266 := by
      apply Matrix.ext; unfold tripleCharges sourceA612 sourceB612 sourceC612 difference raw10266; decide +kernel
    rw [ha]
    exact (canonical10266 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA612 + difference 1 3) (sourceB612 + difference 3 1) sourceC612) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2964) := by
    have ha : (tripleCharges (sourceA612 + difference 1 3) (sourceB612 + difference 3 1) sourceC612) = raw10267 := by
      apply Matrix.ext; unfold tripleCharges sourceA612 sourceB612 sourceC612 difference raw10267; decide +kernel
    rw [ha]
    exact (canonical10267 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA612 + difference 1 4) (sourceB612 + difference 4 1) sourceC612) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3113) := by
    have ha : (tripleCharges (sourceA612 + difference 1 4) (sourceB612 + difference 4 1) sourceC612) = raw10268 := by
      apply Matrix.ext; unfold tripleCharges sourceA612 sourceB612 sourceC612 difference raw10268; decide +kernel
    rw [ha]
    exact (canonical10268 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA612 + difference 1 5) (sourceB612 + difference 5 1) sourceC612) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2769) := by
    have ha : (tripleCharges (sourceA612 + difference 1 5) (sourceB612 + difference 5 1) sourceC612) = raw10269 := by
      apply Matrix.ext; unfold tripleCharges sourceA612 sourceB612 sourceC612 difference raw10269; decide +kernel
    rw [ha]
    exact (canonical10269 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA612 + difference 2 0) (sourceB612 + difference 0 2) sourceC612) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1306) := by
    have ha : (tripleCharges (sourceA612 + difference 2 0) (sourceB612 + difference 0 2) sourceC612) = raw10270 := by
      apply Matrix.ext; unfold tripleCharges sourceA612 sourceB612 sourceC612 difference raw10270; decide +kernel
    rw [ha]
    exact (canonical10270 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA612 + difference 2 1) (sourceB612 + difference 1 2) sourceC612) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2964) := by
    have ha : (tripleCharges (sourceA612 + difference 2 1) (sourceB612 + difference 1 2) sourceC612) = raw10271 := by
      apply Matrix.ext; unfold tripleCharges sourceA612 sourceB612 sourceC612 difference raw10271; decide +kernel
    rw [ha]
    exact (canonical10271 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA612 + difference 2 3) (sourceB612 + difference 3 2) sourceC612) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2964) := by
    have ha : (tripleCharges (sourceA612 + difference 2 3) (sourceB612 + difference 3 2) sourceC612) = raw10272 := by
      apply Matrix.ext; unfold tripleCharges sourceA612 sourceB612 sourceC612 difference raw10272; decide +kernel
    rw [ha]
    exact (canonical10272 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA612 + difference 2 4) (sourceB612 + difference 4 2) sourceC612) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3113) := by
    have ha : (tripleCharges (sourceA612 + difference 2 4) (sourceB612 + difference 4 2) sourceC612) = raw10273 := by
      apply Matrix.ext; unfold tripleCharges sourceA612 sourceB612 sourceC612 difference raw10273; decide +kernel
    rw [ha]
    exact (canonical10273 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA612 + difference 2 5) (sourceB612 + difference 5 2) sourceC612) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2769) := by
    have ha : (tripleCharges (sourceA612 + difference 2 5) (sourceB612 + difference 5 2) sourceC612) = raw10274 := by
      apply Matrix.ext; unfold tripleCharges sourceA612 sourceB612 sourceC612 difference raw10274; decide +kernel
    rw [ha]
    exact (canonical10274 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA612 + difference 3 0) (sourceB612 + difference 0 3) sourceC612) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1306) := by
    have ha : (tripleCharges (sourceA612 + difference 3 0) (sourceB612 + difference 0 3) sourceC612) = raw10275 := by
      apply Matrix.ext; unfold tripleCharges sourceA612 sourceB612 sourceC612 difference raw10275; decide +kernel
    rw [ha]
    exact (canonical10275 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA612 + difference 3 1) (sourceB612 + difference 1 3) sourceC612) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2964) := by
    have ha : (tripleCharges (sourceA612 + difference 3 1) (sourceB612 + difference 1 3) sourceC612) = raw10276 := by
      apply Matrix.ext; unfold tripleCharges sourceA612 sourceB612 sourceC612 difference raw10276; decide +kernel
    rw [ha]
    exact (canonical10276 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA612 + difference 3 2) (sourceB612 + difference 2 3) sourceC612) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2964) := by
    have ha : (tripleCharges (sourceA612 + difference 3 2) (sourceB612 + difference 2 3) sourceC612) = raw10277 := by
      apply Matrix.ext; unfold tripleCharges sourceA612 sourceB612 sourceC612 difference raw10277; decide +kernel
    rw [ha]
    exact (canonical10277 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA612 + difference 3 4) (sourceB612 + difference 4 3) sourceC612) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3113) := by
    have ha : (tripleCharges (sourceA612 + difference 3 4) (sourceB612 + difference 4 3) sourceC612) = raw10278 := by
      apply Matrix.ext; unfold tripleCharges sourceA612 sourceB612 sourceC612 difference raw10278; decide +kernel
    rw [ha]
    exact (canonical10278 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA612 + difference 3 5) (sourceB612 + difference 5 3) sourceC612) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2769) := by
    have ha : (tripleCharges (sourceA612 + difference 3 5) (sourceB612 + difference 5 3) sourceC612) = raw10279 := by
      apply Matrix.ext; unfold tripleCharges sourceA612 sourceB612 sourceC612 difference raw10279; decide +kernel
    rw [ha]
    exact (canonical10279 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA612 + difference 4 0) (sourceB612 + difference 0 4) sourceC612) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1310) := by
    have ha : (tripleCharges (sourceA612 + difference 4 0) (sourceB612 + difference 0 4) sourceC612) = raw10280 := by
      apply Matrix.ext; unfold tripleCharges sourceA612 sourceB612 sourceC612 difference raw10280; decide +kernel
    rw [ha]
    exact (canonical10280 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA612 + difference 4 1) (sourceB612 + difference 1 4) sourceC612) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2967) := by
    have ha : (tripleCharges (sourceA612 + difference 4 1) (sourceB612 + difference 1 4) sourceC612) = raw10281 := by
      apply Matrix.ext; unfold tripleCharges sourceA612 sourceB612 sourceC612 difference raw10281; decide +kernel
    rw [ha]
    exact (canonical10281 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA612 + difference 4 2) (sourceB612 + difference 2 4) sourceC612) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2967) := by
    have ha : (tripleCharges (sourceA612 + difference 4 2) (sourceB612 + difference 2 4) sourceC612) = raw10282 := by
      apply Matrix.ext; unfold tripleCharges sourceA612 sourceB612 sourceC612 difference raw10282; decide +kernel
    rw [ha]
    exact (canonical10282 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA612 + difference 4 3) (sourceB612 + difference 3 4) sourceC612) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2967) := by
    have ha : (tripleCharges (sourceA612 + difference 4 3) (sourceB612 + difference 3 4) sourceC612) = raw10283 := by
      apply Matrix.ext; unfold tripleCharges sourceA612 sourceB612 sourceC612 difference raw10283; decide +kernel
    rw [ha]
    exact (canonical10283 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA612 + difference 4 5) (sourceB612 + difference 5 4) sourceC612) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2789) := by
    have ha : (tripleCharges (sourceA612 + difference 4 5) (sourceB612 + difference 5 4) sourceC612) = raw10284 := by
      apply Matrix.ext; unfold tripleCharges sourceA612 sourceB612 sourceC612 difference raw10284; decide +kernel
    rw [ha]
    exact (canonical10284 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA612 + difference 5 0) (sourceB612 + difference 0 5) sourceC612) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1308) := by
    have ha : (tripleCharges (sourceA612 + difference 5 0) (sourceB612 + difference 0 5) sourceC612) = raw10285 := by
      apply Matrix.ext; unfold tripleCharges sourceA612 sourceB612 sourceC612 difference raw10285; decide +kernel
    rw [ha]
    exact (canonical10285 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA612 + difference 5 1) (sourceB612 + difference 1 5) sourceC612) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2966) := by
    have ha : (tripleCharges (sourceA612 + difference 5 1) (sourceB612 + difference 1 5) sourceC612) = raw10286 := by
      apply Matrix.ext; unfold tripleCharges sourceA612 sourceB612 sourceC612 difference raw10286; decide +kernel
    rw [ha]
    exact (canonical10286 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA612 + difference 5 2) (sourceB612 + difference 2 5) sourceC612) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2966) := by
    have ha : (tripleCharges (sourceA612 + difference 5 2) (sourceB612 + difference 2 5) sourceC612) = raw10287 := by
      apply Matrix.ext; unfold tripleCharges sourceA612 sourceB612 sourceC612 difference raw10287; decide +kernel
    rw [ha]
    exact (canonical10287 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA612 + difference 5 3) (sourceB612 + difference 3 5) sourceC612) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2966) := by
    have ha : (tripleCharges (sourceA612 + difference 5 3) (sourceB612 + difference 3 5) sourceC612) = raw10288 := by
      apply Matrix.ext; unfold tripleCharges sourceA612 sourceB612 sourceC612 difference raw10288; decide +kernel
    rw [ha]
    exact (canonical10288 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA612 + difference 5 4) (sourceB612 + difference 4 5) sourceC612) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3114) := by
    have ha : (tripleCharges (sourceA612 + difference 5 4) (sourceB612 + difference 4 5) sourceC612) = raw10289 := by
      apply Matrix.ext; unfold tripleCharges sourceA612 sourceB612 sourceC612 difference raw10289; decide +kernel
    rw [ha]
    exact (canonical10289 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA612 sourceB612 sourceC612
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm612, Integer.Sparse.eval]
  linarith only [hs]

def sourceA613 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB613 : Charge := ![1, 0, 0, 0, -2, 1]
def sourceC613 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceForm613 : Integer.Sparse Master := [(Sum.inr 2261, 3), (Sum.inr 2289, 1), (Sum.inr 2292, 1), (Sum.inr 2719, 6), (Sum.inr 2737, 3), (Sum.inr 2740, 3), (Sum.inr 2761, 3), (Sum.inr 2765, 3), (Sum.inr 2780, 1), (Sum.inr 2786, 1), (Sum.inr 2789, 1), (Sum.inr 3098, 3), (Sum.inr 3121, 1)]

theorem sourceEq613 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm613 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA613 + difference 0 1) (sourceB613 + difference 1 0) sourceC613) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2765) := by
    have ha : (tripleCharges (sourceA613 + difference 0 1) (sourceB613 + difference 1 0) sourceC613) = raw10290 := by
      apply Matrix.ext; unfold tripleCharges sourceA613 sourceB613 sourceC613 difference raw10290; decide +kernel
    rw [ha]
    exact (canonical10290 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA613 + difference 0 2) (sourceB613 + difference 2 0) sourceC613) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2765) := by
    have ha : (tripleCharges (sourceA613 + difference 0 2) (sourceB613 + difference 2 0) sourceC613) = raw10291 := by
      apply Matrix.ext; unfold tripleCharges sourceA613 sourceB613 sourceC613 difference raw10291; decide +kernel
    rw [ha]
    exact (canonical10291 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA613 + difference 0 3) (sourceB613 + difference 3 0) sourceC613) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2765) := by
    have ha : (tripleCharges (sourceA613 + difference 0 3) (sourceB613 + difference 3 0) sourceC613) = raw10292 := by
      apply Matrix.ext; unfold tripleCharges sourceA613 sourceB613 sourceC613 difference raw10292; decide +kernel
    rw [ha]
    exact (canonical10292 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA613 + difference 0 4) (sourceB613 + difference 4 0) sourceC613) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2786) := by
    have ha : (tripleCharges (sourceA613 + difference 0 4) (sourceB613 + difference 4 0) sourceC613) = raw5135 := by
      apply Matrix.ext; unfold tripleCharges sourceA613 sourceB613 sourceC613 difference raw5135; decide +kernel
    rw [ha]
    exact (canonical5135 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA613 + difference 0 5) (sourceB613 + difference 5 0) sourceC613) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3121) := by
    have ha : (tripleCharges (sourceA613 + difference 0 5) (sourceB613 + difference 5 0) sourceC613) = raw10293 := by
      apply Matrix.ext; unfold tripleCharges sourceA613 sourceB613 sourceC613 difference raw10293; decide +kernel
    rw [ha]
    exact (canonical10293 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA613 + difference 1 0) (sourceB613 + difference 0 1) sourceC613) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2737) := by
    have ha : (tripleCharges (sourceA613 + difference 1 0) (sourceB613 + difference 0 1) sourceC613) = raw10294 := by
      apply Matrix.ext; unfold tripleCharges sourceA613 sourceB613 sourceC613 difference raw10294; decide +kernel
    rw [ha]
    exact (canonical10294 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA613 + difference 1 2) (sourceB613 + difference 2 1) sourceC613) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2719) := by
    have ha : (tripleCharges (sourceA613 + difference 1 2) (sourceB613 + difference 2 1) sourceC613) = raw10295 := by
      apply Matrix.ext; unfold tripleCharges sourceA613 sourceB613 sourceC613 difference raw10295; decide +kernel
    rw [ha]
    exact (canonical10295 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA613 + difference 1 3) (sourceB613 + difference 3 1) sourceC613) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2719) := by
    have ha : (tripleCharges (sourceA613 + difference 1 3) (sourceB613 + difference 3 1) sourceC613) = raw10296 := by
      apply Matrix.ext; unfold tripleCharges sourceA613 sourceB613 sourceC613 difference raw10296; decide +kernel
    rw [ha]
    exact (canonical10296 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA613 + difference 1 4) (sourceB613 + difference 4 1) sourceC613) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2740) := by
    have ha : (tripleCharges (sourceA613 + difference 1 4) (sourceB613 + difference 4 1) sourceC613) = raw5140 := by
      apply Matrix.ext; unfold tripleCharges sourceA613 sourceB613 sourceC613 difference raw5140; decide +kernel
    rw [ha]
    exact (canonical5140 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA613 + difference 1 5) (sourceB613 + difference 5 1) sourceC613) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3098) := by
    have ha : (tripleCharges (sourceA613 + difference 1 5) (sourceB613 + difference 5 1) sourceC613) = raw10297 := by
      apply Matrix.ext; unfold tripleCharges sourceA613 sourceB613 sourceC613 difference raw10297; decide +kernel
    rw [ha]
    exact (canonical10297 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA613 + difference 2 0) (sourceB613 + difference 0 2) sourceC613) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2737) := by
    have ha : (tripleCharges (sourceA613 + difference 2 0) (sourceB613 + difference 0 2) sourceC613) = raw10298 := by
      apply Matrix.ext; unfold tripleCharges sourceA613 sourceB613 sourceC613 difference raw10298; decide +kernel
    rw [ha]
    exact (canonical10298 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA613 + difference 2 1) (sourceB613 + difference 1 2) sourceC613) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2719) := by
    have ha : (tripleCharges (sourceA613 + difference 2 1) (sourceB613 + difference 1 2) sourceC613) = raw10299 := by
      apply Matrix.ext; unfold tripleCharges sourceA613 sourceB613 sourceC613 difference raw10299; decide +kernel
    rw [ha]
    exact (canonical10299 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA613 + difference 2 3) (sourceB613 + difference 3 2) sourceC613) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2719) := by
    have ha : (tripleCharges (sourceA613 + difference 2 3) (sourceB613 + difference 3 2) sourceC613) = raw10300 := by
      apply Matrix.ext; unfold tripleCharges sourceA613 sourceB613 sourceC613 difference raw10300; decide +kernel
    rw [ha]
    exact (canonical10300 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA613 + difference 2 4) (sourceB613 + difference 4 2) sourceC613) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2740) := by
    have ha : (tripleCharges (sourceA613 + difference 2 4) (sourceB613 + difference 4 2) sourceC613) = raw5145 := by
      apply Matrix.ext; unfold tripleCharges sourceA613 sourceB613 sourceC613 difference raw5145; decide +kernel
    rw [ha]
    exact (canonical5145 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA613 + difference 2 5) (sourceB613 + difference 5 2) sourceC613) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3098) := by
    have ha : (tripleCharges (sourceA613 + difference 2 5) (sourceB613 + difference 5 2) sourceC613) = raw10301 := by
      apply Matrix.ext; unfold tripleCharges sourceA613 sourceB613 sourceC613 difference raw10301; decide +kernel
    rw [ha]
    exact (canonical10301 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA613 + difference 3 0) (sourceB613 + difference 0 3) sourceC613) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2737) := by
    have ha : (tripleCharges (sourceA613 + difference 3 0) (sourceB613 + difference 0 3) sourceC613) = raw10302 := by
      apply Matrix.ext; unfold tripleCharges sourceA613 sourceB613 sourceC613 difference raw10302; decide +kernel
    rw [ha]
    exact (canonical10302 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA613 + difference 3 1) (sourceB613 + difference 1 3) sourceC613) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2719) := by
    have ha : (tripleCharges (sourceA613 + difference 3 1) (sourceB613 + difference 1 3) sourceC613) = raw10303 := by
      apply Matrix.ext; unfold tripleCharges sourceA613 sourceB613 sourceC613 difference raw10303; decide +kernel
    rw [ha]
    exact (canonical10303 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA613 + difference 3 2) (sourceB613 + difference 2 3) sourceC613) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2719) := by
    have ha : (tripleCharges (sourceA613 + difference 3 2) (sourceB613 + difference 2 3) sourceC613) = raw10304 := by
      apply Matrix.ext; unfold tripleCharges sourceA613 sourceB613 sourceC613 difference raw10304; decide +kernel
    rw [ha]
    exact (canonical10304 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA613 + difference 3 4) (sourceB613 + difference 4 3) sourceC613) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2740) := by
    have ha : (tripleCharges (sourceA613 + difference 3 4) (sourceB613 + difference 4 3) sourceC613) = raw5150 := by
      apply Matrix.ext; unfold tripleCharges sourceA613 sourceB613 sourceC613 difference raw5150; decide +kernel
    rw [ha]
    exact (canonical5150 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA613 + difference 3 5) (sourceB613 + difference 5 3) sourceC613) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3098) := by
    have ha : (tripleCharges (sourceA613 + difference 3 5) (sourceB613 + difference 5 3) sourceC613) = raw10305 := by
      apply Matrix.ext; unfold tripleCharges sourceA613 sourceB613 sourceC613 difference raw10305; decide +kernel
    rw [ha]
    exact (canonical10305 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA613 + difference 4 0) (sourceB613 + difference 0 4) sourceC613) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2780) := by
    have ha : (tripleCharges (sourceA613 + difference 4 0) (sourceB613 + difference 0 4) sourceC613) = raw10306 := by
      apply Matrix.ext; unfold tripleCharges sourceA613 sourceB613 sourceC613 difference raw10306; decide +kernel
    rw [ha]
    exact (canonical10306 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA613 + difference 4 1) (sourceB613 + difference 1 4) sourceC613) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2761) := by
    have ha : (tripleCharges (sourceA613 + difference 4 1) (sourceB613 + difference 1 4) sourceC613) = raw10307 := by
      apply Matrix.ext; unfold tripleCharges sourceA613 sourceB613 sourceC613 difference raw10307; decide +kernel
    rw [ha]
    exact (canonical10307 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA613 + difference 4 2) (sourceB613 + difference 2 4) sourceC613) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2761) := by
    have ha : (tripleCharges (sourceA613 + difference 4 2) (sourceB613 + difference 2 4) sourceC613) = raw10308 := by
      apply Matrix.ext; unfold tripleCharges sourceA613 sourceB613 sourceC613 difference raw10308; decide +kernel
    rw [ha]
    exact (canonical10308 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA613 + difference 4 3) (sourceB613 + difference 3 4) sourceC613) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2761) := by
    have ha : (tripleCharges (sourceA613 + difference 4 3) (sourceB613 + difference 3 4) sourceC613) = raw10309 := by
      apply Matrix.ext; unfold tripleCharges sourceA613 sourceB613 sourceC613 difference raw10309; decide +kernel
    rw [ha]
    exact (canonical10309 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA613 + difference 4 5) (sourceB613 + difference 5 4) sourceC613) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2789) := by
    have ha : (tripleCharges (sourceA613 + difference 4 5) (sourceB613 + difference 5 4) sourceC613) = raw10310 := by
      apply Matrix.ext; unfold tripleCharges sourceA613 sourceB613 sourceC613 difference raw10310; decide +kernel
    rw [ha]
    exact (canonical10310 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA613 + difference 5 0) (sourceB613 + difference 0 5) sourceC613) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2289) := by
    have ha : (tripleCharges (sourceA613 + difference 5 0) (sourceB613 + difference 0 5) sourceC613) = raw5151 := by
      apply Matrix.ext; unfold tripleCharges sourceA613 sourceB613 sourceC613 difference raw5151; decide +kernel
    rw [ha]
    exact (canonical5151 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA613 + difference 5 1) (sourceB613 + difference 1 5) sourceC613) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2261) := by
    have ha : (tripleCharges (sourceA613 + difference 5 1) (sourceB613 + difference 1 5) sourceC613) = raw5152 := by
      apply Matrix.ext; unfold tripleCharges sourceA613 sourceB613 sourceC613 difference raw5152; decide +kernel
    rw [ha]
    exact (canonical5152 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA613 + difference 5 2) (sourceB613 + difference 2 5) sourceC613) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2261) := by
    have ha : (tripleCharges (sourceA613 + difference 5 2) (sourceB613 + difference 2 5) sourceC613) = raw5153 := by
      apply Matrix.ext; unfold tripleCharges sourceA613 sourceB613 sourceC613 difference raw5153; decide +kernel
    rw [ha]
    exact (canonical5153 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA613 + difference 5 3) (sourceB613 + difference 3 5) sourceC613) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2261) := by
    have ha : (tripleCharges (sourceA613 + difference 5 3) (sourceB613 + difference 3 5) sourceC613) = raw5154 := by
      apply Matrix.ext; unfold tripleCharges sourceA613 sourceB613 sourceC613 difference raw5154; decide +kernel
    rw [ha]
    exact (canonical5154 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA613 + difference 5 4) (sourceB613 + difference 4 5) sourceC613) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2292) := by
    have ha : (tripleCharges (sourceA613 + difference 5 4) (sourceB613 + difference 4 5) sourceC613) = raw10311 := by
      apply Matrix.ext; unfold tripleCharges sourceA613 sourceB613 sourceC613 difference raw10311; decide +kernel
    rw [ha]
    exact (canonical10311 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA613 sourceB613 sourceC613
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm613, Integer.Sparse.eval]
  linarith only [hs]

def sourceA614 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB614 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceC614 : Charge := ![1, 0, 0, 0, -2, 1]
def sourceForm614 : Integer.Sparse Master := [(Sum.inr 4490, 6), (Sum.inr 4493, 1), (Sum.inr 4510, 2), (Sum.inr 5094, 6), (Sum.inr 5110, 6), (Sum.inr 5304, 6), (Sum.inr 5310, 2), (Sum.inr 5494, 1)]

theorem sourceEq614 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm614 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA614 + difference 0 1) (sourceB614 + difference 1 0) sourceC614) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA614 + difference 0 1) (sourceB614 + difference 1 0) sourceC614) = raw10312 := by
      apply Matrix.ext; unfold tripleCharges sourceA614 sourceB614 sourceC614 difference raw10312; decide +kernel
    rw [ha]
    exact (canonical10312 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA614 + difference 0 2) (sourceB614 + difference 2 0) sourceC614) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA614 + difference 0 2) (sourceB614 + difference 2 0) sourceC614) = raw10313 := by
      apply Matrix.ext; unfold tripleCharges sourceA614 sourceB614 sourceC614 difference raw10313; decide +kernel
    rw [ha]
    exact (canonical10313 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA614 + difference 0 3) (sourceB614 + difference 3 0) sourceC614) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA614 + difference 0 3) (sourceB614 + difference 3 0) sourceC614) = raw10314 := by
      apply Matrix.ext; unfold tripleCharges sourceA614 sourceB614 sourceC614 difference raw10314; decide +kernel
    rw [ha]
    exact (canonical10314 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA614 + difference 0 4) (sourceB614 + difference 4 0) sourceC614) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5310) := by
    have ha : (tripleCharges (sourceA614 + difference 0 4) (sourceB614 + difference 4 0) sourceC614) = raw10315 := by
      apply Matrix.ext; unfold tripleCharges sourceA614 sourceB614 sourceC614 difference raw10315; decide +kernel
    rw [ha]
    exact (canonical10315 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA614 + difference 0 5) (sourceB614 + difference 5 0) sourceC614) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5494) := by
    have ha : (tripleCharges (sourceA614 + difference 0 5) (sourceB614 + difference 5 0) sourceC614) = raw10316 := by
      apply Matrix.ext; unfold tripleCharges sourceA614 sourceB614 sourceC614 difference raw10316; decide +kernel
    rw [ha]
    exact (canonical10316 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA614 + difference 1 0) (sourceB614 + difference 0 1) sourceC614) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4490) := by
    have ha : (tripleCharges (sourceA614 + difference 1 0) (sourceB614 + difference 0 1) sourceC614) = raw10317 := by
      apply Matrix.ext; unfold tripleCharges sourceA614 sourceB614 sourceC614 difference raw10317; decide +kernel
    rw [ha]
    exact (canonical10317 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA614 + difference 1 2) (sourceB614 + difference 2 1) sourceC614) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5094) := by
    have ha : (tripleCharges (sourceA614 + difference 1 2) (sourceB614 + difference 2 1) sourceC614) = raw10318 := by
      apply Matrix.ext; unfold tripleCharges sourceA614 sourceB614 sourceC614 difference raw10318; decide +kernel
    rw [ha]
    exact (canonical10318 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA614 + difference 1 3) (sourceB614 + difference 3 1) sourceC614) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5094) := by
    have ha : (tripleCharges (sourceA614 + difference 1 3) (sourceB614 + difference 3 1) sourceC614) = raw10319 := by
      apply Matrix.ext; unfold tripleCharges sourceA614 sourceB614 sourceC614 difference raw10319; decide +kernel
    rw [ha]
    exact (canonical10319 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA614 + difference 1 4) (sourceB614 + difference 4 1) sourceC614) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5110) := by
    have ha : (tripleCharges (sourceA614 + difference 1 4) (sourceB614 + difference 4 1) sourceC614) = raw10320 := by
      apply Matrix.ext; unfold tripleCharges sourceA614 sourceB614 sourceC614 difference raw10320; decide +kernel
    rw [ha]
    exact (canonical10320 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA614 + difference 1 5) (sourceB614 + difference 5 1) sourceC614) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA614 + difference 1 5) (sourceB614 + difference 5 1) sourceC614) = raw10321 := by
      apply Matrix.ext; unfold tripleCharges sourceA614 sourceB614 sourceC614 difference raw10321; decide +kernel
    rw [ha]
    exact (canonical10321 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA614 + difference 2 0) (sourceB614 + difference 0 2) sourceC614) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4490) := by
    have ha : (tripleCharges (sourceA614 + difference 2 0) (sourceB614 + difference 0 2) sourceC614) = raw10322 := by
      apply Matrix.ext; unfold tripleCharges sourceA614 sourceB614 sourceC614 difference raw10322; decide +kernel
    rw [ha]
    exact (canonical10322 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA614 + difference 2 1) (sourceB614 + difference 1 2) sourceC614) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5094) := by
    have ha : (tripleCharges (sourceA614 + difference 2 1) (sourceB614 + difference 1 2) sourceC614) = raw10323 := by
      apply Matrix.ext; unfold tripleCharges sourceA614 sourceB614 sourceC614 difference raw10323; decide +kernel
    rw [ha]
    exact (canonical10323 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA614 + difference 2 3) (sourceB614 + difference 3 2) sourceC614) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5094) := by
    have ha : (tripleCharges (sourceA614 + difference 2 3) (sourceB614 + difference 3 2) sourceC614) = raw10324 := by
      apply Matrix.ext; unfold tripleCharges sourceA614 sourceB614 sourceC614 difference raw10324; decide +kernel
    rw [ha]
    exact (canonical10324 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA614 + difference 2 4) (sourceB614 + difference 4 2) sourceC614) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5110) := by
    have ha : (tripleCharges (sourceA614 + difference 2 4) (sourceB614 + difference 4 2) sourceC614) = raw10325 := by
      apply Matrix.ext; unfold tripleCharges sourceA614 sourceB614 sourceC614 difference raw10325; decide +kernel
    rw [ha]
    exact (canonical10325 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA614 + difference 2 5) (sourceB614 + difference 5 2) sourceC614) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA614 + difference 2 5) (sourceB614 + difference 5 2) sourceC614) = raw10326 := by
      apply Matrix.ext; unfold tripleCharges sourceA614 sourceB614 sourceC614 difference raw10326; decide +kernel
    rw [ha]
    exact (canonical10326 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA614 + difference 3 0) (sourceB614 + difference 0 3) sourceC614) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4490) := by
    have ha : (tripleCharges (sourceA614 + difference 3 0) (sourceB614 + difference 0 3) sourceC614) = raw10327 := by
      apply Matrix.ext; unfold tripleCharges sourceA614 sourceB614 sourceC614 difference raw10327; decide +kernel
    rw [ha]
    exact (canonical10327 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA614 + difference 3 1) (sourceB614 + difference 1 3) sourceC614) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5094) := by
    have ha : (tripleCharges (sourceA614 + difference 3 1) (sourceB614 + difference 1 3) sourceC614) = raw10328 := by
      apply Matrix.ext; unfold tripleCharges sourceA614 sourceB614 sourceC614 difference raw10328; decide +kernel
    rw [ha]
    exact (canonical10328 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA614 + difference 3 2) (sourceB614 + difference 2 3) sourceC614) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5094) := by
    have ha : (tripleCharges (sourceA614 + difference 3 2) (sourceB614 + difference 2 3) sourceC614) = raw10329 := by
      apply Matrix.ext; unfold tripleCharges sourceA614 sourceB614 sourceC614 difference raw10329; decide +kernel
    rw [ha]
    exact (canonical10329 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA614 + difference 3 4) (sourceB614 + difference 4 3) sourceC614) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5110) := by
    have ha : (tripleCharges (sourceA614 + difference 3 4) (sourceB614 + difference 4 3) sourceC614) = raw10330 := by
      apply Matrix.ext; unfold tripleCharges sourceA614 sourceB614 sourceC614 difference raw10330; decide +kernel
    rw [ha]
    exact (canonical10330 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA614 + difference 3 5) (sourceB614 + difference 5 3) sourceC614) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA614 + difference 3 5) (sourceB614 + difference 5 3) sourceC614) = raw10331 := by
      apply Matrix.ext; unfold tripleCharges sourceA614 sourceB614 sourceC614 difference raw10331; decide +kernel
    rw [ha]
    exact (canonical10331 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA614 + difference 4 0) (sourceB614 + difference 0 4) sourceC614) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4510) := by
    have ha : (tripleCharges (sourceA614 + difference 4 0) (sourceB614 + difference 0 4) sourceC614) = raw10332 := by
      apply Matrix.ext; unfold tripleCharges sourceA614 sourceB614 sourceC614 difference raw10332; decide +kernel
    rw [ha]
    exact (canonical10332 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA614 + difference 4 1) (sourceB614 + difference 1 4) sourceC614) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5110) := by
    have ha : (tripleCharges (sourceA614 + difference 4 1) (sourceB614 + difference 1 4) sourceC614) = raw10333 := by
      apply Matrix.ext; unfold tripleCharges sourceA614 sourceB614 sourceC614 difference raw10333; decide +kernel
    rw [ha]
    exact (canonical10333 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA614 + difference 4 2) (sourceB614 + difference 2 4) sourceC614) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5110) := by
    have ha : (tripleCharges (sourceA614 + difference 4 2) (sourceB614 + difference 2 4) sourceC614) = raw10334 := by
      apply Matrix.ext; unfold tripleCharges sourceA614 sourceB614 sourceC614 difference raw10334; decide +kernel
    rw [ha]
    exact (canonical10334 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA614 + difference 4 3) (sourceB614 + difference 3 4) sourceC614) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5110) := by
    have ha : (tripleCharges (sourceA614 + difference 4 3) (sourceB614 + difference 3 4) sourceC614) = raw10335 := by
      apply Matrix.ext; unfold tripleCharges sourceA614 sourceB614 sourceC614 difference raw10335; decide +kernel
    rw [ha]
    exact (canonical10335 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA614 + difference 4 5) (sourceB614 + difference 5 4) sourceC614) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5310) := by
    have ha : (tripleCharges (sourceA614 + difference 4 5) (sourceB614 + difference 5 4) sourceC614) = raw10336 := by
      apply Matrix.ext; unfold tripleCharges sourceA614 sourceB614 sourceC614 difference raw10336; decide +kernel
    rw [ha]
    exact (canonical10336 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA614 + difference 5 0) (sourceB614 + difference 0 5) sourceC614) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4493) := by
    have ha : (tripleCharges (sourceA614 + difference 5 0) (sourceB614 + difference 0 5) sourceC614) = raw10337 := by
      apply Matrix.ext; unfold tripleCharges sourceA614 sourceB614 sourceC614 difference raw10337; decide +kernel
    rw [ha]
    exact (canonical10337 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA614 + difference 5 1) (sourceB614 + difference 1 5) sourceC614) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4490) := by
    have ha : (tripleCharges (sourceA614 + difference 5 1) (sourceB614 + difference 1 5) sourceC614) = raw10338 := by
      apply Matrix.ext; unfold tripleCharges sourceA614 sourceB614 sourceC614 difference raw10338; decide +kernel
    rw [ha]
    exact (canonical10338 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA614 + difference 5 2) (sourceB614 + difference 2 5) sourceC614) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4490) := by
    have ha : (tripleCharges (sourceA614 + difference 5 2) (sourceB614 + difference 2 5) sourceC614) = raw10339 := by
      apply Matrix.ext; unfold tripleCharges sourceA614 sourceB614 sourceC614 difference raw10339; decide +kernel
    rw [ha]
    exact (canonical10339 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA614 + difference 5 3) (sourceB614 + difference 3 5) sourceC614) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4490) := by
    have ha : (tripleCharges (sourceA614 + difference 5 3) (sourceB614 + difference 3 5) sourceC614) = raw10340 := by
      apply Matrix.ext; unfold tripleCharges sourceA614 sourceB614 sourceC614 difference raw10340; decide +kernel
    rw [ha]
    exact (canonical10340 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA614 + difference 5 4) (sourceB614 + difference 4 5) sourceC614) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4510) := by
    have ha : (tripleCharges (sourceA614 + difference 5 4) (sourceB614 + difference 4 5) sourceC614) = raw10341 := by
      apply Matrix.ext; unfold tripleCharges sourceA614 sourceB614 sourceC614 difference raw10341; decide +kernel
    rw [ha]
    exact (canonical10341 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA614 sourceB614 sourceC614
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm614, Integer.Sparse.eval]
  linarith only [hs]

def sourceA615 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB615 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceC615 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceForm615 : Integer.Sparse Master := [(Sum.inr 4603, 2), (Sum.inr 4609, 1), (Sum.inr 4612, 1), (Sum.inr 4620, 1), (Sum.inr 5102, 2), (Sum.inr 5109, 1), (Sum.inr 5111, 1), (Sum.inr 5135, 2), (Sum.inr 5139, 2), (Sum.inr 5141, 2), (Sum.inr 5164, 2), (Sum.inr 5266, 2), (Sum.inr 5268, 1), (Sum.inr 5271, 2), (Sum.inr 5274, 1), (Sum.inr 5300, 1), (Sum.inr 5304, 1), (Sum.inr 5413, 1), (Sum.inr 5428, 2), (Sum.inr 5442, 1), (Sum.inr 5443, 1)]

theorem sourceEq615 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm615 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA615 + difference 0 1) (sourceB615 + difference 1 0) sourceC615) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5428) := by
    have ha : (tripleCharges (sourceA615 + difference 0 1) (sourceB615 + difference 1 0) sourceC615) = raw10342 := by
      apply Matrix.ext; unfold tripleCharges sourceA615 sourceB615 sourceC615 difference raw10342; decide +kernel
    rw [ha]
    exact (canonical10342 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA615 + difference 0 2) (sourceB615 + difference 2 0) sourceC615) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5428) := by
    have ha : (tripleCharges (sourceA615 + difference 0 2) (sourceB615 + difference 2 0) sourceC615) = raw10343 := by
      apply Matrix.ext; unfold tripleCharges sourceA615 sourceB615 sourceC615 difference raw10343; decide +kernel
    rw [ha]
    exact (canonical10343 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA615 + difference 0 3) (sourceB615 + difference 3 0) sourceC615) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5413) := by
    have ha : (tripleCharges (sourceA615 + difference 0 3) (sourceB615 + difference 3 0) sourceC615) = raw10344 := by
      apply Matrix.ext; unfold tripleCharges sourceA615 sourceB615 sourceC615 difference raw10344; decide +kernel
    rw [ha]
    exact (canonical10344 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA615 + difference 0 4) (sourceB615 + difference 4 0) sourceC615) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA615 + difference 0 4) (sourceB615 + difference 4 0) sourceC615) = raw10345 := by
      apply Matrix.ext; unfold tripleCharges sourceA615 sourceB615 sourceC615 difference raw10345; decide +kernel
    rw [ha]
    exact (canonical10345 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA615 + difference 0 5) (sourceB615 + difference 5 0) sourceC615) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5442) := by
    have ha : (tripleCharges (sourceA615 + difference 0 5) (sourceB615 + difference 5 0) sourceC615) = raw10346 := by
      apply Matrix.ext; unfold tripleCharges sourceA615 sourceB615 sourceC615 difference raw10346; decide +kernel
    rw [ha]
    exact (canonical10346 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA615 + difference 1 0) (sourceB615 + difference 0 1) sourceC615) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4603) := by
    have ha : (tripleCharges (sourceA615 + difference 1 0) (sourceB615 + difference 0 1) sourceC615) = raw10347 := by
      apply Matrix.ext; unfold tripleCharges sourceA615 sourceB615 sourceC615 difference raw10347; decide +kernel
    rw [ha]
    exact (canonical10347 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA615 + difference 1 2) (sourceB615 + difference 2 1) sourceC615) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5135) := by
    have ha : (tripleCharges (sourceA615 + difference 1 2) (sourceB615 + difference 2 1) sourceC615) = raw10348 := by
      apply Matrix.ext; unfold tripleCharges sourceA615 sourceB615 sourceC615 difference raw10348; decide +kernel
    rw [ha]
    exact (canonical10348 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA615 + difference 1 3) (sourceB615 + difference 3 1) sourceC615) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5102) := by
    have ha : (tripleCharges (sourceA615 + difference 1 3) (sourceB615 + difference 3 1) sourceC615) = raw10349 := by
      apply Matrix.ext; unfold tripleCharges sourceA615 sourceB615 sourceC615 difference raw10349; decide +kernel
    rw [ha]
    exact (canonical10349 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA615 + difference 1 4) (sourceB615 + difference 4 1) sourceC615) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA615 + difference 1 4) (sourceB615 + difference 4 1) sourceC615) = raw10350 := by
      apply Matrix.ext; unfold tripleCharges sourceA615 sourceB615 sourceC615 difference raw10350; decide +kernel
    rw [ha]
    exact (canonical10350 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA615 + difference 1 5) (sourceB615 + difference 5 1) sourceC615) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA615 + difference 1 5) (sourceB615 + difference 5 1) sourceC615) = raw10351 := by
      apply Matrix.ext; unfold tripleCharges sourceA615 sourceB615 sourceC615 difference raw10351; decide +kernel
    rw [ha]
    exact (canonical10351 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA615 + difference 2 0) (sourceB615 + difference 0 2) sourceC615) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4603) := by
    have ha : (tripleCharges (sourceA615 + difference 2 0) (sourceB615 + difference 0 2) sourceC615) = raw10352 := by
      apply Matrix.ext; unfold tripleCharges sourceA615 sourceB615 sourceC615 difference raw10352; decide +kernel
    rw [ha]
    exact (canonical10352 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA615 + difference 2 1) (sourceB615 + difference 1 2) sourceC615) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5135) := by
    have ha : (tripleCharges (sourceA615 + difference 2 1) (sourceB615 + difference 1 2) sourceC615) = raw10353 := by
      apply Matrix.ext; unfold tripleCharges sourceA615 sourceB615 sourceC615 difference raw10353; decide +kernel
    rw [ha]
    exact (canonical10353 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA615 + difference 2 3) (sourceB615 + difference 3 2) sourceC615) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5102) := by
    have ha : (tripleCharges (sourceA615 + difference 2 3) (sourceB615 + difference 3 2) sourceC615) = raw10354 := by
      apply Matrix.ext; unfold tripleCharges sourceA615 sourceB615 sourceC615 difference raw10354; decide +kernel
    rw [ha]
    exact (canonical10354 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA615 + difference 2 4) (sourceB615 + difference 4 2) sourceC615) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA615 + difference 2 4) (sourceB615 + difference 4 2) sourceC615) = raw10355 := by
      apply Matrix.ext; unfold tripleCharges sourceA615 sourceB615 sourceC615 difference raw10355; decide +kernel
    rw [ha]
    exact (canonical10355 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA615 + difference 2 5) (sourceB615 + difference 5 2) sourceC615) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA615 + difference 2 5) (sourceB615 + difference 5 2) sourceC615) = raw10356 := by
      apply Matrix.ext; unfold tripleCharges sourceA615 sourceB615 sourceC615 difference raw10356; decide +kernel
    rw [ha]
    exact (canonical10356 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA615 + difference 3 0) (sourceB615 + difference 0 3) sourceC615) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4620) := by
    have ha : (tripleCharges (sourceA615 + difference 3 0) (sourceB615 + difference 0 3) sourceC615) = raw10357 := by
      apply Matrix.ext; unfold tripleCharges sourceA615 sourceB615 sourceC615 difference raw10357; decide +kernel
    rw [ha]
    exact (canonical10357 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA615 + difference 3 1) (sourceB615 + difference 1 3) sourceC615) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5164) := by
    have ha : (tripleCharges (sourceA615 + difference 3 1) (sourceB615 + difference 1 3) sourceC615) = raw10358 := by
      apply Matrix.ext; unfold tripleCharges sourceA615 sourceB615 sourceC615 difference raw10358; decide +kernel
    rw [ha]
    exact (canonical10358 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA615 + difference 3 2) (sourceB615 + difference 2 3) sourceC615) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5164) := by
    have ha : (tripleCharges (sourceA615 + difference 3 2) (sourceB615 + difference 2 3) sourceC615) = raw10359 := by
      apply Matrix.ext; unfold tripleCharges sourceA615 sourceB615 sourceC615 difference raw10359; decide +kernel
    rw [ha]
    exact (canonical10359 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA615 + difference 3 4) (sourceB615 + difference 4 3) sourceC615) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5300) := by
    have ha : (tripleCharges (sourceA615 + difference 3 4) (sourceB615 + difference 4 3) sourceC615) = raw10360 := by
      apply Matrix.ext; unfold tripleCharges sourceA615 sourceB615 sourceC615 difference raw10360; decide +kernel
    rw [ha]
    exact (canonical10360 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA615 + difference 3 5) (sourceB615 + difference 5 3) sourceC615) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA615 + difference 3 5) (sourceB615 + difference 5 3) sourceC615) = raw10361 := by
      apply Matrix.ext; unfold tripleCharges sourceA615 sourceB615 sourceC615 difference raw10361; decide +kernel
    rw [ha]
    exact (canonical10361 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA615 + difference 4 0) (sourceB615 + difference 0 4) sourceC615) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA615 + difference 4 0) (sourceB615 + difference 0 4) sourceC615) = raw10362 := by
      apply Matrix.ext; unfold tripleCharges sourceA615 sourceB615 sourceC615 difference raw10362; decide +kernel
    rw [ha]
    exact (canonical10362 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA615 + difference 4 1) (sourceB615 + difference 1 4) sourceC615) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA615 + difference 4 1) (sourceB615 + difference 1 4) sourceC615) = raw10363 := by
      apply Matrix.ext; unfold tripleCharges sourceA615 sourceB615 sourceC615 difference raw10363; decide +kernel
    rw [ha]
    exact (canonical10363 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA615 + difference 4 2) (sourceB615 + difference 2 4) sourceC615) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA615 + difference 4 2) (sourceB615 + difference 2 4) sourceC615) = raw10364 := by
      apply Matrix.ext; unfold tripleCharges sourceA615 sourceB615 sourceC615 difference raw10364; decide +kernel
    rw [ha]
    exact (canonical10364 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA615 + difference 4 3) (sourceB615 + difference 3 4) sourceC615) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5111) := by
    have ha : (tripleCharges (sourceA615 + difference 4 3) (sourceB615 + difference 3 4) sourceC615) = raw10365 := by
      apply Matrix.ext; unfold tripleCharges sourceA615 sourceB615 sourceC615 difference raw10365; decide +kernel
    rw [ha]
    exact (canonical10365 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA615 + difference 4 5) (sourceB615 + difference 5 4) sourceC615) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5274) := by
    have ha : (tripleCharges (sourceA615 + difference 4 5) (sourceB615 + difference 5 4) sourceC615) = raw10366 := by
      apply Matrix.ext; unfold tripleCharges sourceA615 sourceB615 sourceC615 difference raw10366; decide +kernel
    rw [ha]
    exact (canonical10366 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA615 + difference 5 0) (sourceB615 + difference 0 5) sourceC615) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4609) := by
    have ha : (tripleCharges (sourceA615 + difference 5 0) (sourceB615 + difference 0 5) sourceC615) = raw10367 := by
      apply Matrix.ext; unfold tripleCharges sourceA615 sourceB615 sourceC615 difference raw10367; decide +kernel
    rw [ha]
    exact (canonical10367 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA615 + difference 5 1) (sourceB615 + difference 1 5) sourceC615) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5139) := by
    have ha : (tripleCharges (sourceA615 + difference 5 1) (sourceB615 + difference 1 5) sourceC615) = raw10368 := by
      apply Matrix.ext; unfold tripleCharges sourceA615 sourceB615 sourceC615 difference raw10368; decide +kernel
    rw [ha]
    exact (canonical10368 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA615 + difference 5 2) (sourceB615 + difference 2 5) sourceC615) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5139) := by
    have ha : (tripleCharges (sourceA615 + difference 5 2) (sourceB615 + difference 2 5) sourceC615) = raw10369 := by
      apply Matrix.ext; unfold tripleCharges sourceA615 sourceB615 sourceC615 difference raw10369; decide +kernel
    rw [ha]
    exact (canonical10369 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA615 + difference 5 3) (sourceB615 + difference 3 5) sourceC615) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5109) := by
    have ha : (tripleCharges (sourceA615 + difference 5 3) (sourceB615 + difference 3 5) sourceC615) = raw10370 := by
      apply Matrix.ext; unfold tripleCharges sourceA615 sourceB615 sourceC615 difference raw10370; decide +kernel
    rw [ha]
    exact (canonical10370 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA615 + difference 5 4) (sourceB615 + difference 4 5) sourceC615) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5268) := by
    have ha : (tripleCharges (sourceA615 + difference 5 4) (sourceB615 + difference 4 5) sourceC615) = raw10371 := by
      apply Matrix.ext; unfold tripleCharges sourceA615 sourceB615 sourceC615 difference raw10371; decide +kernel
    rw [ha]
    exact (canonical10371 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA615 sourceB615 sourceC615
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm615, Integer.Sparse.eval]
  linarith only [hs]

def sourceA616 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB616 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceC616 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceForm616 : Integer.Sparse Master := [(Sum.inr 1262, 2), (Sum.inr 1264, 1), (Sum.inr 1274, 1), (Sum.inr 1295, 1), (Sum.inr 2618, 2), (Sum.inr 2640, 1), (Sum.inr 2734, 1), (Sum.inr 2934, 2), (Sum.inr 2943, 2), (Sum.inr 2955, 2), (Sum.inr 2998, 2), (Sum.inr 3006, 1), (Sum.inr 3039, 2), (Sum.inr 3055, 1), (Sum.inr 3109, 2), (Sum.inr 3112, 1), (Sum.inr 3119, 1), (Sum.inr 3889, 1), (Sum.inr 4001, 1), (Sum.inr 4003, 2), (Sum.inr 4006, 1)]

theorem sourceEq616 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm616 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA616 + difference 0 1) (sourceB616 + difference 1 0) sourceC616) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4003) := by
    have ha : (tripleCharges (sourceA616 + difference 0 1) (sourceB616 + difference 1 0) sourceC616) = raw10372 := by
      apply Matrix.ext; unfold tripleCharges sourceA616 sourceB616 sourceC616 difference raw10372; decide +kernel
    rw [ha]
    exact (canonical10372 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA616 + difference 0 2) (sourceB616 + difference 2 0) sourceC616) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4003) := by
    have ha : (tripleCharges (sourceA616 + difference 0 2) (sourceB616 + difference 2 0) sourceC616) = raw10373 := by
      apply Matrix.ext; unfold tripleCharges sourceA616 sourceB616 sourceC616 difference raw10373; decide +kernel
    rw [ha]
    exact (canonical10373 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA616 + difference 0 3) (sourceB616 + difference 3 0) sourceC616) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4006) := by
    have ha : (tripleCharges (sourceA616 + difference 0 3) (sourceB616 + difference 3 0) sourceC616) = raw10374 := by
      apply Matrix.ext; unfold tripleCharges sourceA616 sourceB616 sourceC616 difference raw10374; decide +kernel
    rw [ha]
    exact (canonical10374 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA616 + difference 0 4) (sourceB616 + difference 4 0) sourceC616) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3889) := by
    have ha : (tripleCharges (sourceA616 + difference 0 4) (sourceB616 + difference 4 0) sourceC616) = raw10375 := by
      apply Matrix.ext; unfold tripleCharges sourceA616 sourceB616 sourceC616 difference raw10375; decide +kernel
    rw [ha]
    exact (canonical10375 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA616 + difference 0 5) (sourceB616 + difference 5 0) sourceC616) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4001) := by
    have ha : (tripleCharges (sourceA616 + difference 0 5) (sourceB616 + difference 5 0) sourceC616) = raw10376 := by
      apply Matrix.ext; unfold tripleCharges sourceA616 sourceB616 sourceC616 difference raw10376; decide +kernel
    rw [ha]
    exact (canonical10376 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA616 + difference 1 0) (sourceB616 + difference 0 1) sourceC616) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1262) := by
    have ha : (tripleCharges (sourceA616 + difference 1 0) (sourceB616 + difference 0 1) sourceC616) = raw10377 := by
      apply Matrix.ext; unfold tripleCharges sourceA616 sourceB616 sourceC616 difference raw10377; decide +kernel
    rw [ha]
    exact (canonical10377 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA616 + difference 1 2) (sourceB616 + difference 2 1) sourceC616) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2934) := by
    have ha : (tripleCharges (sourceA616 + difference 1 2) (sourceB616 + difference 2 1) sourceC616) = raw10378 := by
      apply Matrix.ext; unfold tripleCharges sourceA616 sourceB616 sourceC616 difference raw10378; decide +kernel
    rw [ha]
    exact (canonical10378 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA616 + difference 1 3) (sourceB616 + difference 3 1) sourceC616) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2998) := by
    have ha : (tripleCharges (sourceA616 + difference 1 3) (sourceB616 + difference 3 1) sourceC616) = raw10379 := by
      apply Matrix.ext; unfold tripleCharges sourceA616 sourceB616 sourceC616 difference raw10379; decide +kernel
    rw [ha]
    exact (canonical10379 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA616 + difference 1 4) (sourceB616 + difference 4 1) sourceC616) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3039) := by
    have ha : (tripleCharges (sourceA616 + difference 1 4) (sourceB616 + difference 4 1) sourceC616) = raw10380 := by
      apply Matrix.ext; unfold tripleCharges sourceA616 sourceB616 sourceC616 difference raw10380; decide +kernel
    rw [ha]
    exact (canonical10380 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA616 + difference 1 5) (sourceB616 + difference 5 1) sourceC616) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3109) := by
    have ha : (tripleCharges (sourceA616 + difference 1 5) (sourceB616 + difference 5 1) sourceC616) = raw10381 := by
      apply Matrix.ext; unfold tripleCharges sourceA616 sourceB616 sourceC616 difference raw10381; decide +kernel
    rw [ha]
    exact (canonical10381 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA616 + difference 2 0) (sourceB616 + difference 0 2) sourceC616) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1262) := by
    have ha : (tripleCharges (sourceA616 + difference 2 0) (sourceB616 + difference 0 2) sourceC616) = raw10382 := by
      apply Matrix.ext; unfold tripleCharges sourceA616 sourceB616 sourceC616 difference raw10382; decide +kernel
    rw [ha]
    exact (canonical10382 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA616 + difference 2 1) (sourceB616 + difference 1 2) sourceC616) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2934) := by
    have ha : (tripleCharges (sourceA616 + difference 2 1) (sourceB616 + difference 1 2) sourceC616) = raw10383 := by
      apply Matrix.ext; unfold tripleCharges sourceA616 sourceB616 sourceC616 difference raw10383; decide +kernel
    rw [ha]
    exact (canonical10383 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA616 + difference 2 3) (sourceB616 + difference 3 2) sourceC616) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2998) := by
    have ha : (tripleCharges (sourceA616 + difference 2 3) (sourceB616 + difference 3 2) sourceC616) = raw10384 := by
      apply Matrix.ext; unfold tripleCharges sourceA616 sourceB616 sourceC616 difference raw10384; decide +kernel
    rw [ha]
    exact (canonical10384 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA616 + difference 2 4) (sourceB616 + difference 4 2) sourceC616) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3039) := by
    have ha : (tripleCharges (sourceA616 + difference 2 4) (sourceB616 + difference 4 2) sourceC616) = raw10385 := by
      apply Matrix.ext; unfold tripleCharges sourceA616 sourceB616 sourceC616 difference raw10385; decide +kernel
    rw [ha]
    exact (canonical10385 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA616 + difference 2 5) (sourceB616 + difference 5 2) sourceC616) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3109) := by
    have ha : (tripleCharges (sourceA616 + difference 2 5) (sourceB616 + difference 5 2) sourceC616) = raw10386 := by
      apply Matrix.ext; unfold tripleCharges sourceA616 sourceB616 sourceC616 difference raw10386; decide +kernel
    rw [ha]
    exact (canonical10386 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA616 + difference 3 0) (sourceB616 + difference 0 3) sourceC616) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1295) := by
    have ha : (tripleCharges (sourceA616 + difference 3 0) (sourceB616 + difference 0 3) sourceC616) = raw10387 := by
      apply Matrix.ext; unfold tripleCharges sourceA616 sourceB616 sourceC616 difference raw10387; decide +kernel
    rw [ha]
    exact (canonical10387 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA616 + difference 3 1) (sourceB616 + difference 1 3) sourceC616) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2955) := by
    have ha : (tripleCharges (sourceA616 + difference 3 1) (sourceB616 + difference 1 3) sourceC616) = raw10388 := by
      apply Matrix.ext; unfold tripleCharges sourceA616 sourceB616 sourceC616 difference raw10388; decide +kernel
    rw [ha]
    exact (canonical10388 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA616 + difference 3 2) (sourceB616 + difference 2 3) sourceC616) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2955) := by
    have ha : (tripleCharges (sourceA616 + difference 3 2) (sourceB616 + difference 2 3) sourceC616) = raw10389 := by
      apply Matrix.ext; unfold tripleCharges sourceA616 sourceB616 sourceC616 difference raw10389; decide +kernel
    rw [ha]
    exact (canonical10389 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA616 + difference 3 4) (sourceB616 + difference 4 3) sourceC616) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3055) := by
    have ha : (tripleCharges (sourceA616 + difference 3 4) (sourceB616 + difference 4 3) sourceC616) = raw10390 := by
      apply Matrix.ext; unfold tripleCharges sourceA616 sourceB616 sourceC616 difference raw10390; decide +kernel
    rw [ha]
    exact (canonical10390 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA616 + difference 3 5) (sourceB616 + difference 5 3) sourceC616) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3119) := by
    have ha : (tripleCharges (sourceA616 + difference 3 5) (sourceB616 + difference 5 3) sourceC616) = raw10391 := by
      apply Matrix.ext; unfold tripleCharges sourceA616 sourceB616 sourceC616 difference raw10391; decide +kernel
    rw [ha]
    exact (canonical10391 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA616 + difference 4 0) (sourceB616 + difference 0 4) sourceC616) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1274) := by
    have ha : (tripleCharges (sourceA616 + difference 4 0) (sourceB616 + difference 0 4) sourceC616) = raw10392 := by
      apply Matrix.ext; unfold tripleCharges sourceA616 sourceB616 sourceC616 difference raw10392; decide +kernel
    rw [ha]
    exact (canonical10392 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA616 + difference 4 1) (sourceB616 + difference 1 4) sourceC616) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2943) := by
    have ha : (tripleCharges (sourceA616 + difference 4 1) (sourceB616 + difference 1 4) sourceC616) = raw10393 := by
      apply Matrix.ext; unfold tripleCharges sourceA616 sourceB616 sourceC616 difference raw10393; decide +kernel
    rw [ha]
    exact (canonical10393 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA616 + difference 4 2) (sourceB616 + difference 2 4) sourceC616) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2943) := by
    have ha : (tripleCharges (sourceA616 + difference 4 2) (sourceB616 + difference 2 4) sourceC616) = raw10394 := by
      apply Matrix.ext; unfold tripleCharges sourceA616 sourceB616 sourceC616 difference raw10394; decide +kernel
    rw [ha]
    exact (canonical10394 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA616 + difference 4 3) (sourceB616 + difference 3 4) sourceC616) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3006) := by
    have ha : (tripleCharges (sourceA616 + difference 4 3) (sourceB616 + difference 3 4) sourceC616) = raw10395 := by
      apply Matrix.ext; unfold tripleCharges sourceA616 sourceB616 sourceC616 difference raw10395; decide +kernel
    rw [ha]
    exact (canonical10395 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA616 + difference 4 5) (sourceB616 + difference 5 4) sourceC616) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3112) := by
    have ha : (tripleCharges (sourceA616 + difference 4 5) (sourceB616 + difference 5 4) sourceC616) = raw10396 := by
      apply Matrix.ext; unfold tripleCharges sourceA616 sourceB616 sourceC616 difference raw10396; decide +kernel
    rw [ha]
    exact (canonical10396 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA616 + difference 5 0) (sourceB616 + difference 0 5) sourceC616) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1264) := by
    have ha : (tripleCharges (sourceA616 + difference 5 0) (sourceB616 + difference 0 5) sourceC616) = raw10397 := by
      apply Matrix.ext; unfold tripleCharges sourceA616 sourceB616 sourceC616 difference raw10397; decide +kernel
    rw [ha]
    exact (canonical10397 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA616 + difference 5 1) (sourceB616 + difference 1 5) sourceC616) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2618) := by
    have ha : (tripleCharges (sourceA616 + difference 5 1) (sourceB616 + difference 1 5) sourceC616) = raw10398 := by
      apply Matrix.ext; unfold tripleCharges sourceA616 sourceB616 sourceC616 difference raw10398; decide +kernel
    rw [ha]
    exact (canonical10398 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA616 + difference 5 2) (sourceB616 + difference 2 5) sourceC616) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2618) := by
    have ha : (tripleCharges (sourceA616 + difference 5 2) (sourceB616 + difference 2 5) sourceC616) = raw10399 := by
      apply Matrix.ext; unfold tripleCharges sourceA616 sourceB616 sourceC616 difference raw10399; decide +kernel
    rw [ha]
    exact (canonical10399 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA616 + difference 5 3) (sourceB616 + difference 3 5) sourceC616) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2640) := by
    have ha : (tripleCharges (sourceA616 + difference 5 3) (sourceB616 + difference 3 5) sourceC616) = raw10400 := by
      apply Matrix.ext; unfold tripleCharges sourceA616 sourceB616 sourceC616 difference raw10400; decide +kernel
    rw [ha]
    exact (canonical10400 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA616 + difference 5 4) (sourceB616 + difference 4 5) sourceC616) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2734) := by
    have ha : (tripleCharges (sourceA616 + difference 5 4) (sourceB616 + difference 4 5) sourceC616) = raw10401 := by
      apply Matrix.ext; unfold tripleCharges sourceA616 sourceB616 sourceC616 difference raw10401; decide +kernel
    rw [ha]
    exact (canonical10401 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA616 sourceB616 sourceC616
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm616, Integer.Sparse.eval]
  linarith only [hs]

def sourceA617 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB617 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceC617 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceForm617 : Integer.Sparse Master := [(Sum.inr 3294, 2), (Sum.inr 3301, 1), (Sum.inr 3302, 1), (Sum.inr 3306, 1), (Sum.inr 3471, 2), (Sum.inr 3485, 1), (Sum.inr 3486, 1), (Sum.inr 3515, 2), (Sum.inr 3522, 2), (Sum.inr 3523, 2), (Sum.inr 3534, 2), (Sum.inr 3535, 2), (Sum.inr 3547, 1), (Sum.inr 3549, 1), (Sum.inr 3565, 2), (Sum.inr 3583, 1), (Sum.inr 3584, 1), (Sum.inr 3817, 1), (Sum.inr 3845, 2), (Sum.inr 3861, 1), (Sum.inr 3862, 1)]

theorem sourceEq617 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm617 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA617 + difference 0 1) (sourceB617 + difference 1 0) sourceC617) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3845) := by
    have ha : (tripleCharges (sourceA617 + difference 0 1) (sourceB617 + difference 1 0) sourceC617) = raw10402 := by
      apply Matrix.ext; unfold tripleCharges sourceA617 sourceB617 sourceC617 difference raw10402; decide +kernel
    rw [ha]
    exact (canonical10402 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA617 + difference 0 2) (sourceB617 + difference 2 0) sourceC617) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3845) := by
    have ha : (tripleCharges (sourceA617 + difference 0 2) (sourceB617 + difference 2 0) sourceC617) = raw10403 := by
      apply Matrix.ext; unfold tripleCharges sourceA617 sourceB617 sourceC617 difference raw10403; decide +kernel
    rw [ha]
    exact (canonical10403 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA617 + difference 0 3) (sourceB617 + difference 3 0) sourceC617) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3817) := by
    have ha : (tripleCharges (sourceA617 + difference 0 3) (sourceB617 + difference 3 0) sourceC617) = raw10404 := by
      apply Matrix.ext; unfold tripleCharges sourceA617 sourceB617 sourceC617 difference raw10404; decide +kernel
    rw [ha]
    exact (canonical10404 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA617 + difference 0 4) (sourceB617 + difference 4 0) sourceC617) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3862) := by
    have ha : (tripleCharges (sourceA617 + difference 0 4) (sourceB617 + difference 4 0) sourceC617) = raw10405 := by
      apply Matrix.ext; unfold tripleCharges sourceA617 sourceB617 sourceC617 difference raw10405; decide +kernel
    rw [ha]
    exact (canonical10405 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA617 + difference 0 5) (sourceB617 + difference 5 0) sourceC617) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3861) := by
    have ha : (tripleCharges (sourceA617 + difference 0 5) (sourceB617 + difference 5 0) sourceC617) = raw10406 := by
      apply Matrix.ext; unfold tripleCharges sourceA617 sourceB617 sourceC617 difference raw10406; decide +kernel
    rw [ha]
    exact (canonical10406 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA617 + difference 1 0) (sourceB617 + difference 0 1) sourceC617) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3294) := by
    have ha : (tripleCharges (sourceA617 + difference 1 0) (sourceB617 + difference 0 1) sourceC617) = raw10407 := by
      apply Matrix.ext; unfold tripleCharges sourceA617 sourceB617 sourceC617 difference raw10407; decide +kernel
    rw [ha]
    exact (canonical10407 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA617 + difference 1 2) (sourceB617 + difference 2 1) sourceC617) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3515) := by
    have ha : (tripleCharges (sourceA617 + difference 1 2) (sourceB617 + difference 2 1) sourceC617) = raw10408 := by
      apply Matrix.ext; unfold tripleCharges sourceA617 sourceB617 sourceC617 difference raw10408; decide +kernel
    rw [ha]
    exact (canonical10408 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA617 + difference 1 3) (sourceB617 + difference 3 1) sourceC617) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3471) := by
    have ha : (tripleCharges (sourceA617 + difference 1 3) (sourceB617 + difference 3 1) sourceC617) = raw10409 := by
      apply Matrix.ext; unfold tripleCharges sourceA617 sourceB617 sourceC617 difference raw10409; decide +kernel
    rw [ha]
    exact (canonical10409 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA617 + difference 1 4) (sourceB617 + difference 4 1) sourceC617) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3535) := by
    have ha : (tripleCharges (sourceA617 + difference 1 4) (sourceB617 + difference 4 1) sourceC617) = raw10410 := by
      apply Matrix.ext; unfold tripleCharges sourceA617 sourceB617 sourceC617 difference raw10410; decide +kernel
    rw [ha]
    exact (canonical10410 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA617 + difference 1 5) (sourceB617 + difference 5 1) sourceC617) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3534) := by
    have ha : (tripleCharges (sourceA617 + difference 1 5) (sourceB617 + difference 5 1) sourceC617) = raw10411 := by
      apply Matrix.ext; unfold tripleCharges sourceA617 sourceB617 sourceC617 difference raw10411; decide +kernel
    rw [ha]
    exact (canonical10411 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA617 + difference 2 0) (sourceB617 + difference 0 2) sourceC617) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3294) := by
    have ha : (tripleCharges (sourceA617 + difference 2 0) (sourceB617 + difference 0 2) sourceC617) = raw10412 := by
      apply Matrix.ext; unfold tripleCharges sourceA617 sourceB617 sourceC617 difference raw10412; decide +kernel
    rw [ha]
    exact (canonical10412 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA617 + difference 2 1) (sourceB617 + difference 1 2) sourceC617) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3515) := by
    have ha : (tripleCharges (sourceA617 + difference 2 1) (sourceB617 + difference 1 2) sourceC617) = raw10413 := by
      apply Matrix.ext; unfold tripleCharges sourceA617 sourceB617 sourceC617 difference raw10413; decide +kernel
    rw [ha]
    exact (canonical10413 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA617 + difference 2 3) (sourceB617 + difference 3 2) sourceC617) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3471) := by
    have ha : (tripleCharges (sourceA617 + difference 2 3) (sourceB617 + difference 3 2) sourceC617) = raw10414 := by
      apply Matrix.ext; unfold tripleCharges sourceA617 sourceB617 sourceC617 difference raw10414; decide +kernel
    rw [ha]
    exact (canonical10414 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA617 + difference 2 4) (sourceB617 + difference 4 2) sourceC617) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3535) := by
    have ha : (tripleCharges (sourceA617 + difference 2 4) (sourceB617 + difference 4 2) sourceC617) = raw10415 := by
      apply Matrix.ext; unfold tripleCharges sourceA617 sourceB617 sourceC617 difference raw10415; decide +kernel
    rw [ha]
    exact (canonical10415 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA617 + difference 2 5) (sourceB617 + difference 5 2) sourceC617) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3534) := by
    have ha : (tripleCharges (sourceA617 + difference 2 5) (sourceB617 + difference 5 2) sourceC617) = raw10416 := by
      apply Matrix.ext; unfold tripleCharges sourceA617 sourceB617 sourceC617 difference raw10416; decide +kernel
    rw [ha]
    exact (canonical10416 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA617 + difference 3 0) (sourceB617 + difference 0 3) sourceC617) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3306) := by
    have ha : (tripleCharges (sourceA617 + difference 3 0) (sourceB617 + difference 0 3) sourceC617) = raw10417 := by
      apply Matrix.ext; unfold tripleCharges sourceA617 sourceB617 sourceC617 difference raw10417; decide +kernel
    rw [ha]
    exact (canonical10417 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA617 + difference 3 1) (sourceB617 + difference 1 3) sourceC617) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3565) := by
    have ha : (tripleCharges (sourceA617 + difference 3 1) (sourceB617 + difference 1 3) sourceC617) = raw10418 := by
      apply Matrix.ext; unfold tripleCharges sourceA617 sourceB617 sourceC617 difference raw10418; decide +kernel
    rw [ha]
    exact (canonical10418 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA617 + difference 3 2) (sourceB617 + difference 2 3) sourceC617) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3565) := by
    have ha : (tripleCharges (sourceA617 + difference 3 2) (sourceB617 + difference 2 3) sourceC617) = raw10419 := by
      apply Matrix.ext; unfold tripleCharges sourceA617 sourceB617 sourceC617 difference raw10419; decide +kernel
    rw [ha]
    exact (canonical10419 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA617 + difference 3 4) (sourceB617 + difference 4 3) sourceC617) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3584) := by
    have ha : (tripleCharges (sourceA617 + difference 3 4) (sourceB617 + difference 4 3) sourceC617) = raw10420 := by
      apply Matrix.ext; unfold tripleCharges sourceA617 sourceB617 sourceC617 difference raw10420; decide +kernel
    rw [ha]
    exact (canonical10420 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA617 + difference 3 5) (sourceB617 + difference 5 3) sourceC617) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3583) := by
    have ha : (tripleCharges (sourceA617 + difference 3 5) (sourceB617 + difference 5 3) sourceC617) = raw10421 := by
      apply Matrix.ext; unfold tripleCharges sourceA617 sourceB617 sourceC617 difference raw10421; decide +kernel
    rw [ha]
    exact (canonical10421 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA617 + difference 4 0) (sourceB617 + difference 0 4) sourceC617) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3301) := by
    have ha : (tripleCharges (sourceA617 + difference 4 0) (sourceB617 + difference 0 4) sourceC617) = raw10422 := by
      apply Matrix.ext; unfold tripleCharges sourceA617 sourceB617 sourceC617 difference raw10422; decide +kernel
    rw [ha]
    exact (canonical10422 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA617 + difference 4 1) (sourceB617 + difference 1 4) sourceC617) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3522) := by
    have ha : (tripleCharges (sourceA617 + difference 4 1) (sourceB617 + difference 1 4) sourceC617) = raw10423 := by
      apply Matrix.ext; unfold tripleCharges sourceA617 sourceB617 sourceC617 difference raw10423; decide +kernel
    rw [ha]
    exact (canonical10423 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA617 + difference 4 2) (sourceB617 + difference 2 4) sourceC617) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3522) := by
    have ha : (tripleCharges (sourceA617 + difference 4 2) (sourceB617 + difference 2 4) sourceC617) = raw10424 := by
      apply Matrix.ext; unfold tripleCharges sourceA617 sourceB617 sourceC617 difference raw10424; decide +kernel
    rw [ha]
    exact (canonical10424 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA617 + difference 4 3) (sourceB617 + difference 3 4) sourceC617) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3485) := by
    have ha : (tripleCharges (sourceA617 + difference 4 3) (sourceB617 + difference 3 4) sourceC617) = raw10425 := by
      apply Matrix.ext; unfold tripleCharges sourceA617 sourceB617 sourceC617 difference raw10425; decide +kernel
    rw [ha]
    exact (canonical10425 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA617 + difference 4 5) (sourceB617 + difference 5 4) sourceC617) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3547) := by
    have ha : (tripleCharges (sourceA617 + difference 4 5) (sourceB617 + difference 5 4) sourceC617) = raw10426 := by
      apply Matrix.ext; unfold tripleCharges sourceA617 sourceB617 sourceC617 difference raw10426; decide +kernel
    rw [ha]
    exact (canonical10426 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA617 + difference 5 0) (sourceB617 + difference 0 5) sourceC617) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3302) := by
    have ha : (tripleCharges (sourceA617 + difference 5 0) (sourceB617 + difference 0 5) sourceC617) = raw10427 := by
      apply Matrix.ext; unfold tripleCharges sourceA617 sourceB617 sourceC617 difference raw10427; decide +kernel
    rw [ha]
    exact (canonical10427 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA617 + difference 5 1) (sourceB617 + difference 1 5) sourceC617) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3523) := by
    have ha : (tripleCharges (sourceA617 + difference 5 1) (sourceB617 + difference 1 5) sourceC617) = raw10428 := by
      apply Matrix.ext; unfold tripleCharges sourceA617 sourceB617 sourceC617 difference raw10428; decide +kernel
    rw [ha]
    exact (canonical10428 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA617 + difference 5 2) (sourceB617 + difference 2 5) sourceC617) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3523) := by
    have ha : (tripleCharges (sourceA617 + difference 5 2) (sourceB617 + difference 2 5) sourceC617) = raw10429 := by
      apply Matrix.ext; unfold tripleCharges sourceA617 sourceB617 sourceC617 difference raw10429; decide +kernel
    rw [ha]
    exact (canonical10429 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA617 + difference 5 3) (sourceB617 + difference 3 5) sourceC617) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3486) := by
    have ha : (tripleCharges (sourceA617 + difference 5 3) (sourceB617 + difference 3 5) sourceC617) = raw10430 := by
      apply Matrix.ext; unfold tripleCharges sourceA617 sourceB617 sourceC617 difference raw10430; decide +kernel
    rw [ha]
    exact (canonical10430 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA617 + difference 5 4) (sourceB617 + difference 4 5) sourceC617) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3549) := by
    have ha : (tripleCharges (sourceA617 + difference 5 4) (sourceB617 + difference 4 5) sourceC617) = raw10431 := by
      apply Matrix.ext; unfold tripleCharges sourceA617 sourceB617 sourceC617 difference raw10431; decide +kernel
    rw [ha]
    exact (canonical10431 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA617 sourceB617 sourceC617
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm617, Integer.Sparse.eval]
  linarith only [hs]

def sourceA618 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB618 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceC618 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceForm618 : Integer.Sparse Master := [(Sum.inr 2743, 1), (Sum.inr 3817, 1), (Sum.inr 3845, 2), (Sum.inr 3907, 1), (Sum.inr 3908, 1), (Sum.inr 4092, -1)]

theorem sourceEq618 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm618 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA618 + difference 0 0) (sourceB618 + difference 0 0) sourceC618) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2743) := by
    have ha : (tripleCharges (sourceA618 + difference 0 0) (sourceB618 + difference 0 0) sourceC618) = raw10432 := by
      apply Matrix.ext; unfold tripleCharges sourceA618 sourceB618 sourceC618 difference raw10432; decide +kernel
    rw [ha]
    exact (canonical10432 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA618 + difference 0 1) (sourceB618 + difference 1 0) sourceC618) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3845) := by
    have ha : (tripleCharges (sourceA618 + difference 0 1) (sourceB618 + difference 1 0) sourceC618) = raw10433 := by
      apply Matrix.ext; unfold tripleCharges sourceA618 sourceB618 sourceC618 difference raw10433; decide +kernel
    rw [ha]
    exact (canonical10433 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA618 + difference 0 2) (sourceB618 + difference 2 0) sourceC618) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3845) := by
    have ha : (tripleCharges (sourceA618 + difference 0 2) (sourceB618 + difference 2 0) sourceC618) = raw10434 := by
      apply Matrix.ext; unfold tripleCharges sourceA618 sourceB618 sourceC618 difference raw10434; decide +kernel
    rw [ha]
    exact (canonical10434 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA618 + difference 0 3) (sourceB618 + difference 3 0) sourceC618) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3817) := by
    have ha : (tripleCharges (sourceA618 + difference 0 3) (sourceB618 + difference 3 0) sourceC618) = raw10435 := by
      apply Matrix.ext; unfold tripleCharges sourceA618 sourceB618 sourceC618 difference raw10435; decide +kernel
    rw [ha]
    exact (canonical10435 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA618 + difference 0 4) (sourceB618 + difference 4 0) sourceC618) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3907) := by
    have ha : (tripleCharges (sourceA618 + difference 0 4) (sourceB618 + difference 4 0) sourceC618) = raw10436 := by
      apply Matrix.ext; unfold tripleCharges sourceA618 sourceB618 sourceC618 difference raw10436; decide +kernel
    rw [ha]
    exact (canonical10436 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA618 + difference 0 5) (sourceB618 + difference 5 0) sourceC618) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3908) := by
    have ha : (tripleCharges (sourceA618 + difference 0 5) (sourceB618 + difference 5 0) sourceC618) = raw10437 := by
      apply Matrix.ext; unfold tripleCharges sourceA618 sourceB618 sourceC618 difference raw10437; decide +kernel
    rw [ha]
    exact (canonical10437 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA618 + sourceB618) sourceC618) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA618 + sourceB618) sourceC618) = raw10438 := by
      apply Matrix.ext; unfold doubleCharges sourceA618 sourceB618 sourceC618 raw10438; decide +kernel
    rw [ha]
    exact (canonical10438 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA618 sourceB618 sourceC618
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm618, Integer.Sparse.eval]
  linarith only [hs]

def sourceA619 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB619 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceC619 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceForm619 : Integer.Sparse Master := [(Sum.inr 2554, 1), (Sum.inr 2558, 1), (Sum.inr 2561, 1), (Sum.inr 2591, 1), (Sum.inr 2743, 1), (Sum.inr 3845, 1), (Sum.inr 4092, -1)]

theorem sourceEq619 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm619 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA619 + difference 0 1) (sourceB619 + difference 1 0) sourceC619) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3845) := by
    have ha : (tripleCharges (sourceA619 + difference 0 1) (sourceB619 + difference 1 0) sourceC619) = raw10433 := by
      apply Matrix.ext; unfold tripleCharges sourceA619 sourceB619 sourceC619 difference raw10433; decide +kernel
    rw [ha]
    exact (canonical10433 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA619 + difference 1 1) (sourceB619 + difference 1 1) sourceC619) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2743) := by
    have ha : (tripleCharges (sourceA619 + difference 1 1) (sourceB619 + difference 1 1) sourceC619) = raw10432 := by
      apply Matrix.ext; unfold tripleCharges sourceA619 sourceB619 sourceC619 difference raw10432; decide +kernel
    rw [ha]
    exact (canonical10432 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA619 + difference 2 1) (sourceB619 + difference 1 2) sourceC619) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2554) := by
    have ha : (tripleCharges (sourceA619 + difference 2 1) (sourceB619 + difference 1 2) sourceC619) = raw10439 := by
      apply Matrix.ext; unfold tripleCharges sourceA619 sourceB619 sourceC619 difference raw10439; decide +kernel
    rw [ha]
    exact (canonical10439 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA619 + difference 3 1) (sourceB619 + difference 1 3) sourceC619) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2591) := by
    have ha : (tripleCharges (sourceA619 + difference 3 1) (sourceB619 + difference 1 3) sourceC619) = raw10440 := by
      apply Matrix.ext; unfold tripleCharges sourceA619 sourceB619 sourceC619 difference raw10440; decide +kernel
    rw [ha]
    exact (canonical10440 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA619 + difference 4 1) (sourceB619 + difference 1 4) sourceC619) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2561) := by
    have ha : (tripleCharges (sourceA619 + difference 4 1) (sourceB619 + difference 1 4) sourceC619) = raw10441 := by
      apply Matrix.ext; unfold tripleCharges sourceA619 sourceB619 sourceC619 difference raw10441; decide +kernel
    rw [ha]
    exact (canonical10441 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA619 + difference 5 1) (sourceB619 + difference 1 5) sourceC619) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2558) := by
    have ha : (tripleCharges (sourceA619 + difference 5 1) (sourceB619 + difference 1 5) sourceC619) = raw10442 := by
      apply Matrix.ext; unfold tripleCharges sourceA619 sourceB619 sourceC619 difference raw10442; decide +kernel
    rw [ha]
    exact (canonical10442 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA619 + sourceB619) sourceC619) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA619 + sourceB619) sourceC619) = raw10438 := by
      apply Matrix.ext; unfold doubleCharges sourceA619 sourceB619 sourceC619 raw10438; decide +kernel
    rw [ha]
    exact (canonical10438 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA619 sourceB619 sourceC619
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm619, Integer.Sparse.eval]
  linarith only [hs]

def sourceA620 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB620 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceC620 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceForm620 : Integer.Sparse Master := [(Sum.inr 2512, 2), (Sum.inr 2519, 1), (Sum.inr 2523, 1), (Sum.inr 2743, 1), (Sum.inr 3817, 1), (Sum.inr 4092, -1)]

theorem sourceEq620 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm620 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA620 + difference 0 3) (sourceB620 + difference 3 0) sourceC620) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3817) := by
    have ha : (tripleCharges (sourceA620 + difference 0 3) (sourceB620 + difference 3 0) sourceC620) = raw10435 := by
      apply Matrix.ext; unfold tripleCharges sourceA620 sourceB620 sourceC620 difference raw10435; decide +kernel
    rw [ha]
    exact (canonical10435 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA620 + difference 1 3) (sourceB620 + difference 3 1) sourceC620) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2512) := by
    have ha : (tripleCharges (sourceA620 + difference 1 3) (sourceB620 + difference 3 1) sourceC620) = raw10443 := by
      apply Matrix.ext; unfold tripleCharges sourceA620 sourceB620 sourceC620 difference raw10443; decide +kernel
    rw [ha]
    exact (canonical10443 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA620 + difference 2 3) (sourceB620 + difference 3 2) sourceC620) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2512) := by
    have ha : (tripleCharges (sourceA620 + difference 2 3) (sourceB620 + difference 3 2) sourceC620) = raw10444 := by
      apply Matrix.ext; unfold tripleCharges sourceA620 sourceB620 sourceC620 difference raw10444; decide +kernel
    rw [ha]
    exact (canonical10444 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA620 + difference 3 3) (sourceB620 + difference 3 3) sourceC620) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2743) := by
    have ha : (tripleCharges (sourceA620 + difference 3 3) (sourceB620 + difference 3 3) sourceC620) = raw10432 := by
      apply Matrix.ext; unfold tripleCharges sourceA620 sourceB620 sourceC620 difference raw10432; decide +kernel
    rw [ha]
    exact (canonical10432 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA620 + difference 4 3) (sourceB620 + difference 3 4) sourceC620) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2523) := by
    have ha : (tripleCharges (sourceA620 + difference 4 3) (sourceB620 + difference 3 4) sourceC620) = raw10445 := by
      apply Matrix.ext; unfold tripleCharges sourceA620 sourceB620 sourceC620 difference raw10445; decide +kernel
    rw [ha]
    exact (canonical10445 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA620 + difference 5 3) (sourceB620 + difference 3 5) sourceC620) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2519) := by
    have ha : (tripleCharges (sourceA620 + difference 5 3) (sourceB620 + difference 3 5) sourceC620) = raw10446 := by
      apply Matrix.ext; unfold tripleCharges sourceA620 sourceB620 sourceC620 difference raw10446; decide +kernel
    rw [ha]
    exact (canonical10446 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA620 + sourceB620) sourceC620) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA620 + sourceB620) sourceC620) = raw10438 := by
      apply Matrix.ext; unfold doubleCharges sourceA620 sourceB620 sourceC620 raw10438; decide +kernel
    rw [ha]
    exact (canonical10438 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA620 sourceB620 sourceC620
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm620, Integer.Sparse.eval]
  linarith only [hs]

def sourceA621 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB621 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceC621 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceForm621 : Integer.Sparse Master := [(Sum.inr 1246, 1), (Sum.inr 2523, 1), (Sum.inr 2561, 2), (Sum.inr 2742, 1), (Sum.inr 2743, 1), (Sum.inr 4092, -1)]

theorem sourceEq621 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm621 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA621 + difference 4 0) (sourceB621 + difference 0 4) sourceC621) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1246) := by
    have ha : (tripleCharges (sourceA621 + difference 4 0) (sourceB621 + difference 0 4) sourceC621) = raw10447 := by
      apply Matrix.ext; unfold tripleCharges sourceA621 sourceB621 sourceC621 difference raw10447; decide +kernel
    rw [ha]
    exact (canonical10447 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA621 + difference 4 1) (sourceB621 + difference 1 4) sourceC621) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2561) := by
    have ha : (tripleCharges (sourceA621 + difference 4 1) (sourceB621 + difference 1 4) sourceC621) = raw10441 := by
      apply Matrix.ext; unfold tripleCharges sourceA621 sourceB621 sourceC621 difference raw10441; decide +kernel
    rw [ha]
    exact (canonical10441 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA621 + difference 4 2) (sourceB621 + difference 2 4) sourceC621) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2561) := by
    have ha : (tripleCharges (sourceA621 + difference 4 2) (sourceB621 + difference 2 4) sourceC621) = raw10448 := by
      apply Matrix.ext; unfold tripleCharges sourceA621 sourceB621 sourceC621 difference raw10448; decide +kernel
    rw [ha]
    exact (canonical10448 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA621 + difference 4 3) (sourceB621 + difference 3 4) sourceC621) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2523) := by
    have ha : (tripleCharges (sourceA621 + difference 4 3) (sourceB621 + difference 3 4) sourceC621) = raw10445 := by
      apply Matrix.ext; unfold tripleCharges sourceA621 sourceB621 sourceC621 difference raw10445; decide +kernel
    rw [ha]
    exact (canonical10445 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA621 + difference 4 4) (sourceB621 + difference 4 4) sourceC621) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2743) := by
    have ha : (tripleCharges (sourceA621 + difference 4 4) (sourceB621 + difference 4 4) sourceC621) = raw10432 := by
      apply Matrix.ext; unfold tripleCharges sourceA621 sourceB621 sourceC621 difference raw10432; decide +kernel
    rw [ha]
    exact (canonical10432 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA621 + difference 4 5) (sourceB621 + difference 5 4) sourceC621) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2742) := by
    have ha : (tripleCharges (sourceA621 + difference 4 5) (sourceB621 + difference 5 4) sourceC621) = raw10449 := by
      apply Matrix.ext; unfold tripleCharges sourceA621 sourceB621 sourceC621 difference raw10449; decide +kernel
    rw [ha]
    exact (canonical10449 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA621 + sourceB621) sourceC621) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA621 + sourceB621) sourceC621) = raw10438 := by
      apply Matrix.ext; unfold doubleCharges sourceA621 sourceB621 sourceC621 raw10438; decide +kernel
    rw [ha]
    exact (canonical10438 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA621 sourceB621 sourceC621
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm621, Integer.Sparse.eval]
  linarith only [hs]

def sourceA622 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB622 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceC622 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceForm622 : Integer.Sparse Master := [(Sum.inr 4424, 2), (Sum.inr 4428, 1), (Sum.inr 4431, 1), (Sum.inr 4499, 1), (Sum.inr 5000, 2), (Sum.inr 5014, 2), (Sum.inr 5018, 2), (Sum.inr 5021, 1), (Sum.inr 5023, 1), (Sum.inr 5059, 2), (Sum.inr 5102, 2), (Sum.inr 5259, 2), (Sum.inr 5261, 1), (Sum.inr 5271, 2), (Sum.inr 5272, 1), (Sum.inr 5293, 1), (Sum.inr 5306, 1), (Sum.inr 5473, 2), (Sum.inr 5475, 1), (Sum.inr 5491, 1), (Sum.inr 5492, 1)]

theorem sourceEq622 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm622 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA622 + difference 0 1) (sourceB622 + difference 1 0) sourceC622) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA622 + difference 0 1) (sourceB622 + difference 1 0) sourceC622) = raw10450 := by
      apply Matrix.ext; unfold tripleCharges sourceA622 sourceB622 sourceC622 difference raw10450; decide +kernel
    rw [ha]
    exact (canonical10450 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA622 + difference 0 2) (sourceB622 + difference 2 0) sourceC622) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA622 + difference 0 2) (sourceB622 + difference 2 0) sourceC622) = raw10451 := by
      apply Matrix.ext; unfold tripleCharges sourceA622 sourceB622 sourceC622 difference raw10451; decide +kernel
    rw [ha]
    exact (canonical10451 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA622 + difference 0 3) (sourceB622 + difference 3 0) sourceC622) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5475) := by
    have ha : (tripleCharges (sourceA622 + difference 0 3) (sourceB622 + difference 3 0) sourceC622) = raw10452 := by
      apply Matrix.ext; unfold tripleCharges sourceA622 sourceB622 sourceC622 difference raw10452; decide +kernel
    rw [ha]
    exact (canonical10452 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA622 + difference 0 4) (sourceB622 + difference 4 0) sourceC622) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5491) := by
    have ha : (tripleCharges (sourceA622 + difference 0 4) (sourceB622 + difference 4 0) sourceC622) = raw10453 := by
      apply Matrix.ext; unfold tripleCharges sourceA622 sourceB622 sourceC622 difference raw10453; decide +kernel
    rw [ha]
    exact (canonical10453 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA622 + difference 0 5) (sourceB622 + difference 5 0) sourceC622) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5492) := by
    have ha : (tripleCharges (sourceA622 + difference 0 5) (sourceB622 + difference 5 0) sourceC622) = raw10454 := by
      apply Matrix.ext; unfold tripleCharges sourceA622 sourceB622 sourceC622 difference raw10454; decide +kernel
    rw [ha]
    exact (canonical10454 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA622 + difference 1 0) (sourceB622 + difference 0 1) sourceC622) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4424) := by
    have ha : (tripleCharges (sourceA622 + difference 1 0) (sourceB622 + difference 0 1) sourceC622) = raw10455 := by
      apply Matrix.ext; unfold tripleCharges sourceA622 sourceB622 sourceC622 difference raw10455; decide +kernel
    rw [ha]
    exact (canonical10455 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA622 + difference 1 2) (sourceB622 + difference 2 1) sourceC622) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5059) := by
    have ha : (tripleCharges (sourceA622 + difference 1 2) (sourceB622 + difference 2 1) sourceC622) = raw10456 := by
      apply Matrix.ext; unfold tripleCharges sourceA622 sourceB622 sourceC622 difference raw10456; decide +kernel
    rw [ha]
    exact (canonical10456 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA622 + difference 1 3) (sourceB622 + difference 3 1) sourceC622) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5018) := by
    have ha : (tripleCharges (sourceA622 + difference 1 3) (sourceB622 + difference 3 1) sourceC622) = raw10457 := by
      apply Matrix.ext; unfold tripleCharges sourceA622 sourceB622 sourceC622 difference raw10457; decide +kernel
    rw [ha]
    exact (canonical10457 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA622 + difference 1 4) (sourceB622 + difference 4 1) sourceC622) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA622 + difference 1 4) (sourceB622 + difference 4 1) sourceC622) = raw10458 := by
      apply Matrix.ext; unfold tripleCharges sourceA622 sourceB622 sourceC622 difference raw10458; decide +kernel
    rw [ha]
    exact (canonical10458 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA622 + difference 1 5) (sourceB622 + difference 5 1) sourceC622) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA622 + difference 1 5) (sourceB622 + difference 5 1) sourceC622) = raw10459 := by
      apply Matrix.ext; unfold tripleCharges sourceA622 sourceB622 sourceC622 difference raw10459; decide +kernel
    rw [ha]
    exact (canonical10459 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA622 + difference 2 0) (sourceB622 + difference 0 2) sourceC622) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4424) := by
    have ha : (tripleCharges (sourceA622 + difference 2 0) (sourceB622 + difference 0 2) sourceC622) = raw10460 := by
      apply Matrix.ext; unfold tripleCharges sourceA622 sourceB622 sourceC622 difference raw10460; decide +kernel
    rw [ha]
    exact (canonical10460 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA622 + difference 2 1) (sourceB622 + difference 1 2) sourceC622) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5059) := by
    have ha : (tripleCharges (sourceA622 + difference 2 1) (sourceB622 + difference 1 2) sourceC622) = raw10461 := by
      apply Matrix.ext; unfold tripleCharges sourceA622 sourceB622 sourceC622 difference raw10461; decide +kernel
    rw [ha]
    exact (canonical10461 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA622 + difference 2 3) (sourceB622 + difference 3 2) sourceC622) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5018) := by
    have ha : (tripleCharges (sourceA622 + difference 2 3) (sourceB622 + difference 3 2) sourceC622) = raw10462 := by
      apply Matrix.ext; unfold tripleCharges sourceA622 sourceB622 sourceC622 difference raw10462; decide +kernel
    rw [ha]
    exact (canonical10462 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA622 + difference 2 4) (sourceB622 + difference 4 2) sourceC622) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA622 + difference 2 4) (sourceB622 + difference 4 2) sourceC622) = raw10463 := by
      apply Matrix.ext; unfold tripleCharges sourceA622 sourceB622 sourceC622 difference raw10463; decide +kernel
    rw [ha]
    exact (canonical10463 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA622 + difference 2 5) (sourceB622 + difference 5 2) sourceC622) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA622 + difference 2 5) (sourceB622 + difference 5 2) sourceC622) = raw10464 := by
      apply Matrix.ext; unfold tripleCharges sourceA622 sourceB622 sourceC622 difference raw10464; decide +kernel
    rw [ha]
    exact (canonical10464 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA622 + difference 3 0) (sourceB622 + difference 0 3) sourceC622) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4499) := by
    have ha : (tripleCharges (sourceA622 + difference 3 0) (sourceB622 + difference 0 3) sourceC622) = raw10465 := by
      apply Matrix.ext; unfold tripleCharges sourceA622 sourceB622 sourceC622 difference raw10465; decide +kernel
    rw [ha]
    exact (canonical10465 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA622 + difference 3 1) (sourceB622 + difference 1 3) sourceC622) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5102) := by
    have ha : (tripleCharges (sourceA622 + difference 3 1) (sourceB622 + difference 1 3) sourceC622) = raw10466 := by
      apply Matrix.ext; unfold tripleCharges sourceA622 sourceB622 sourceC622 difference raw10466; decide +kernel
    rw [ha]
    exact (canonical10466 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA622 + difference 3 2) (sourceB622 + difference 2 3) sourceC622) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5102) := by
    have ha : (tripleCharges (sourceA622 + difference 3 2) (sourceB622 + difference 2 3) sourceC622) = raw10467 := by
      apply Matrix.ext; unfold tripleCharges sourceA622 sourceB622 sourceC622 difference raw10467; decide +kernel
    rw [ha]
    exact (canonical10467 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA622 + difference 3 4) (sourceB622 + difference 4 3) sourceC622) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA622 + difference 3 4) (sourceB622 + difference 4 3) sourceC622) = raw10468 := by
      apply Matrix.ext; unfold tripleCharges sourceA622 sourceB622 sourceC622 difference raw10468; decide +kernel
    rw [ha]
    exact (canonical10468 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA622 + difference 3 5) (sourceB622 + difference 5 3) sourceC622) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5306) := by
    have ha : (tripleCharges (sourceA622 + difference 3 5) (sourceB622 + difference 5 3) sourceC622) = raw10469 := by
      apply Matrix.ext; unfold tripleCharges sourceA622 sourceB622 sourceC622 difference raw10469; decide +kernel
    rw [ha]
    exact (canonical10469 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA622 + difference 4 0) (sourceB622 + difference 0 4) sourceC622) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4431) := by
    have ha : (tripleCharges (sourceA622 + difference 4 0) (sourceB622 + difference 0 4) sourceC622) = raw10470 := by
      apply Matrix.ext; unfold tripleCharges sourceA622 sourceB622 sourceC622 difference raw10470; decide +kernel
    rw [ha]
    exact (canonical10470 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA622 + difference 4 1) (sourceB622 + difference 1 4) sourceC622) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5014) := by
    have ha : (tripleCharges (sourceA622 + difference 4 1) (sourceB622 + difference 1 4) sourceC622) = raw10471 := by
      apply Matrix.ext; unfold tripleCharges sourceA622 sourceB622 sourceC622 difference raw10471; decide +kernel
    rw [ha]
    exact (canonical10471 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA622 + difference 4 2) (sourceB622 + difference 2 4) sourceC622) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5014) := by
    have ha : (tripleCharges (sourceA622 + difference 4 2) (sourceB622 + difference 2 4) sourceC622) = raw10472 := by
      apply Matrix.ext; unfold tripleCharges sourceA622 sourceB622 sourceC622 difference raw10472; decide +kernel
    rw [ha]
    exact (canonical10472 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA622 + difference 4 3) (sourceB622 + difference 3 4) sourceC622) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5023) := by
    have ha : (tripleCharges (sourceA622 + difference 4 3) (sourceB622 + difference 3 4) sourceC622) = raw10473 := by
      apply Matrix.ext; unfold tripleCharges sourceA622 sourceB622 sourceC622 difference raw10473; decide +kernel
    rw [ha]
    exact (canonical10473 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA622 + difference 4 5) (sourceB622 + difference 5 4) sourceC622) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5272) := by
    have ha : (tripleCharges (sourceA622 + difference 4 5) (sourceB622 + difference 5 4) sourceC622) = raw10474 := by
      apply Matrix.ext; unfold tripleCharges sourceA622 sourceB622 sourceC622 difference raw10474; decide +kernel
    rw [ha]
    exact (canonical10474 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA622 + difference 5 0) (sourceB622 + difference 0 5) sourceC622) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4428) := by
    have ha : (tripleCharges (sourceA622 + difference 5 0) (sourceB622 + difference 0 5) sourceC622) = raw10475 := by
      apply Matrix.ext; unfold tripleCharges sourceA622 sourceB622 sourceC622 difference raw10475; decide +kernel
    rw [ha]
    exact (canonical10475 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA622 + difference 5 1) (sourceB622 + difference 1 5) sourceC622) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5000) := by
    have ha : (tripleCharges (sourceA622 + difference 5 1) (sourceB622 + difference 1 5) sourceC622) = raw10476 := by
      apply Matrix.ext; unfold tripleCharges sourceA622 sourceB622 sourceC622 difference raw10476; decide +kernel
    rw [ha]
    exact (canonical10476 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA622 + difference 5 2) (sourceB622 + difference 2 5) sourceC622) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5000) := by
    have ha : (tripleCharges (sourceA622 + difference 5 2) (sourceB622 + difference 2 5) sourceC622) = raw10477 := by
      apply Matrix.ext; unfold tripleCharges sourceA622 sourceB622 sourceC622 difference raw10477; decide +kernel
    rw [ha]
    exact (canonical10477 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA622 + difference 5 3) (sourceB622 + difference 3 5) sourceC622) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5021) := by
    have ha : (tripleCharges (sourceA622 + difference 5 3) (sourceB622 + difference 3 5) sourceC622) = raw10478 := by
      apply Matrix.ext; unfold tripleCharges sourceA622 sourceB622 sourceC622 difference raw10478; decide +kernel
    rw [ha]
    exact (canonical10478 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA622 + difference 5 4) (sourceB622 + difference 4 5) sourceC622) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5261) := by
    have ha : (tripleCharges (sourceA622 + difference 5 4) (sourceB622 + difference 4 5) sourceC622) = raw10479 := by
      apply Matrix.ext; unfold tripleCharges sourceA622 sourceB622 sourceC622 difference raw10479; decide +kernel
    rw [ha]
    exact (canonical10479 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA622 sourceB622 sourceC622
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm622, Integer.Sparse.eval]
  linarith only [hs]

def sourceA623 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB623 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceC623 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceForm623 : Integer.Sparse Master := [(Sum.inr 1005, 2), (Sum.inr 1009, 1), (Sum.inr 1012, 1), (Sum.inr 1083, 1), (Sum.inr 2385, 2), (Sum.inr 2404, 2), (Sum.inr 2407, 1), (Sum.inr 2410, 1), (Sum.inr 2462, 2), (Sum.inr 2467, 2), (Sum.inr 2512, 2), (Sum.inr 2723, 2), (Sum.inr 2726, 1), (Sum.inr 2739, 2), (Sum.inr 2740, 1), (Sum.inr 2767, 1), (Sum.inr 2784, 1), (Sum.inr 3958, 2), (Sum.inr 3963, 1), (Sum.inr 4014, 1), (Sum.inr 4015, 1)]

theorem sourceEq623 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm623 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA623 + difference 0 1) (sourceB623 + difference 1 0) sourceC623) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3958) := by
    have ha : (tripleCharges (sourceA623 + difference 0 1) (sourceB623 + difference 1 0) sourceC623) = raw10480 := by
      apply Matrix.ext; unfold tripleCharges sourceA623 sourceB623 sourceC623 difference raw10480; decide +kernel
    rw [ha]
    exact (canonical10480 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA623 + difference 0 2) (sourceB623 + difference 2 0) sourceC623) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3958) := by
    have ha : (tripleCharges (sourceA623 + difference 0 2) (sourceB623 + difference 2 0) sourceC623) = raw10481 := by
      apply Matrix.ext; unfold tripleCharges sourceA623 sourceB623 sourceC623 difference raw10481; decide +kernel
    rw [ha]
    exact (canonical10481 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA623 + difference 0 3) (sourceB623 + difference 3 0) sourceC623) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3963) := by
    have ha : (tripleCharges (sourceA623 + difference 0 3) (sourceB623 + difference 3 0) sourceC623) = raw10482 := by
      apply Matrix.ext; unfold tripleCharges sourceA623 sourceB623 sourceC623 difference raw10482; decide +kernel
    rw [ha]
    exact (canonical10482 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA623 + difference 0 4) (sourceB623 + difference 4 0) sourceC623) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4014) := by
    have ha : (tripleCharges (sourceA623 + difference 0 4) (sourceB623 + difference 4 0) sourceC623) = raw10483 := by
      apply Matrix.ext; unfold tripleCharges sourceA623 sourceB623 sourceC623 difference raw10483; decide +kernel
    rw [ha]
    exact (canonical10483 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA623 + difference 0 5) (sourceB623 + difference 5 0) sourceC623) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4015) := by
    have ha : (tripleCharges (sourceA623 + difference 0 5) (sourceB623 + difference 5 0) sourceC623) = raw10484 := by
      apply Matrix.ext; unfold tripleCharges sourceA623 sourceB623 sourceC623 difference raw10484; decide +kernel
    rw [ha]
    exact (canonical10484 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA623 + difference 1 0) (sourceB623 + difference 0 1) sourceC623) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1005) := by
    have ha : (tripleCharges (sourceA623 + difference 1 0) (sourceB623 + difference 0 1) sourceC623) = raw10485 := by
      apply Matrix.ext; unfold tripleCharges sourceA623 sourceB623 sourceC623 difference raw10485; decide +kernel
    rw [ha]
    exact (canonical10485 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA623 + difference 1 2) (sourceB623 + difference 2 1) sourceC623) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2462) := by
    have ha : (tripleCharges (sourceA623 + difference 1 2) (sourceB623 + difference 2 1) sourceC623) = raw10486 := by
      apply Matrix.ext; unfold tripleCharges sourceA623 sourceB623 sourceC623 difference raw10486; decide +kernel
    rw [ha]
    exact (canonical10486 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA623 + difference 1 3) (sourceB623 + difference 3 1) sourceC623) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2404) := by
    have ha : (tripleCharges (sourceA623 + difference 1 3) (sourceB623 + difference 3 1) sourceC623) = raw10487 := by
      apply Matrix.ext; unfold tripleCharges sourceA623 sourceB623 sourceC623 difference raw10487; decide +kernel
    rw [ha]
    exact (canonical10487 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA623 + difference 1 4) (sourceB623 + difference 4 1) sourceC623) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA623 + difference 1 4) (sourceB623 + difference 4 1) sourceC623) = raw10488 := by
      apply Matrix.ext; unfold tripleCharges sourceA623 sourceB623 sourceC623 difference raw10488; decide +kernel
    rw [ha]
    exact (canonical10488 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA623 + difference 1 5) (sourceB623 + difference 5 1) sourceC623) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2739) := by
    have ha : (tripleCharges (sourceA623 + difference 1 5) (sourceB623 + difference 5 1) sourceC623) = raw10489 := by
      apply Matrix.ext; unfold tripleCharges sourceA623 sourceB623 sourceC623 difference raw10489; decide +kernel
    rw [ha]
    exact (canonical10489 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA623 + difference 2 0) (sourceB623 + difference 0 2) sourceC623) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1005) := by
    have ha : (tripleCharges (sourceA623 + difference 2 0) (sourceB623 + difference 0 2) sourceC623) = raw10490 := by
      apply Matrix.ext; unfold tripleCharges sourceA623 sourceB623 sourceC623 difference raw10490; decide +kernel
    rw [ha]
    exact (canonical10490 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA623 + difference 2 1) (sourceB623 + difference 1 2) sourceC623) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2462) := by
    have ha : (tripleCharges (sourceA623 + difference 2 1) (sourceB623 + difference 1 2) sourceC623) = raw10491 := by
      apply Matrix.ext; unfold tripleCharges sourceA623 sourceB623 sourceC623 difference raw10491; decide +kernel
    rw [ha]
    exact (canonical10491 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA623 + difference 2 3) (sourceB623 + difference 3 2) sourceC623) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2404) := by
    have ha : (tripleCharges (sourceA623 + difference 2 3) (sourceB623 + difference 3 2) sourceC623) = raw10492 := by
      apply Matrix.ext; unfold tripleCharges sourceA623 sourceB623 sourceC623 difference raw10492; decide +kernel
    rw [ha]
    exact (canonical10492 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA623 + difference 2 4) (sourceB623 + difference 4 2) sourceC623) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA623 + difference 2 4) (sourceB623 + difference 4 2) sourceC623) = raw10493 := by
      apply Matrix.ext; unfold tripleCharges sourceA623 sourceB623 sourceC623 difference raw10493; decide +kernel
    rw [ha]
    exact (canonical10493 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA623 + difference 2 5) (sourceB623 + difference 5 2) sourceC623) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2739) := by
    have ha : (tripleCharges (sourceA623 + difference 2 5) (sourceB623 + difference 5 2) sourceC623) = raw10494 := by
      apply Matrix.ext; unfold tripleCharges sourceA623 sourceB623 sourceC623 difference raw10494; decide +kernel
    rw [ha]
    exact (canonical10494 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA623 + difference 3 0) (sourceB623 + difference 0 3) sourceC623) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1083) := by
    have ha : (tripleCharges (sourceA623 + difference 3 0) (sourceB623 + difference 0 3) sourceC623) = raw10495 := by
      apply Matrix.ext; unfold tripleCharges sourceA623 sourceB623 sourceC623 difference raw10495; decide +kernel
    rw [ha]
    exact (canonical10495 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA623 + difference 3 1) (sourceB623 + difference 1 3) sourceC623) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2512) := by
    have ha : (tripleCharges (sourceA623 + difference 3 1) (sourceB623 + difference 1 3) sourceC623) = raw10496 := by
      apply Matrix.ext; unfold tripleCharges sourceA623 sourceB623 sourceC623 difference raw10496; decide +kernel
    rw [ha]
    exact (canonical10496 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA623 + difference 3 2) (sourceB623 + difference 2 3) sourceC623) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2512) := by
    have ha : (tripleCharges (sourceA623 + difference 3 2) (sourceB623 + difference 2 3) sourceC623) = raw10497 := by
      apply Matrix.ext; unfold tripleCharges sourceA623 sourceB623 sourceC623 difference raw10497; decide +kernel
    rw [ha]
    exact (canonical10497 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA623 + difference 3 4) (sourceB623 + difference 4 3) sourceC623) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2767) := by
    have ha : (tripleCharges (sourceA623 + difference 3 4) (sourceB623 + difference 4 3) sourceC623) = raw10498 := by
      apply Matrix.ext; unfold tripleCharges sourceA623 sourceB623 sourceC623 difference raw10498; decide +kernel
    rw [ha]
    exact (canonical10498 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA623 + difference 3 5) (sourceB623 + difference 5 3) sourceC623) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2784) := by
    have ha : (tripleCharges (sourceA623 + difference 3 5) (sourceB623 + difference 5 3) sourceC623) = raw10499 := by
      apply Matrix.ext; unfold tripleCharges sourceA623 sourceB623 sourceC623 difference raw10499; decide +kernel
    rw [ha]
    exact (canonical10499 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA623 + difference 4 0) (sourceB623 + difference 0 4) sourceC623) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1012) := by
    have ha : (tripleCharges (sourceA623 + difference 4 0) (sourceB623 + difference 0 4) sourceC623) = raw10500 := by
      apply Matrix.ext; unfold tripleCharges sourceA623 sourceB623 sourceC623 difference raw10500; decide +kernel
    rw [ha]
    exact (canonical10500 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA623 + difference 4 1) (sourceB623 + difference 1 4) sourceC623) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2467) := by
    have ha : (tripleCharges (sourceA623 + difference 4 1) (sourceB623 + difference 1 4) sourceC623) = raw10501 := by
      apply Matrix.ext; unfold tripleCharges sourceA623 sourceB623 sourceC623 difference raw10501; decide +kernel
    rw [ha]
    exact (canonical10501 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA623 + difference 4 2) (sourceB623 + difference 2 4) sourceC623) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2467) := by
    have ha : (tripleCharges (sourceA623 + difference 4 2) (sourceB623 + difference 2 4) sourceC623) = raw10502 := by
      apply Matrix.ext; unfold tripleCharges sourceA623 sourceB623 sourceC623 difference raw10502; decide +kernel
    rw [ha]
    exact (canonical10502 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA623 + difference 4 3) (sourceB623 + difference 3 4) sourceC623) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2410) := by
    have ha : (tripleCharges (sourceA623 + difference 4 3) (sourceB623 + difference 3 4) sourceC623) = raw10503 := by
      apply Matrix.ext; unfold tripleCharges sourceA623 sourceB623 sourceC623 difference raw10503; decide +kernel
    rw [ha]
    exact (canonical10503 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA623 + difference 4 5) (sourceB623 + difference 5 4) sourceC623) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2740) := by
    have ha : (tripleCharges (sourceA623 + difference 4 5) (sourceB623 + difference 5 4) sourceC623) = raw10504 := by
      apply Matrix.ext; unfold tripleCharges sourceA623 sourceB623 sourceC623 difference raw10504; decide +kernel
    rw [ha]
    exact (canonical10504 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA623 + difference 5 0) (sourceB623 + difference 0 5) sourceC623) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1009) := by
    have ha : (tripleCharges (sourceA623 + difference 5 0) (sourceB623 + difference 0 5) sourceC623) = raw10505 := by
      apply Matrix.ext; unfold tripleCharges sourceA623 sourceB623 sourceC623 difference raw10505; decide +kernel
    rw [ha]
    exact (canonical10505 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA623 + difference 5 1) (sourceB623 + difference 1 5) sourceC623) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2385) := by
    have ha : (tripleCharges (sourceA623 + difference 5 1) (sourceB623 + difference 1 5) sourceC623) = raw10506 := by
      apply Matrix.ext; unfold tripleCharges sourceA623 sourceB623 sourceC623 difference raw10506; decide +kernel
    rw [ha]
    exact (canonical10506 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA623 + difference 5 2) (sourceB623 + difference 2 5) sourceC623) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2385) := by
    have ha : (tripleCharges (sourceA623 + difference 5 2) (sourceB623 + difference 2 5) sourceC623) = raw10507 := by
      apply Matrix.ext; unfold tripleCharges sourceA623 sourceB623 sourceC623 difference raw10507; decide +kernel
    rw [ha]
    exact (canonical10507 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA623 + difference 5 3) (sourceB623 + difference 3 5) sourceC623) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2407) := by
    have ha : (tripleCharges (sourceA623 + difference 5 3) (sourceB623 + difference 3 5) sourceC623) = raw10508 := by
      apply Matrix.ext; unfold tripleCharges sourceA623 sourceB623 sourceC623 difference raw10508; decide +kernel
    rw [ha]
    exact (canonical10508 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA623 + difference 5 4) (sourceB623 + difference 4 5) sourceC623) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2726) := by
    have ha : (tripleCharges (sourceA623 + difference 5 4) (sourceB623 + difference 4 5) sourceC623) = raw10509 := by
      apply Matrix.ext; unfold tripleCharges sourceA623 sourceB623 sourceC623 difference raw10509; decide +kernel
    rw [ha]
    exact (canonical10509 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA623 sourceB623 sourceC623
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm623, Integer.Sparse.eval]
  linarith only [hs]

def sourceA624 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceB624 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceC624 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm624 : Integer.Sparse Master := [(Sum.inr 4835, 2), (Sum.inr 4843, 1), (Sum.inr 4846, 1), (Sum.inr 4901, 1), (Sum.inr 5205, 2), (Sum.inr 5206, 1), (Sum.inr 5229, 2), (Sum.inr 5238, 1), (Sum.inr 5242, 2), (Sum.inr 5248, 2), (Sum.inr 5259, 2), (Sum.inr 5260, 2), (Sum.inr 5274, 1), (Sum.inr 5275, 2), (Sum.inr 5276, 1), (Sum.inr 5282, 2), (Sum.inr 5291, 1), (Sum.inr 5293, 1), (Sum.inr 5300, 1), (Sum.inr 5309, 1), (Sum.inr 5310, 1)]

theorem sourceEq624 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm624 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA624 + difference 0 1) (sourceB624 + difference 1 0) sourceC624) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5282) := by
    have ha : (tripleCharges (sourceA624 + difference 0 1) (sourceB624 + difference 1 0) sourceC624) = raw10510 := by
      apply Matrix.ext; unfold tripleCharges sourceA624 sourceB624 sourceC624 difference raw10510; decide +kernel
    rw [ha]
    exact (canonical10510 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA624 + difference 0 2) (sourceB624 + difference 2 0) sourceC624) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5282) := by
    have ha : (tripleCharges (sourceA624 + difference 0 2) (sourceB624 + difference 2 0) sourceC624) = raw10511 := by
      apply Matrix.ext; unfold tripleCharges sourceA624 sourceB624 sourceC624 difference raw10511; decide +kernel
    rw [ha]
    exact (canonical10511 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA624 + difference 0 3) (sourceB624 + difference 3 0) sourceC624) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5300) := by
    have ha : (tripleCharges (sourceA624 + difference 0 3) (sourceB624 + difference 3 0) sourceC624) = raw10512 := by
      apply Matrix.ext; unfold tripleCharges sourceA624 sourceB624 sourceC624 difference raw10512; decide +kernel
    rw [ha]
    exact (canonical10512 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA624 + difference 0 4) (sourceB624 + difference 4 0) sourceC624) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA624 + difference 0 4) (sourceB624 + difference 4 0) sourceC624) = raw9891 := by
      apply Matrix.ext; unfold tripleCharges sourceA624 sourceB624 sourceC624 difference raw9891; decide +kernel
    rw [ha]
    exact (canonical9891 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA624 + difference 0 5) (sourceB624 + difference 5 0) sourceC624) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5291) := by
    have ha : (tripleCharges (sourceA624 + difference 0 5) (sourceB624 + difference 5 0) sourceC624) = raw7645 := by
      apply Matrix.ext; unfold tripleCharges sourceA624 sourceB624 sourceC624 difference raw7645; decide +kernel
    rw [ha]
    exact (canonical7645 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA624 + difference 1 0) (sourceB624 + difference 0 1) sourceC624) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4835) := by
    have ha : (tripleCharges (sourceA624 + difference 1 0) (sourceB624 + difference 0 1) sourceC624) = raw9908 := by
      apply Matrix.ext; unfold tripleCharges sourceA624 sourceB624 sourceC624 difference raw9908; decide +kernel
    rw [ha]
    exact (canonical9908 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA624 + difference 1 2) (sourceB624 + difference 2 1) sourceC624) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5242) := by
    have ha : (tripleCharges (sourceA624 + difference 1 2) (sourceB624 + difference 2 1) sourceC624) = raw9909 := by
      apply Matrix.ext; unfold tripleCharges sourceA624 sourceB624 sourceC624 difference raw9909; decide +kernel
    rw [ha]
    exact (canonical9909 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA624 + difference 1 3) (sourceB624 + difference 3 1) sourceC624) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5229) := by
    have ha : (tripleCharges (sourceA624 + difference 1 3) (sourceB624 + difference 3 1) sourceC624) = raw9910 := by
      apply Matrix.ext; unfold tripleCharges sourceA624 sourceB624 sourceC624 difference raw9910; decide +kernel
    rw [ha]
    exact (canonical9910 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA624 + difference 1 4) (sourceB624 + difference 4 1) sourceC624) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA624 + difference 1 4) (sourceB624 + difference 4 1) sourceC624) = raw10155 := by
      apply Matrix.ext; unfold tripleCharges sourceA624 sourceB624 sourceC624 difference raw10155; decide +kernel
    rw [ha]
    exact (canonical10155 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA624 + difference 1 5) (sourceB624 + difference 5 1) sourceC624) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5260) := by
    have ha : (tripleCharges (sourceA624 + difference 1 5) (sourceB624 + difference 5 1) sourceC624) = raw7650 := by
      apply Matrix.ext; unfold tripleCharges sourceA624 sourceB624 sourceC624 difference raw7650; decide +kernel
    rw [ha]
    exact (canonical7650 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA624 + difference 2 0) (sourceB624 + difference 0 2) sourceC624) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4835) := by
    have ha : (tripleCharges (sourceA624 + difference 2 0) (sourceB624 + difference 0 2) sourceC624) = raw10513 := by
      apply Matrix.ext; unfold tripleCharges sourceA624 sourceB624 sourceC624 difference raw10513; decide +kernel
    rw [ha]
    exact (canonical10513 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA624 + difference 2 1) (sourceB624 + difference 1 2) sourceC624) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5242) := by
    have ha : (tripleCharges (sourceA624 + difference 2 1) (sourceB624 + difference 1 2) sourceC624) = raw10514 := by
      apply Matrix.ext; unfold tripleCharges sourceA624 sourceB624 sourceC624 difference raw10514; decide +kernel
    rw [ha]
    exact (canonical10514 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA624 + difference 2 3) (sourceB624 + difference 3 2) sourceC624) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5229) := by
    have ha : (tripleCharges (sourceA624 + difference 2 3) (sourceB624 + difference 3 2) sourceC624) = raw10515 := by
      apply Matrix.ext; unfold tripleCharges sourceA624 sourceB624 sourceC624 difference raw10515; decide +kernel
    rw [ha]
    exact (canonical10515 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA624 + difference 2 4) (sourceB624 + difference 4 2) sourceC624) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA624 + difference 2 4) (sourceB624 + difference 4 2) sourceC624) = raw9902 := by
      apply Matrix.ext; unfold tripleCharges sourceA624 sourceB624 sourceC624 difference raw9902; decide +kernel
    rw [ha]
    exact (canonical9902 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA624 + difference 2 5) (sourceB624 + difference 5 2) sourceC624) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5260) := by
    have ha : (tripleCharges (sourceA624 + difference 2 5) (sourceB624 + difference 5 2) sourceC624) = raw7654 := by
      apply Matrix.ext; unfold tripleCharges sourceA624 sourceB624 sourceC624 difference raw7654; decide +kernel
    rw [ha]
    exact (canonical7654 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA624 + difference 3 0) (sourceB624 + difference 0 3) sourceC624) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4901) := by
    have ha : (tripleCharges (sourceA624 + difference 3 0) (sourceB624 + difference 0 3) sourceC624) = raw7656 := by
      apply Matrix.ext; unfold tripleCharges sourceA624 sourceB624 sourceC624 difference raw7656; decide +kernel
    rw [ha]
    exact (canonical7656 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA624 + difference 3 1) (sourceB624 + difference 1 3) sourceC624) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5275) := by
    have ha : (tripleCharges (sourceA624 + difference 3 1) (sourceB624 + difference 1 3) sourceC624) = raw6039 := by
      apply Matrix.ext; unfold tripleCharges sourceA624 sourceB624 sourceC624 difference raw6039; decide +kernel
    rw [ha]
    exact (canonical6039 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA624 + difference 3 2) (sourceB624 + difference 2 3) sourceC624) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5275) := by
    have ha : (tripleCharges (sourceA624 + difference 3 2) (sourceB624 + difference 2 3) sourceC624) = raw7657 := by
      apply Matrix.ext; unfold tripleCharges sourceA624 sourceB624 sourceC624 difference raw7657; decide +kernel
    rw [ha]
    exact (canonical7657 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA624 + difference 3 4) (sourceB624 + difference 4 3) sourceC624) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5309) := by
    have ha : (tripleCharges (sourceA624 + difference 3 4) (sourceB624 + difference 4 3) sourceC624) = raw7659 := by
      apply Matrix.ext; unfold tripleCharges sourceA624 sourceB624 sourceC624 difference raw7659; decide +kernel
    rw [ha]
    exact (canonical7659 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA624 + difference 3 5) (sourceB624 + difference 5 3) sourceC624) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5310) := by
    have ha : (tripleCharges (sourceA624 + difference 3 5) (sourceB624 + difference 5 3) sourceC624) = raw6018 := by
      apply Matrix.ext; unfold tripleCharges sourceA624 sourceB624 sourceC624 difference raw6018; decide +kernel
    rw [ha]
    exact (canonical6018 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA624 + difference 4 0) (sourceB624 + difference 0 4) sourceC624) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4843) := by
    have ha : (tripleCharges (sourceA624 + difference 4 0) (sourceB624 + difference 0 4) sourceC624) = raw10516 := by
      apply Matrix.ext; unfold tripleCharges sourceA624 sourceB624 sourceC624 difference raw10516; decide +kernel
    rw [ha]
    exact (canonical10516 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA624 + difference 4 1) (sourceB624 + difference 1 4) sourceC624) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5205) := by
    have ha : (tripleCharges (sourceA624 + difference 4 1) (sourceB624 + difference 1 4) sourceC624) = raw6038 := by
      apply Matrix.ext; unfold tripleCharges sourceA624 sourceB624 sourceC624 difference raw6038; decide +kernel
    rw [ha]
    exact (canonical6038 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA624 + difference 4 2) (sourceB624 + difference 2 4) sourceC624) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5205) := by
    have ha : (tripleCharges (sourceA624 + difference 4 2) (sourceB624 + difference 2 4) sourceC624) = raw10517 := by
      apply Matrix.ext; unfold tripleCharges sourceA624 sourceB624 sourceC624 difference raw10517; decide +kernel
    rw [ha]
    exact (canonical10517 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA624 + difference 4 3) (sourceB624 + difference 3 4) sourceC624) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5206) := by
    have ha : (tripleCharges (sourceA624 + difference 4 3) (sourceB624 + difference 3 4) sourceC624) = raw10518 := by
      apply Matrix.ext; unfold tripleCharges sourceA624 sourceB624 sourceC624 difference raw10518; decide +kernel
    rw [ha]
    exact (canonical10518 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA624 + difference 4 5) (sourceB624 + difference 5 4) sourceC624) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5276) := by
    have ha : (tripleCharges (sourceA624 + difference 4 5) (sourceB624 + difference 5 4) sourceC624) = raw6017 := by
      apply Matrix.ext; unfold tripleCharges sourceA624 sourceB624 sourceC624 difference raw6017; decide +kernel
    rw [ha]
    exact (canonical6017 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA624 + difference 5 0) (sourceB624 + difference 0 5) sourceC624) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4846) := by
    have ha : (tripleCharges (sourceA624 + difference 5 0) (sourceB624 + difference 0 5) sourceC624) = raw10519 := by
      apply Matrix.ext; unfold tripleCharges sourceA624 sourceB624 sourceC624 difference raw10519; decide +kernel
    rw [ha]
    exact (canonical10519 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA624 + difference 5 1) (sourceB624 + difference 1 5) sourceC624) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5248) := by
    have ha : (tripleCharges (sourceA624 + difference 5 1) (sourceB624 + difference 1 5) sourceC624) = raw10520 := by
      apply Matrix.ext; unfold tripleCharges sourceA624 sourceB624 sourceC624 difference raw10520; decide +kernel
    rw [ha]
    exact (canonical10520 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA624 + difference 5 2) (sourceB624 + difference 2 5) sourceC624) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5248) := by
    have ha : (tripleCharges (sourceA624 + difference 5 2) (sourceB624 + difference 2 5) sourceC624) = raw10521 := by
      apply Matrix.ext; unfold tripleCharges sourceA624 sourceB624 sourceC624 difference raw10521; decide +kernel
    rw [ha]
    exact (canonical10521 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA624 + difference 5 3) (sourceB624 + difference 3 5) sourceC624) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5238) := by
    have ha : (tripleCharges (sourceA624 + difference 5 3) (sourceB624 + difference 3 5) sourceC624) = raw10522 := by
      apply Matrix.ext; unfold tripleCharges sourceA624 sourceB624 sourceC624 difference raw10522; decide +kernel
    rw [ha]
    exact (canonical10522 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA624 + difference 5 4) (sourceB624 + difference 4 5) sourceC624) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5274) := by
    have ha : (tripleCharges (sourceA624 + difference 5 4) (sourceB624 + difference 4 5) sourceC624) = raw9912 := by
      apply Matrix.ext; unfold tripleCharges sourceA624 sourceB624 sourceC624 difference raw9912; decide +kernel
    rw [ha]
    exact (canonical9912 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA624 sourceB624 sourceC624
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm624, Integer.Sparse.eval]
  linarith only [hs]

def sourceA625 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceB625 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceC625 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm625 : Integer.Sparse Master := [(Sum.inr 2206, 2), (Sum.inr 2229, 1), (Sum.inr 2230, 1), (Sum.inr 2293, 1), (Sum.inr 2673, 2), (Sum.inr 2686, 1), (Sum.inr 2687, 1), (Sum.inr 2695, 2), (Sum.inr 2705, 2), (Sum.inr 2706, 2), (Sum.inr 2723, 2), (Sum.inr 2724, 2), (Sum.inr 2742, 1), (Sum.inr 2743, 2), (Sum.inr 2744, 1), (Sum.inr 2787, 1), (Sum.inr 2788, 1), (Sum.inr 3055, 1), (Sum.inr 3078, 2), (Sum.inr 3102, 1), (Sum.inr 3103, 1)]

theorem sourceEq625 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm625 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA625 + difference 0 1) (sourceB625 + difference 1 0) sourceC625) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3078) := by
    have ha : (tripleCharges (sourceA625 + difference 0 1) (sourceB625 + difference 1 0) sourceC625) = raw10523 := by
      apply Matrix.ext; unfold tripleCharges sourceA625 sourceB625 sourceC625 difference raw10523; decide +kernel
    rw [ha]
    exact (canonical10523 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA625 + difference 0 2) (sourceB625 + difference 2 0) sourceC625) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3078) := by
    have ha : (tripleCharges (sourceA625 + difference 0 2) (sourceB625 + difference 2 0) sourceC625) = raw10524 := by
      apply Matrix.ext; unfold tripleCharges sourceA625 sourceB625 sourceC625 difference raw10524; decide +kernel
    rw [ha]
    exact (canonical10524 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA625 + difference 0 3) (sourceB625 + difference 3 0) sourceC625) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3055) := by
    have ha : (tripleCharges (sourceA625 + difference 0 3) (sourceB625 + difference 3 0) sourceC625) = raw10525 := by
      apply Matrix.ext; unfold tripleCharges sourceA625 sourceB625 sourceC625 difference raw10525; decide +kernel
    rw [ha]
    exact (canonical10525 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA625 + difference 0 4) (sourceB625 + difference 4 0) sourceC625) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3102) := by
    have ha : (tripleCharges (sourceA625 + difference 0 4) (sourceB625 + difference 4 0) sourceC625) = raw9915 := by
      apply Matrix.ext; unfold tripleCharges sourceA625 sourceB625 sourceC625 difference raw9915; decide +kernel
    rw [ha]
    exact (canonical9915 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA625 + difference 0 5) (sourceB625 + difference 5 0) sourceC625) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3103) := by
    have ha : (tripleCharges (sourceA625 + difference 0 5) (sourceB625 + difference 5 0) sourceC625) = raw7661 := by
      apply Matrix.ext; unfold tripleCharges sourceA625 sourceB625 sourceC625 difference raw7661; decide +kernel
    rw [ha]
    exact (canonical7661 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA625 + difference 1 0) (sourceB625 + difference 0 1) sourceC625) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2206) := by
    have ha : (tripleCharges (sourceA625 + difference 1 0) (sourceB625 + difference 0 1) sourceC625) = raw9932 := by
      apply Matrix.ext; unfold tripleCharges sourceA625 sourceB625 sourceC625 difference raw9932; decide +kernel
    rw [ha]
    exact (canonical9932 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA625 + difference 1 2) (sourceB625 + difference 2 1) sourceC625) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2695) := by
    have ha : (tripleCharges (sourceA625 + difference 1 2) (sourceB625 + difference 2 1) sourceC625) = raw9933 := by
      apply Matrix.ext; unfold tripleCharges sourceA625 sourceB625 sourceC625 difference raw9933; decide +kernel
    rw [ha]
    exact (canonical9933 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA625 + difference 1 3) (sourceB625 + difference 3 1) sourceC625) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2673) := by
    have ha : (tripleCharges (sourceA625 + difference 1 3) (sourceB625 + difference 3 1) sourceC625) = raw9934 := by
      apply Matrix.ext; unfold tripleCharges sourceA625 sourceB625 sourceC625 difference raw9934; decide +kernel
    rw [ha]
    exact (canonical9934 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA625 + difference 1 4) (sourceB625 + difference 4 1) sourceC625) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA625 + difference 1 4) (sourceB625 + difference 4 1) sourceC625) = raw10170 := by
      apply Matrix.ext; unfold tripleCharges sourceA625 sourceB625 sourceC625 difference raw10170; decide +kernel
    rw [ha]
    exact (canonical10170 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA625 + difference 1 5) (sourceB625 + difference 5 1) sourceC625) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2724) := by
    have ha : (tripleCharges (sourceA625 + difference 1 5) (sourceB625 + difference 5 1) sourceC625) = raw7666 := by
      apply Matrix.ext; unfold tripleCharges sourceA625 sourceB625 sourceC625 difference raw7666; decide +kernel
    rw [ha]
    exact (canonical7666 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA625 + difference 2 0) (sourceB625 + difference 0 2) sourceC625) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2206) := by
    have ha : (tripleCharges (sourceA625 + difference 2 0) (sourceB625 + difference 0 2) sourceC625) = raw10526 := by
      apply Matrix.ext; unfold tripleCharges sourceA625 sourceB625 sourceC625 difference raw10526; decide +kernel
    rw [ha]
    exact (canonical10526 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA625 + difference 2 1) (sourceB625 + difference 1 2) sourceC625) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2695) := by
    have ha : (tripleCharges (sourceA625 + difference 2 1) (sourceB625 + difference 1 2) sourceC625) = raw10527 := by
      apply Matrix.ext; unfold tripleCharges sourceA625 sourceB625 sourceC625 difference raw10527; decide +kernel
    rw [ha]
    exact (canonical10527 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA625 + difference 2 3) (sourceB625 + difference 3 2) sourceC625) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2673) := by
    have ha : (tripleCharges (sourceA625 + difference 2 3) (sourceB625 + difference 3 2) sourceC625) = raw10528 := by
      apply Matrix.ext; unfold tripleCharges sourceA625 sourceB625 sourceC625 difference raw10528; decide +kernel
    rw [ha]
    exact (canonical10528 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA625 + difference 2 4) (sourceB625 + difference 4 2) sourceC625) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA625 + difference 2 4) (sourceB625 + difference 4 2) sourceC625) = raw9926 := by
      apply Matrix.ext; unfold tripleCharges sourceA625 sourceB625 sourceC625 difference raw9926; decide +kernel
    rw [ha]
    exact (canonical9926 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA625 + difference 2 5) (sourceB625 + difference 5 2) sourceC625) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2724) := by
    have ha : (tripleCharges (sourceA625 + difference 2 5) (sourceB625 + difference 5 2) sourceC625) = raw7670 := by
      apply Matrix.ext; unfold tripleCharges sourceA625 sourceB625 sourceC625 difference raw7670; decide +kernel
    rw [ha]
    exact (canonical7670 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA625 + difference 3 0) (sourceB625 + difference 0 3) sourceC625) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2293) := by
    have ha : (tripleCharges (sourceA625 + difference 3 0) (sourceB625 + difference 0 3) sourceC625) = raw7672 := by
      apply Matrix.ext; unfold tripleCharges sourceA625 sourceB625 sourceC625 difference raw7672; decide +kernel
    rw [ha]
    exact (canonical7672 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA625 + difference 3 1) (sourceB625 + difference 1 3) sourceC625) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2743) := by
    have ha : (tripleCharges (sourceA625 + difference 3 1) (sourceB625 + difference 1 3) sourceC625) = raw6069 := by
      apply Matrix.ext; unfold tripleCharges sourceA625 sourceB625 sourceC625 difference raw6069; decide +kernel
    rw [ha]
    exact (canonical6069 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA625 + difference 3 2) (sourceB625 + difference 2 3) sourceC625) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2743) := by
    have ha : (tripleCharges (sourceA625 + difference 3 2) (sourceB625 + difference 2 3) sourceC625) = raw7673 := by
      apply Matrix.ext; unfold tripleCharges sourceA625 sourceB625 sourceC625 difference raw7673; decide +kernel
    rw [ha]
    exact (canonical7673 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA625 + difference 3 4) (sourceB625 + difference 4 3) sourceC625) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2787) := by
    have ha : (tripleCharges (sourceA625 + difference 3 4) (sourceB625 + difference 4 3) sourceC625) = raw7675 := by
      apply Matrix.ext; unfold tripleCharges sourceA625 sourceB625 sourceC625 difference raw7675; decide +kernel
    rw [ha]
    exact (canonical7675 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA625 + difference 3 5) (sourceB625 + difference 5 3) sourceC625) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2788) := by
    have ha : (tripleCharges (sourceA625 + difference 3 5) (sourceB625 + difference 5 3) sourceC625) = raw6048 := by
      apply Matrix.ext; unfold tripleCharges sourceA625 sourceB625 sourceC625 difference raw6048; decide +kernel
    rw [ha]
    exact (canonical6048 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA625 + difference 4 0) (sourceB625 + difference 0 4) sourceC625) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2230) := by
    have ha : (tripleCharges (sourceA625 + difference 4 0) (sourceB625 + difference 0 4) sourceC625) = raw10529 := by
      apply Matrix.ext; unfold tripleCharges sourceA625 sourceB625 sourceC625 difference raw10529; decide +kernel
    rw [ha]
    exact (canonical10529 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA625 + difference 4 1) (sourceB625 + difference 1 4) sourceC625) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2706) := by
    have ha : (tripleCharges (sourceA625 + difference 4 1) (sourceB625 + difference 1 4) sourceC625) = raw6068 := by
      apply Matrix.ext; unfold tripleCharges sourceA625 sourceB625 sourceC625 difference raw6068; decide +kernel
    rw [ha]
    exact (canonical6068 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA625 + difference 4 2) (sourceB625 + difference 2 4) sourceC625) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2706) := by
    have ha : (tripleCharges (sourceA625 + difference 4 2) (sourceB625 + difference 2 4) sourceC625) = raw10530 := by
      apply Matrix.ext; unfold tripleCharges sourceA625 sourceB625 sourceC625 difference raw10530; decide +kernel
    rw [ha]
    exact (canonical10530 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA625 + difference 4 3) (sourceB625 + difference 3 4) sourceC625) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2687) := by
    have ha : (tripleCharges (sourceA625 + difference 4 3) (sourceB625 + difference 3 4) sourceC625) = raw10531 := by
      apply Matrix.ext; unfold tripleCharges sourceA625 sourceB625 sourceC625 difference raw10531; decide +kernel
    rw [ha]
    exact (canonical10531 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA625 + difference 4 5) (sourceB625 + difference 5 4) sourceC625) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2744) := by
    have ha : (tripleCharges (sourceA625 + difference 4 5) (sourceB625 + difference 5 4) sourceC625) = raw6047 := by
      apply Matrix.ext; unfold tripleCharges sourceA625 sourceB625 sourceC625 difference raw6047; decide +kernel
    rw [ha]
    exact (canonical6047 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA625 + difference 5 0) (sourceB625 + difference 0 5) sourceC625) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2229) := by
    have ha : (tripleCharges (sourceA625 + difference 5 0) (sourceB625 + difference 0 5) sourceC625) = raw10532 := by
      apply Matrix.ext; unfold tripleCharges sourceA625 sourceB625 sourceC625 difference raw10532; decide +kernel
    rw [ha]
    exact (canonical10532 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA625 + difference 5 1) (sourceB625 + difference 1 5) sourceC625) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2705) := by
    have ha : (tripleCharges (sourceA625 + difference 5 1) (sourceB625 + difference 1 5) sourceC625) = raw10533 := by
      apply Matrix.ext; unfold tripleCharges sourceA625 sourceB625 sourceC625 difference raw10533; decide +kernel
    rw [ha]
    exact (canonical10533 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA625 + difference 5 2) (sourceB625 + difference 2 5) sourceC625) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2705) := by
    have ha : (tripleCharges (sourceA625 + difference 5 2) (sourceB625 + difference 2 5) sourceC625) = raw10534 := by
      apply Matrix.ext; unfold tripleCharges sourceA625 sourceB625 sourceC625 difference raw10534; decide +kernel
    rw [ha]
    exact (canonical10534 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA625 + difference 5 3) (sourceB625 + difference 3 5) sourceC625) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2686) := by
    have ha : (tripleCharges (sourceA625 + difference 5 3) (sourceB625 + difference 3 5) sourceC625) = raw10535 := by
      apply Matrix.ext; unfold tripleCharges sourceA625 sourceB625 sourceC625 difference raw10535; decide +kernel
    rw [ha]
    exact (canonical10535 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA625 + difference 5 4) (sourceB625 + difference 4 5) sourceC625) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2742) := by
    have ha : (tripleCharges (sourceA625 + difference 5 4) (sourceB625 + difference 4 5) sourceC625) = raw9936 := by
      apply Matrix.ext; unfold tripleCharges sourceA625 sourceB625 sourceC625 difference raw9936; decide +kernel
    rw [ha]
    exact (canonical9936 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA625 sourceB625 sourceC625
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm625, Integer.Sparse.eval]
  linarith only [hs]

def sourceA626 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceB626 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceC626 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm626 : Integer.Sparse Master := [(Sum.inr 2054, 2), (Sum.inr 2062, 1), (Sum.inr 2066, 1), (Sum.inr 2293, 1), (Sum.inr 3548, 1), (Sum.inr 4084, -1)]

theorem sourceEq626 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm626 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA626 + difference 0 0) (sourceB626 + difference 0 0) sourceC626) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3548) := by
    have ha : (tripleCharges (sourceA626 + difference 0 0) (sourceB626 + difference 0 0) sourceC626) = raw7700 := by
      apply Matrix.ext; unfold tripleCharges sourceA626 sourceB626 sourceC626 difference raw7700; decide +kernel
    rw [ha]
    exact (canonical7700 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA626 + difference 1 0) (sourceB626 + difference 0 1) sourceC626) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2054) := by
    have ha : (tripleCharges (sourceA626 + difference 1 0) (sourceB626 + difference 0 1) sourceC626) = raw9967 := by
      apply Matrix.ext; unfold tripleCharges sourceA626 sourceB626 sourceC626 difference raw9967; decide +kernel
    rw [ha]
    exact (canonical9967 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA626 + difference 2 0) (sourceB626 + difference 0 2) sourceC626) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2054) := by
    have ha : (tripleCharges (sourceA626 + difference 2 0) (sourceB626 + difference 0 2) sourceC626) = raw10536 := by
      apply Matrix.ext; unfold tripleCharges sourceA626 sourceB626 sourceC626 difference raw10536; decide +kernel
    rw [ha]
    exact (canonical10536 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA626 + difference 3 0) (sourceB626 + difference 0 3) sourceC626) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2293) := by
    have ha : (tripleCharges (sourceA626 + difference 3 0) (sourceB626 + difference 0 3) sourceC626) = raw7698 := by
      apply Matrix.ext; unfold tripleCharges sourceA626 sourceB626 sourceC626 difference raw7698; decide +kernel
    rw [ha]
    exact (canonical7698 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA626 + difference 4 0) (sourceB626 + difference 0 4) sourceC626) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2062) := by
    have ha : (tripleCharges (sourceA626 + difference 4 0) (sourceB626 + difference 0 4) sourceC626) = raw10537 := by
      apply Matrix.ext; unfold tripleCharges sourceA626 sourceB626 sourceC626 difference raw10537; decide +kernel
    rw [ha]
    exact (canonical10537 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA626 + difference 5 0) (sourceB626 + difference 0 5) sourceC626) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2066) := by
    have ha : (tripleCharges (sourceA626 + difference 5 0) (sourceB626 + difference 0 5) sourceC626) = raw10538 := by
      apply Matrix.ext; unfold tripleCharges sourceA626 sourceB626 sourceC626 difference raw10538; decide +kernel
    rw [ha]
    exact (canonical10538 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA626 + sourceB626) sourceC626) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA626 + sourceB626) sourceC626) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA626 sourceB626 sourceC626 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA626 sourceB626 sourceC626
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm626, Integer.Sparse.eval]
  linarith only [hs]

def sourceA627 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB627 : Charge := ![1, 0, 0, -1, 0, 0]
def sourceC627 : Charge := ![2, 0, 0, 1, -1, -2]
def sourceForm627 : Integer.Sparse Master := [(Sum.inr 4092, 1), (Sum.inr 4602, 2), (Sum.inr 4608, 1), (Sum.inr 4612, 1), (Sum.inr 4619, 1), (Sum.inr 5075, 2), (Sum.inr 5101, 2), (Sum.inr 5107, 1), (Sum.inr 5111, 1), (Sum.inr 5134, 2), (Sum.inr 5141, 2), (Sum.inr 5163, 2), (Sum.inr 5258, 2), (Sum.inr 5261, 1), (Sum.inr 5271, 2), (Sum.inr 5275, 1), (Sum.inr 5291, 1), (Sum.inr 5304, 1), (Sum.inr 5409, 2), (Sum.inr 5441, 1), (Sum.inr 5442, 1)]

theorem sourceEq627 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm627 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA627 + difference 0 1) (sourceB627 + difference 1 0) sourceC627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5409) := by
    have ha : (tripleCharges (sourceA627 + difference 0 1) (sourceB627 + difference 1 0) sourceC627) = raw10539 := by
      apply Matrix.ext; unfold tripleCharges sourceA627 sourceB627 sourceC627 difference raw10539; decide +kernel
    rw [ha]
    exact (canonical10539 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA627 + difference 0 2) (sourceB627 + difference 2 0) sourceC627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5409) := by
    have ha : (tripleCharges (sourceA627 + difference 0 2) (sourceB627 + difference 2 0) sourceC627) = raw10540 := by
      apply Matrix.ext; unfold tripleCharges sourceA627 sourceB627 sourceC627 difference raw10540; decide +kernel
    rw [ha]
    exact (canonical10540 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA627 + difference 0 3) (sourceB627 + difference 3 0) sourceC627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA627 + difference 0 3) (sourceB627 + difference 3 0) sourceC627) = raw10541 := by
      apply Matrix.ext; unfold tripleCharges sourceA627 sourceB627 sourceC627 difference raw10541; decide +kernel
    rw [ha]
    exact (canonical10541 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA627 + difference 0 4) (sourceB627 + difference 4 0) sourceC627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5441) := by
    have ha : (tripleCharges (sourceA627 + difference 0 4) (sourceB627 + difference 4 0) sourceC627) = raw10542 := by
      apply Matrix.ext; unfold tripleCharges sourceA627 sourceB627 sourceC627 difference raw10542; decide +kernel
    rw [ha]
    exact (canonical10542 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA627 + difference 0 5) (sourceB627 + difference 5 0) sourceC627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5442) := by
    have ha : (tripleCharges (sourceA627 + difference 0 5) (sourceB627 + difference 5 0) sourceC627) = raw10543 := by
      apply Matrix.ext; unfold tripleCharges sourceA627 sourceB627 sourceC627 difference raw10543; decide +kernel
    rw [ha]
    exact (canonical10543 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA627 + difference 1 0) (sourceB627 + difference 0 1) sourceC627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA627 + difference 1 0) (sourceB627 + difference 0 1) sourceC627) = raw10544 := by
      apply Matrix.ext; unfold tripleCharges sourceA627 sourceB627 sourceC627 difference raw10544; decide +kernel
    rw [ha]
    exact (canonical10544 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA627 + difference 1 2) (sourceB627 + difference 2 1) sourceC627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5134) := by
    have ha : (tripleCharges (sourceA627 + difference 1 2) (sourceB627 + difference 2 1) sourceC627) = raw10545 := by
      apply Matrix.ext; unfold tripleCharges sourceA627 sourceB627 sourceC627 difference raw10545; decide +kernel
    rw [ha]
    exact (canonical10545 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA627 + difference 1 3) (sourceB627 + difference 3 1) sourceC627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5101) := by
    have ha : (tripleCharges (sourceA627 + difference 1 3) (sourceB627 + difference 3 1) sourceC627) = raw10546 := by
      apply Matrix.ext; unfold tripleCharges sourceA627 sourceB627 sourceC627 difference raw10546; decide +kernel
    rw [ha]
    exact (canonical10546 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA627 + difference 1 4) (sourceB627 + difference 4 1) sourceC627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA627 + difference 1 4) (sourceB627 + difference 4 1) sourceC627) = raw10547 := by
      apply Matrix.ext; unfold tripleCharges sourceA627 sourceB627 sourceC627 difference raw10547; decide +kernel
    rw [ha]
    exact (canonical10547 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA627 + difference 1 5) (sourceB627 + difference 5 1) sourceC627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA627 + difference 1 5) (sourceB627 + difference 5 1) sourceC627) = raw10548 := by
      apply Matrix.ext; unfold tripleCharges sourceA627 sourceB627 sourceC627 difference raw10548; decide +kernel
    rw [ha]
    exact (canonical10548 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA627 + difference 2 0) (sourceB627 + difference 0 2) sourceC627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA627 + difference 2 0) (sourceB627 + difference 0 2) sourceC627) = raw10549 := by
      apply Matrix.ext; unfold tripleCharges sourceA627 sourceB627 sourceC627 difference raw10549; decide +kernel
    rw [ha]
    exact (canonical10549 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA627 + difference 2 1) (sourceB627 + difference 1 2) sourceC627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5134) := by
    have ha : (tripleCharges (sourceA627 + difference 2 1) (sourceB627 + difference 1 2) sourceC627) = raw10550 := by
      apply Matrix.ext; unfold tripleCharges sourceA627 sourceB627 sourceC627 difference raw10550; decide +kernel
    rw [ha]
    exact (canonical10550 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA627 + difference 2 3) (sourceB627 + difference 3 2) sourceC627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5101) := by
    have ha : (tripleCharges (sourceA627 + difference 2 3) (sourceB627 + difference 3 2) sourceC627) = raw10551 := by
      apply Matrix.ext; unfold tripleCharges sourceA627 sourceB627 sourceC627 difference raw10551; decide +kernel
    rw [ha]
    exact (canonical10551 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA627 + difference 2 4) (sourceB627 + difference 4 2) sourceC627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA627 + difference 2 4) (sourceB627 + difference 4 2) sourceC627) = raw10552 := by
      apply Matrix.ext; unfold tripleCharges sourceA627 sourceB627 sourceC627 difference raw10552; decide +kernel
    rw [ha]
    exact (canonical10552 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA627 + difference 2 5) (sourceB627 + difference 5 2) sourceC627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA627 + difference 2 5) (sourceB627 + difference 5 2) sourceC627) = raw10553 := by
      apply Matrix.ext; unfold tripleCharges sourceA627 sourceB627 sourceC627 difference raw10553; decide +kernel
    rw [ha]
    exact (canonical10553 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA627 + difference 3 0) (sourceB627 + difference 0 3) sourceC627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4619) := by
    have ha : (tripleCharges (sourceA627 + difference 3 0) (sourceB627 + difference 0 3) sourceC627) = raw10554 := by
      apply Matrix.ext; unfold tripleCharges sourceA627 sourceB627 sourceC627 difference raw10554; decide +kernel
    rw [ha]
    exact (canonical10554 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA627 + difference 3 1) (sourceB627 + difference 1 3) sourceC627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5163) := by
    have ha : (tripleCharges (sourceA627 + difference 3 1) (sourceB627 + difference 1 3) sourceC627) = raw10555 := by
      apply Matrix.ext; unfold tripleCharges sourceA627 sourceB627 sourceC627 difference raw10555; decide +kernel
    rw [ha]
    exact (canonical10555 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA627 + difference 3 2) (sourceB627 + difference 2 3) sourceC627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5163) := by
    have ha : (tripleCharges (sourceA627 + difference 3 2) (sourceB627 + difference 2 3) sourceC627) = raw10556 := by
      apply Matrix.ext; unfold tripleCharges sourceA627 sourceB627 sourceC627 difference raw10556; decide +kernel
    rw [ha]
    exact (canonical10556 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA627 + difference 3 4) (sourceB627 + difference 4 3) sourceC627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5291) := by
    have ha : (tripleCharges (sourceA627 + difference 3 4) (sourceB627 + difference 4 3) sourceC627) = raw10557 := by
      apply Matrix.ext; unfold tripleCharges sourceA627 sourceB627 sourceC627 difference raw10557; decide +kernel
    rw [ha]
    exact (canonical10557 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA627 + difference 3 5) (sourceB627 + difference 5 3) sourceC627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA627 + difference 3 5) (sourceB627 + difference 5 3) sourceC627) = raw10558 := by
      apply Matrix.ext; unfold tripleCharges sourceA627 sourceB627 sourceC627 difference raw10558; decide +kernel
    rw [ha]
    exact (canonical10558 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA627 + difference 4 0) (sourceB627 + difference 0 4) sourceC627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA627 + difference 4 0) (sourceB627 + difference 0 4) sourceC627) = raw10559 := by
      apply Matrix.ext; unfold tripleCharges sourceA627 sourceB627 sourceC627 difference raw10559; decide +kernel
    rw [ha]
    exact (canonical10559 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA627 + difference 4 1) (sourceB627 + difference 1 4) sourceC627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA627 + difference 4 1) (sourceB627 + difference 1 4) sourceC627) = raw10560 := by
      apply Matrix.ext; unfold tripleCharges sourceA627 sourceB627 sourceC627 difference raw10560; decide +kernel
    rw [ha]
    exact (canonical10560 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA627 + difference 4 2) (sourceB627 + difference 2 4) sourceC627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA627 + difference 4 2) (sourceB627 + difference 2 4) sourceC627) = raw10561 := by
      apply Matrix.ext; unfold tripleCharges sourceA627 sourceB627 sourceC627 difference raw10561; decide +kernel
    rw [ha]
    exact (canonical10561 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA627 + difference 4 3) (sourceB627 + difference 3 4) sourceC627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5111) := by
    have ha : (tripleCharges (sourceA627 + difference 4 3) (sourceB627 + difference 3 4) sourceC627) = raw10562 := by
      apply Matrix.ext; unfold tripleCharges sourceA627 sourceB627 sourceC627 difference raw10562; decide +kernel
    rw [ha]
    exact (canonical10562 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA627 + difference 4 5) (sourceB627 + difference 5 4) sourceC627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5275) := by
    have ha : (tripleCharges (sourceA627 + difference 4 5) (sourceB627 + difference 5 4) sourceC627) = raw10563 := by
      apply Matrix.ext; unfold tripleCharges sourceA627 sourceB627 sourceC627 difference raw10563; decide +kernel
    rw [ha]
    exact (canonical10563 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA627 + difference 5 0) (sourceB627 + difference 0 5) sourceC627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4608) := by
    have ha : (tripleCharges (sourceA627 + difference 5 0) (sourceB627 + difference 0 5) sourceC627) = raw10564 := by
      apply Matrix.ext; unfold tripleCharges sourceA627 sourceB627 sourceC627 difference raw10564; decide +kernel
    rw [ha]
    exact (canonical10564 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA627 + difference 5 1) (sourceB627 + difference 1 5) sourceC627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA627 + difference 5 1) (sourceB627 + difference 1 5) sourceC627) = raw10565 := by
      apply Matrix.ext; unfold tripleCharges sourceA627 sourceB627 sourceC627 difference raw10565; decide +kernel
    rw [ha]
    exact (canonical10565 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA627 + difference 5 2) (sourceB627 + difference 2 5) sourceC627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA627 + difference 5 2) (sourceB627 + difference 2 5) sourceC627) = raw10566 := by
      apply Matrix.ext; unfold tripleCharges sourceA627 sourceB627 sourceC627 difference raw10566; decide +kernel
    rw [ha]
    exact (canonical10566 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA627 + difference 5 3) (sourceB627 + difference 3 5) sourceC627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5107) := by
    have ha : (tripleCharges (sourceA627 + difference 5 3) (sourceB627 + difference 3 5) sourceC627) = raw10567 := by
      apply Matrix.ext; unfold tripleCharges sourceA627 sourceB627 sourceC627 difference raw10567; decide +kernel
    rw [ha]
    exact (canonical10567 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA627 + difference 5 4) (sourceB627 + difference 4 5) sourceC627) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5261) := by
    have ha : (tripleCharges (sourceA627 + difference 5 4) (sourceB627 + difference 4 5) sourceC627) = raw10568 := by
      apply Matrix.ext; unfold tripleCharges sourceA627 sourceB627 sourceC627 difference raw10568; decide +kernel
    rw [ha]
    exact (canonical10568 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA627 sourceB627 sourceC627
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm627, Integer.Sparse.eval]
  linarith only [hs]

def sourceA628 : Charge := ![1, 0, 0, -1, 0, 0]
def sourceB628 : Charge := ![2, 0, 0, 1, -1, -2]
def sourceC628 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm628 : Integer.Sparse Master := [(Sum.inr 4084, 1), (Sum.inr 4834, 2), (Sum.inr 4841, 1), (Sum.inr 4846, 1), (Sum.inr 5099, 2), (Sum.inr 5110, 1), (Sum.inr 5228, 2), (Sum.inr 5238, 1), (Sum.inr 5241, 2), (Sum.inr 5248, 2), (Sum.inr 5258, 2), (Sum.inr 5259, 2), (Sum.inr 5272, 1), (Sum.inr 5274, 2), (Sum.inr 5275, 1), (Sum.inr 5284, 2), (Sum.inr 5293, 1), (Sum.inr 5294, 1), (Sum.inr 5302, 1), (Sum.inr 5308, 1), (Sum.inr 5309, 1)]

theorem sourceEq628 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm628 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA628 + difference 0 1) (sourceB628 + difference 1 0) sourceC628) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA628 + difference 0 1) (sourceB628 + difference 1 0) sourceC628) = raw10569 := by
      apply Matrix.ext; unfold tripleCharges sourceA628 sourceB628 sourceC628 difference raw10569; decide +kernel
    rw [ha]
    exact (canonical10569 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA628 + difference 0 2) (sourceB628 + difference 2 0) sourceC628) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA628 + difference 0 2) (sourceB628 + difference 2 0) sourceC628) = raw10570 := by
      apply Matrix.ext; unfold tripleCharges sourceA628 sourceB628 sourceC628 difference raw10570; decide +kernel
    rw [ha]
    exact (canonical10570 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA628 + difference 0 3) (sourceB628 + difference 3 0) sourceC628) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA628 + difference 0 3) (sourceB628 + difference 3 0) sourceC628) = raw10571 := by
      apply Matrix.ext; unfold tripleCharges sourceA628 sourceB628 sourceC628 difference raw10571; decide +kernel
    rw [ha]
    exact (canonical10571 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA628 + difference 0 4) (sourceB628 + difference 4 0) sourceC628) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA628 + difference 0 4) (sourceB628 + difference 4 0) sourceC628) = raw10145 := by
      apply Matrix.ext; unfold tripleCharges sourceA628 sourceB628 sourceC628 difference raw10145; decide +kernel
    rw [ha]
    exact (canonical10145 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA628 + difference 0 5) (sourceB628 + difference 5 0) sourceC628) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA628 + difference 0 5) (sourceB628 + difference 5 0) sourceC628) = raw9891 := by
      apply Matrix.ext; unfold tripleCharges sourceA628 sourceB628 sourceC628 difference raw9891; decide +kernel
    rw [ha]
    exact (canonical9891 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA628 + difference 1 0) (sourceB628 + difference 0 1) sourceC628) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4834) := by
    have ha : (tripleCharges (sourceA628 + difference 1 0) (sourceB628 + difference 0 1) sourceC628) = raw9911 := by
      apply Matrix.ext; unfold tripleCharges sourceA628 sourceB628 sourceC628 difference raw9911; decide +kernel
    rw [ha]
    exact (canonical9911 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA628 + difference 1 2) (sourceB628 + difference 2 1) sourceC628) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5241) := by
    have ha : (tripleCharges (sourceA628 + difference 1 2) (sourceB628 + difference 2 1) sourceC628) = raw9913 := by
      apply Matrix.ext; unfold tripleCharges sourceA628 sourceB628 sourceC628 difference raw9913; decide +kernel
    rw [ha]
    exact (canonical9913 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA628 + difference 1 3) (sourceB628 + difference 3 1) sourceC628) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5228) := by
    have ha : (tripleCharges (sourceA628 + difference 1 3) (sourceB628 + difference 3 1) sourceC628) = raw9914 := by
      apply Matrix.ext; unfold tripleCharges sourceA628 sourceB628 sourceC628 difference raw9914; decide +kernel
    rw [ha]
    exact (canonical9914 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA628 + difference 1 4) (sourceB628 + difference 4 1) sourceC628) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA628 + difference 1 4) (sourceB628 + difference 4 1) sourceC628) = raw9670 := by
      apply Matrix.ext; unfold tripleCharges sourceA628 sourceB628 sourceC628 difference raw9670; decide +kernel
    rw [ha]
    exact (canonical9670 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA628 + difference 1 5) (sourceB628 + difference 5 1) sourceC628) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA628 + difference 1 5) (sourceB628 + difference 5 1) sourceC628) = raw10155 := by
      apply Matrix.ext; unfold tripleCharges sourceA628 sourceB628 sourceC628 difference raw10155; decide +kernel
    rw [ha]
    exact (canonical10155 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA628 + difference 2 0) (sourceB628 + difference 0 2) sourceC628) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4834) := by
    have ha : (tripleCharges (sourceA628 + difference 2 0) (sourceB628 + difference 0 2) sourceC628) = raw10572 := by
      apply Matrix.ext; unfold tripleCharges sourceA628 sourceB628 sourceC628 difference raw10572; decide +kernel
    rw [ha]
    exact (canonical10572 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA628 + difference 2 1) (sourceB628 + difference 1 2) sourceC628) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5241) := by
    have ha : (tripleCharges (sourceA628 + difference 2 1) (sourceB628 + difference 1 2) sourceC628) = raw10573 := by
      apply Matrix.ext; unfold tripleCharges sourceA628 sourceB628 sourceC628 difference raw10573; decide +kernel
    rw [ha]
    exact (canonical10573 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA628 + difference 2 3) (sourceB628 + difference 3 2) sourceC628) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5228) := by
    have ha : (tripleCharges (sourceA628 + difference 2 3) (sourceB628 + difference 3 2) sourceC628) = raw10574 := by
      apply Matrix.ext; unfold tripleCharges sourceA628 sourceB628 sourceC628 difference raw10574; decide +kernel
    rw [ha]
    exact (canonical10574 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA628 + difference 2 4) (sourceB628 + difference 4 2) sourceC628) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA628 + difference 2 4) (sourceB628 + difference 4 2) sourceC628) = raw10152 := by
      apply Matrix.ext; unfold tripleCharges sourceA628 sourceB628 sourceC628 difference raw10152; decide +kernel
    rw [ha]
    exact (canonical10152 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA628 + difference 2 5) (sourceB628 + difference 5 2) sourceC628) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA628 + difference 2 5) (sourceB628 + difference 5 2) sourceC628) = raw9902 := by
      apply Matrix.ext; unfold tripleCharges sourceA628 sourceB628 sourceC628 difference raw9902; decide +kernel
    rw [ha]
    exact (canonical9902 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA628 + difference 3 0) (sourceB628 + difference 0 3) sourceC628) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA628 + difference 3 0) (sourceB628 + difference 0 3) sourceC628) = raw10575 := by
      apply Matrix.ext; unfold tripleCharges sourceA628 sourceB628 sourceC628 difference raw10575; decide +kernel
    rw [ha]
    exact (canonical10575 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA628 + difference 3 1) (sourceB628 + difference 1 3) sourceC628) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5274) := by
    have ha : (tripleCharges (sourceA628 + difference 3 1) (sourceB628 + difference 1 3) sourceC628) = raw10576 := by
      apply Matrix.ext; unfold tripleCharges sourceA628 sourceB628 sourceC628 difference raw10576; decide +kernel
    rw [ha]
    exact (canonical10576 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA628 + difference 3 2) (sourceB628 + difference 2 3) sourceC628) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5274) := by
    have ha : (tripleCharges (sourceA628 + difference 3 2) (sourceB628 + difference 2 3) sourceC628) = raw10577 := by
      apply Matrix.ext; unfold tripleCharges sourceA628 sourceB628 sourceC628 difference raw10577; decide +kernel
    rw [ha]
    exact (canonical10577 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA628 + difference 3 4) (sourceB628 + difference 4 3) sourceC628) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5308) := by
    have ha : (tripleCharges (sourceA628 + difference 3 4) (sourceB628 + difference 4 3) sourceC628) = raw7929 := by
      apply Matrix.ext; unfold tripleCharges sourceA628 sourceB628 sourceC628 difference raw7929; decide +kernel
    rw [ha]
    exact (canonical7929 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA628 + difference 3 5) (sourceB628 + difference 5 3) sourceC628) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5309) := by
    have ha : (tripleCharges (sourceA628 + difference 3 5) (sourceB628 + difference 5 3) sourceC628) = raw7659 := by
      apply Matrix.ext; unfold tripleCharges sourceA628 sourceB628 sourceC628 difference raw7659; decide +kernel
    rw [ha]
    exact (canonical7659 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA628 + difference 4 0) (sourceB628 + difference 0 4) sourceC628) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4846) := by
    have ha : (tripleCharges (sourceA628 + difference 4 0) (sourceB628 + difference 0 4) sourceC628) = raw10519 := by
      apply Matrix.ext; unfold tripleCharges sourceA628 sourceB628 sourceC628 difference raw10519; decide +kernel
    rw [ha]
    exact (canonical10519 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA628 + difference 4 1) (sourceB628 + difference 1 4) sourceC628) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5248) := by
    have ha : (tripleCharges (sourceA628 + difference 4 1) (sourceB628 + difference 1 4) sourceC628) = raw10520 := by
      apply Matrix.ext; unfold tripleCharges sourceA628 sourceB628 sourceC628 difference raw10520; decide +kernel
    rw [ha]
    exact (canonical10520 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA628 + difference 4 2) (sourceB628 + difference 2 4) sourceC628) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5248) := by
    have ha : (tripleCharges (sourceA628 + difference 4 2) (sourceB628 + difference 2 4) sourceC628) = raw10521 := by
      apply Matrix.ext; unfold tripleCharges sourceA628 sourceB628 sourceC628 difference raw10521; decide +kernel
    rw [ha]
    exact (canonical10521 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA628 + difference 4 3) (sourceB628 + difference 3 4) sourceC628) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5238) := by
    have ha : (tripleCharges (sourceA628 + difference 4 3) (sourceB628 + difference 3 4) sourceC628) = raw10522 := by
      apply Matrix.ext; unfold tripleCharges sourceA628 sourceB628 sourceC628 difference raw10522; decide +kernel
    rw [ha]
    exact (canonical10522 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA628 + difference 4 5) (sourceB628 + difference 5 4) sourceC628) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5275) := by
    have ha : (tripleCharges (sourceA628 + difference 4 5) (sourceB628 + difference 5 4) sourceC628) = raw7658 := by
      apply Matrix.ext; unfold tripleCharges sourceA628 sourceB628 sourceC628 difference raw7658; decide +kernel
    rw [ha]
    exact (canonical7658 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA628 + difference 5 0) (sourceB628 + difference 0 5) sourceC628) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4841) := by
    have ha : (tripleCharges (sourceA628 + difference 5 0) (sourceB628 + difference 0 5) sourceC628) = raw10578 := by
      apply Matrix.ext; unfold tripleCharges sourceA628 sourceB628 sourceC628 difference raw10578; decide +kernel
    rw [ha]
    exact (canonical10578 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA628 + difference 5 1) (sourceB628 + difference 1 5) sourceC628) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5099) := by
    have ha : (tripleCharges (sourceA628 + difference 5 1) (sourceB628 + difference 1 5) sourceC628) = raw10579 := by
      apply Matrix.ext; unfold tripleCharges sourceA628 sourceB628 sourceC628 difference raw10579; decide +kernel
    rw [ha]
    exact (canonical10579 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA628 + difference 5 2) (sourceB628 + difference 2 5) sourceC628) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5099) := by
    have ha : (tripleCharges (sourceA628 + difference 5 2) (sourceB628 + difference 2 5) sourceC628) = raw10580 := by
      apply Matrix.ext; unfold tripleCharges sourceA628 sourceB628 sourceC628 difference raw10580; decide +kernel
    rw [ha]
    exact (canonical10580 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA628 + difference 5 3) (sourceB628 + difference 3 5) sourceC628) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5110) := by
    have ha : (tripleCharges (sourceA628 + difference 5 3) (sourceB628 + difference 3 5) sourceC628) = raw10581 := by
      apply Matrix.ext; unfold tripleCharges sourceA628 sourceB628 sourceC628 difference raw10581; decide +kernel
    rw [ha]
    exact (canonical10581 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA628 + difference 5 4) (sourceB628 + difference 4 5) sourceC628) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5272) := by
    have ha : (tripleCharges (sourceA628 + difference 5 4) (sourceB628 + difference 4 5) sourceC628) = raw10157 := by
      apply Matrix.ext; unfold tripleCharges sourceA628 sourceB628 sourceC628 difference raw10157; decide +kernel
    rw [ha]
    exact (canonical10157 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA628 sourceB628 sourceC628
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm628, Integer.Sparse.eval]
  linarith only [hs]

def sourceA629 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB629 : Charge := ![1, 0, 0, -1, -1, 1]
def sourceC629 : Charge := ![2, 0, 0, 1, 0, -3]
def sourceForm629 : Integer.Sparse Master := [(Sum.inr 4600, 2), (Sum.inr 4605, 1), (Sum.inr 4611, 1), (Sum.inr 4617, 1), (Sum.inr 4804, 2), (Sum.inr 4841, 1), (Sum.inr 4897, 1), (Sum.inr 5099, 2), (Sum.inr 5110, 1), (Sum.inr 5133, 2), (Sum.inr 5140, 2), (Sum.inr 5161, 2), (Sum.inr 5258, 2), (Sum.inr 5270, 2), (Sum.inr 5272, 2), (Sum.inr 5274, 1), (Sum.inr 5276, 1), (Sum.inr 5294, 1), (Sum.inr 5295, 1), (Sum.inr 5305, 1), (Sum.inr 5308, 1)]

theorem sourceEq629 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm629 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA629 + difference 0 1) (sourceB629 + difference 1 0) sourceC629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA629 + difference 0 1) (sourceB629 + difference 1 0) sourceC629) = raw10582 := by
      apply Matrix.ext; unfold tripleCharges sourceA629 sourceB629 sourceC629 difference raw10582; decide +kernel
    rw [ha]
    exact (canonical10582 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA629 + difference 0 2) (sourceB629 + difference 2 0) sourceC629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA629 + difference 0 2) (sourceB629 + difference 2 0) sourceC629) = raw10583 := by
      apply Matrix.ext; unfold tripleCharges sourceA629 sourceB629 sourceC629 difference raw10583; decide +kernel
    rw [ha]
    exact (canonical10583 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA629 + difference 0 3) (sourceB629 + difference 3 0) sourceC629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5274) := by
    have ha : (tripleCharges (sourceA629 + difference 0 3) (sourceB629 + difference 3 0) sourceC629) = raw10584 := by
      apply Matrix.ext; unfold tripleCharges sourceA629 sourceB629 sourceC629 difference raw10584; decide +kernel
    rw [ha]
    exact (canonical10584 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA629 + difference 0 4) (sourceB629 + difference 4 0) sourceC629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5308) := by
    have ha : (tripleCharges (sourceA629 + difference 0 4) (sourceB629 + difference 4 0) sourceC629) = raw10585 := by
      apply Matrix.ext; unfold tripleCharges sourceA629 sourceB629 sourceC629 difference raw10585; decide +kernel
    rw [ha]
    exact (canonical10585 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA629 + difference 0 5) (sourceB629 + difference 5 0) sourceC629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA629 + difference 0 5) (sourceB629 + difference 5 0) sourceC629) = raw10586 := by
      apply Matrix.ext; unfold tripleCharges sourceA629 sourceB629 sourceC629 difference raw10586; decide +kernel
    rw [ha]
    exact (canonical10586 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA629 + difference 1 0) (sourceB629 + difference 0 1) sourceC629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4600) := by
    have ha : (tripleCharges (sourceA629 + difference 1 0) (sourceB629 + difference 0 1) sourceC629) = raw10587 := by
      apply Matrix.ext; unfold tripleCharges sourceA629 sourceB629 sourceC629 difference raw10587; decide +kernel
    rw [ha]
    exact (canonical10587 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA629 + difference 1 2) (sourceB629 + difference 2 1) sourceC629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5133) := by
    have ha : (tripleCharges (sourceA629 + difference 1 2) (sourceB629 + difference 2 1) sourceC629) = raw10588 := by
      apply Matrix.ext; unfold tripleCharges sourceA629 sourceB629 sourceC629 difference raw10588; decide +kernel
    rw [ha]
    exact (canonical10588 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA629 + difference 1 3) (sourceB629 + difference 3 1) sourceC629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5099) := by
    have ha : (tripleCharges (sourceA629 + difference 1 3) (sourceB629 + difference 3 1) sourceC629) = raw10589 := by
      apply Matrix.ext; unfold tripleCharges sourceA629 sourceB629 sourceC629 difference raw10589; decide +kernel
    rw [ha]
    exact (canonical10589 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA629 + difference 1 4) (sourceB629 + difference 4 1) sourceC629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5272) := by
    have ha : (tripleCharges (sourceA629 + difference 1 4) (sourceB629 + difference 4 1) sourceC629) = raw10590 := by
      apply Matrix.ext; unfold tripleCharges sourceA629 sourceB629 sourceC629 difference raw10590; decide +kernel
    rw [ha]
    exact (canonical10590 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA629 + difference 1 5) (sourceB629 + difference 5 1) sourceC629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5270) := by
    have ha : (tripleCharges (sourceA629 + difference 1 5) (sourceB629 + difference 5 1) sourceC629) = raw10591 := by
      apply Matrix.ext; unfold tripleCharges sourceA629 sourceB629 sourceC629 difference raw10591; decide +kernel
    rw [ha]
    exact (canonical10591 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA629 + difference 2 0) (sourceB629 + difference 0 2) sourceC629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4600) := by
    have ha : (tripleCharges (sourceA629 + difference 2 0) (sourceB629 + difference 0 2) sourceC629) = raw10592 := by
      apply Matrix.ext; unfold tripleCharges sourceA629 sourceB629 sourceC629 difference raw10592; decide +kernel
    rw [ha]
    exact (canonical10592 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA629 + difference 2 1) (sourceB629 + difference 1 2) sourceC629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5133) := by
    have ha : (tripleCharges (sourceA629 + difference 2 1) (sourceB629 + difference 1 2) sourceC629) = raw10593 := by
      apply Matrix.ext; unfold tripleCharges sourceA629 sourceB629 sourceC629 difference raw10593; decide +kernel
    rw [ha]
    exact (canonical10593 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA629 + difference 2 3) (sourceB629 + difference 3 2) sourceC629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5099) := by
    have ha : (tripleCharges (sourceA629 + difference 2 3) (sourceB629 + difference 3 2) sourceC629) = raw10594 := by
      apply Matrix.ext; unfold tripleCharges sourceA629 sourceB629 sourceC629 difference raw10594; decide +kernel
    rw [ha]
    exact (canonical10594 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA629 + difference 2 4) (sourceB629 + difference 4 2) sourceC629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5272) := by
    have ha : (tripleCharges (sourceA629 + difference 2 4) (sourceB629 + difference 4 2) sourceC629) = raw10595 := by
      apply Matrix.ext; unfold tripleCharges sourceA629 sourceB629 sourceC629 difference raw10595; decide +kernel
    rw [ha]
    exact (canonical10595 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA629 + difference 2 5) (sourceB629 + difference 5 2) sourceC629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5270) := by
    have ha : (tripleCharges (sourceA629 + difference 2 5) (sourceB629 + difference 5 2) sourceC629) = raw10596 := by
      apply Matrix.ext; unfold tripleCharges sourceA629 sourceB629 sourceC629 difference raw10596; decide +kernel
    rw [ha]
    exact (canonical10596 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA629 + difference 3 0) (sourceB629 + difference 0 3) sourceC629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4617) := by
    have ha : (tripleCharges (sourceA629 + difference 3 0) (sourceB629 + difference 0 3) sourceC629) = raw10597 := by
      apply Matrix.ext; unfold tripleCharges sourceA629 sourceB629 sourceC629 difference raw10597; decide +kernel
    rw [ha]
    exact (canonical10597 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA629 + difference 3 1) (sourceB629 + difference 1 3) sourceC629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5161) := by
    have ha : (tripleCharges (sourceA629 + difference 3 1) (sourceB629 + difference 1 3) sourceC629) = raw10598 := by
      apply Matrix.ext; unfold tripleCharges sourceA629 sourceB629 sourceC629 difference raw10598; decide +kernel
    rw [ha]
    exact (canonical10598 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA629 + difference 3 2) (sourceB629 + difference 2 3) sourceC629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5161) := by
    have ha : (tripleCharges (sourceA629 + difference 3 2) (sourceB629 + difference 2 3) sourceC629) = raw10599 := by
      apply Matrix.ext; unfold tripleCharges sourceA629 sourceB629 sourceC629 difference raw10599; decide +kernel
    rw [ha]
    exact (canonical10599 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA629 + difference 3 4) (sourceB629 + difference 4 3) sourceC629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5305) := by
    have ha : (tripleCharges (sourceA629 + difference 3 4) (sourceB629 + difference 4 3) sourceC629) = raw10600 := by
      apply Matrix.ext; unfold tripleCharges sourceA629 sourceB629 sourceC629 difference raw10600; decide +kernel
    rw [ha]
    exact (canonical10600 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA629 + difference 3 5) (sourceB629 + difference 5 3) sourceC629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5295) := by
    have ha : (tripleCharges (sourceA629 + difference 3 5) (sourceB629 + difference 5 3) sourceC629) = raw10601 := by
      apply Matrix.ext; unfold tripleCharges sourceA629 sourceB629 sourceC629 difference raw10601; decide +kernel
    rw [ha]
    exact (canonical10601 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA629 + difference 4 0) (sourceB629 + difference 0 4) sourceC629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4611) := by
    have ha : (tripleCharges (sourceA629 + difference 4 0) (sourceB629 + difference 0 4) sourceC629) = raw10602 := by
      apply Matrix.ext; unfold tripleCharges sourceA629 sourceB629 sourceC629 difference raw10602; decide +kernel
    rw [ha]
    exact (canonical10602 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA629 + difference 4 1) (sourceB629 + difference 1 4) sourceC629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5140) := by
    have ha : (tripleCharges (sourceA629 + difference 4 1) (sourceB629 + difference 1 4) sourceC629) = raw10603 := by
      apply Matrix.ext; unfold tripleCharges sourceA629 sourceB629 sourceC629 difference raw10603; decide +kernel
    rw [ha]
    exact (canonical10603 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA629 + difference 4 2) (sourceB629 + difference 2 4) sourceC629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5140) := by
    have ha : (tripleCharges (sourceA629 + difference 4 2) (sourceB629 + difference 2 4) sourceC629) = raw10604 := by
      apply Matrix.ext; unfold tripleCharges sourceA629 sourceB629 sourceC629 difference raw10604; decide +kernel
    rw [ha]
    exact (canonical10604 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA629 + difference 4 3) (sourceB629 + difference 3 4) sourceC629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5110) := by
    have ha : (tripleCharges (sourceA629 + difference 4 3) (sourceB629 + difference 3 4) sourceC629) = raw10605 := by
      apply Matrix.ext; unfold tripleCharges sourceA629 sourceB629 sourceC629 difference raw10605; decide +kernel
    rw [ha]
    exact (canonical10605 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA629 + difference 4 5) (sourceB629 + difference 5 4) sourceC629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5276) := by
    have ha : (tripleCharges (sourceA629 + difference 4 5) (sourceB629 + difference 5 4) sourceC629) = raw10606 := by
      apply Matrix.ext; unfold tripleCharges sourceA629 sourceB629 sourceC629 difference raw10606; decide +kernel
    rw [ha]
    exact (canonical10606 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA629 + difference 5 0) (sourceB629 + difference 0 5) sourceC629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4605) := by
    have ha : (tripleCharges (sourceA629 + difference 5 0) (sourceB629 + difference 0 5) sourceC629) = raw10607 := by
      apply Matrix.ext; unfold tripleCharges sourceA629 sourceB629 sourceC629 difference raw10607; decide +kernel
    rw [ha]
    exact (canonical10607 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA629 + difference 5 1) (sourceB629 + difference 1 5) sourceC629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA629 + difference 5 1) (sourceB629 + difference 1 5) sourceC629) = raw10608 := by
      apply Matrix.ext; unfold tripleCharges sourceA629 sourceB629 sourceC629 difference raw10608; decide +kernel
    rw [ha]
    exact (canonical10608 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA629 + difference 5 2) (sourceB629 + difference 2 5) sourceC629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA629 + difference 5 2) (sourceB629 + difference 2 5) sourceC629) = raw10609 := by
      apply Matrix.ext; unfold tripleCharges sourceA629 sourceB629 sourceC629 difference raw10609; decide +kernel
    rw [ha]
    exact (canonical10609 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA629 + difference 5 3) (sourceB629 + difference 3 5) sourceC629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4841) := by
    have ha : (tripleCharges (sourceA629 + difference 5 3) (sourceB629 + difference 3 5) sourceC629) = raw10610 := by
      apply Matrix.ext; unfold tripleCharges sourceA629 sourceB629 sourceC629 difference raw10610; decide +kernel
    rw [ha]
    exact (canonical10610 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA629 + difference 5 4) (sourceB629 + difference 4 5) sourceC629) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4897) := by
    have ha : (tripleCharges (sourceA629 + difference 5 4) (sourceB629 + difference 4 5) sourceC629) = raw10611 := by
      apply Matrix.ext; unfold tripleCharges sourceA629 sourceB629 sourceC629 difference raw10611; decide +kernel
    rw [ha]
    exact (canonical10611 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA629 sourceB629 sourceC629
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm629, Integer.Sparse.eval]
  linarith only [hs]

def sourceA630 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB630 : Charge := ![1, 0, 0, -1, -1, 1]
def sourceC630 : Charge := ![2, 0, 0, 1, 0, -3]
def sourceForm630 : Integer.Sparse Master := [(Sum.inr 1270, 2), (Sum.inr 1271, 1), (Sum.inr 1273, 1), (Sum.inr 1306, 1), (Sum.inr 2754, 2), (Sum.inr 2768, 1), (Sum.inr 2769, 1), (Sum.inr 2777, 1), (Sum.inr 2940, 2), (Sum.inr 2941, 2), (Sum.inr 2942, 2), (Sum.inr 2964, 2), (Sum.inr 3003, 2), (Sum.inr 3004, 1), (Sum.inr 3005, 1), (Sum.inr 3089, 2), (Sum.inr 3112, 1), (Sum.inr 3113, 2), (Sum.inr 3114, 1), (Sum.inr 3124, 1), (Sum.inr 3125, 1)]

theorem sourceEq630 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm630 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA630 + difference 0 1) (sourceB630 + difference 1 0) sourceC630) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3089) := by
    have ha : (tripleCharges (sourceA630 + difference 0 1) (sourceB630 + difference 1 0) sourceC630) = raw10612 := by
      apply Matrix.ext; unfold tripleCharges sourceA630 sourceB630 sourceC630 difference raw10612; decide +kernel
    rw [ha]
    exact (canonical10612 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA630 + difference 0 2) (sourceB630 + difference 2 0) sourceC630) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3089) := by
    have ha : (tripleCharges (sourceA630 + difference 0 2) (sourceB630 + difference 2 0) sourceC630) = raw10613 := by
      apply Matrix.ext; unfold tripleCharges sourceA630 sourceB630 sourceC630 difference raw10613; decide +kernel
    rw [ha]
    exact (canonical10613 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA630 + difference 0 3) (sourceB630 + difference 3 0) sourceC630) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3112) := by
    have ha : (tripleCharges (sourceA630 + difference 0 3) (sourceB630 + difference 3 0) sourceC630) = raw10614 := by
      apply Matrix.ext; unfold tripleCharges sourceA630 sourceB630 sourceC630 difference raw10614; decide +kernel
    rw [ha]
    exact (canonical10614 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA630 + difference 0 4) (sourceB630 + difference 4 0) sourceC630) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3124) := by
    have ha : (tripleCharges (sourceA630 + difference 0 4) (sourceB630 + difference 4 0) sourceC630) = raw10615 := by
      apply Matrix.ext; unfold tripleCharges sourceA630 sourceB630 sourceC630 difference raw10615; decide +kernel
    rw [ha]
    exact (canonical10615 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA630 + difference 0 5) (sourceB630 + difference 5 0) sourceC630) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2768) := by
    have ha : (tripleCharges (sourceA630 + difference 0 5) (sourceB630 + difference 5 0) sourceC630) = raw10616 := by
      apply Matrix.ext; unfold tripleCharges sourceA630 sourceB630 sourceC630 difference raw10616; decide +kernel
    rw [ha]
    exact (canonical10616 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA630 + difference 1 0) (sourceB630 + difference 0 1) sourceC630) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1270) := by
    have ha : (tripleCharges (sourceA630 + difference 1 0) (sourceB630 + difference 0 1) sourceC630) = raw10617 := by
      apply Matrix.ext; unfold tripleCharges sourceA630 sourceB630 sourceC630 difference raw10617; decide +kernel
    rw [ha]
    exact (canonical10617 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA630 + difference 1 2) (sourceB630 + difference 2 1) sourceC630) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2940) := by
    have ha : (tripleCharges (sourceA630 + difference 1 2) (sourceB630 + difference 2 1) sourceC630) = raw10618 := by
      apply Matrix.ext; unfold tripleCharges sourceA630 sourceB630 sourceC630 difference raw10618; decide +kernel
    rw [ha]
    exact (canonical10618 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA630 + difference 1 3) (sourceB630 + difference 3 1) sourceC630) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3003) := by
    have ha : (tripleCharges (sourceA630 + difference 1 3) (sourceB630 + difference 3 1) sourceC630) = raw10619 := by
      apply Matrix.ext; unfold tripleCharges sourceA630 sourceB630 sourceC630 difference raw10619; decide +kernel
    rw [ha]
    exact (canonical10619 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA630 + difference 1 4) (sourceB630 + difference 4 1) sourceC630) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3113) := by
    have ha : (tripleCharges (sourceA630 + difference 1 4) (sourceB630 + difference 4 1) sourceC630) = raw10620 := by
      apply Matrix.ext; unfold tripleCharges sourceA630 sourceB630 sourceC630 difference raw10620; decide +kernel
    rw [ha]
    exact (canonical10620 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA630 + difference 1 5) (sourceB630 + difference 5 1) sourceC630) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2754) := by
    have ha : (tripleCharges (sourceA630 + difference 1 5) (sourceB630 + difference 5 1) sourceC630) = raw10621 := by
      apply Matrix.ext; unfold tripleCharges sourceA630 sourceB630 sourceC630 difference raw10621; decide +kernel
    rw [ha]
    exact (canonical10621 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA630 + difference 2 0) (sourceB630 + difference 0 2) sourceC630) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1270) := by
    have ha : (tripleCharges (sourceA630 + difference 2 0) (sourceB630 + difference 0 2) sourceC630) = raw10622 := by
      apply Matrix.ext; unfold tripleCharges sourceA630 sourceB630 sourceC630 difference raw10622; decide +kernel
    rw [ha]
    exact (canonical10622 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA630 + difference 2 1) (sourceB630 + difference 1 2) sourceC630) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2940) := by
    have ha : (tripleCharges (sourceA630 + difference 2 1) (sourceB630 + difference 1 2) sourceC630) = raw10623 := by
      apply Matrix.ext; unfold tripleCharges sourceA630 sourceB630 sourceC630 difference raw10623; decide +kernel
    rw [ha]
    exact (canonical10623 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA630 + difference 2 3) (sourceB630 + difference 3 2) sourceC630) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3003) := by
    have ha : (tripleCharges (sourceA630 + difference 2 3) (sourceB630 + difference 3 2) sourceC630) = raw10624 := by
      apply Matrix.ext; unfold tripleCharges sourceA630 sourceB630 sourceC630 difference raw10624; decide +kernel
    rw [ha]
    exact (canonical10624 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA630 + difference 2 4) (sourceB630 + difference 4 2) sourceC630) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3113) := by
    have ha : (tripleCharges (sourceA630 + difference 2 4) (sourceB630 + difference 4 2) sourceC630) = raw10625 := by
      apply Matrix.ext; unfold tripleCharges sourceA630 sourceB630 sourceC630 difference raw10625; decide +kernel
    rw [ha]
    exact (canonical10625 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA630 + difference 2 5) (sourceB630 + difference 5 2) sourceC630) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2754) := by
    have ha : (tripleCharges (sourceA630 + difference 2 5) (sourceB630 + difference 5 2) sourceC630) = raw10626 := by
      apply Matrix.ext; unfold tripleCharges sourceA630 sourceB630 sourceC630 difference raw10626; decide +kernel
    rw [ha]
    exact (canonical10626 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA630 + difference 3 0) (sourceB630 + difference 0 3) sourceC630) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1306) := by
    have ha : (tripleCharges (sourceA630 + difference 3 0) (sourceB630 + difference 0 3) sourceC630) = raw10627 := by
      apply Matrix.ext; unfold tripleCharges sourceA630 sourceB630 sourceC630 difference raw10627; decide +kernel
    rw [ha]
    exact (canonical10627 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA630 + difference 3 1) (sourceB630 + difference 1 3) sourceC630) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2964) := by
    have ha : (tripleCharges (sourceA630 + difference 3 1) (sourceB630 + difference 1 3) sourceC630) = raw10628 := by
      apply Matrix.ext; unfold tripleCharges sourceA630 sourceB630 sourceC630 difference raw10628; decide +kernel
    rw [ha]
    exact (canonical10628 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA630 + difference 3 2) (sourceB630 + difference 2 3) sourceC630) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2964) := by
    have ha : (tripleCharges (sourceA630 + difference 3 2) (sourceB630 + difference 2 3) sourceC630) = raw10629 := by
      apply Matrix.ext; unfold tripleCharges sourceA630 sourceB630 sourceC630 difference raw10629; decide +kernel
    rw [ha]
    exact (canonical10629 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA630 + difference 3 4) (sourceB630 + difference 4 3) sourceC630) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3125) := by
    have ha : (tripleCharges (sourceA630 + difference 3 4) (sourceB630 + difference 4 3) sourceC630) = raw10630 := by
      apply Matrix.ext; unfold tripleCharges sourceA630 sourceB630 sourceC630 difference raw10630; decide +kernel
    rw [ha]
    exact (canonical10630 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA630 + difference 3 5) (sourceB630 + difference 5 3) sourceC630) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2769) := by
    have ha : (tripleCharges (sourceA630 + difference 3 5) (sourceB630 + difference 5 3) sourceC630) = raw10631 := by
      apply Matrix.ext; unfold tripleCharges sourceA630 sourceB630 sourceC630 difference raw10631; decide +kernel
    rw [ha]
    exact (canonical10631 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA630 + difference 4 0) (sourceB630 + difference 0 4) sourceC630) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1273) := by
    have ha : (tripleCharges (sourceA630 + difference 4 0) (sourceB630 + difference 0 4) sourceC630) = raw10632 := by
      apply Matrix.ext; unfold tripleCharges sourceA630 sourceB630 sourceC630 difference raw10632; decide +kernel
    rw [ha]
    exact (canonical10632 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA630 + difference 4 1) (sourceB630 + difference 1 4) sourceC630) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2942) := by
    have ha : (tripleCharges (sourceA630 + difference 4 1) (sourceB630 + difference 1 4) sourceC630) = raw10633 := by
      apply Matrix.ext; unfold tripleCharges sourceA630 sourceB630 sourceC630 difference raw10633; decide +kernel
    rw [ha]
    exact (canonical10633 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA630 + difference 4 2) (sourceB630 + difference 2 4) sourceC630) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2942) := by
    have ha : (tripleCharges (sourceA630 + difference 4 2) (sourceB630 + difference 2 4) sourceC630) = raw10634 := by
      apply Matrix.ext; unfold tripleCharges sourceA630 sourceB630 sourceC630 difference raw10634; decide +kernel
    rw [ha]
    exact (canonical10634 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA630 + difference 4 3) (sourceB630 + difference 3 4) sourceC630) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3005) := by
    have ha : (tripleCharges (sourceA630 + difference 4 3) (sourceB630 + difference 3 4) sourceC630) = raw10635 := by
      apply Matrix.ext; unfold tripleCharges sourceA630 sourceB630 sourceC630 difference raw10635; decide +kernel
    rw [ha]
    exact (canonical10635 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA630 + difference 4 5) (sourceB630 + difference 5 4) sourceC630) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2777) := by
    have ha : (tripleCharges (sourceA630 + difference 4 5) (sourceB630 + difference 5 4) sourceC630) = raw10636 := by
      apply Matrix.ext; unfold tripleCharges sourceA630 sourceB630 sourceC630 difference raw10636; decide +kernel
    rw [ha]
    exact (canonical10636 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA630 + difference 5 0) (sourceB630 + difference 0 5) sourceC630) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1271) := by
    have ha : (tripleCharges (sourceA630 + difference 5 0) (sourceB630 + difference 0 5) sourceC630) = raw10637 := by
      apply Matrix.ext; unfold tripleCharges sourceA630 sourceB630 sourceC630 difference raw10637; decide +kernel
    rw [ha]
    exact (canonical10637 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA630 + difference 5 1) (sourceB630 + difference 1 5) sourceC630) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2941) := by
    have ha : (tripleCharges (sourceA630 + difference 5 1) (sourceB630 + difference 1 5) sourceC630) = raw10638 := by
      apply Matrix.ext; unfold tripleCharges sourceA630 sourceB630 sourceC630 difference raw10638; decide +kernel
    rw [ha]
    exact (canonical10638 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA630 + difference 5 2) (sourceB630 + difference 2 5) sourceC630) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2941) := by
    have ha : (tripleCharges (sourceA630 + difference 5 2) (sourceB630 + difference 2 5) sourceC630) = raw10639 := by
      apply Matrix.ext; unfold tripleCharges sourceA630 sourceB630 sourceC630 difference raw10639; decide +kernel
    rw [ha]
    exact (canonical10639 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA630 + difference 5 3) (sourceB630 + difference 3 5) sourceC630) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3004) := by
    have ha : (tripleCharges (sourceA630 + difference 5 3) (sourceB630 + difference 3 5) sourceC630) = raw10640 := by
      apply Matrix.ext; unfold tripleCharges sourceA630 sourceB630 sourceC630 difference raw10640; decide +kernel
    rw [ha]
    exact (canonical10640 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA630 + difference 5 4) (sourceB630 + difference 4 5) sourceC630) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3114) := by
    have ha : (tripleCharges (sourceA630 + difference 5 4) (sourceB630 + difference 4 5) sourceC630) = raw10641 := by
      apply Matrix.ext; unfold tripleCharges sourceA630 sourceB630 sourceC630 difference raw10641; decide +kernel
    rw [ha]
    exact (canonical10641 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA630 sourceB630 sourceC630
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm630, Integer.Sparse.eval]
  linarith only [hs]

def sourceA631 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB631 : Charge := ![1, 0, 0, -1, -1, 1]
def sourceC631 : Charge := ![2, 0, 0, 1, 0, -3]
def sourceForm631 : Integer.Sparse Master := [(Sum.inr 2203, 2), (Sum.inr 2226, 1), (Sum.inr 2228, 1), (Sum.inr 2292, 1), (Sum.inr 2670, 2), (Sum.inr 2683, 1), (Sum.inr 2685, 1), (Sum.inr 2693, 2), (Sum.inr 2702, 2), (Sum.inr 2704, 2), (Sum.inr 2719, 2), (Sum.inr 2722, 2), (Sum.inr 2737, 1), (Sum.inr 2740, 2), (Sum.inr 2742, 1), (Sum.inr 2783, 1), (Sum.inr 2786, 1), (Sum.inr 3052, 1), (Sum.inr 3075, 2), (Sum.inr 3098, 1), (Sum.inr 3101, 1)]

theorem sourceEq631 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm631 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA631 + difference 0 1) (sourceB631 + difference 1 0) sourceC631) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA631 + difference 0 1) (sourceB631 + difference 1 0) sourceC631) = raw10642 := by
      apply Matrix.ext; unfold tripleCharges sourceA631 sourceB631 sourceC631 difference raw10642; decide +kernel
    rw [ha]
    exact (canonical10642 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA631 + difference 0 2) (sourceB631 + difference 2 0) sourceC631) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA631 + difference 0 2) (sourceB631 + difference 2 0) sourceC631) = raw10643 := by
      apply Matrix.ext; unfold tripleCharges sourceA631 sourceB631 sourceC631 difference raw10643; decide +kernel
    rw [ha]
    exact (canonical10643 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA631 + difference 0 3) (sourceB631 + difference 3 0) sourceC631) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2742) := by
    have ha : (tripleCharges (sourceA631 + difference 0 3) (sourceB631 + difference 3 0) sourceC631) = raw10644 := by
      apply Matrix.ext; unfold tripleCharges sourceA631 sourceB631 sourceC631 difference raw10644; decide +kernel
    rw [ha]
    exact (canonical10644 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA631 + difference 0 4) (sourceB631 + difference 4 0) sourceC631) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2786) := by
    have ha : (tripleCharges (sourceA631 + difference 0 4) (sourceB631 + difference 4 0) sourceC631) = raw10645 := by
      apply Matrix.ext; unfold tripleCharges sourceA631 sourceB631 sourceC631 difference raw10645; decide +kernel
    rw [ha]
    exact (canonical10645 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA631 + difference 0 5) (sourceB631 + difference 5 0) sourceC631) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3101) := by
    have ha : (tripleCharges (sourceA631 + difference 0 5) (sourceB631 + difference 5 0) sourceC631) = raw10646 := by
      apply Matrix.ext; unfold tripleCharges sourceA631 sourceB631 sourceC631 difference raw10646; decide +kernel
    rw [ha]
    exact (canonical10646 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA631 + difference 1 0) (sourceB631 + difference 0 1) sourceC631) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2702) := by
    have ha : (tripleCharges (sourceA631 + difference 1 0) (sourceB631 + difference 0 1) sourceC631) = raw10647 := by
      apply Matrix.ext; unfold tripleCharges sourceA631 sourceB631 sourceC631 difference raw10647; decide +kernel
    rw [ha]
    exact (canonical10647 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA631 + difference 1 2) (sourceB631 + difference 2 1) sourceC631) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2693) := by
    have ha : (tripleCharges (sourceA631 + difference 1 2) (sourceB631 + difference 2 1) sourceC631) = raw10648 := by
      apply Matrix.ext; unfold tripleCharges sourceA631 sourceB631 sourceC631 difference raw10648; decide +kernel
    rw [ha]
    exact (canonical10648 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA631 + difference 1 3) (sourceB631 + difference 3 1) sourceC631) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2704) := by
    have ha : (tripleCharges (sourceA631 + difference 1 3) (sourceB631 + difference 3 1) sourceC631) = raw10649 := by
      apply Matrix.ext; unfold tripleCharges sourceA631 sourceB631 sourceC631 difference raw10649; decide +kernel
    rw [ha]
    exact (canonical10649 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA631 + difference 1 4) (sourceB631 + difference 4 1) sourceC631) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2740) := by
    have ha : (tripleCharges (sourceA631 + difference 1 4) (sourceB631 + difference 4 1) sourceC631) = raw10650 := by
      apply Matrix.ext; unfold tripleCharges sourceA631 sourceB631 sourceC631 difference raw10650; decide +kernel
    rw [ha]
    exact (canonical10650 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA631 + difference 1 5) (sourceB631 + difference 5 1) sourceC631) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3075) := by
    have ha : (tripleCharges (sourceA631 + difference 1 5) (sourceB631 + difference 5 1) sourceC631) = raw10651 := by
      apply Matrix.ext; unfold tripleCharges sourceA631 sourceB631 sourceC631 difference raw10651; decide +kernel
    rw [ha]
    exact (canonical10651 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA631 + difference 2 0) (sourceB631 + difference 0 2) sourceC631) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2702) := by
    have ha : (tripleCharges (sourceA631 + difference 2 0) (sourceB631 + difference 0 2) sourceC631) = raw10652 := by
      apply Matrix.ext; unfold tripleCharges sourceA631 sourceB631 sourceC631 difference raw10652; decide +kernel
    rw [ha]
    exact (canonical10652 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA631 + difference 2 1) (sourceB631 + difference 1 2) sourceC631) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2693) := by
    have ha : (tripleCharges (sourceA631 + difference 2 1) (sourceB631 + difference 1 2) sourceC631) = raw10653 := by
      apply Matrix.ext; unfold tripleCharges sourceA631 sourceB631 sourceC631 difference raw10653; decide +kernel
    rw [ha]
    exact (canonical10653 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA631 + difference 2 3) (sourceB631 + difference 3 2) sourceC631) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2704) := by
    have ha : (tripleCharges (sourceA631 + difference 2 3) (sourceB631 + difference 3 2) sourceC631) = raw10654 := by
      apply Matrix.ext; unfold tripleCharges sourceA631 sourceB631 sourceC631 difference raw10654; decide +kernel
    rw [ha]
    exact (canonical10654 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA631 + difference 2 4) (sourceB631 + difference 4 2) sourceC631) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2740) := by
    have ha : (tripleCharges (sourceA631 + difference 2 4) (sourceB631 + difference 4 2) sourceC631) = raw10655 := by
      apply Matrix.ext; unfold tripleCharges sourceA631 sourceB631 sourceC631 difference raw10655; decide +kernel
    rw [ha]
    exact (canonical10655 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA631 + difference 2 5) (sourceB631 + difference 5 2) sourceC631) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3075) := by
    have ha : (tripleCharges (sourceA631 + difference 2 5) (sourceB631 + difference 5 2) sourceC631) = raw10656 := by
      apply Matrix.ext; unfold tripleCharges sourceA631 sourceB631 sourceC631 difference raw10656; decide +kernel
    rw [ha]
    exact (canonical10656 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA631 + difference 3 0) (sourceB631 + difference 0 3) sourceC631) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2737) := by
    have ha : (tripleCharges (sourceA631 + difference 3 0) (sourceB631 + difference 0 3) sourceC631) = raw10657 := by
      apply Matrix.ext; unfold tripleCharges sourceA631 sourceB631 sourceC631 difference raw10657; decide +kernel
    rw [ha]
    exact (canonical10657 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA631 + difference 3 1) (sourceB631 + difference 1 3) sourceC631) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2719) := by
    have ha : (tripleCharges (sourceA631 + difference 3 1) (sourceB631 + difference 1 3) sourceC631) = raw10658 := by
      apply Matrix.ext; unfold tripleCharges sourceA631 sourceB631 sourceC631 difference raw10658; decide +kernel
    rw [ha]
    exact (canonical10658 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA631 + difference 3 2) (sourceB631 + difference 2 3) sourceC631) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2719) := by
    have ha : (tripleCharges (sourceA631 + difference 3 2) (sourceB631 + difference 2 3) sourceC631) = raw10659 := by
      apply Matrix.ext; unfold tripleCharges sourceA631 sourceB631 sourceC631 difference raw10659; decide +kernel
    rw [ha]
    exact (canonical10659 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA631 + difference 3 4) (sourceB631 + difference 4 3) sourceC631) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2783) := by
    have ha : (tripleCharges (sourceA631 + difference 3 4) (sourceB631 + difference 4 3) sourceC631) = raw10660 := by
      apply Matrix.ext; unfold tripleCharges sourceA631 sourceB631 sourceC631 difference raw10660; decide +kernel
    rw [ha]
    exact (canonical10660 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA631 + difference 3 5) (sourceB631 + difference 5 3) sourceC631) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3098) := by
    have ha : (tripleCharges (sourceA631 + difference 3 5) (sourceB631 + difference 5 3) sourceC631) = raw10661 := by
      apply Matrix.ext; unfold tripleCharges sourceA631 sourceB631 sourceC631 difference raw10661; decide +kernel
    rw [ha]
    exact (canonical10661 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA631 + difference 4 0) (sourceB631 + difference 0 4) sourceC631) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2683) := by
    have ha : (tripleCharges (sourceA631 + difference 4 0) (sourceB631 + difference 0 4) sourceC631) = raw10662 := by
      apply Matrix.ext; unfold tripleCharges sourceA631 sourceB631 sourceC631 difference raw10662; decide +kernel
    rw [ha]
    exact (canonical10662 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA631 + difference 4 1) (sourceB631 + difference 1 4) sourceC631) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2670) := by
    have ha : (tripleCharges (sourceA631 + difference 4 1) (sourceB631 + difference 1 4) sourceC631) = raw10663 := by
      apply Matrix.ext; unfold tripleCharges sourceA631 sourceB631 sourceC631 difference raw10663; decide +kernel
    rw [ha]
    exact (canonical10663 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA631 + difference 4 2) (sourceB631 + difference 2 4) sourceC631) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2670) := by
    have ha : (tripleCharges (sourceA631 + difference 4 2) (sourceB631 + difference 2 4) sourceC631) = raw10664 := by
      apply Matrix.ext; unfold tripleCharges sourceA631 sourceB631 sourceC631 difference raw10664; decide +kernel
    rw [ha]
    exact (canonical10664 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA631 + difference 4 3) (sourceB631 + difference 3 4) sourceC631) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2685) := by
    have ha : (tripleCharges (sourceA631 + difference 4 3) (sourceB631 + difference 3 4) sourceC631) = raw10665 := by
      apply Matrix.ext; unfold tripleCharges sourceA631 sourceB631 sourceC631 difference raw10665; decide +kernel
    rw [ha]
    exact (canonical10665 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA631 + difference 4 5) (sourceB631 + difference 5 4) sourceC631) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3052) := by
    have ha : (tripleCharges (sourceA631 + difference 4 5) (sourceB631 + difference 5 4) sourceC631) = raw10666 := by
      apply Matrix.ext; unfold tripleCharges sourceA631 sourceB631 sourceC631 difference raw10666; decide +kernel
    rw [ha]
    exact (canonical10666 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA631 + difference 5 0) (sourceB631 + difference 0 5) sourceC631) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2226) := by
    have ha : (tripleCharges (sourceA631 + difference 5 0) (sourceB631 + difference 0 5) sourceC631) = raw10667 := by
      apply Matrix.ext; unfold tripleCharges sourceA631 sourceB631 sourceC631 difference raw10667; decide +kernel
    rw [ha]
    exact (canonical10667 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA631 + difference 5 1) (sourceB631 + difference 1 5) sourceC631) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2203) := by
    have ha : (tripleCharges (sourceA631 + difference 5 1) (sourceB631 + difference 1 5) sourceC631) = raw10668 := by
      apply Matrix.ext; unfold tripleCharges sourceA631 sourceB631 sourceC631 difference raw10668; decide +kernel
    rw [ha]
    exact (canonical10668 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA631 + difference 5 2) (sourceB631 + difference 2 5) sourceC631) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2203) := by
    have ha : (tripleCharges (sourceA631 + difference 5 2) (sourceB631 + difference 2 5) sourceC631) = raw10669 := by
      apply Matrix.ext; unfold tripleCharges sourceA631 sourceB631 sourceC631 difference raw10669; decide +kernel
    rw [ha]
    exact (canonical10669 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA631 + difference 5 3) (sourceB631 + difference 3 5) sourceC631) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2228) := by
    have ha : (tripleCharges (sourceA631 + difference 5 3) (sourceB631 + difference 3 5) sourceC631) = raw10670 := by
      apply Matrix.ext; unfold tripleCharges sourceA631 sourceB631 sourceC631 difference raw10670; decide +kernel
    rw [ha]
    exact (canonical10670 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA631 + difference 5 4) (sourceB631 + difference 4 5) sourceC631) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2292) := by
    have ha : (tripleCharges (sourceA631 + difference 5 4) (sourceB631 + difference 4 5) sourceC631) = raw10671 := by
      apply Matrix.ext; unfold tripleCharges sourceA631 sourceB631 sourceC631 difference raw10671; decide +kernel
    rw [ha]
    exact (canonical10671 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA631 sourceB631 sourceC631
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm631, Integer.Sparse.eval]
  linarith only [hs]

def sourceA632 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB632 : Charge := ![2, 0, 0, 1, 0, -3]
def sourceC632 : Charge := ![1, 0, 0, -1, -1, 1]
def sourceForm632 : Integer.Sparse Master := [(Sum.inr 4418, 4), (Sum.inr 4421, 1), (Sum.inr 4431, 2), (Sum.inr 4496, 2), (Sum.inr 5014, 4), (Sum.inr 5023, 1), (Sum.inr 5055, 2), (Sum.inr 5099, 4), (Sum.inr 5271, 4), (Sum.inr 5272, 1), (Sum.inr 5275, 2), (Sum.inr 5306, 2), (Sum.inr 5492, 1)]

theorem sourceEq632 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm632 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA632 + difference 0 1) (sourceB632 + difference 1 0) sourceC632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA632 + difference 0 1) (sourceB632 + difference 1 0) sourceC632) = raw10672 := by
      apply Matrix.ext; unfold tripleCharges sourceA632 sourceB632 sourceC632 difference raw10672; decide +kernel
    rw [ha]
    exact (canonical10672 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA632 + difference 0 2) (sourceB632 + difference 2 0) sourceC632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA632 + difference 0 2) (sourceB632 + difference 2 0) sourceC632) = raw10673 := by
      apply Matrix.ext; unfold tripleCharges sourceA632 sourceB632 sourceC632 difference raw10673; decide +kernel
    rw [ha]
    exact (canonical10673 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA632 + difference 0 3) (sourceB632 + difference 3 0) sourceC632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5275) := by
    have ha : (tripleCharges (sourceA632 + difference 0 3) (sourceB632 + difference 3 0) sourceC632) = raw10674 := by
      apply Matrix.ext; unfold tripleCharges sourceA632 sourceB632 sourceC632 difference raw10674; decide +kernel
    rw [ha]
    exact (canonical10674 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA632 + difference 0 4) (sourceB632 + difference 4 0) sourceC632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5306) := by
    have ha : (tripleCharges (sourceA632 + difference 0 4) (sourceB632 + difference 4 0) sourceC632) = raw10675 := by
      apply Matrix.ext; unfold tripleCharges sourceA632 sourceB632 sourceC632 difference raw10675; decide +kernel
    rw [ha]
    exact (canonical10675 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA632 + difference 0 5) (sourceB632 + difference 5 0) sourceC632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5492) := by
    have ha : (tripleCharges (sourceA632 + difference 0 5) (sourceB632 + difference 5 0) sourceC632) = raw10676 := by
      apply Matrix.ext; unfold tripleCharges sourceA632 sourceB632 sourceC632 difference raw10676; decide +kernel
    rw [ha]
    exact (canonical10676 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA632 + difference 1 0) (sourceB632 + difference 0 1) sourceC632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4418) := by
    have ha : (tripleCharges (sourceA632 + difference 1 0) (sourceB632 + difference 0 1) sourceC632) = raw10677 := by
      apply Matrix.ext; unfold tripleCharges sourceA632 sourceB632 sourceC632 difference raw10677; decide +kernel
    rw [ha]
    exact (canonical10677 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA632 + difference 1 2) (sourceB632 + difference 2 1) sourceC632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5055) := by
    have ha : (tripleCharges (sourceA632 + difference 1 2) (sourceB632 + difference 2 1) sourceC632) = raw10678 := by
      apply Matrix.ext; unfold tripleCharges sourceA632 sourceB632 sourceC632 difference raw10678; decide +kernel
    rw [ha]
    exact (canonical10678 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA632 + difference 1 3) (sourceB632 + difference 3 1) sourceC632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5014) := by
    have ha : (tripleCharges (sourceA632 + difference 1 3) (sourceB632 + difference 3 1) sourceC632) = raw10679 := by
      apply Matrix.ext; unfold tripleCharges sourceA632 sourceB632 sourceC632 difference raw10679; decide +kernel
    rw [ha]
    exact (canonical10679 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA632 + difference 1 4) (sourceB632 + difference 4 1) sourceC632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5099) := by
    have ha : (tripleCharges (sourceA632 + difference 1 4) (sourceB632 + difference 4 1) sourceC632) = raw10680 := by
      apply Matrix.ext; unfold tripleCharges sourceA632 sourceB632 sourceC632 difference raw10680; decide +kernel
    rw [ha]
    exact (canonical10680 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA632 + difference 1 5) (sourceB632 + difference 5 1) sourceC632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA632 + difference 1 5) (sourceB632 + difference 5 1) sourceC632) = raw10681 := by
      apply Matrix.ext; unfold tripleCharges sourceA632 sourceB632 sourceC632 difference raw10681; decide +kernel
    rw [ha]
    exact (canonical10681 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA632 + difference 2 0) (sourceB632 + difference 0 2) sourceC632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4418) := by
    have ha : (tripleCharges (sourceA632 + difference 2 0) (sourceB632 + difference 0 2) sourceC632) = raw10682 := by
      apply Matrix.ext; unfold tripleCharges sourceA632 sourceB632 sourceC632 difference raw10682; decide +kernel
    rw [ha]
    exact (canonical10682 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA632 + difference 2 1) (sourceB632 + difference 1 2) sourceC632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5055) := by
    have ha : (tripleCharges (sourceA632 + difference 2 1) (sourceB632 + difference 1 2) sourceC632) = raw10683 := by
      apply Matrix.ext; unfold tripleCharges sourceA632 sourceB632 sourceC632 difference raw10683; decide +kernel
    rw [ha]
    exact (canonical10683 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA632 + difference 2 3) (sourceB632 + difference 3 2) sourceC632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5014) := by
    have ha : (tripleCharges (sourceA632 + difference 2 3) (sourceB632 + difference 3 2) sourceC632) = raw10684 := by
      apply Matrix.ext; unfold tripleCharges sourceA632 sourceB632 sourceC632 difference raw10684; decide +kernel
    rw [ha]
    exact (canonical10684 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA632 + difference 2 4) (sourceB632 + difference 4 2) sourceC632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5099) := by
    have ha : (tripleCharges (sourceA632 + difference 2 4) (sourceB632 + difference 4 2) sourceC632) = raw10685 := by
      apply Matrix.ext; unfold tripleCharges sourceA632 sourceB632 sourceC632 difference raw10685; decide +kernel
    rw [ha]
    exact (canonical10685 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA632 + difference 2 5) (sourceB632 + difference 5 2) sourceC632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA632 + difference 2 5) (sourceB632 + difference 5 2) sourceC632) = raw10686 := by
      apply Matrix.ext; unfold tripleCharges sourceA632 sourceB632 sourceC632 difference raw10686; decide +kernel
    rw [ha]
    exact (canonical10686 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA632 + difference 3 0) (sourceB632 + difference 0 3) sourceC632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4496) := by
    have ha : (tripleCharges (sourceA632 + difference 3 0) (sourceB632 + difference 0 3) sourceC632) = raw10687 := by
      apply Matrix.ext; unfold tripleCharges sourceA632 sourceB632 sourceC632 difference raw10687; decide +kernel
    rw [ha]
    exact (canonical10687 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA632 + difference 3 1) (sourceB632 + difference 1 3) sourceC632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5099) := by
    have ha : (tripleCharges (sourceA632 + difference 3 1) (sourceB632 + difference 1 3) sourceC632) = raw10688 := by
      apply Matrix.ext; unfold tripleCharges sourceA632 sourceB632 sourceC632 difference raw10688; decide +kernel
    rw [ha]
    exact (canonical10688 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA632 + difference 3 2) (sourceB632 + difference 2 3) sourceC632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5099) := by
    have ha : (tripleCharges (sourceA632 + difference 3 2) (sourceB632 + difference 2 3) sourceC632) = raw10689 := by
      apply Matrix.ext; unfold tripleCharges sourceA632 sourceB632 sourceC632 difference raw10689; decide +kernel
    rw [ha]
    exact (canonical10689 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA632 + difference 3 4) (sourceB632 + difference 4 3) sourceC632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5272) := by
    have ha : (tripleCharges (sourceA632 + difference 3 4) (sourceB632 + difference 4 3) sourceC632) = raw10690 := by
      apply Matrix.ext; unfold tripleCharges sourceA632 sourceB632 sourceC632 difference raw10690; decide +kernel
    rw [ha]
    exact (canonical10690 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA632 + difference 3 5) (sourceB632 + difference 5 3) sourceC632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5306) := by
    have ha : (tripleCharges (sourceA632 + difference 3 5) (sourceB632 + difference 5 3) sourceC632) = raw10691 := by
      apply Matrix.ext; unfold tripleCharges sourceA632 sourceB632 sourceC632 difference raw10691; decide +kernel
    rw [ha]
    exact (canonical10691 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA632 + difference 4 0) (sourceB632 + difference 0 4) sourceC632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4431) := by
    have ha : (tripleCharges (sourceA632 + difference 4 0) (sourceB632 + difference 0 4) sourceC632) = raw10692 := by
      apply Matrix.ext; unfold tripleCharges sourceA632 sourceB632 sourceC632 difference raw10692; decide +kernel
    rw [ha]
    exact (canonical10692 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA632 + difference 4 1) (sourceB632 + difference 1 4) sourceC632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5014) := by
    have ha : (tripleCharges (sourceA632 + difference 4 1) (sourceB632 + difference 1 4) sourceC632) = raw10693 := by
      apply Matrix.ext; unfold tripleCharges sourceA632 sourceB632 sourceC632 difference raw10693; decide +kernel
    rw [ha]
    exact (canonical10693 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA632 + difference 4 2) (sourceB632 + difference 2 4) sourceC632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5014) := by
    have ha : (tripleCharges (sourceA632 + difference 4 2) (sourceB632 + difference 2 4) sourceC632) = raw10694 := by
      apply Matrix.ext; unfold tripleCharges sourceA632 sourceB632 sourceC632 difference raw10694; decide +kernel
    rw [ha]
    exact (canonical10694 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA632 + difference 4 3) (sourceB632 + difference 3 4) sourceC632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5023) := by
    have ha : (tripleCharges (sourceA632 + difference 4 3) (sourceB632 + difference 3 4) sourceC632) = raw10695 := by
      apply Matrix.ext; unfold tripleCharges sourceA632 sourceB632 sourceC632 difference raw10695; decide +kernel
    rw [ha]
    exact (canonical10695 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA632 + difference 4 5) (sourceB632 + difference 5 4) sourceC632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5275) := by
    have ha : (tripleCharges (sourceA632 + difference 4 5) (sourceB632 + difference 5 4) sourceC632) = raw10696 := by
      apply Matrix.ext; unfold tripleCharges sourceA632 sourceB632 sourceC632 difference raw10696; decide +kernel
    rw [ha]
    exact (canonical10696 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA632 + difference 5 0) (sourceB632 + difference 0 5) sourceC632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4421) := by
    have ha : (tripleCharges (sourceA632 + difference 5 0) (sourceB632 + difference 0 5) sourceC632) = raw10697 := by
      apply Matrix.ext; unfold tripleCharges sourceA632 sourceB632 sourceC632 difference raw10697; decide +kernel
    rw [ha]
    exact (canonical10697 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA632 + difference 5 1) (sourceB632 + difference 1 5) sourceC632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4418) := by
    have ha : (tripleCharges (sourceA632 + difference 5 1) (sourceB632 + difference 1 5) sourceC632) = raw10698 := by
      apply Matrix.ext; unfold tripleCharges sourceA632 sourceB632 sourceC632 difference raw10698; decide +kernel
    rw [ha]
    exact (canonical10698 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA632 + difference 5 2) (sourceB632 + difference 2 5) sourceC632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4418) := by
    have ha : (tripleCharges (sourceA632 + difference 5 2) (sourceB632 + difference 2 5) sourceC632) = raw10699 := by
      apply Matrix.ext; unfold tripleCharges sourceA632 sourceB632 sourceC632 difference raw10699; decide +kernel
    rw [ha]
    exact (canonical10699 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA632 + difference 5 3) (sourceB632 + difference 3 5) sourceC632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4431) := by
    have ha : (tripleCharges (sourceA632 + difference 5 3) (sourceB632 + difference 3 5) sourceC632) = raw10700 := by
      apply Matrix.ext; unfold tripleCharges sourceA632 sourceB632 sourceC632 difference raw10700; decide +kernel
    rw [ha]
    exact (canonical10700 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA632 + difference 5 4) (sourceB632 + difference 4 5) sourceC632) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4496) := by
    have ha : (tripleCharges (sourceA632 + difference 5 4) (sourceB632 + difference 4 5) sourceC632) = raw10701 := by
      apply Matrix.ext; unfold tripleCharges sourceA632 sourceB632 sourceC632 difference raw10701; decide +kernel
    rw [ha]
    exact (canonical10701 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA632 sourceB632 sourceC632
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm632, Integer.Sparse.eval]
  linarith only [hs]

def sourceA633 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB633 : Charge := ![0, 2, 0, 0, 0, -2]
def sourceC633 : Charge := ![3, -2, 0, 0, -1, 0]
def sourceForm633 : Integer.Sparse Master := [(Sum.inr 4475, 2), (Sum.inr 4478, 1), (Sum.inr 4480, 1), (Sum.inr 4503, 1), (Sum.inr 4816, 2), (Sum.inr 4819, 2), (Sum.inr 4821, 2), (Sum.inr 4839, 2), (Sum.inr 4844, 1), (Sum.inr 4880, 2), (Sum.inr 4884, 1), (Sum.inr 4889, 2), (Sum.inr 4891, 2), (Sum.inr 4892, 1), (Sum.inr 4895, 1), (Sum.inr 4896, 2), (Sum.inr 5267, 2), (Sum.inr 5276, 1), (Sum.inr 5294, 1), (Sum.inr 5302, 1)]

theorem sourceEq633 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm633 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA633 + difference 0 1) (sourceB633 + difference 1 0) sourceC633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5276) := by
    have ha : (tripleCharges (sourceA633 + difference 0 1) (sourceB633 + difference 1 0) sourceC633) = raw10702 := by
      apply Matrix.ext; unfold tripleCharges sourceA633 sourceB633 sourceC633 difference raw10702; decide +kernel
    rw [ha]
    exact (canonical10702 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA633 + difference 0 2) (sourceB633 + difference 2 0) sourceC633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5267) := by
    have ha : (tripleCharges (sourceA633 + difference 0 2) (sourceB633 + difference 2 0) sourceC633) = raw10703 := by
      apply Matrix.ext; unfold tripleCharges sourceA633 sourceB633 sourceC633 difference raw10703; decide +kernel
    rw [ha]
    exact (canonical10703 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA633 + difference 0 3) (sourceB633 + difference 3 0) sourceC633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5267) := by
    have ha : (tripleCharges (sourceA633 + difference 0 3) (sourceB633 + difference 3 0) sourceC633) = raw10704 := by
      apply Matrix.ext; unfold tripleCharges sourceA633 sourceB633 sourceC633 difference raw10704; decide +kernel
    rw [ha]
    exact (canonical10704 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA633 + difference 0 4) (sourceB633 + difference 4 0) sourceC633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA633 + difference 0 4) (sourceB633 + difference 4 0) sourceC633) = raw10705 := by
      apply Matrix.ext; unfold tripleCharges sourceA633 sourceB633 sourceC633 difference raw10705; decide +kernel
    rw [ha]
    exact (canonical10705 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA633 + difference 0 5) (sourceB633 + difference 5 0) sourceC633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA633 + difference 0 5) (sourceB633 + difference 5 0) sourceC633) = raw10706 := by
      apply Matrix.ext; unfold tripleCharges sourceA633 sourceB633 sourceC633 difference raw10706; decide +kernel
    rw [ha]
    exact (canonical10706 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA633 + difference 1 0) (sourceB633 + difference 0 1) sourceC633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4503) := by
    have ha : (tripleCharges (sourceA633 + difference 1 0) (sourceB633 + difference 0 1) sourceC633) = raw10707 := by
      apply Matrix.ext; unfold tripleCharges sourceA633 sourceB633 sourceC633 difference raw10707; decide +kernel
    rw [ha]
    exact (canonical10707 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA633 + difference 1 2) (sourceB633 + difference 2 1) sourceC633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4839) := by
    have ha : (tripleCharges (sourceA633 + difference 1 2) (sourceB633 + difference 2 1) sourceC633) = raw10708 := by
      apply Matrix.ext; unfold tripleCharges sourceA633 sourceB633 sourceC633 difference raw10708; decide +kernel
    rw [ha]
    exact (canonical10708 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA633 + difference 1 3) (sourceB633 + difference 3 1) sourceC633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4839) := by
    have ha : (tripleCharges (sourceA633 + difference 1 3) (sourceB633 + difference 3 1) sourceC633) = raw10709 := by
      apply Matrix.ext; unfold tripleCharges sourceA633 sourceB633 sourceC633 difference raw10709; decide +kernel
    rw [ha]
    exact (canonical10709 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA633 + difference 1 4) (sourceB633 + difference 4 1) sourceC633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4896) := by
    have ha : (tripleCharges (sourceA633 + difference 1 4) (sourceB633 + difference 4 1) sourceC633) = raw10710 := by
      apply Matrix.ext; unfold tripleCharges sourceA633 sourceB633 sourceC633 difference raw10710; decide +kernel
    rw [ha]
    exact (canonical10710 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA633 + difference 1 5) (sourceB633 + difference 5 1) sourceC633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA633 + difference 1 5) (sourceB633 + difference 5 1) sourceC633) = raw10711 := by
      apply Matrix.ext; unfold tripleCharges sourceA633 sourceB633 sourceC633 difference raw10711; decide +kernel
    rw [ha]
    exact (canonical10711 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA633 + difference 2 0) (sourceB633 + difference 0 2) sourceC633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4475) := by
    have ha : (tripleCharges (sourceA633 + difference 2 0) (sourceB633 + difference 0 2) sourceC633) = raw10712 := by
      apply Matrix.ext; unfold tripleCharges sourceA633 sourceB633 sourceC633 difference raw10712; decide +kernel
    rw [ha]
    exact (canonical10712 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA633 + difference 2 1) (sourceB633 + difference 1 2) sourceC633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4880) := by
    have ha : (tripleCharges (sourceA633 + difference 2 1) (sourceB633 + difference 1 2) sourceC633) = raw10713 := by
      apply Matrix.ext; unfold tripleCharges sourceA633 sourceB633 sourceC633 difference raw10713; decide +kernel
    rw [ha]
    exact (canonical10713 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA633 + difference 2 3) (sourceB633 + difference 3 2) sourceC633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4816) := by
    have ha : (tripleCharges (sourceA633 + difference 2 3) (sourceB633 + difference 3 2) sourceC633) = raw10714 := by
      apply Matrix.ext; unfold tripleCharges sourceA633 sourceB633 sourceC633 difference raw10714; decide +kernel
    rw [ha]
    exact (canonical10714 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA633 + difference 2 4) (sourceB633 + difference 4 2) sourceC633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4891) := by
    have ha : (tripleCharges (sourceA633 + difference 2 4) (sourceB633 + difference 4 2) sourceC633) = raw10715 := by
      apply Matrix.ext; unfold tripleCharges sourceA633 sourceB633 sourceC633 difference raw10715; decide +kernel
    rw [ha]
    exact (canonical10715 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA633 + difference 2 5) (sourceB633 + difference 5 2) sourceC633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA633 + difference 2 5) (sourceB633 + difference 5 2) sourceC633) = raw10716 := by
      apply Matrix.ext; unfold tripleCharges sourceA633 sourceB633 sourceC633 difference raw10716; decide +kernel
    rw [ha]
    exact (canonical10716 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA633 + difference 3 0) (sourceB633 + difference 0 3) sourceC633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4475) := by
    have ha : (tripleCharges (sourceA633 + difference 3 0) (sourceB633 + difference 0 3) sourceC633) = raw10717 := by
      apply Matrix.ext; unfold tripleCharges sourceA633 sourceB633 sourceC633 difference raw10717; decide +kernel
    rw [ha]
    exact (canonical10717 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA633 + difference 3 1) (sourceB633 + difference 1 3) sourceC633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4880) := by
    have ha : (tripleCharges (sourceA633 + difference 3 1) (sourceB633 + difference 1 3) sourceC633) = raw10718 := by
      apply Matrix.ext; unfold tripleCharges sourceA633 sourceB633 sourceC633 difference raw10718; decide +kernel
    rw [ha]
    exact (canonical10718 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA633 + difference 3 2) (sourceB633 + difference 2 3) sourceC633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4816) := by
    have ha : (tripleCharges (sourceA633 + difference 3 2) (sourceB633 + difference 2 3) sourceC633) = raw10719 := by
      apply Matrix.ext; unfold tripleCharges sourceA633 sourceB633 sourceC633 difference raw10719; decide +kernel
    rw [ha]
    exact (canonical10719 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA633 + difference 3 4) (sourceB633 + difference 4 3) sourceC633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4891) := by
    have ha : (tripleCharges (sourceA633 + difference 3 4) (sourceB633 + difference 4 3) sourceC633) = raw10720 := by
      apply Matrix.ext; unfold tripleCharges sourceA633 sourceB633 sourceC633 difference raw10720; decide +kernel
    rw [ha]
    exact (canonical10720 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA633 + difference 3 5) (sourceB633 + difference 5 3) sourceC633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA633 + difference 3 5) (sourceB633 + difference 5 3) sourceC633) = raw10721 := by
      apply Matrix.ext; unfold tripleCharges sourceA633 sourceB633 sourceC633 difference raw10721; decide +kernel
    rw [ha]
    exact (canonical10721 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA633 + difference 4 0) (sourceB633 + difference 0 4) sourceC633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4480) := by
    have ha : (tripleCharges (sourceA633 + difference 4 0) (sourceB633 + difference 0 4) sourceC633) = raw10722 := by
      apply Matrix.ext; unfold tripleCharges sourceA633 sourceB633 sourceC633 difference raw10722; decide +kernel
    rw [ha]
    exact (canonical10722 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA633 + difference 4 1) (sourceB633 + difference 1 4) sourceC633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4884) := by
    have ha : (tripleCharges (sourceA633 + difference 4 1) (sourceB633 + difference 1 4) sourceC633) = raw10723 := by
      apply Matrix.ext; unfold tripleCharges sourceA633 sourceB633 sourceC633 difference raw10723; decide +kernel
    rw [ha]
    exact (canonical10723 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA633 + difference 4 2) (sourceB633 + difference 2 4) sourceC633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4821) := by
    have ha : (tripleCharges (sourceA633 + difference 4 2) (sourceB633 + difference 2 4) sourceC633) = raw10724 := by
      apply Matrix.ext; unfold tripleCharges sourceA633 sourceB633 sourceC633 difference raw10724; decide +kernel
    rw [ha]
    exact (canonical10724 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA633 + difference 4 3) (sourceB633 + difference 3 4) sourceC633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4821) := by
    have ha : (tripleCharges (sourceA633 + difference 4 3) (sourceB633 + difference 3 4) sourceC633) = raw10725 := by
      apply Matrix.ext; unfold tripleCharges sourceA633 sourceB633 sourceC633 difference raw10725; decide +kernel
    rw [ha]
    exact (canonical10725 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA633 + difference 4 5) (sourceB633 + difference 5 4) sourceC633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4896) := by
    have ha : (tripleCharges (sourceA633 + difference 4 5) (sourceB633 + difference 5 4) sourceC633) = raw10726 := by
      apply Matrix.ext; unfold tripleCharges sourceA633 sourceB633 sourceC633 difference raw10726; decide +kernel
    rw [ha]
    exact (canonical10726 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA633 + difference 5 0) (sourceB633 + difference 0 5) sourceC633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4478) := by
    have ha : (tripleCharges (sourceA633 + difference 5 0) (sourceB633 + difference 0 5) sourceC633) = raw10727 := by
      apply Matrix.ext; unfold tripleCharges sourceA633 sourceB633 sourceC633 difference raw10727; decide +kernel
    rw [ha]
    exact (canonical10727 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA633 + difference 5 1) (sourceB633 + difference 1 5) sourceC633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4844) := by
    have ha : (tripleCharges (sourceA633 + difference 5 1) (sourceB633 + difference 1 5) sourceC633) = raw10728 := by
      apply Matrix.ext; unfold tripleCharges sourceA633 sourceB633 sourceC633 difference raw10728; decide +kernel
    rw [ha]
    exact (canonical10728 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA633 + difference 5 2) (sourceB633 + difference 2 5) sourceC633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4819) := by
    have ha : (tripleCharges (sourceA633 + difference 5 2) (sourceB633 + difference 2 5) sourceC633) = raw10729 := by
      apply Matrix.ext; unfold tripleCharges sourceA633 sourceB633 sourceC633 difference raw10729; decide +kernel
    rw [ha]
    exact (canonical10729 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA633 + difference 5 3) (sourceB633 + difference 3 5) sourceC633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4819) := by
    have ha : (tripleCharges (sourceA633 + difference 5 3) (sourceB633 + difference 3 5) sourceC633) = raw10730 := by
      apply Matrix.ext; unfold tripleCharges sourceA633 sourceB633 sourceC633 difference raw10730; decide +kernel
    rw [ha]
    exact (canonical10730 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA633 + difference 5 4) (sourceB633 + difference 4 5) sourceC633) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4892) := by
    have ha : (tripleCharges (sourceA633 + difference 5 4) (sourceB633 + difference 4 5) sourceC633) = raw10731 := by
      apply Matrix.ext; unfold tripleCharges sourceA633 sourceB633 sourceC633 difference raw10731; decide +kernel
    rw [ha]
    exact (canonical10731 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA633 sourceB633 sourceC633
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm633, Integer.Sparse.eval]
  linarith only [hs]

def sourceA634 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB634 : Charge := ![0, 2, 0, 0, 0, -2]
def sourceC634 : Charge := ![3, -2, 0, 0, -1, 0]
def sourceForm634 : Integer.Sparse Master := [(Sum.inr 1715, 2), (Sum.inr 1739, 1), (Sum.inr 1740, 1), (Sum.inr 1746, 1), (Sum.inr 2196, 2), (Sum.inr 2216, 2), (Sum.inr 2217, 2), (Sum.inr 2221, 2), (Sum.inr 2222, 1), (Sum.inr 2245, 2), (Sum.inr 2253, 2), (Sum.inr 2254, 2), (Sum.inr 2265, 1), (Sum.inr 2266, 1), (Sum.inr 2278, 1), (Sum.inr 2280, 1), (Sum.inr 2284, 1), (Sum.inr 2732, 2), (Sum.inr 2768, 1), (Sum.inr 2776, 1), (Sum.inr 2777, 1)]

theorem sourceEq634 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm634 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA634 + difference 0 1) (sourceB634 + difference 1 0) sourceC634) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2777) := by
    have ha : (tripleCharges (sourceA634 + difference 0 1) (sourceB634 + difference 1 0) sourceC634) = raw10732 := by
      apply Matrix.ext; unfold tripleCharges sourceA634 sourceB634 sourceC634 difference raw10732; decide +kernel
    rw [ha]
    exact (canonical10732 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA634 + difference 0 2) (sourceB634 + difference 2 0) sourceC634) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2732) := by
    have ha : (tripleCharges (sourceA634 + difference 0 2) (sourceB634 + difference 2 0) sourceC634) = raw10733 := by
      apply Matrix.ext; unfold tripleCharges sourceA634 sourceB634 sourceC634 difference raw10733; decide +kernel
    rw [ha]
    exact (canonical10733 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA634 + difference 0 3) (sourceB634 + difference 3 0) sourceC634) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2732) := by
    have ha : (tripleCharges (sourceA634 + difference 0 3) (sourceB634 + difference 3 0) sourceC634) = raw10734 := by
      apply Matrix.ext; unfold tripleCharges sourceA634 sourceB634 sourceC634 difference raw10734; decide +kernel
    rw [ha]
    exact (canonical10734 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA634 + difference 0 4) (sourceB634 + difference 4 0) sourceC634) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2776) := by
    have ha : (tripleCharges (sourceA634 + difference 0 4) (sourceB634 + difference 4 0) sourceC634) = raw10735 := by
      apply Matrix.ext; unfold tripleCharges sourceA634 sourceB634 sourceC634 difference raw10735; decide +kernel
    rw [ha]
    exact (canonical10735 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA634 + difference 0 5) (sourceB634 + difference 5 0) sourceC634) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2768) := by
    have ha : (tripleCharges (sourceA634 + difference 0 5) (sourceB634 + difference 5 0) sourceC634) = raw10736 := by
      apply Matrix.ext; unfold tripleCharges sourceA634 sourceB634 sourceC634 difference raw10736; decide +kernel
    rw [ha]
    exact (canonical10736 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA634 + difference 1 0) (sourceB634 + difference 0 1) sourceC634) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1739) := by
    have ha : (tripleCharges (sourceA634 + difference 1 0) (sourceB634 + difference 0 1) sourceC634) = raw10737 := by
      apply Matrix.ext; unfold tripleCharges sourceA634 sourceB634 sourceC634 difference raw10737; decide +kernel
    rw [ha]
    exact (canonical10737 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA634 + difference 1 2) (sourceB634 + difference 2 1) sourceC634) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2216) := by
    have ha : (tripleCharges (sourceA634 + difference 1 2) (sourceB634 + difference 2 1) sourceC634) = raw10738 := by
      apply Matrix.ext; unfold tripleCharges sourceA634 sourceB634 sourceC634 difference raw10738; decide +kernel
    rw [ha]
    exact (canonical10738 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA634 + difference 1 3) (sourceB634 + difference 3 1) sourceC634) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2216) := by
    have ha : (tripleCharges (sourceA634 + difference 1 3) (sourceB634 + difference 3 1) sourceC634) = raw10739 := by
      apply Matrix.ext; unfold tripleCharges sourceA634 sourceB634 sourceC634 difference raw10739; decide +kernel
    rw [ha]
    exact (canonical10739 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA634 + difference 1 4) (sourceB634 + difference 4 1) sourceC634) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2278) := by
    have ha : (tripleCharges (sourceA634 + difference 1 4) (sourceB634 + difference 4 1) sourceC634) = raw10740 := by
      apply Matrix.ext; unfold tripleCharges sourceA634 sourceB634 sourceC634 difference raw10740; decide +kernel
    rw [ha]
    exact (canonical10740 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA634 + difference 1 5) (sourceB634 + difference 5 1) sourceC634) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2265) := by
    have ha : (tripleCharges (sourceA634 + difference 1 5) (sourceB634 + difference 5 1) sourceC634) = raw10741 := by
      apply Matrix.ext; unfold tripleCharges sourceA634 sourceB634 sourceC634 difference raw10741; decide +kernel
    rw [ha]
    exact (canonical10741 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA634 + difference 2 0) (sourceB634 + difference 0 2) sourceC634) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1715) := by
    have ha : (tripleCharges (sourceA634 + difference 2 0) (sourceB634 + difference 0 2) sourceC634) = raw10742 := by
      apply Matrix.ext; unfold tripleCharges sourceA634 sourceB634 sourceC634 difference raw10742; decide +kernel
    rw [ha]
    exact (canonical10742 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA634 + difference 2 1) (sourceB634 + difference 1 2) sourceC634) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2254) := by
    have ha : (tripleCharges (sourceA634 + difference 2 1) (sourceB634 + difference 1 2) sourceC634) = raw10743 := by
      apply Matrix.ext; unfold tripleCharges sourceA634 sourceB634 sourceC634 difference raw10743; decide +kernel
    rw [ha]
    exact (canonical10743 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA634 + difference 2 3) (sourceB634 + difference 3 2) sourceC634) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2196) := by
    have ha : (tripleCharges (sourceA634 + difference 2 3) (sourceB634 + difference 3 2) sourceC634) = raw10744 := by
      apply Matrix.ext; unfold tripleCharges sourceA634 sourceB634 sourceC634 difference raw10744; decide +kernel
    rw [ha]
    exact (canonical10744 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA634 + difference 2 4) (sourceB634 + difference 4 2) sourceC634) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2253) := by
    have ha : (tripleCharges (sourceA634 + difference 2 4) (sourceB634 + difference 4 2) sourceC634) = raw10745 := by
      apply Matrix.ext; unfold tripleCharges sourceA634 sourceB634 sourceC634 difference raw10745; decide +kernel
    rw [ha]
    exact (canonical10745 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA634 + difference 2 5) (sourceB634 + difference 5 2) sourceC634) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2245) := by
    have ha : (tripleCharges (sourceA634 + difference 2 5) (sourceB634 + difference 5 2) sourceC634) = raw10746 := by
      apply Matrix.ext; unfold tripleCharges sourceA634 sourceB634 sourceC634 difference raw10746; decide +kernel
    rw [ha]
    exact (canonical10746 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA634 + difference 3 0) (sourceB634 + difference 0 3) sourceC634) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1715) := by
    have ha : (tripleCharges (sourceA634 + difference 3 0) (sourceB634 + difference 0 3) sourceC634) = raw10747 := by
      apply Matrix.ext; unfold tripleCharges sourceA634 sourceB634 sourceC634 difference raw10747; decide +kernel
    rw [ha]
    exact (canonical10747 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA634 + difference 3 1) (sourceB634 + difference 1 3) sourceC634) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2254) := by
    have ha : (tripleCharges (sourceA634 + difference 3 1) (sourceB634 + difference 1 3) sourceC634) = raw10748 := by
      apply Matrix.ext; unfold tripleCharges sourceA634 sourceB634 sourceC634 difference raw10748; decide +kernel
    rw [ha]
    exact (canonical10748 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA634 + difference 3 2) (sourceB634 + difference 2 3) sourceC634) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2196) := by
    have ha : (tripleCharges (sourceA634 + difference 3 2) (sourceB634 + difference 2 3) sourceC634) = raw10749 := by
      apply Matrix.ext; unfold tripleCharges sourceA634 sourceB634 sourceC634 difference raw10749; decide +kernel
    rw [ha]
    exact (canonical10749 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA634 + difference 3 4) (sourceB634 + difference 4 3) sourceC634) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2253) := by
    have ha : (tripleCharges (sourceA634 + difference 3 4) (sourceB634 + difference 4 3) sourceC634) = raw10750 := by
      apply Matrix.ext; unfold tripleCharges sourceA634 sourceB634 sourceC634 difference raw10750; decide +kernel
    rw [ha]
    exact (canonical10750 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA634 + difference 3 5) (sourceB634 + difference 5 3) sourceC634) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2245) := by
    have ha : (tripleCharges (sourceA634 + difference 3 5) (sourceB634 + difference 5 3) sourceC634) = raw10751 := by
      apply Matrix.ext; unfold tripleCharges sourceA634 sourceB634 sourceC634 difference raw10751; decide +kernel
    rw [ha]
    exact (canonical10751 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA634 + difference 4 0) (sourceB634 + difference 0 4) sourceC634) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1740) := by
    have ha : (tripleCharges (sourceA634 + difference 4 0) (sourceB634 + difference 0 4) sourceC634) = raw10752 := by
      apply Matrix.ext; unfold tripleCharges sourceA634 sourceB634 sourceC634 difference raw10752; decide +kernel
    rw [ha]
    exact (canonical10752 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA634 + difference 4 1) (sourceB634 + difference 1 4) sourceC634) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2280) := by
    have ha : (tripleCharges (sourceA634 + difference 4 1) (sourceB634 + difference 1 4) sourceC634) = raw10753 := by
      apply Matrix.ext; unfold tripleCharges sourceA634 sourceB634 sourceC634 difference raw10753; decide +kernel
    rw [ha]
    exact (canonical10753 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA634 + difference 4 2) (sourceB634 + difference 2 4) sourceC634) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2217) := by
    have ha : (tripleCharges (sourceA634 + difference 4 2) (sourceB634 + difference 2 4) sourceC634) = raw10754 := by
      apply Matrix.ext; unfold tripleCharges sourceA634 sourceB634 sourceC634 difference raw10754; decide +kernel
    rw [ha]
    exact (canonical10754 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA634 + difference 4 3) (sourceB634 + difference 3 4) sourceC634) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2217) := by
    have ha : (tripleCharges (sourceA634 + difference 4 3) (sourceB634 + difference 3 4) sourceC634) = raw10755 := by
      apply Matrix.ext; unfold tripleCharges sourceA634 sourceB634 sourceC634 difference raw10755; decide +kernel
    rw [ha]
    exact (canonical10755 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA634 + difference 4 5) (sourceB634 + difference 5 4) sourceC634) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2266) := by
    have ha : (tripleCharges (sourceA634 + difference 4 5) (sourceB634 + difference 5 4) sourceC634) = raw10756 := by
      apply Matrix.ext; unfold tripleCharges sourceA634 sourceB634 sourceC634 difference raw10756; decide +kernel
    rw [ha]
    exact (canonical10756 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA634 + difference 5 0) (sourceB634 + difference 0 5) sourceC634) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1746) := by
    have ha : (tripleCharges (sourceA634 + difference 5 0) (sourceB634 + difference 0 5) sourceC634) = raw10757 := by
      apply Matrix.ext; unfold tripleCharges sourceA634 sourceB634 sourceC634 difference raw10757; decide +kernel
    rw [ha]
    exact (canonical10757 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA634 + difference 5 1) (sourceB634 + difference 1 5) sourceC634) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2222) := by
    have ha : (tripleCharges (sourceA634 + difference 5 1) (sourceB634 + difference 1 5) sourceC634) = raw10758 := by
      apply Matrix.ext; unfold tripleCharges sourceA634 sourceB634 sourceC634 difference raw10758; decide +kernel
    rw [ha]
    exact (canonical10758 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA634 + difference 5 2) (sourceB634 + difference 2 5) sourceC634) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2221) := by
    have ha : (tripleCharges (sourceA634 + difference 5 2) (sourceB634 + difference 2 5) sourceC634) = raw10759 := by
      apply Matrix.ext; unfold tripleCharges sourceA634 sourceB634 sourceC634 difference raw10759; decide +kernel
    rw [ha]
    exact (canonical10759 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA634 + difference 5 3) (sourceB634 + difference 3 5) sourceC634) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2221) := by
    have ha : (tripleCharges (sourceA634 + difference 5 3) (sourceB634 + difference 3 5) sourceC634) = raw10760 := by
      apply Matrix.ext; unfold tripleCharges sourceA634 sourceB634 sourceC634 difference raw10760; decide +kernel
    rw [ha]
    exact (canonical10760 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA634 + difference 5 4) (sourceB634 + difference 4 5) sourceC634) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2284) := by
    have ha : (tripleCharges (sourceA634 + difference 5 4) (sourceB634 + difference 4 5) sourceC634) = raw10761 := by
      apply Matrix.ext; unfold tripleCharges sourceA634 sourceB634 sourceC634 difference raw10761; decide +kernel
    rw [ha]
    exact (canonical10761 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA634 sourceB634 sourceC634
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm634, Integer.Sparse.eval]
  linarith only [hs]

def sourceA635 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB635 : Charge := ![0, 2, 0, 0, 0, -2]
def sourceC635 : Charge := ![3, -2, 0, 0, -1, 0]
def sourceForm635 : Integer.Sparse Master := [(Sum.inr 1087, 1), (Sum.inr 2058, 2), (Sum.inr 2266, 1), (Sum.inr 2279, 1), (Sum.inr 2291, 1), (Sum.inr 4084, -1)]

theorem sourceEq635 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm635 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA635 + difference 1 0) (sourceB635 + difference 0 1) sourceC635) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1087) := by
    have ha : (tripleCharges (sourceA635 + difference 1 0) (sourceB635 + difference 0 1) sourceC635) = raw10762 := by
      apply Matrix.ext; unfold tripleCharges sourceA635 sourceB635 sourceC635 difference raw10762; decide +kernel
    rw [ha]
    exact (canonical10762 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA635 + difference 1 1) (sourceB635 + difference 1 1) sourceC635) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2279) := by
    have ha : (tripleCharges (sourceA635 + difference 1 1) (sourceB635 + difference 1 1) sourceC635) = raw10763 := by
      apply Matrix.ext; unfold tripleCharges sourceA635 sourceB635 sourceC635 difference raw10763; decide +kernel
    rw [ha]
    exact (canonical10763 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA635 + difference 1 2) (sourceB635 + difference 2 1) sourceC635) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2058) := by
    have ha : (tripleCharges (sourceA635 + difference 1 2) (sourceB635 + difference 2 1) sourceC635) = raw10764 := by
      apply Matrix.ext; unfold tripleCharges sourceA635 sourceB635 sourceC635 difference raw10764; decide +kernel
    rw [ha]
    exact (canonical10764 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA635 + difference 1 3) (sourceB635 + difference 3 1) sourceC635) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2058) := by
    have ha : (tripleCharges (sourceA635 + difference 1 3) (sourceB635 + difference 3 1) sourceC635) = raw10765 := by
      apply Matrix.ext; unfold tripleCharges sourceA635 sourceB635 sourceC635 difference raw10765; decide +kernel
    rw [ha]
    exact (canonical10765 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA635 + difference 1 4) (sourceB635 + difference 4 1) sourceC635) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2266) := by
    have ha : (tripleCharges (sourceA635 + difference 1 4) (sourceB635 + difference 4 1) sourceC635) = raw10766 := by
      apply Matrix.ext; unfold tripleCharges sourceA635 sourceB635 sourceC635 difference raw10766; decide +kernel
    rw [ha]
    exact (canonical10766 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA635 + difference 1 5) (sourceB635 + difference 5 1) sourceC635) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2291) := by
    have ha : (tripleCharges (sourceA635 + difference 1 5) (sourceB635 + difference 5 1) sourceC635) = raw10767 := by
      apply Matrix.ext; unfold tripleCharges sourceA635 sourceB635 sourceC635 difference raw10767; decide +kernel
    rw [ha]
    exact (canonical10767 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA635 + sourceB635) sourceC635) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA635 + sourceB635) sourceC635) = raw10768 := by
      apply Matrix.ext; unfold doubleCharges sourceA635 sourceB635 sourceC635 raw10768; decide +kernel
    rw [ha]
    exact (canonical10768 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA635 sourceB635 sourceC635
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm635, Integer.Sparse.eval]
  linarith only [hs]

def sourceA636 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB636 : Charge := ![3, -2, 0, 0, -1, 0]
def sourceC636 : Charge := ![0, 2, 0, 0, 0, -2]
def sourceForm636 : Integer.Sparse Master := [(Sum.inr 4275, 2), (Sum.inr 4276, 2), (Sum.inr 4278, 1), (Sum.inr 4746, 2), (Sum.inr 4747, 4), (Sum.inr 4749, 2), (Sum.inr 4869, 4), (Sum.inr 4871, 2), (Sum.inr 4874, 2), (Sum.inr 4898, 2), (Sum.inr 4899, 2), (Sum.inr 5412, 2), (Sum.inr 5443, 2), (Sum.inr 5456, 1)]

theorem sourceEq636 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm636 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA636 + difference 0 1) (sourceB636 + difference 1 0) sourceC636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA636 + difference 0 1) (sourceB636 + difference 1 0) sourceC636) = raw10769 := by
      apply Matrix.ext; unfold tripleCharges sourceA636 sourceB636 sourceC636 difference raw10769; decide +kernel
    rw [ha]
    exact (canonical10769 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA636 + difference 0 2) (sourceB636 + difference 2 0) sourceC636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5412) := by
    have ha : (tripleCharges (sourceA636 + difference 0 2) (sourceB636 + difference 2 0) sourceC636) = raw10770 := by
      apply Matrix.ext; unfold tripleCharges sourceA636 sourceB636 sourceC636 difference raw10770; decide +kernel
    rw [ha]
    exact (canonical10770 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA636 + difference 0 3) (sourceB636 + difference 3 0) sourceC636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5412) := by
    have ha : (tripleCharges (sourceA636 + difference 0 3) (sourceB636 + difference 3 0) sourceC636) = raw10771 := by
      apply Matrix.ext; unfold tripleCharges sourceA636 sourceB636 sourceC636 difference raw10771; decide +kernel
    rw [ha]
    exact (canonical10771 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA636 + difference 0 4) (sourceB636 + difference 4 0) sourceC636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5456) := by
    have ha : (tripleCharges (sourceA636 + difference 0 4) (sourceB636 + difference 4 0) sourceC636) = raw10772 := by
      apply Matrix.ext; unfold tripleCharges sourceA636 sourceB636 sourceC636 difference raw10772; decide +kernel
    rw [ha]
    exact (canonical10772 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA636 + difference 0 5) (sourceB636 + difference 5 0) sourceC636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA636 + difference 0 5) (sourceB636 + difference 5 0) sourceC636) = raw10773 := by
      apply Matrix.ext; unfold tripleCharges sourceA636 sourceB636 sourceC636 difference raw10773; decide +kernel
    rw [ha]
    exact (canonical10773 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA636 + difference 1 0) (sourceB636 + difference 0 1) sourceC636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4276) := by
    have ha : (tripleCharges (sourceA636 + difference 1 0) (sourceB636 + difference 0 1) sourceC636) = raw10774 := by
      apply Matrix.ext; unfold tripleCharges sourceA636 sourceB636 sourceC636 difference raw10774; decide +kernel
    rw [ha]
    exact (canonical10774 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA636 + difference 1 2) (sourceB636 + difference 2 1) sourceC636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4747) := by
    have ha : (tripleCharges (sourceA636 + difference 1 2) (sourceB636 + difference 2 1) sourceC636) = raw10775 := by
      apply Matrix.ext; unfold tripleCharges sourceA636 sourceB636 sourceC636 difference raw10775; decide +kernel
    rw [ha]
    exact (canonical10775 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA636 + difference 1 3) (sourceB636 + difference 3 1) sourceC636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4747) := by
    have ha : (tripleCharges (sourceA636 + difference 1 3) (sourceB636 + difference 3 1) sourceC636) = raw10776 := by
      apply Matrix.ext; unfold tripleCharges sourceA636 sourceB636 sourceC636 difference raw10776; decide +kernel
    rw [ha]
    exact (canonical10776 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA636 + difference 1 4) (sourceB636 + difference 4 1) sourceC636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4899) := by
    have ha : (tripleCharges (sourceA636 + difference 1 4) (sourceB636 + difference 4 1) sourceC636) = raw10777 := by
      apply Matrix.ext; unfold tripleCharges sourceA636 sourceB636 sourceC636 difference raw10777; decide +kernel
    rw [ha]
    exact (canonical10777 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA636 + difference 1 5) (sourceB636 + difference 5 1) sourceC636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4871) := by
    have ha : (tripleCharges (sourceA636 + difference 1 5) (sourceB636 + difference 5 1) sourceC636) = raw10778 := by
      apply Matrix.ext; unfold tripleCharges sourceA636 sourceB636 sourceC636 difference raw10778; decide +kernel
    rw [ha]
    exact (canonical10778 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA636 + difference 2 0) (sourceB636 + difference 0 2) sourceC636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4275) := by
    have ha : (tripleCharges (sourceA636 + difference 2 0) (sourceB636 + difference 0 2) sourceC636) = raw10779 := by
      apply Matrix.ext; unfold tripleCharges sourceA636 sourceB636 sourceC636 difference raw10779; decide +kernel
    rw [ha]
    exact (canonical10779 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA636 + difference 2 1) (sourceB636 + difference 1 2) sourceC636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4869) := by
    have ha : (tripleCharges (sourceA636 + difference 2 1) (sourceB636 + difference 1 2) sourceC636) = raw10780 := by
      apply Matrix.ext; unfold tripleCharges sourceA636 sourceB636 sourceC636 difference raw10780; decide +kernel
    rw [ha]
    exact (canonical10780 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA636 + difference 2 3) (sourceB636 + difference 3 2) sourceC636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4746) := by
    have ha : (tripleCharges (sourceA636 + difference 2 3) (sourceB636 + difference 3 2) sourceC636) = raw10781 := by
      apply Matrix.ext; unfold tripleCharges sourceA636 sourceB636 sourceC636 difference raw10781; decide +kernel
    rw [ha]
    exact (canonical10781 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA636 + difference 2 4) (sourceB636 + difference 4 2) sourceC636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4898) := by
    have ha : (tripleCharges (sourceA636 + difference 2 4) (sourceB636 + difference 4 2) sourceC636) = raw10782 := by
      apply Matrix.ext; unfold tripleCharges sourceA636 sourceB636 sourceC636 difference raw10782; decide +kernel
    rw [ha]
    exact (canonical10782 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA636 + difference 2 5) (sourceB636 + difference 5 2) sourceC636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4869) := by
    have ha : (tripleCharges (sourceA636 + difference 2 5) (sourceB636 + difference 5 2) sourceC636) = raw10783 := by
      apply Matrix.ext; unfold tripleCharges sourceA636 sourceB636 sourceC636 difference raw10783; decide +kernel
    rw [ha]
    exact (canonical10783 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA636 + difference 3 0) (sourceB636 + difference 0 3) sourceC636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4275) := by
    have ha : (tripleCharges (sourceA636 + difference 3 0) (sourceB636 + difference 0 3) sourceC636) = raw10784 := by
      apply Matrix.ext; unfold tripleCharges sourceA636 sourceB636 sourceC636 difference raw10784; decide +kernel
    rw [ha]
    exact (canonical10784 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA636 + difference 3 1) (sourceB636 + difference 1 3) sourceC636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4869) := by
    have ha : (tripleCharges (sourceA636 + difference 3 1) (sourceB636 + difference 1 3) sourceC636) = raw10785 := by
      apply Matrix.ext; unfold tripleCharges sourceA636 sourceB636 sourceC636 difference raw10785; decide +kernel
    rw [ha]
    exact (canonical10785 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA636 + difference 3 2) (sourceB636 + difference 2 3) sourceC636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4746) := by
    have ha : (tripleCharges (sourceA636 + difference 3 2) (sourceB636 + difference 2 3) sourceC636) = raw10786 := by
      apply Matrix.ext; unfold tripleCharges sourceA636 sourceB636 sourceC636 difference raw10786; decide +kernel
    rw [ha]
    exact (canonical10786 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA636 + difference 3 4) (sourceB636 + difference 4 3) sourceC636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4898) := by
    have ha : (tripleCharges (sourceA636 + difference 3 4) (sourceB636 + difference 4 3) sourceC636) = raw10787 := by
      apply Matrix.ext; unfold tripleCharges sourceA636 sourceB636 sourceC636 difference raw10787; decide +kernel
    rw [ha]
    exact (canonical10787 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA636 + difference 3 5) (sourceB636 + difference 5 3) sourceC636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4869) := by
    have ha : (tripleCharges (sourceA636 + difference 3 5) (sourceB636 + difference 5 3) sourceC636) = raw10788 := by
      apply Matrix.ext; unfold tripleCharges sourceA636 sourceB636 sourceC636 difference raw10788; decide +kernel
    rw [ha]
    exact (canonical10788 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA636 + difference 4 0) (sourceB636 + difference 0 4) sourceC636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4278) := by
    have ha : (tripleCharges (sourceA636 + difference 4 0) (sourceB636 + difference 0 4) sourceC636) = raw10789 := by
      apply Matrix.ext; unfold tripleCharges sourceA636 sourceB636 sourceC636 difference raw10789; decide +kernel
    rw [ha]
    exact (canonical10789 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA636 + difference 4 1) (sourceB636 + difference 1 4) sourceC636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4874) := by
    have ha : (tripleCharges (sourceA636 + difference 4 1) (sourceB636 + difference 1 4) sourceC636) = raw10790 := by
      apply Matrix.ext; unfold tripleCharges sourceA636 sourceB636 sourceC636 difference raw10790; decide +kernel
    rw [ha]
    exact (canonical10790 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA636 + difference 4 2) (sourceB636 + difference 2 4) sourceC636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4749) := by
    have ha : (tripleCharges (sourceA636 + difference 4 2) (sourceB636 + difference 2 4) sourceC636) = raw10791 := by
      apply Matrix.ext; unfold tripleCharges sourceA636 sourceB636 sourceC636 difference raw10791; decide +kernel
    rw [ha]
    exact (canonical10791 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA636 + difference 4 3) (sourceB636 + difference 3 4) sourceC636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4749) := by
    have ha : (tripleCharges (sourceA636 + difference 4 3) (sourceB636 + difference 3 4) sourceC636) = raw10792 := by
      apply Matrix.ext; unfold tripleCharges sourceA636 sourceB636 sourceC636 difference raw10792; decide +kernel
    rw [ha]
    exact (canonical10792 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA636 + difference 4 5) (sourceB636 + difference 5 4) sourceC636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4874) := by
    have ha : (tripleCharges (sourceA636 + difference 4 5) (sourceB636 + difference 5 4) sourceC636) = raw10793 := by
      apply Matrix.ext; unfold tripleCharges sourceA636 sourceB636 sourceC636 difference raw10793; decide +kernel
    rw [ha]
    exact (canonical10793 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA636 + difference 5 0) (sourceB636 + difference 0 5) sourceC636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4276) := by
    have ha : (tripleCharges (sourceA636 + difference 5 0) (sourceB636 + difference 0 5) sourceC636) = raw10794 := by
      apply Matrix.ext; unfold tripleCharges sourceA636 sourceB636 sourceC636 difference raw10794; decide +kernel
    rw [ha]
    exact (canonical10794 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA636 + difference 5 1) (sourceB636 + difference 1 5) sourceC636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4871) := by
    have ha : (tripleCharges (sourceA636 + difference 5 1) (sourceB636 + difference 1 5) sourceC636) = raw10795 := by
      apply Matrix.ext; unfold tripleCharges sourceA636 sourceB636 sourceC636 difference raw10795; decide +kernel
    rw [ha]
    exact (canonical10795 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA636 + difference 5 2) (sourceB636 + difference 2 5) sourceC636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4747) := by
    have ha : (tripleCharges (sourceA636 + difference 5 2) (sourceB636 + difference 2 5) sourceC636) = raw10796 := by
      apply Matrix.ext; unfold tripleCharges sourceA636 sourceB636 sourceC636 difference raw10796; decide +kernel
    rw [ha]
    exact (canonical10796 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA636 + difference 5 3) (sourceB636 + difference 3 5) sourceC636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4747) := by
    have ha : (tripleCharges (sourceA636 + difference 5 3) (sourceB636 + difference 3 5) sourceC636) = raw10797 := by
      apply Matrix.ext; unfold tripleCharges sourceA636 sourceB636 sourceC636 difference raw10797; decide +kernel
    rw [ha]
    exact (canonical10797 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA636 + difference 5 4) (sourceB636 + difference 4 5) sourceC636) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4899) := by
    have ha : (tripleCharges (sourceA636 + difference 5 4) (sourceB636 + difference 4 5) sourceC636) = raw10798 := by
      apply Matrix.ext; unfold tripleCharges sourceA636 sourceB636 sourceC636 difference raw10798; decide +kernel
    rw [ha]
    exact (canonical10798 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA636 sourceB636 sourceC636
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm636, Integer.Sparse.eval]
  linarith only [hs]

def sourceA637 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB637 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceC637 : Charge := ![3, -2, 0, 0, 0, -1]
def sourceForm637 : Integer.Sparse Master := [(Sum.inr 4474, 2), (Sum.inr 4476, 1), (Sum.inr 4480, 1), (Sum.inr 4499, 1), (Sum.inr 4815, 2), (Sum.inr 4817, 2), (Sum.inr 4821, 2), (Sum.inr 4835, 2), (Sum.inr 4879, 2), (Sum.inr 4881, 1), (Sum.inr 4884, 1), (Sum.inr 4889, 2), (Sum.inr 4895, 1), (Sum.inr 4896, 2), (Sum.inr 4898, 1), (Sum.inr 4899, 1), (Sum.inr 4901, 1), (Sum.inr 5260, 2), (Sum.inr 5294, 1), (Sum.inr 5295, 1), (Sum.inr 5310, 1)]

theorem sourceEq637 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm637 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA637 + difference 0 1) (sourceB637 + difference 1 0) sourceC637) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5295) := by
    have ha : (tripleCharges (sourceA637 + difference 0 1) (sourceB637 + difference 1 0) sourceC637) = raw10799 := by
      apply Matrix.ext; unfold tripleCharges sourceA637 sourceB637 sourceC637 difference raw10799; decide +kernel
    rw [ha]
    exact (canonical10799 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA637 + difference 0 2) (sourceB637 + difference 2 0) sourceC637) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5260) := by
    have ha : (tripleCharges (sourceA637 + difference 0 2) (sourceB637 + difference 2 0) sourceC637) = raw10800 := by
      apply Matrix.ext; unfold tripleCharges sourceA637 sourceB637 sourceC637 difference raw10800; decide +kernel
    rw [ha]
    exact (canonical10800 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA637 + difference 0 3) (sourceB637 + difference 3 0) sourceC637) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5260) := by
    have ha : (tripleCharges (sourceA637 + difference 0 3) (sourceB637 + difference 3 0) sourceC637) = raw10801 := by
      apply Matrix.ext; unfold tripleCharges sourceA637 sourceB637 sourceC637 difference raw10801; decide +kernel
    rw [ha]
    exact (canonical10801 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA637 + difference 0 4) (sourceB637 + difference 4 0) sourceC637) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5310) := by
    have ha : (tripleCharges (sourceA637 + difference 0 4) (sourceB637 + difference 4 0) sourceC637) = raw10802 := by
      apply Matrix.ext; unfold tripleCharges sourceA637 sourceB637 sourceC637 difference raw10802; decide +kernel
    rw [ha]
    exact (canonical10802 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA637 + difference 0 5) (sourceB637 + difference 5 0) sourceC637) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA637 + difference 0 5) (sourceB637 + difference 5 0) sourceC637) = raw10803 := by
      apply Matrix.ext; unfold tripleCharges sourceA637 sourceB637 sourceC637 difference raw10803; decide +kernel
    rw [ha]
    exact (canonical10803 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA637 + difference 1 0) (sourceB637 + difference 0 1) sourceC637) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4499) := by
    have ha : (tripleCharges (sourceA637 + difference 1 0) (sourceB637 + difference 0 1) sourceC637) = raw10804 := by
      apply Matrix.ext; unfold tripleCharges sourceA637 sourceB637 sourceC637 difference raw10804; decide +kernel
    rw [ha]
    exact (canonical10804 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA637 + difference 1 2) (sourceB637 + difference 2 1) sourceC637) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4835) := by
    have ha : (tripleCharges (sourceA637 + difference 1 2) (sourceB637 + difference 2 1) sourceC637) = raw10805 := by
      apply Matrix.ext; unfold tripleCharges sourceA637 sourceB637 sourceC637 difference raw10805; decide +kernel
    rw [ha]
    exact (canonical10805 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA637 + difference 1 3) (sourceB637 + difference 3 1) sourceC637) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4835) := by
    have ha : (tripleCharges (sourceA637 + difference 1 3) (sourceB637 + difference 3 1) sourceC637) = raw10806 := by
      apply Matrix.ext; unfold tripleCharges sourceA637 sourceB637 sourceC637 difference raw10806; decide +kernel
    rw [ha]
    exact (canonical10806 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA637 + difference 1 4) (sourceB637 + difference 4 1) sourceC637) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4901) := by
    have ha : (tripleCharges (sourceA637 + difference 1 4) (sourceB637 + difference 4 1) sourceC637) = raw10807 := by
      apply Matrix.ext; unfold tripleCharges sourceA637 sourceB637 sourceC637 difference raw10807; decide +kernel
    rw [ha]
    exact (canonical10807 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA637 + difference 1 5) (sourceB637 + difference 5 1) sourceC637) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA637 + difference 1 5) (sourceB637 + difference 5 1) sourceC637) = raw10808 := by
      apply Matrix.ext; unfold tripleCharges sourceA637 sourceB637 sourceC637 difference raw10808; decide +kernel
    rw [ha]
    exact (canonical10808 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA637 + difference 2 0) (sourceB637 + difference 0 2) sourceC637) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4474) := by
    have ha : (tripleCharges (sourceA637 + difference 2 0) (sourceB637 + difference 0 2) sourceC637) = raw10809 := by
      apply Matrix.ext; unfold tripleCharges sourceA637 sourceB637 sourceC637 difference raw10809; decide +kernel
    rw [ha]
    exact (canonical10809 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA637 + difference 2 1) (sourceB637 + difference 1 2) sourceC637) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4879) := by
    have ha : (tripleCharges (sourceA637 + difference 2 1) (sourceB637 + difference 1 2) sourceC637) = raw10810 := by
      apply Matrix.ext; unfold tripleCharges sourceA637 sourceB637 sourceC637 difference raw10810; decide +kernel
    rw [ha]
    exact (canonical10810 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA637 + difference 2 3) (sourceB637 + difference 3 2) sourceC637) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4815) := by
    have ha : (tripleCharges (sourceA637 + difference 2 3) (sourceB637 + difference 3 2) sourceC637) = raw10811 := by
      apply Matrix.ext; unfold tripleCharges sourceA637 sourceB637 sourceC637 difference raw10811; decide +kernel
    rw [ha]
    exact (canonical10811 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA637 + difference 2 4) (sourceB637 + difference 4 2) sourceC637) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4896) := by
    have ha : (tripleCharges (sourceA637 + difference 2 4) (sourceB637 + difference 4 2) sourceC637) = raw10812 := by
      apply Matrix.ext; unfold tripleCharges sourceA637 sourceB637 sourceC637 difference raw10812; decide +kernel
    rw [ha]
    exact (canonical10812 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA637 + difference 2 5) (sourceB637 + difference 5 2) sourceC637) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA637 + difference 2 5) (sourceB637 + difference 5 2) sourceC637) = raw10813 := by
      apply Matrix.ext; unfold tripleCharges sourceA637 sourceB637 sourceC637 difference raw10813; decide +kernel
    rw [ha]
    exact (canonical10813 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA637 + difference 3 0) (sourceB637 + difference 0 3) sourceC637) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4474) := by
    have ha : (tripleCharges (sourceA637 + difference 3 0) (sourceB637 + difference 0 3) sourceC637) = raw10814 := by
      apply Matrix.ext; unfold tripleCharges sourceA637 sourceB637 sourceC637 difference raw10814; decide +kernel
    rw [ha]
    exact (canonical10814 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA637 + difference 3 1) (sourceB637 + difference 1 3) sourceC637) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4879) := by
    have ha : (tripleCharges (sourceA637 + difference 3 1) (sourceB637 + difference 1 3) sourceC637) = raw10815 := by
      apply Matrix.ext; unfold tripleCharges sourceA637 sourceB637 sourceC637 difference raw10815; decide +kernel
    rw [ha]
    exact (canonical10815 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA637 + difference 3 2) (sourceB637 + difference 2 3) sourceC637) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4815) := by
    have ha : (tripleCharges (sourceA637 + difference 3 2) (sourceB637 + difference 2 3) sourceC637) = raw10816 := by
      apply Matrix.ext; unfold tripleCharges sourceA637 sourceB637 sourceC637 difference raw10816; decide +kernel
    rw [ha]
    exact (canonical10816 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA637 + difference 3 4) (sourceB637 + difference 4 3) sourceC637) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4896) := by
    have ha : (tripleCharges (sourceA637 + difference 3 4) (sourceB637 + difference 4 3) sourceC637) = raw10817 := by
      apply Matrix.ext; unfold tripleCharges sourceA637 sourceB637 sourceC637 difference raw10817; decide +kernel
    rw [ha]
    exact (canonical10817 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA637 + difference 3 5) (sourceB637 + difference 5 3) sourceC637) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA637 + difference 3 5) (sourceB637 + difference 5 3) sourceC637) = raw10818 := by
      apply Matrix.ext; unfold tripleCharges sourceA637 sourceB637 sourceC637 difference raw10818; decide +kernel
    rw [ha]
    exact (canonical10818 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA637 + difference 4 0) (sourceB637 + difference 0 4) sourceC637) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4480) := by
    have ha : (tripleCharges (sourceA637 + difference 4 0) (sourceB637 + difference 0 4) sourceC637) = raw10819 := by
      apply Matrix.ext; unfold tripleCharges sourceA637 sourceB637 sourceC637 difference raw10819; decide +kernel
    rw [ha]
    exact (canonical10819 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA637 + difference 4 1) (sourceB637 + difference 1 4) sourceC637) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4884) := by
    have ha : (tripleCharges (sourceA637 + difference 4 1) (sourceB637 + difference 1 4) sourceC637) = raw10820 := by
      apply Matrix.ext; unfold tripleCharges sourceA637 sourceB637 sourceC637 difference raw10820; decide +kernel
    rw [ha]
    exact (canonical10820 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA637 + difference 4 2) (sourceB637 + difference 2 4) sourceC637) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4821) := by
    have ha : (tripleCharges (sourceA637 + difference 4 2) (sourceB637 + difference 2 4) sourceC637) = raw10821 := by
      apply Matrix.ext; unfold tripleCharges sourceA637 sourceB637 sourceC637 difference raw10821; decide +kernel
    rw [ha]
    exact (canonical10821 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA637 + difference 4 3) (sourceB637 + difference 3 4) sourceC637) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4821) := by
    have ha : (tripleCharges (sourceA637 + difference 4 3) (sourceB637 + difference 3 4) sourceC637) = raw10822 := by
      apply Matrix.ext; unfold tripleCharges sourceA637 sourceB637 sourceC637 difference raw10822; decide +kernel
    rw [ha]
    exact (canonical10822 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA637 + difference 4 5) (sourceB637 + difference 5 4) sourceC637) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4898) := by
    have ha : (tripleCharges (sourceA637 + difference 4 5) (sourceB637 + difference 5 4) sourceC637) = raw10823 := by
      apply Matrix.ext; unfold tripleCharges sourceA637 sourceB637 sourceC637 difference raw10823; decide +kernel
    rw [ha]
    exact (canonical10823 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA637 + difference 5 0) (sourceB637 + difference 0 5) sourceC637) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4476) := by
    have ha : (tripleCharges (sourceA637 + difference 5 0) (sourceB637 + difference 0 5) sourceC637) = raw10824 := by
      apply Matrix.ext; unfold tripleCharges sourceA637 sourceB637 sourceC637 difference raw10824; decide +kernel
    rw [ha]
    exact (canonical10824 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA637 + difference 5 1) (sourceB637 + difference 1 5) sourceC637) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4881) := by
    have ha : (tripleCharges (sourceA637 + difference 5 1) (sourceB637 + difference 1 5) sourceC637) = raw10825 := by
      apply Matrix.ext; unfold tripleCharges sourceA637 sourceB637 sourceC637 difference raw10825; decide +kernel
    rw [ha]
    exact (canonical10825 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA637 + difference 5 2) (sourceB637 + difference 2 5) sourceC637) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4817) := by
    have ha : (tripleCharges (sourceA637 + difference 5 2) (sourceB637 + difference 2 5) sourceC637) = raw10826 := by
      apply Matrix.ext; unfold tripleCharges sourceA637 sourceB637 sourceC637 difference raw10826; decide +kernel
    rw [ha]
    exact (canonical10826 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA637 + difference 5 3) (sourceB637 + difference 3 5) sourceC637) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4817) := by
    have ha : (tripleCharges (sourceA637 + difference 5 3) (sourceB637 + difference 3 5) sourceC637) = raw10827 := by
      apply Matrix.ext; unfold tripleCharges sourceA637 sourceB637 sourceC637 difference raw10827; decide +kernel
    rw [ha]
    exact (canonical10827 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA637 + difference 5 4) (sourceB637 + difference 4 5) sourceC637) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4899) := by
    have ha : (tripleCharges (sourceA637 + difference 5 4) (sourceB637 + difference 4 5) sourceC637) = raw10828 := by
      apply Matrix.ext; unfold tripleCharges sourceA637 sourceB637 sourceC637 difference raw10828; decide +kernel
    rw [ha]
    exact (canonical10828 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA637 sourceB637 sourceC637
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm637, Integer.Sparse.eval]
  linarith only [hs]

def sourceA638 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB638 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceC638 : Charge := ![3, -2, 0, 0, 0, -1]
def sourceForm638 : Integer.Sparse Master := [(Sum.inr 1370, 2), (Sum.inr 1372, 1), (Sum.inr 1375, 1), (Sum.inr 1443, 1), (Sum.inr 2497, 2), (Sum.inr 2520, 1), (Sum.inr 2778, 1), (Sum.inr 3086, 2), (Sum.inr 3098, 1), (Sum.inr 3101, 1), (Sum.inr 3121, 1), (Sum.inr 3158, 2), (Sum.inr 3161, 1), (Sum.inr 3197, 2), (Sum.inr 3198, 2), (Sum.inr 3211, 2), (Sum.inr 3223, 2), (Sum.inr 3224, 1), (Sum.inr 3225, 2), (Sum.inr 3229, 1), (Sum.inr 3231, 1)]

theorem sourceEq638 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm638 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA638 + difference 0 1) (sourceB638 + difference 1 0) sourceC638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3098) := by
    have ha : (tripleCharges (sourceA638 + difference 0 1) (sourceB638 + difference 1 0) sourceC638) = raw10829 := by
      apply Matrix.ext; unfold tripleCharges sourceA638 sourceB638 sourceC638 difference raw10829; decide +kernel
    rw [ha]
    exact (canonical10829 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA638 + difference 0 2) (sourceB638 + difference 2 0) sourceC638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3086) := by
    have ha : (tripleCharges (sourceA638 + difference 0 2) (sourceB638 + difference 2 0) sourceC638) = raw10830 := by
      apply Matrix.ext; unfold tripleCharges sourceA638 sourceB638 sourceC638 difference raw10830; decide +kernel
    rw [ha]
    exact (canonical10830 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA638 + difference 0 3) (sourceB638 + difference 3 0) sourceC638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3086) := by
    have ha : (tripleCharges (sourceA638 + difference 0 3) (sourceB638 + difference 3 0) sourceC638) = raw10831 := by
      apply Matrix.ext; unfold tripleCharges sourceA638 sourceB638 sourceC638 difference raw10831; decide +kernel
    rw [ha]
    exact (canonical10831 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA638 + difference 0 4) (sourceB638 + difference 4 0) sourceC638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3121) := by
    have ha : (tripleCharges (sourceA638 + difference 0 4) (sourceB638 + difference 4 0) sourceC638) = raw10832 := by
      apply Matrix.ext; unfold tripleCharges sourceA638 sourceB638 sourceC638 difference raw10832; decide +kernel
    rw [ha]
    exact (canonical10832 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA638 + difference 0 5) (sourceB638 + difference 5 0) sourceC638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3101) := by
    have ha : (tripleCharges (sourceA638 + difference 0 5) (sourceB638 + difference 5 0) sourceC638) = raw10833 := by
      apply Matrix.ext; unfold tripleCharges sourceA638 sourceB638 sourceC638 difference raw10833; decide +kernel
    rw [ha]
    exact (canonical10833 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA638 + difference 1 0) (sourceB638 + difference 0 1) sourceC638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1443) := by
    have ha : (tripleCharges (sourceA638 + difference 1 0) (sourceB638 + difference 0 1) sourceC638) = raw10834 := by
      apply Matrix.ext; unfold tripleCharges sourceA638 sourceB638 sourceC638 difference raw10834; decide +kernel
    rw [ha]
    exact (canonical10834 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA638 + difference 1 2) (sourceB638 + difference 2 1) sourceC638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3211) := by
    have ha : (tripleCharges (sourceA638 + difference 1 2) (sourceB638 + difference 2 1) sourceC638) = raw10835 := by
      apply Matrix.ext; unfold tripleCharges sourceA638 sourceB638 sourceC638 difference raw10835; decide +kernel
    rw [ha]
    exact (canonical10835 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA638 + difference 1 3) (sourceB638 + difference 3 1) sourceC638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3211) := by
    have ha : (tripleCharges (sourceA638 + difference 1 3) (sourceB638 + difference 3 1) sourceC638) = raw10836 := by
      apply Matrix.ext; unfold tripleCharges sourceA638 sourceB638 sourceC638 difference raw10836; decide +kernel
    rw [ha]
    exact (canonical10836 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA638 + difference 1 4) (sourceB638 + difference 4 1) sourceC638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3231) := by
    have ha : (tripleCharges (sourceA638 + difference 1 4) (sourceB638 + difference 4 1) sourceC638) = raw10837 := by
      apply Matrix.ext; unfold tripleCharges sourceA638 sourceB638 sourceC638 difference raw10837; decide +kernel
    rw [ha]
    exact (canonical10837 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA638 + difference 1 5) (sourceB638 + difference 5 1) sourceC638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3229) := by
    have ha : (tripleCharges (sourceA638 + difference 1 5) (sourceB638 + difference 5 1) sourceC638) = raw10838 := by
      apply Matrix.ext; unfold tripleCharges sourceA638 sourceB638 sourceC638 difference raw10838; decide +kernel
    rw [ha]
    exact (canonical10838 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA638 + difference 2 0) (sourceB638 + difference 0 2) sourceC638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1370) := by
    have ha : (tripleCharges (sourceA638 + difference 2 0) (sourceB638 + difference 0 2) sourceC638) = raw10839 := by
      apply Matrix.ext; unfold tripleCharges sourceA638 sourceB638 sourceC638 difference raw10839; decide +kernel
    rw [ha]
    exact (canonical10839 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA638 + difference 2 1) (sourceB638 + difference 1 2) sourceC638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3158) := by
    have ha : (tripleCharges (sourceA638 + difference 2 1) (sourceB638 + difference 1 2) sourceC638) = raw10840 := by
      apply Matrix.ext; unfold tripleCharges sourceA638 sourceB638 sourceC638 difference raw10840; decide +kernel
    rw [ha]
    exact (canonical10840 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA638 + difference 2 3) (sourceB638 + difference 3 2) sourceC638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3197) := by
    have ha : (tripleCharges (sourceA638 + difference 2 3) (sourceB638 + difference 3 2) sourceC638) = raw10841 := by
      apply Matrix.ext; unfold tripleCharges sourceA638 sourceB638 sourceC638 difference raw10841; decide +kernel
    rw [ha]
    exact (canonical10841 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA638 + difference 2 4) (sourceB638 + difference 4 2) sourceC638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3225) := by
    have ha : (tripleCharges (sourceA638 + difference 2 4) (sourceB638 + difference 4 2) sourceC638) = raw10842 := by
      apply Matrix.ext; unfold tripleCharges sourceA638 sourceB638 sourceC638 difference raw10842; decide +kernel
    rw [ha]
    exact (canonical10842 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA638 + difference 2 5) (sourceB638 + difference 5 2) sourceC638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3223) := by
    have ha : (tripleCharges (sourceA638 + difference 2 5) (sourceB638 + difference 5 2) sourceC638) = raw10843 := by
      apply Matrix.ext; unfold tripleCharges sourceA638 sourceB638 sourceC638 difference raw10843; decide +kernel
    rw [ha]
    exact (canonical10843 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA638 + difference 3 0) (sourceB638 + difference 0 3) sourceC638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1370) := by
    have ha : (tripleCharges (sourceA638 + difference 3 0) (sourceB638 + difference 0 3) sourceC638) = raw10844 := by
      apply Matrix.ext; unfold tripleCharges sourceA638 sourceB638 sourceC638 difference raw10844; decide +kernel
    rw [ha]
    exact (canonical10844 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA638 + difference 3 1) (sourceB638 + difference 1 3) sourceC638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3158) := by
    have ha : (tripleCharges (sourceA638 + difference 3 1) (sourceB638 + difference 1 3) sourceC638) = raw10845 := by
      apply Matrix.ext; unfold tripleCharges sourceA638 sourceB638 sourceC638 difference raw10845; decide +kernel
    rw [ha]
    exact (canonical10845 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA638 + difference 3 2) (sourceB638 + difference 2 3) sourceC638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3197) := by
    have ha : (tripleCharges (sourceA638 + difference 3 2) (sourceB638 + difference 2 3) sourceC638) = raw10846 := by
      apply Matrix.ext; unfold tripleCharges sourceA638 sourceB638 sourceC638 difference raw10846; decide +kernel
    rw [ha]
    exact (canonical10846 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA638 + difference 3 4) (sourceB638 + difference 4 3) sourceC638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3225) := by
    have ha : (tripleCharges (sourceA638 + difference 3 4) (sourceB638 + difference 4 3) sourceC638) = raw10847 := by
      apply Matrix.ext; unfold tripleCharges sourceA638 sourceB638 sourceC638 difference raw10847; decide +kernel
    rw [ha]
    exact (canonical10847 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA638 + difference 3 5) (sourceB638 + difference 5 3) sourceC638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3223) := by
    have ha : (tripleCharges (sourceA638 + difference 3 5) (sourceB638 + difference 5 3) sourceC638) = raw10848 := by
      apply Matrix.ext; unfold tripleCharges sourceA638 sourceB638 sourceC638 difference raw10848; decide +kernel
    rw [ha]
    exact (canonical10848 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA638 + difference 4 0) (sourceB638 + difference 0 4) sourceC638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1375) := by
    have ha : (tripleCharges (sourceA638 + difference 4 0) (sourceB638 + difference 0 4) sourceC638) = raw10849 := by
      apply Matrix.ext; unfold tripleCharges sourceA638 sourceB638 sourceC638 difference raw10849; decide +kernel
    rw [ha]
    exact (canonical10849 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA638 + difference 4 1) (sourceB638 + difference 1 4) sourceC638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3161) := by
    have ha : (tripleCharges (sourceA638 + difference 4 1) (sourceB638 + difference 1 4) sourceC638) = raw10850 := by
      apply Matrix.ext; unfold tripleCharges sourceA638 sourceB638 sourceC638 difference raw10850; decide +kernel
    rw [ha]
    exact (canonical10850 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA638 + difference 4 2) (sourceB638 + difference 2 4) sourceC638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3198) := by
    have ha : (tripleCharges (sourceA638 + difference 4 2) (sourceB638 + difference 2 4) sourceC638) = raw10851 := by
      apply Matrix.ext; unfold tripleCharges sourceA638 sourceB638 sourceC638 difference raw10851; decide +kernel
    rw [ha]
    exact (canonical10851 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA638 + difference 4 3) (sourceB638 + difference 3 4) sourceC638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3198) := by
    have ha : (tripleCharges (sourceA638 + difference 4 3) (sourceB638 + difference 3 4) sourceC638) = raw10852 := by
      apply Matrix.ext; unfold tripleCharges sourceA638 sourceB638 sourceC638 difference raw10852; decide +kernel
    rw [ha]
    exact (canonical10852 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA638 + difference 4 5) (sourceB638 + difference 5 4) sourceC638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3224) := by
    have ha : (tripleCharges (sourceA638 + difference 4 5) (sourceB638 + difference 5 4) sourceC638) = raw10853 := by
      apply Matrix.ext; unfold tripleCharges sourceA638 sourceB638 sourceC638 difference raw10853; decide +kernel
    rw [ha]
    exact (canonical10853 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA638 + difference 5 0) (sourceB638 + difference 0 5) sourceC638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1372) := by
    have ha : (tripleCharges (sourceA638 + difference 5 0) (sourceB638 + difference 0 5) sourceC638) = raw10854 := by
      apply Matrix.ext; unfold tripleCharges sourceA638 sourceB638 sourceC638 difference raw10854; decide +kernel
    rw [ha]
    exact (canonical10854 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA638 + difference 5 1) (sourceB638 + difference 1 5) sourceC638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2520) := by
    have ha : (tripleCharges (sourceA638 + difference 5 1) (sourceB638 + difference 1 5) sourceC638) = raw10855 := by
      apply Matrix.ext; unfold tripleCharges sourceA638 sourceB638 sourceC638 difference raw10855; decide +kernel
    rw [ha]
    exact (canonical10855 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA638 + difference 5 2) (sourceB638 + difference 2 5) sourceC638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2497) := by
    have ha : (tripleCharges (sourceA638 + difference 5 2) (sourceB638 + difference 2 5) sourceC638) = raw10856 := by
      apply Matrix.ext; unfold tripleCharges sourceA638 sourceB638 sourceC638 difference raw10856; decide +kernel
    rw [ha]
    exact (canonical10856 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA638 + difference 5 3) (sourceB638 + difference 3 5) sourceC638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2497) := by
    have ha : (tripleCharges (sourceA638 + difference 5 3) (sourceB638 + difference 3 5) sourceC638) = raw10857 := by
      apply Matrix.ext; unfold tripleCharges sourceA638 sourceB638 sourceC638 difference raw10857; decide +kernel
    rw [ha]
    exact (canonical10857 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA638 + difference 5 4) (sourceB638 + difference 4 5) sourceC638) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2778) := by
    have ha : (tripleCharges (sourceA638 + difference 5 4) (sourceB638 + difference 4 5) sourceC638) = raw10858 := by
      apply Matrix.ext; unfold tripleCharges sourceA638 sourceB638 sourceC638 difference raw10858; decide +kernel
    rw [ha]
    exact (canonical10858 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA638 sourceB638 sourceC638
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm638, Integer.Sparse.eval]
  linarith only [hs]

def sourceA639 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB639 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceC639 : Charge := ![3, -2, 0, 0, 0, -1]
def sourceForm639 : Integer.Sparse Master := [(Sum.inr 1709, 2), (Sum.inr 1728, 1), (Sum.inr 1729, 1), (Sum.inr 1740, 1), (Sum.inr 2192, 2), (Sum.inr 2206, 2), (Sum.inr 2207, 2), (Sum.inr 2217, 2), (Sum.inr 2245, 2), (Sum.inr 2246, 2), (Sum.inr 2265, 1), (Sum.inr 2266, 2), (Sum.inr 2267, 1), (Sum.inr 2279, 1), (Sum.inr 2280, 1), (Sum.inr 2293, 1), (Sum.inr 2294, 1), (Sum.inr 2724, 2), (Sum.inr 2768, 1), (Sum.inr 2769, 1), (Sum.inr 2788, 1)]

theorem sourceEq639 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm639 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA639 + difference 0 1) (sourceB639 + difference 1 0) sourceC639) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2769) := by
    have ha : (tripleCharges (sourceA639 + difference 0 1) (sourceB639 + difference 1 0) sourceC639) = raw10859 := by
      apply Matrix.ext; unfold tripleCharges sourceA639 sourceB639 sourceC639 difference raw10859; decide +kernel
    rw [ha]
    exact (canonical10859 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA639 + difference 0 2) (sourceB639 + difference 2 0) sourceC639) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2724) := by
    have ha : (tripleCharges (sourceA639 + difference 0 2) (sourceB639 + difference 2 0) sourceC639) = raw10860 := by
      apply Matrix.ext; unfold tripleCharges sourceA639 sourceB639 sourceC639 difference raw10860; decide +kernel
    rw [ha]
    exact (canonical10860 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA639 + difference 0 3) (sourceB639 + difference 3 0) sourceC639) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2724) := by
    have ha : (tripleCharges (sourceA639 + difference 0 3) (sourceB639 + difference 3 0) sourceC639) = raw10861 := by
      apply Matrix.ext; unfold tripleCharges sourceA639 sourceB639 sourceC639 difference raw10861; decide +kernel
    rw [ha]
    exact (canonical10861 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA639 + difference 0 4) (sourceB639 + difference 4 0) sourceC639) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2788) := by
    have ha : (tripleCharges (sourceA639 + difference 0 4) (sourceB639 + difference 4 0) sourceC639) = raw10862 := by
      apply Matrix.ext; unfold tripleCharges sourceA639 sourceB639 sourceC639 difference raw10862; decide +kernel
    rw [ha]
    exact (canonical10862 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA639 + difference 0 5) (sourceB639 + difference 5 0) sourceC639) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2768) := by
    have ha : (tripleCharges (sourceA639 + difference 0 5) (sourceB639 + difference 5 0) sourceC639) = raw10863 := by
      apply Matrix.ext; unfold tripleCharges sourceA639 sourceB639 sourceC639 difference raw10863; decide +kernel
    rw [ha]
    exact (canonical10863 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA639 + difference 1 0) (sourceB639 + difference 0 1) sourceC639) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1728) := by
    have ha : (tripleCharges (sourceA639 + difference 1 0) (sourceB639 + difference 0 1) sourceC639) = raw10864 := by
      apply Matrix.ext; unfold tripleCharges sourceA639 sourceB639 sourceC639 difference raw10864; decide +kernel
    rw [ha]
    exact (canonical10864 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA639 + difference 1 2) (sourceB639 + difference 2 1) sourceC639) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2206) := by
    have ha : (tripleCharges (sourceA639 + difference 1 2) (sourceB639 + difference 2 1) sourceC639) = raw10865 := by
      apply Matrix.ext; unfold tripleCharges sourceA639 sourceB639 sourceC639 difference raw10865; decide +kernel
    rw [ha]
    exact (canonical10865 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA639 + difference 1 3) (sourceB639 + difference 3 1) sourceC639) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2206) := by
    have ha : (tripleCharges (sourceA639 + difference 1 3) (sourceB639 + difference 3 1) sourceC639) = raw10866 := by
      apply Matrix.ext; unfold tripleCharges sourceA639 sourceB639 sourceC639 difference raw10866; decide +kernel
    rw [ha]
    exact (canonical10866 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA639 + difference 1 4) (sourceB639 + difference 4 1) sourceC639) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2293) := by
    have ha : (tripleCharges (sourceA639 + difference 1 4) (sourceB639 + difference 4 1) sourceC639) = raw10867 := by
      apply Matrix.ext; unfold tripleCharges sourceA639 sourceB639 sourceC639 difference raw10867; decide +kernel
    rw [ha]
    exact (canonical10867 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA639 + difference 1 5) (sourceB639 + difference 5 1) sourceC639) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2265) := by
    have ha : (tripleCharges (sourceA639 + difference 1 5) (sourceB639 + difference 5 1) sourceC639) = raw10868 := by
      apply Matrix.ext; unfold tripleCharges sourceA639 sourceB639 sourceC639 difference raw10868; decide +kernel
    rw [ha]
    exact (canonical10868 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA639 + difference 2 0) (sourceB639 + difference 0 2) sourceC639) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1709) := by
    have ha : (tripleCharges (sourceA639 + difference 2 0) (sourceB639 + difference 0 2) sourceC639) = raw10869 := by
      apply Matrix.ext; unfold tripleCharges sourceA639 sourceB639 sourceC639 difference raw10869; decide +kernel
    rw [ha]
    exact (canonical10869 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA639 + difference 2 1) (sourceB639 + difference 1 2) sourceC639) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2246) := by
    have ha : (tripleCharges (sourceA639 + difference 2 1) (sourceB639 + difference 1 2) sourceC639) = raw10870 := by
      apply Matrix.ext; unfold tripleCharges sourceA639 sourceB639 sourceC639 difference raw10870; decide +kernel
    rw [ha]
    exact (canonical10870 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA639 + difference 2 3) (sourceB639 + difference 3 2) sourceC639) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2192) := by
    have ha : (tripleCharges (sourceA639 + difference 2 3) (sourceB639 + difference 3 2) sourceC639) = raw10871 := by
      apply Matrix.ext; unfold tripleCharges sourceA639 sourceB639 sourceC639 difference raw10871; decide +kernel
    rw [ha]
    exact (canonical10871 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA639 + difference 2 4) (sourceB639 + difference 4 2) sourceC639) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2266) := by
    have ha : (tripleCharges (sourceA639 + difference 2 4) (sourceB639 + difference 4 2) sourceC639) = raw10872 := by
      apply Matrix.ext; unfold tripleCharges sourceA639 sourceB639 sourceC639 difference raw10872; decide +kernel
    rw [ha]
    exact (canonical10872 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA639 + difference 2 5) (sourceB639 + difference 5 2) sourceC639) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2245) := by
    have ha : (tripleCharges (sourceA639 + difference 2 5) (sourceB639 + difference 5 2) sourceC639) = raw10873 := by
      apply Matrix.ext; unfold tripleCharges sourceA639 sourceB639 sourceC639 difference raw10873; decide +kernel
    rw [ha]
    exact (canonical10873 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA639 + difference 3 0) (sourceB639 + difference 0 3) sourceC639) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1709) := by
    have ha : (tripleCharges (sourceA639 + difference 3 0) (sourceB639 + difference 0 3) sourceC639) = raw10874 := by
      apply Matrix.ext; unfold tripleCharges sourceA639 sourceB639 sourceC639 difference raw10874; decide +kernel
    rw [ha]
    exact (canonical10874 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA639 + difference 3 1) (sourceB639 + difference 1 3) sourceC639) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2246) := by
    have ha : (tripleCharges (sourceA639 + difference 3 1) (sourceB639 + difference 1 3) sourceC639) = raw10875 := by
      apply Matrix.ext; unfold tripleCharges sourceA639 sourceB639 sourceC639 difference raw10875; decide +kernel
    rw [ha]
    exact (canonical10875 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA639 + difference 3 2) (sourceB639 + difference 2 3) sourceC639) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2192) := by
    have ha : (tripleCharges (sourceA639 + difference 3 2) (sourceB639 + difference 2 3) sourceC639) = raw10876 := by
      apply Matrix.ext; unfold tripleCharges sourceA639 sourceB639 sourceC639 difference raw10876; decide +kernel
    rw [ha]
    exact (canonical10876 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA639 + difference 3 4) (sourceB639 + difference 4 3) sourceC639) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2266) := by
    have ha : (tripleCharges (sourceA639 + difference 3 4) (sourceB639 + difference 4 3) sourceC639) = raw10877 := by
      apply Matrix.ext; unfold tripleCharges sourceA639 sourceB639 sourceC639 difference raw10877; decide +kernel
    rw [ha]
    exact (canonical10877 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA639 + difference 3 5) (sourceB639 + difference 5 3) sourceC639) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2245) := by
    have ha : (tripleCharges (sourceA639 + difference 3 5) (sourceB639 + difference 5 3) sourceC639) = raw10878 := by
      apply Matrix.ext; unfold tripleCharges sourceA639 sourceB639 sourceC639 difference raw10878; decide +kernel
    rw [ha]
    exact (canonical10878 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA639 + difference 4 0) (sourceB639 + difference 0 4) sourceC639) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1740) := by
    have ha : (tripleCharges (sourceA639 + difference 4 0) (sourceB639 + difference 0 4) sourceC639) = raw10879 := by
      apply Matrix.ext; unfold tripleCharges sourceA639 sourceB639 sourceC639 difference raw10879; decide +kernel
    rw [ha]
    exact (canonical10879 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA639 + difference 4 1) (sourceB639 + difference 1 4) sourceC639) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2280) := by
    have ha : (tripleCharges (sourceA639 + difference 4 1) (sourceB639 + difference 1 4) sourceC639) = raw10880 := by
      apply Matrix.ext; unfold tripleCharges sourceA639 sourceB639 sourceC639 difference raw10880; decide +kernel
    rw [ha]
    exact (canonical10880 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA639 + difference 4 2) (sourceB639 + difference 2 4) sourceC639) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2217) := by
    have ha : (tripleCharges (sourceA639 + difference 4 2) (sourceB639 + difference 2 4) sourceC639) = raw10881 := by
      apply Matrix.ext; unfold tripleCharges sourceA639 sourceB639 sourceC639 difference raw10881; decide +kernel
    rw [ha]
    exact (canonical10881 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA639 + difference 4 3) (sourceB639 + difference 3 4) sourceC639) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2217) := by
    have ha : (tripleCharges (sourceA639 + difference 4 3) (sourceB639 + difference 3 4) sourceC639) = raw10882 := by
      apply Matrix.ext; unfold tripleCharges sourceA639 sourceB639 sourceC639 difference raw10882; decide +kernel
    rw [ha]
    exact (canonical10882 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA639 + difference 4 5) (sourceB639 + difference 5 4) sourceC639) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2279) := by
    have ha : (tripleCharges (sourceA639 + difference 4 5) (sourceB639 + difference 5 4) sourceC639) = raw10883 := by
      apply Matrix.ext; unfold tripleCharges sourceA639 sourceB639 sourceC639 difference raw10883; decide +kernel
    rw [ha]
    exact (canonical10883 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA639 + difference 5 0) (sourceB639 + difference 0 5) sourceC639) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1729) := by
    have ha : (tripleCharges (sourceA639 + difference 5 0) (sourceB639 + difference 0 5) sourceC639) = raw10884 := by
      apply Matrix.ext; unfold tripleCharges sourceA639 sourceB639 sourceC639 difference raw10884; decide +kernel
    rw [ha]
    exact (canonical10884 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA639 + difference 5 1) (sourceB639 + difference 1 5) sourceC639) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2267) := by
    have ha : (tripleCharges (sourceA639 + difference 5 1) (sourceB639 + difference 1 5) sourceC639) = raw10885 := by
      apply Matrix.ext; unfold tripleCharges sourceA639 sourceB639 sourceC639 difference raw10885; decide +kernel
    rw [ha]
    exact (canonical10885 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA639 + difference 5 2) (sourceB639 + difference 2 5) sourceC639) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2207) := by
    have ha : (tripleCharges (sourceA639 + difference 5 2) (sourceB639 + difference 2 5) sourceC639) = raw10886 := by
      apply Matrix.ext; unfold tripleCharges sourceA639 sourceB639 sourceC639 difference raw10886; decide +kernel
    rw [ha]
    exact (canonical10886 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA639 + difference 5 3) (sourceB639 + difference 3 5) sourceC639) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2207) := by
    have ha : (tripleCharges (sourceA639 + difference 5 3) (sourceB639 + difference 3 5) sourceC639) = raw10887 := by
      apply Matrix.ext; unfold tripleCharges sourceA639 sourceB639 sourceC639 difference raw10887; decide +kernel
    rw [ha]
    exact (canonical10887 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA639 + difference 5 4) (sourceB639 + difference 4 5) sourceC639) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2294) := by
    have ha : (tripleCharges (sourceA639 + difference 5 4) (sourceB639 + difference 4 5) sourceC639) = raw10888 := by
      apply Matrix.ext; unfold tripleCharges sourceA639 sourceB639 sourceC639 difference raw10888; decide +kernel
    rw [ha]
    exact (canonical10888 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA639 sourceB639 sourceC639
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm639, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
