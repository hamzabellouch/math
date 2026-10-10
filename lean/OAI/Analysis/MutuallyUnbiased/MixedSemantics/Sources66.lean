import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical94
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical138
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical143
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical159
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical167
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical174
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical175
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical176
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical181
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical189
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical191
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical193
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical214
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical215
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical223
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical229
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical230
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical231

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA2112 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2112 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceC2112 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceForm2112 : Integer.Sparse Master := [(Sum.inr 2320, 1), (Sum.inr 2797, 1), (Sum.inr 2900, 1), (Sum.inr 2931, 1), (Sum.inr 2981, 1), (Sum.inr 3690, 1), (Sum.inr 4091, -1)]

theorem sourceEq2112 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2112 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2112 + difference 0 2) (sourceB2112 + difference 2 0) sourceC2112) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3690) := by
    have ha : (tripleCharges (sourceA2112 + difference 0 2) (sourceB2112 + difference 2 0) sourceC2112) = raw29408 := by
      apply Matrix.ext; unfold tripleCharges sourceA2112 sourceB2112 sourceC2112 difference raw29408; decide +kernel
    rw [ha]
    exact (canonical29408 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2112 + difference 1 2) (sourceB2112 + difference 2 1) sourceC2112) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2931) := by
    have ha : (tripleCharges (sourceA2112 + difference 1 2) (sourceB2112 + difference 2 1) sourceC2112) = raw9031 := by
      apply Matrix.ext; unfold tripleCharges sourceA2112 sourceB2112 sourceC2112 difference raw9031; decide +kernel
    rw [ha]
    exact (canonical9031 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2112 + difference 2 2) (sourceB2112 + difference 2 2) sourceC2112) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2981) := by
    have ha : (tripleCharges (sourceA2112 + difference 2 2) (sourceB2112 + difference 2 2) sourceC2112) = raw9025 := by
      apply Matrix.ext; unfold tripleCharges sourceA2112 sourceB2112 sourceC2112 difference raw9025; decide +kernel
    rw [ha]
    exact (canonical9025 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2112 + difference 3 2) (sourceB2112 + difference 2 3) sourceC2112) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2900) := by
    have ha : (tripleCharges (sourceA2112 + difference 3 2) (sourceB2112 + difference 2 3) sourceC2112) = raw29409 := by
      apply Matrix.ext; unfold tripleCharges sourceA2112 sourceB2112 sourceC2112 difference raw29409; decide +kernel
    rw [ha]
    exact (canonical29409 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2112 + difference 4 2) (sourceB2112 + difference 2 4) sourceC2112) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2320) := by
    have ha : (tripleCharges (sourceA2112 + difference 4 2) (sourceB2112 + difference 2 4) sourceC2112) = raw29410 := by
      apply Matrix.ext; unfold tripleCharges sourceA2112 sourceB2112 sourceC2112 difference raw29410; decide +kernel
    rw [ha]
    exact (canonical29410 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2112 + difference 5 2) (sourceB2112 + difference 2 5) sourceC2112) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2797) := by
    have ha : (tripleCharges (sourceA2112 + difference 5 2) (sourceB2112 + difference 2 5) sourceC2112) = raw29411 := by
      apply Matrix.ext; unfold tripleCharges sourceA2112 sourceB2112 sourceC2112 difference raw29411; decide +kernel
    rw [ha]
    exact (canonical29411 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2112 + sourceB2112) sourceC2112) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA2112 + sourceB2112) sourceC2112) = raw9013 := by
      apply Matrix.ext; unfold doubleCharges sourceA2112 sourceB2112 sourceC2112 raw9013; decide +kernel
    rw [ha]
    exact (canonical9013 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2112 sourceB2112 sourceC2112
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2112, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2113 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceB2113 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceC2113 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceForm2113 : Integer.Sparse Master := [(Sum.inr 2381, 1), (Sum.inr 3476, 1), (Sum.inr 3487, 1), (Sum.inr 3491, 1), (Sum.inr 3522, 2), (Sum.inr 4082, -1)]

theorem sourceEq2113 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2113 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2113 + difference 0 0) (sourceB2113 + difference 0 0) sourceC2113) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3476) := by
    have ha : (tripleCharges (sourceA2113 + difference 0 0) (sourceB2113 + difference 0 0) sourceC2113) = raw29328 := by
      apply Matrix.ext; unfold tripleCharges sourceA2113 sourceB2113 sourceC2113 difference raw29328; decide +kernel
    rw [ha]
    exact (canonical29328 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2113 + difference 0 1) (sourceB2113 + difference 1 0) sourceC2113) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3491) := by
    have ha : (tripleCharges (sourceA2113 + difference 0 1) (sourceB2113 + difference 1 0) sourceC2113) = raw29412 := by
      apply Matrix.ext; unfold tripleCharges sourceA2113 sourceB2113 sourceC2113 difference raw29412; decide +kernel
    rw [ha]
    exact (canonical29412 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2113 + difference 0 2) (sourceB2113 + difference 2 0) sourceC2113) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3522) := by
    have ha : (tripleCharges (sourceA2113 + difference 0 2) (sourceB2113 + difference 2 0) sourceC2113) = raw29391 := by
      apply Matrix.ext; unfold tripleCharges sourceA2113 sourceB2113 sourceC2113 difference raw29391; decide +kernel
    rw [ha]
    exact (canonical29391 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2113 + difference 0 3) (sourceB2113 + difference 3 0) sourceC2113) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3522) := by
    have ha : (tripleCharges (sourceA2113 + difference 0 3) (sourceB2113 + difference 3 0) sourceC2113) = raw29413 := by
      apply Matrix.ext; unfold tripleCharges sourceA2113 sourceB2113 sourceC2113 difference raw29413; decide +kernel
    rw [ha]
    exact (canonical29413 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2113 + difference 0 4) (sourceB2113 + difference 4 0) sourceC2113) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2381) := by
    have ha : (tripleCharges (sourceA2113 + difference 0 4) (sourceB2113 + difference 4 0) sourceC2113) = raw29414 := by
      apply Matrix.ext; unfold tripleCharges sourceA2113 sourceB2113 sourceC2113 difference raw29414; decide +kernel
    rw [ha]
    exact (canonical29414 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2113 + difference 0 5) (sourceB2113 + difference 5 0) sourceC2113) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3487) := by
    have ha : (tripleCharges (sourceA2113 + difference 0 5) (sourceB2113 + difference 5 0) sourceC2113) = raw29415 := by
      apply Matrix.ext; unfold tripleCharges sourceA2113 sourceB2113 sourceC2113 difference raw29415; decide +kernel
    rw [ha]
    exact (canonical29415 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2113 + sourceB2113) sourceC2113) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2113 + sourceB2113) sourceC2113) = raw29319 := by
      apply Matrix.ext; unfold doubleCharges sourceA2113 sourceB2113 sourceC2113 raw29319; decide +kernel
    rw [ha]
    exact (canonical29319 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2113 sourceB2113 sourceC2113
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2113, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2114 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceB2114 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceC2114 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceForm2114 : Integer.Sparse Master := [(Sum.inr 1941, 1), (Sum.inr 3351, 1), (Sum.inr 3476, 2), (Sum.inr 3482, 2), (Sum.inr 4082, -1)]

theorem sourceEq2114 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2114 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2114 + difference 4 0) (sourceB2114 + difference 0 4) sourceC2114) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1941) := by
    have ha : (tripleCharges (sourceA2114 + difference 4 0) (sourceB2114 + difference 0 4) sourceC2114) = raw29416 := by
      apply Matrix.ext; unfold tripleCharges sourceA2114 sourceB2114 sourceC2114 difference raw29416; decide +kernel
    rw [ha]
    exact (canonical29416 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2114 + difference 4 1) (sourceB2114 + difference 1 4) sourceC2114) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3351) := by
    have ha : (tripleCharges (sourceA2114 + difference 4 1) (sourceB2114 + difference 1 4) sourceC2114) = raw29417 := by
      apply Matrix.ext; unfold tripleCharges sourceA2114 sourceB2114 sourceC2114 difference raw29417; decide +kernel
    rw [ha]
    exact (canonical29417 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2114 + difference 4 2) (sourceB2114 + difference 2 4) sourceC2114) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3482) := by
    have ha : (tripleCharges (sourceA2114 + difference 4 2) (sourceB2114 + difference 2 4) sourceC2114) = raw29394 := by
      apply Matrix.ext; unfold tripleCharges sourceA2114 sourceB2114 sourceC2114 difference raw29394; decide +kernel
    rw [ha]
    exact (canonical29394 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2114 + difference 4 3) (sourceB2114 + difference 3 4) sourceC2114) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3482) := by
    have ha : (tripleCharges (sourceA2114 + difference 4 3) (sourceB2114 + difference 3 4) sourceC2114) = raw29418 := by
      apply Matrix.ext; unfold tripleCharges sourceA2114 sourceB2114 sourceC2114 difference raw29418; decide +kernel
    rw [ha]
    exact (canonical29418 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2114 + difference 4 4) (sourceB2114 + difference 4 4) sourceC2114) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3476) := by
    have ha : (tripleCharges (sourceA2114 + difference 4 4) (sourceB2114 + difference 4 4) sourceC2114) = raw29328 := by
      apply Matrix.ext; unfold tripleCharges sourceA2114 sourceB2114 sourceC2114 difference raw29328; decide +kernel
    rw [ha]
    exact (canonical29328 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2114 + difference 4 5) (sourceB2114 + difference 5 4) sourceC2114) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3476) := by
    have ha : (tripleCharges (sourceA2114 + difference 4 5) (sourceB2114 + difference 5 4) sourceC2114) = raw29419 := by
      apply Matrix.ext; unfold tripleCharges sourceA2114 sourceB2114 sourceC2114 difference raw29419; decide +kernel
    rw [ha]
    exact (canonical29419 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2114 + sourceB2114) sourceC2114) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2114 + sourceB2114) sourceC2114) = raw29319 := by
      apply Matrix.ext; unfold doubleCharges sourceA2114 sourceB2114 sourceC2114 raw29319; decide +kernel
    rw [ha]
    exact (canonical29319 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2114 sourceB2114 sourceC2114
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2114, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2115 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceB2115 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceC2115 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceForm2115 : Integer.Sparse Master := [(Sum.inr 1921, 1), (Sum.inr 2668, 1), (Sum.inr 3345, 1), (Sum.inr 3476, 1), (Sum.inr 3478, 2), (Sum.inr 4082, -1)]

theorem sourceEq2115 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2115 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2115 + difference 5 0) (sourceB2115 + difference 0 5) sourceC2115) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1921) := by
    have ha : (tripleCharges (sourceA2115 + difference 5 0) (sourceB2115 + difference 0 5) sourceC2115) = raw29420 := by
      apply Matrix.ext; unfold tripleCharges sourceA2115 sourceB2115 sourceC2115 difference raw29420; decide +kernel
    rw [ha]
    exact (canonical29420 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2115 + difference 5 1) (sourceB2115 + difference 1 5) sourceC2115) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3345) := by
    have ha : (tripleCharges (sourceA2115 + difference 5 1) (sourceB2115 + difference 1 5) sourceC2115) = raw29421 := by
      apply Matrix.ext; unfold tripleCharges sourceA2115 sourceB2115 sourceC2115 difference raw29421; decide +kernel
    rw [ha]
    exact (canonical29421 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2115 + difference 5 2) (sourceB2115 + difference 2 5) sourceC2115) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3478) := by
    have ha : (tripleCharges (sourceA2115 + difference 5 2) (sourceB2115 + difference 2 5) sourceC2115) = raw29395 := by
      apply Matrix.ext; unfold tripleCharges sourceA2115 sourceB2115 sourceC2115 difference raw29395; decide +kernel
    rw [ha]
    exact (canonical29395 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2115 + difference 5 3) (sourceB2115 + difference 3 5) sourceC2115) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3478) := by
    have ha : (tripleCharges (sourceA2115 + difference 5 3) (sourceB2115 + difference 3 5) sourceC2115) = raw29422 := by
      apply Matrix.ext; unfold tripleCharges sourceA2115 sourceB2115 sourceC2115 difference raw29422; decide +kernel
    rw [ha]
    exact (canonical29422 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2115 + difference 5 4) (sourceB2115 + difference 4 5) sourceC2115) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2668) := by
    have ha : (tripleCharges (sourceA2115 + difference 5 4) (sourceB2115 + difference 4 5) sourceC2115) = raw29423 := by
      apply Matrix.ext; unfold tripleCharges sourceA2115 sourceB2115 sourceC2115 difference raw29423; decide +kernel
    rw [ha]
    exact (canonical29423 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2115 + difference 5 5) (sourceB2115 + difference 5 5) sourceC2115) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3476) := by
    have ha : (tripleCharges (sourceA2115 + difference 5 5) (sourceB2115 + difference 5 5) sourceC2115) = raw29328 := by
      apply Matrix.ext; unfold tripleCharges sourceA2115 sourceB2115 sourceC2115 difference raw29328; decide +kernel
    rw [ha]
    exact (canonical29328 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2115 + sourceB2115) sourceC2115) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2115 + sourceB2115) sourceC2115) = raw29319 := by
      apply Matrix.ext; unfold doubleCharges sourceA2115 sourceB2115 sourceC2115 raw29319; decide +kernel
    rw [ha]
    exact (canonical29319 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2115 sourceB2115 sourceC2115
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2115, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2116 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceB2116 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceC2116 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceForm2116 : Integer.Sparse Master := [(Sum.inr 3473, 2), (Sum.inr 3476, 2), (Sum.inr 3487, 1), (Sum.inr 3610, 1), (Sum.inr 4082, -1)]

theorem sourceEq2116 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2116 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2116 + difference 0 5) (sourceB2116 + difference 5 0) sourceC2116) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3487) := by
    have ha : (tripleCharges (sourceA2116 + difference 0 5) (sourceB2116 + difference 5 0) sourceC2116) = raw29415 := by
      apply Matrix.ext; unfold tripleCharges sourceA2116 sourceB2116 sourceC2116 difference raw29415; decide +kernel
    rw [ha]
    exact (canonical29415 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2116 + difference 1 5) (sourceB2116 + difference 5 1) sourceC2116) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3610) := by
    have ha : (tripleCharges (sourceA2116 + difference 1 5) (sourceB2116 + difference 5 1) sourceC2116) = raw29331 := by
      apply Matrix.ext; unfold tripleCharges sourceA2116 sourceB2116 sourceC2116 difference raw29331; decide +kernel
    rw [ha]
    exact (canonical29331 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2116 + difference 2 5) (sourceB2116 + difference 5 2) sourceC2116) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3473) := by
    have ha : (tripleCharges (sourceA2116 + difference 2 5) (sourceB2116 + difference 5 2) sourceC2116) = raw29424 := by
      apply Matrix.ext; unfold tripleCharges sourceA2116 sourceB2116 sourceC2116 difference raw29424; decide +kernel
    rw [ha]
    exact (canonical29424 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2116 + difference 3 5) (sourceB2116 + difference 5 3) sourceC2116) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3473) := by
    have ha : (tripleCharges (sourceA2116 + difference 3 5) (sourceB2116 + difference 5 3) sourceC2116) = raw29425 := by
      apply Matrix.ext; unfold tripleCharges sourceA2116 sourceB2116 sourceC2116 difference raw29425; decide +kernel
    rw [ha]
    exact (canonical29425 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2116 + difference 4 5) (sourceB2116 + difference 5 4) sourceC2116) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3476) := by
    have ha : (tripleCharges (sourceA2116 + difference 4 5) (sourceB2116 + difference 5 4) sourceC2116) = raw29419 := by
      apply Matrix.ext; unfold tripleCharges sourceA2116 sourceB2116 sourceC2116 difference raw29419; decide +kernel
    rw [ha]
    exact (canonical29419 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2116 + difference 5 5) (sourceB2116 + difference 5 5) sourceC2116) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3476) := by
    have ha : (tripleCharges (sourceA2116 + difference 5 5) (sourceB2116 + difference 5 5) sourceC2116) = raw29328 := by
      apply Matrix.ext; unfold tripleCharges sourceA2116 sourceB2116 sourceC2116 difference raw29328; decide +kernel
    rw [ha]
    exact (canonical29328 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2116 + sourceB2116) sourceC2116) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2116 + sourceB2116) sourceC2116) = raw29319 := by
      apply Matrix.ext; unfold doubleCharges sourceA2116 sourceB2116 sourceC2116 raw29319; decide +kernel
    rw [ha]
    exact (canonical29319 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2116 sourceB2116 sourceC2116
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2116, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2117 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2117 : Charge := ![2, 1, -1, -2, 0, 0]
def sourceC2117 : Charge := ![1, 0, 1, 2, -2, -2]
def sourceForm2117 : Integer.Sparse Master := [(Sum.inr 2970, 1), (Sum.inr 3648, 1), (Sum.inr 3651, 1), (Sum.inr 3657, 1), (Sum.inr 3761, 2), (Sum.inr 4088, -1)]

theorem sourceEq2117 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2117 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2117 + difference 0 0) (sourceB2117 + difference 0 0) sourceC2117) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2970) := by
    have ha : (tripleCharges (sourceA2117 + difference 0 0) (sourceB2117 + difference 0 0) sourceC2117) = raw22379 := by
      apply Matrix.ext; unfold tripleCharges sourceA2117 sourceB2117 sourceC2117 difference raw22379; decide +kernel
    rw [ha]
    exact (canonical22379 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2117 + difference 0 1) (sourceB2117 + difference 1 0) sourceC2117) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3648) := by
    have ha : (tripleCharges (sourceA2117 + difference 0 1) (sourceB2117 + difference 1 0) sourceC2117) = raw29426 := by
      apply Matrix.ext; unfold tripleCharges sourceA2117 sourceB2117 sourceC2117 difference raw29426; decide +kernel
    rw [ha]
    exact (canonical29426 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2117 + difference 0 2) (sourceB2117 + difference 2 0) sourceC2117) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3657) := by
    have ha : (tripleCharges (sourceA2117 + difference 0 2) (sourceB2117 + difference 2 0) sourceC2117) = raw29427 := by
      apply Matrix.ext; unfold tripleCharges sourceA2117 sourceB2117 sourceC2117 difference raw29427; decide +kernel
    rw [ha]
    exact (canonical29427 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2117 + difference 0 3) (sourceB2117 + difference 3 0) sourceC2117) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3651) := by
    have ha : (tripleCharges (sourceA2117 + difference 0 3) (sourceB2117 + difference 3 0) sourceC2117) = raw29428 := by
      apply Matrix.ext; unfold tripleCharges sourceA2117 sourceB2117 sourceC2117 difference raw29428; decide +kernel
    rw [ha]
    exact (canonical29428 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2117 + difference 0 4) (sourceB2117 + difference 4 0) sourceC2117) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3761) := by
    have ha : (tripleCharges (sourceA2117 + difference 0 4) (sourceB2117 + difference 4 0) sourceC2117) = raw29429 := by
      apply Matrix.ext; unfold tripleCharges sourceA2117 sourceB2117 sourceC2117 difference raw29429; decide +kernel
    rw [ha]
    exact (canonical29429 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2117 + difference 0 5) (sourceB2117 + difference 5 0) sourceC2117) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3761) := by
    have ha : (tripleCharges (sourceA2117 + difference 0 5) (sourceB2117 + difference 5 0) sourceC2117) = raw29430 := by
      apply Matrix.ext; unfold tripleCharges sourceA2117 sourceB2117 sourceC2117 difference raw29430; decide +kernel
    rw [ha]
    exact (canonical29430 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2117 + sourceB2117) sourceC2117) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA2117 + sourceB2117) sourceC2117) = raw22384 := by
      apply Matrix.ext; unfold doubleCharges sourceA2117 sourceB2117 sourceC2117 raw22384; decide +kernel
    rw [ha]
    exact (canonical22384 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2117 sourceB2117 sourceC2117
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2117, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2118 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2118 : Charge := ![1, 1, -1, 0, -2, 1]
def sourceC2118 : Charge := ![2, 0, 1, 0, 0, -3]
def sourceForm2118 : Integer.Sparse Master := [(Sum.inr 1807, 1), (Sum.inr 2427, 1), (Sum.inr 2435, 1), (Sum.inr 2522, 1), (Sum.inr 2560, 1), (Sum.inr 3391, 1), (Sum.inr 4084, -1)]

theorem sourceEq2118 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2118 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2118 + difference 0 2) (sourceB2118 + difference 2 0) sourceC2118) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3391) := by
    have ha : (tripleCharges (sourceA2118 + difference 0 2) (sourceB2118 + difference 2 0) sourceC2118) = raw29431 := by
      apply Matrix.ext; unfold tripleCharges sourceA2118 sourceB2118 sourceC2118 difference raw29431; decide +kernel
    rw [ha]
    exact (canonical29431 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2118 + difference 1 2) (sourceB2118 + difference 2 1) sourceC2118) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2522) := by
    have ha : (tripleCharges (sourceA2118 + difference 1 2) (sourceB2118 + difference 2 1) sourceC2118) = raw29432 := by
      apply Matrix.ext; unfold tripleCharges sourceA2118 sourceB2118 sourceC2118 difference raw29432; decide +kernel
    rw [ha]
    exact (canonical29432 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2118 + difference 2 2) (sourceB2118 + difference 2 2) sourceC2118) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2560) := by
    have ha : (tripleCharges (sourceA2118 + difference 2 2) (sourceB2118 + difference 2 2) sourceC2118) = raw29433 := by
      apply Matrix.ext; unfold tripleCharges sourceA2118 sourceB2118 sourceC2118 difference raw29433; decide +kernel
    rw [ha]
    exact (canonical29433 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2118 + difference 3 2) (sourceB2118 + difference 2 3) sourceC2118) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2427) := by
    have ha : (tripleCharges (sourceA2118 + difference 3 2) (sourceB2118 + difference 2 3) sourceC2118) = raw29434 := by
      apply Matrix.ext; unfold tripleCharges sourceA2118 sourceB2118 sourceC2118 difference raw29434; decide +kernel
    rw [ha]
    exact (canonical29434 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2118 + difference 4 2) (sourceB2118 + difference 2 4) sourceC2118) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2435) := by
    have ha : (tripleCharges (sourceA2118 + difference 4 2) (sourceB2118 + difference 2 4) sourceC2118) = raw29435 := by
      apply Matrix.ext; unfold tripleCharges sourceA2118 sourceB2118 sourceC2118 difference raw29435; decide +kernel
    rw [ha]
    exact (canonical29435 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2118 + difference 5 2) (sourceB2118 + difference 2 5) sourceC2118) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1807) := by
    have ha : (tripleCharges (sourceA2118 + difference 5 2) (sourceB2118 + difference 2 5) sourceC2118) = raw29436 := by
      apply Matrix.ext; unfold tripleCharges sourceA2118 sourceB2118 sourceC2118 difference raw29436; decide +kernel
    rw [ha]
    exact (canonical29436 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2118 + sourceB2118) sourceC2118) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA2118 + sourceB2118) sourceC2118) = raw29437 := by
      apply Matrix.ext; unfold doubleCharges sourceA2118 sourceB2118 sourceC2118 raw29437; decide +kernel
    rw [ha]
    exact (canonical29437 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2118 sourceB2118 sourceC2118
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2118, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2119 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2119 : Charge := ![2, 0, 1, 0, 0, -3]
def sourceC2119 : Charge := ![1, 1, -1, 0, -2, 1]
def sourceForm2119 : Integer.Sparse Master := [(Sum.inr 1347, 1), (Sum.inr 2831, 1), (Sum.inr 2902, 1), (Sum.inr 2942, 1), (Sum.inr 2954, 1), (Sum.inr 2964, 1), (Sum.inr 4091, -1)]

theorem sourceEq2119 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2119 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2119 + difference 2 0) (sourceB2119 + difference 0 2) sourceC2119) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1347) := by
    have ha : (tripleCharges (sourceA2119 + difference 2 0) (sourceB2119 + difference 0 2) sourceC2119) = raw29438 := by
      apply Matrix.ext; unfold tripleCharges sourceA2119 sourceB2119 sourceC2119 difference raw29438; decide +kernel
    rw [ha]
    exact (canonical29438 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2119 + difference 2 1) (sourceB2119 + difference 1 2) sourceC2119) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2831) := by
    have ha : (tripleCharges (sourceA2119 + difference 2 1) (sourceB2119 + difference 1 2) sourceC2119) = raw29439 := by
      apply Matrix.ext; unfold tripleCharges sourceA2119 sourceB2119 sourceC2119 difference raw29439; decide +kernel
    rw [ha]
    exact (canonical29439 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2119 + difference 2 2) (sourceB2119 + difference 2 2) sourceC2119) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2942) := by
    have ha : (tripleCharges (sourceA2119 + difference 2 2) (sourceB2119 + difference 2 2) sourceC2119) = raw29440 := by
      apply Matrix.ext; unfold tripleCharges sourceA2119 sourceB2119 sourceC2119 difference raw29440; decide +kernel
    rw [ha]
    exact (canonical29440 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2119 + difference 2 3) (sourceB2119 + difference 3 2) sourceC2119) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2902) := by
    have ha : (tripleCharges (sourceA2119 + difference 2 3) (sourceB2119 + difference 3 2) sourceC2119) = raw29441 := by
      apply Matrix.ext; unfold tripleCharges sourceA2119 sourceB2119 sourceC2119 difference raw29441; decide +kernel
    rw [ha]
    exact (canonical29441 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2119 + difference 2 4) (sourceB2119 + difference 4 2) sourceC2119) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2964) := by
    have ha : (tripleCharges (sourceA2119 + difference 2 4) (sourceB2119 + difference 4 2) sourceC2119) = raw29442 := by
      apply Matrix.ext; unfold tripleCharges sourceA2119 sourceB2119 sourceC2119 difference raw29442; decide +kernel
    rw [ha]
    exact (canonical29442 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2119 + difference 2 5) (sourceB2119 + difference 5 2) sourceC2119) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2954) := by
    have ha : (tripleCharges (sourceA2119 + difference 2 5) (sourceB2119 + difference 5 2) sourceC2119) = raw29443 := by
      apply Matrix.ext; unfold tripleCharges sourceA2119 sourceB2119 sourceC2119 difference raw29443; decide +kernel
    rw [ha]
    exact (canonical29443 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2119 + sourceB2119) sourceC2119) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA2119 + sourceB2119) sourceC2119) = raw29444 := by
      apply Matrix.ext; unfold doubleCharges sourceA2119 sourceB2119 sourceC2119 raw29444; decide +kernel
    rw [ha]
    exact (canonical29444 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2119 sourceB2119 sourceC2119
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2119, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2120 : Charge := ![1, 1, -1, 0, -2, 1]
def sourceB2120 : Charge := ![2, 0, 1, 0, 0, -3]
def sourceC2120 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceForm2120 : Integer.Sparse Master := [(Sum.inr 2584, 1), (Sum.inr 2668, 1), (Sum.inr 2670, 1), (Sum.inr 2674, 1), (Sum.inr 2681, 1), (Sum.inr 3478, 1), (Sum.inr 4082, -1)]

theorem sourceEq2120 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2120 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2120 + difference 0 0) (sourceB2120 + difference 0 0) sourceC2120) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2670) := by
    have ha : (tripleCharges (sourceA2120 + difference 0 0) (sourceB2120 + difference 0 0) sourceC2120) = raw29445 := by
      apply Matrix.ext; unfold tripleCharges sourceA2120 sourceB2120 sourceC2120 difference raw29445; decide +kernel
    rw [ha]
    exact (canonical29445 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2120 + difference 0 1) (sourceB2120 + difference 1 0) sourceC2120) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2681) := by
    have ha : (tripleCharges (sourceA2120 + difference 0 1) (sourceB2120 + difference 1 0) sourceC2120) = raw29446 := by
      apply Matrix.ext; unfold tripleCharges sourceA2120 sourceB2120 sourceC2120 difference raw29446; decide +kernel
    rw [ha]
    exact (canonical29446 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2120 + difference 0 2) (sourceB2120 + difference 2 0) sourceC2120) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2674) := by
    have ha : (tripleCharges (sourceA2120 + difference 0 2) (sourceB2120 + difference 2 0) sourceC2120) = raw29447 := by
      apply Matrix.ext; unfold tripleCharges sourceA2120 sourceB2120 sourceC2120 difference raw29447; decide +kernel
    rw [ha]
    exact (canonical29447 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2120 + difference 0 3) (sourceB2120 + difference 3 0) sourceC2120) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2668) := by
    have ha : (tripleCharges (sourceA2120 + difference 0 3) (sourceB2120 + difference 3 0) sourceC2120) = raw29448 := by
      apply Matrix.ext; unfold tripleCharges sourceA2120 sourceB2120 sourceC2120 difference raw29448; decide +kernel
    rw [ha]
    exact (canonical29448 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2120 + difference 0 4) (sourceB2120 + difference 4 0) sourceC2120) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2584) := by
    have ha : (tripleCharges (sourceA2120 + difference 0 4) (sourceB2120 + difference 4 0) sourceC2120) = raw29449 := by
      apply Matrix.ext; unfold tripleCharges sourceA2120 sourceB2120 sourceC2120 difference raw29449; decide +kernel
    rw [ha]
    exact (canonical29449 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2120 + difference 0 5) (sourceB2120 + difference 5 0) sourceC2120) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3478) := by
    have ha : (tripleCharges (sourceA2120 + difference 0 5) (sourceB2120 + difference 5 0) sourceC2120) = raw29450 := by
      apply Matrix.ext; unfold tripleCharges sourceA2120 sourceB2120 sourceC2120 difference raw29450; decide +kernel
    rw [ha]
    exact (canonical29450 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2120 + sourceB2120) sourceC2120) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2120 + sourceB2120) sourceC2120) = raw29319 := by
      apply Matrix.ext; unfold doubleCharges sourceA2120 sourceB2120 sourceC2120 raw29319; decide +kernel
    rw [ha]
    exact (canonical29319 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2120 sourceB2120 sourceC2120
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2120, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2121 : Charge := ![1, 1, -1, 0, -2, 1]
def sourceB2121 : Charge := ![2, 0, 1, 0, 0, -3]
def sourceC2121 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceForm2121 : Integer.Sparse Master := [(Sum.inr 2670, 1), (Sum.inr 3478, 1), (Sum.inr 3516, 1), (Sum.inr 3522, 1), (Sum.inr 3538, 1), (Sum.inr 3614, 1), (Sum.inr 4082, -1)]

theorem sourceEq2121 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2121 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2121 + difference 0 5) (sourceB2121 + difference 5 0) sourceC2121) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3478) := by
    have ha : (tripleCharges (sourceA2121 + difference 0 5) (sourceB2121 + difference 5 0) sourceC2121) = raw29450 := by
      apply Matrix.ext; unfold tripleCharges sourceA2121 sourceB2121 sourceC2121 difference raw29450; decide +kernel
    rw [ha]
    exact (canonical29450 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2121 + difference 1 5) (sourceB2121 + difference 5 1) sourceC2121) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3538) := by
    have ha : (tripleCharges (sourceA2121 + difference 1 5) (sourceB2121 + difference 5 1) sourceC2121) = raw29451 := by
      apply Matrix.ext; unfold tripleCharges sourceA2121 sourceB2121 sourceC2121 difference raw29451; decide +kernel
    rw [ha]
    exact (canonical29451 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2121 + difference 2 5) (sourceB2121 + difference 5 2) sourceC2121) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3614) := by
    have ha : (tripleCharges (sourceA2121 + difference 2 5) (sourceB2121 + difference 5 2) sourceC2121) = raw29452 := by
      apply Matrix.ext; unfold tripleCharges sourceA2121 sourceB2121 sourceC2121 difference raw29452; decide +kernel
    rw [ha]
    exact (canonical29452 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2121 + difference 3 5) (sourceB2121 + difference 5 3) sourceC2121) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3516) := by
    have ha : (tripleCharges (sourceA2121 + difference 3 5) (sourceB2121 + difference 5 3) sourceC2121) = raw29453 := by
      apply Matrix.ext; unfold tripleCharges sourceA2121 sourceB2121 sourceC2121 difference raw29453; decide +kernel
    rw [ha]
    exact (canonical29453 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2121 + difference 4 5) (sourceB2121 + difference 5 4) sourceC2121) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3522) := by
    have ha : (tripleCharges (sourceA2121 + difference 4 5) (sourceB2121 + difference 5 4) sourceC2121) = raw29454 := by
      apply Matrix.ext; unfold tripleCharges sourceA2121 sourceB2121 sourceC2121 difference raw29454; decide +kernel
    rw [ha]
    exact (canonical29454 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2121 + difference 5 5) (sourceB2121 + difference 5 5) sourceC2121) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2670) := by
    have ha : (tripleCharges (sourceA2121 + difference 5 5) (sourceB2121 + difference 5 5) sourceC2121) = raw29445 := by
      apply Matrix.ext; unfold tripleCharges sourceA2121 sourceB2121 sourceC2121 difference raw29445; decide +kernel
    rw [ha]
    exact (canonical29445 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2121 + sourceB2121) sourceC2121) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2121 + sourceB2121) sourceC2121) = raw29319 := by
      apply Matrix.ext; unfold doubleCharges sourceA2121 sourceB2121 sourceC2121 raw29319; decide +kernel
    rw [ha]
    exact (canonical29319 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2121 sourceB2121 sourceC2121
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2121, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2122 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2122 : Charge := ![1, 1, -1, 1, -2, 0]
def sourceC2122 : Charge := ![2, 0, 1, -1, 0, -2]
def sourceForm2122 : Integer.Sparse Master := [(Sum.inr 2347, 1), (Sum.inr 2423, 1), (Sum.inr 2431, 1), (Sum.inr 2488, 1), (Sum.inr 2545, 1), (Sum.inr 3719, 1), (Sum.inr 4092, -1)]

theorem sourceEq2122 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2122 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2122 + difference 0 2) (sourceB2122 + difference 2 0) sourceC2122) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3719) := by
    have ha : (tripleCharges (sourceA2122 + difference 0 2) (sourceB2122 + difference 2 0) sourceC2122) = raw29455 := by
      apply Matrix.ext; unfold tripleCharges sourceA2122 sourceB2122 sourceC2122 difference raw29455; decide +kernel
    rw [ha]
    exact (canonical29455 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2122 + difference 1 2) (sourceB2122 + difference 2 1) sourceC2122) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2488) := by
    have ha : (tripleCharges (sourceA2122 + difference 1 2) (sourceB2122 + difference 2 1) sourceC2122) = raw29456 := by
      apply Matrix.ext; unfold tripleCharges sourceA2122 sourceB2122 sourceC2122 difference raw29456; decide +kernel
    rw [ha]
    exact (canonical29456 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2122 + difference 2 2) (sourceB2122 + difference 2 2) sourceC2122) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2545) := by
    have ha : (tripleCharges (sourceA2122 + difference 2 2) (sourceB2122 + difference 2 2) sourceC2122) = raw29457 := by
      apply Matrix.ext; unfold tripleCharges sourceA2122 sourceB2122 sourceC2122 difference raw29457; decide +kernel
    rw [ha]
    exact (canonical29457 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2122 + difference 3 2) (sourceB2122 + difference 2 3) sourceC2122) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2431) := by
    have ha : (tripleCharges (sourceA2122 + difference 3 2) (sourceB2122 + difference 2 3) sourceC2122) = raw29458 := by
      apply Matrix.ext; unfold tripleCharges sourceA2122 sourceB2122 sourceC2122 difference raw29458; decide +kernel
    rw [ha]
    exact (canonical29458 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2122 + difference 4 2) (sourceB2122 + difference 2 4) sourceC2122) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2423) := by
    have ha : (tripleCharges (sourceA2122 + difference 4 2) (sourceB2122 + difference 2 4) sourceC2122) = raw29459 := by
      apply Matrix.ext; unfold tripleCharges sourceA2122 sourceB2122 sourceC2122 difference raw29459; decide +kernel
    rw [ha]
    exact (canonical29459 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2122 + difference 5 2) (sourceB2122 + difference 2 5) sourceC2122) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2347) := by
    have ha : (tripleCharges (sourceA2122 + difference 5 2) (sourceB2122 + difference 2 5) sourceC2122) = raw27508 := by
      apply Matrix.ext; unfold tripleCharges sourceA2122 sourceB2122 sourceC2122 difference raw27508; decide +kernel
    rw [ha]
    exact (canonical27508 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2122 + sourceB2122) sourceC2122) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2122 + sourceB2122) sourceC2122) = raw24746 := by
      apply Matrix.ext; unfold doubleCharges sourceA2122 sourceB2122 sourceC2122 raw24746; decide +kernel
    rw [ha]
    exact (canonical24746 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2122 sourceB2122 sourceC2122
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2122, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2123 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2123 : Charge := ![1, 1, -1, 1, -2, 0]
def sourceC2123 : Charge := ![2, 0, 1, -1, 0, -2]
def sourceForm2123 : Integer.Sparse Master := [(Sum.inr 1151, 1), (Sum.inr 2350, 1), (Sum.inr 2431, 1), (Sum.inr 2545, 1), (Sum.inr 2553, 1), (Sum.inr 2557, 1), (Sum.inr 4092, -1)]

theorem sourceEq2123 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2123 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2123 + difference 3 0) (sourceB2123 + difference 0 3) sourceC2123) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1151) := by
    have ha : (tripleCharges (sourceA2123 + difference 3 0) (sourceB2123 + difference 0 3) sourceC2123) = raw24750 := by
      apply Matrix.ext; unfold tripleCharges sourceA2123 sourceB2123 sourceC2123 difference raw24750; decide +kernel
    rw [ha]
    exact (canonical24750 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2123 + difference 3 1) (sourceB2123 + difference 1 3) sourceC2123) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2350) := by
    have ha : (tripleCharges (sourceA2123 + difference 3 1) (sourceB2123 + difference 1 3) sourceC2123) = raw29460 := by
      apply Matrix.ext; unfold tripleCharges sourceA2123 sourceB2123 sourceC2123 difference raw29460; decide +kernel
    rw [ha]
    exact (canonical29460 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2123 + difference 3 2) (sourceB2123 + difference 2 3) sourceC2123) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2431) := by
    have ha : (tripleCharges (sourceA2123 + difference 3 2) (sourceB2123 + difference 2 3) sourceC2123) = raw29458 := by
      apply Matrix.ext; unfold tripleCharges sourceA2123 sourceB2123 sourceC2123 difference raw29458; decide +kernel
    rw [ha]
    exact (canonical29458 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2123 + difference 3 3) (sourceB2123 + difference 3 3) sourceC2123) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2545) := by
    have ha : (tripleCharges (sourceA2123 + difference 3 3) (sourceB2123 + difference 3 3) sourceC2123) = raw29457 := by
      apply Matrix.ext; unfold tripleCharges sourceA2123 sourceB2123 sourceC2123 difference raw29457; decide +kernel
    rw [ha]
    exact (canonical29457 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2123 + difference 3 4) (sourceB2123 + difference 4 3) sourceC2123) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2553) := by
    have ha : (tripleCharges (sourceA2123 + difference 3 4) (sourceB2123 + difference 4 3) sourceC2123) = raw24747 := by
      apply Matrix.ext; unfold tripleCharges sourceA2123 sourceB2123 sourceC2123 difference raw24747; decide +kernel
    rw [ha]
    exact (canonical24747 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2123 + difference 3 5) (sourceB2123 + difference 5 3) sourceC2123) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2557) := by
    have ha : (tripleCharges (sourceA2123 + difference 3 5) (sourceB2123 + difference 5 3) sourceC2123) = raw29461 := by
      apply Matrix.ext; unfold tripleCharges sourceA2123 sourceB2123 sourceC2123 difference raw29461; decide +kernel
    rw [ha]
    exact (canonical29461 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2123 + sourceB2123) sourceC2123) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2123 + sourceB2123) sourceC2123) = raw24746 := by
      apply Matrix.ext; unfold doubleCharges sourceA2123 sourceB2123 sourceC2123 raw24746; decide +kernel
    rw [ha]
    exact (canonical24746 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2123 sourceB2123 sourceC2123
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2123, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2124 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2124 : Charge := ![2, 0, 1, -1, 0, -2]
def sourceC2124 : Charge := ![1, 1, -1, 1, -2, 0]
def sourceForm2124 : Integer.Sparse Master := [(Sum.inr 1330, 1), (Sum.inr 2824, 1), (Sum.inr 2896, 1), (Sum.inr 2916, 1), (Sum.inr 2924, 1), (Sum.inr 2928, 1), (Sum.inr 4091, -1)]

theorem sourceEq2124 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2124 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2124 + difference 2 0) (sourceB2124 + difference 0 2) sourceC2124) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1330) := by
    have ha : (tripleCharges (sourceA2124 + difference 2 0) (sourceB2124 + difference 0 2) sourceC2124) = raw29462 := by
      apply Matrix.ext; unfold tripleCharges sourceA2124 sourceB2124 sourceC2124 difference raw29462; decide +kernel
    rw [ha]
    exact (canonical29462 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2124 + difference 2 1) (sourceB2124 + difference 1 2) sourceC2124) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2824) := by
    have ha : (tripleCharges (sourceA2124 + difference 2 1) (sourceB2124 + difference 1 2) sourceC2124) = raw29463 := by
      apply Matrix.ext; unfold tripleCharges sourceA2124 sourceB2124 sourceC2124 difference raw29463; decide +kernel
    rw [ha]
    exact (canonical29463 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2124 + difference 2 2) (sourceB2124 + difference 2 2) sourceC2124) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2916) := by
    have ha : (tripleCharges (sourceA2124 + difference 2 2) (sourceB2124 + difference 2 2) sourceC2124) = raw29464 := by
      apply Matrix.ext; unfold tripleCharges sourceA2124 sourceB2124 sourceC2124 difference raw29464; decide +kernel
    rw [ha]
    exact (canonical29464 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2124 + difference 2 3) (sourceB2124 + difference 3 2) sourceC2124) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2896) := by
    have ha : (tripleCharges (sourceA2124 + difference 2 3) (sourceB2124 + difference 3 2) sourceC2124) = raw29465 := by
      apply Matrix.ext; unfold tripleCharges sourceA2124 sourceB2124 sourceC2124 difference raw29465; decide +kernel
    rw [ha]
    exact (canonical29465 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2124 + difference 2 4) (sourceB2124 + difference 4 2) sourceC2124) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2928) := by
    have ha : (tripleCharges (sourceA2124 + difference 2 4) (sourceB2124 + difference 4 2) sourceC2124) = raw29466 := by
      apply Matrix.ext; unfold tripleCharges sourceA2124 sourceB2124 sourceC2124 difference raw29466; decide +kernel
    rw [ha]
    exact (canonical29466 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2124 + difference 2 5) (sourceB2124 + difference 5 2) sourceC2124) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2924) := by
    have ha : (tripleCharges (sourceA2124 + difference 2 5) (sourceB2124 + difference 5 2) sourceC2124) = raw29467 := by
      apply Matrix.ext; unfold tripleCharges sourceA2124 sourceB2124 sourceC2124 difference raw29467; decide +kernel
    rw [ha]
    exact (canonical29467 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2124 + sourceB2124) sourceC2124) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA2124 + sourceB2124) sourceC2124) = raw29468 := by
      apply Matrix.ext; unfold doubleCharges sourceA2124 sourceB2124 sourceC2124 raw29468; decide +kernel
    rw [ha]
    exact (canonical29468 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2124 sourceB2124 sourceC2124
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2124, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2125 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2125 : Charge := ![2, 0, 1, -1, 0, -2]
def sourceC2125 : Charge := ![1, 1, -1, 1, -2, 0]
def sourceForm2125 : Integer.Sparse Master := [(Sum.inr 2349, 1), (Sum.inr 2890, 1), (Sum.inr 2896, 1), (Sum.inr 2916, 2), (Sum.inr 3721, 1), (Sum.inr 4091, -1)]

theorem sourceEq2125 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2125 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2125 + difference 0 3) (sourceB2125 + difference 3 0) sourceC2125) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3721) := by
    have ha : (tripleCharges (sourceA2125 + difference 0 3) (sourceB2125 + difference 3 0) sourceC2125) = raw29469 := by
      apply Matrix.ext; unfold tripleCharges sourceA2125 sourceB2125 sourceC2125 difference raw29469; decide +kernel
    rw [ha]
    exact (canonical29469 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2125 + difference 1 3) (sourceB2125 + difference 3 1) sourceC2125) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2916) := by
    have ha : (tripleCharges (sourceA2125 + difference 1 3) (sourceB2125 + difference 3 1) sourceC2125) = raw29470 := by
      apply Matrix.ext; unfold tripleCharges sourceA2125 sourceB2125 sourceC2125 difference raw29470; decide +kernel
    rw [ha]
    exact (canonical29470 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2125 + difference 2 3) (sourceB2125 + difference 3 2) sourceC2125) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2896) := by
    have ha : (tripleCharges (sourceA2125 + difference 2 3) (sourceB2125 + difference 3 2) sourceC2125) = raw29465 := by
      apply Matrix.ext; unfold tripleCharges sourceA2125 sourceB2125 sourceC2125 difference raw29465; decide +kernel
    rw [ha]
    exact (canonical29465 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2125 + difference 3 3) (sourceB2125 + difference 3 3) sourceC2125) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2916) := by
    have ha : (tripleCharges (sourceA2125 + difference 3 3) (sourceB2125 + difference 3 3) sourceC2125) = raw29464 := by
      apply Matrix.ext; unfold tripleCharges sourceA2125 sourceB2125 sourceC2125 difference raw29464; decide +kernel
    rw [ha]
    exact (canonical29464 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2125 + difference 4 3) (sourceB2125 + difference 3 4) sourceC2125) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2349) := by
    have ha : (tripleCharges (sourceA2125 + difference 4 3) (sourceB2125 + difference 3 4) sourceC2125) = raw29471 := by
      apply Matrix.ext; unfold tripleCharges sourceA2125 sourceB2125 sourceC2125 difference raw29471; decide +kernel
    rw [ha]
    exact (canonical29471 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2125 + difference 5 3) (sourceB2125 + difference 3 5) sourceC2125) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2890) := by
    have ha : (tripleCharges (sourceA2125 + difference 5 3) (sourceB2125 + difference 3 5) sourceC2125) = raw29472 := by
      apply Matrix.ext; unfold tripleCharges sourceA2125 sourceB2125 sourceC2125 difference raw29472; decide +kernel
    rw [ha]
    exact (canonical29472 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2125 + sourceB2125) sourceC2125) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA2125 + sourceB2125) sourceC2125) = raw29468 := by
      apply Matrix.ext; unfold doubleCharges sourceA2125 sourceB2125 sourceC2125 raw29468; decide +kernel
    rw [ha]
    exact (canonical29468 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2125 sourceB2125 sourceC2125
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2125, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2126 : Charge := ![1, 1, -1, 1, -2, 0]
def sourceB2126 : Charge := ![2, 0, 1, -1, 0, -2]
def sourceC2126 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceForm2126 : Integer.Sparse Master := [(Sum.inr 2534, 1), (Sum.inr 3430, 1), (Sum.inr 3433, 1), (Sum.inr 3478, 1), (Sum.inr 3516, 2), (Sum.inr 4082, -1)]

theorem sourceEq2126 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2126 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2126 + difference 0 0) (sourceB2126 + difference 0 0) sourceC2126) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3516) := by
    have ha : (tripleCharges (sourceA2126 + difference 0 0) (sourceB2126 + difference 0 0) sourceC2126) = raw29453 := by
      apply Matrix.ext; unfold tripleCharges sourceA2126 sourceB2126 sourceC2126 difference raw29453; decide +kernel
    rw [ha]
    exact (canonical29453 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2126 + difference 0 1) (sourceB2126 + difference 1 0) sourceC2126) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3516) := by
    have ha : (tripleCharges (sourceA2126 + difference 0 1) (sourceB2126 + difference 1 0) sourceC2126) = raw29473 := by
      apply Matrix.ext; unfold tripleCharges sourceA2126 sourceB2126 sourceC2126 difference raw29473; decide +kernel
    rw [ha]
    exact (canonical29473 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2126 + difference 0 2) (sourceB2126 + difference 2 0) sourceC2126) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3430) := by
    have ha : (tripleCharges (sourceA2126 + difference 0 2) (sourceB2126 + difference 2 0) sourceC2126) = raw29474 := by
      apply Matrix.ext; unfold tripleCharges sourceA2126 sourceB2126 sourceC2126 difference raw29474; decide +kernel
    rw [ha]
    exact (canonical29474 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2126 + difference 0 3) (sourceB2126 + difference 3 0) sourceC2126) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3478) := by
    have ha : (tripleCharges (sourceA2126 + difference 0 3) (sourceB2126 + difference 3 0) sourceC2126) = raw29450 := by
      apply Matrix.ext; unfold tripleCharges sourceA2126 sourceB2126 sourceC2126 difference raw29450; decide +kernel
    rw [ha]
    exact (canonical29450 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2126 + difference 0 4) (sourceB2126 + difference 4 0) sourceC2126) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2534) := by
    have ha : (tripleCharges (sourceA2126 + difference 0 4) (sourceB2126 + difference 4 0) sourceC2126) = raw29475 := by
      apply Matrix.ext; unfold tripleCharges sourceA2126 sourceB2126 sourceC2126 difference raw29475; decide +kernel
    rw [ha]
    exact (canonical29475 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2126 + difference 0 5) (sourceB2126 + difference 5 0) sourceC2126) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3433) := by
    have ha : (tripleCharges (sourceA2126 + difference 0 5) (sourceB2126 + difference 5 0) sourceC2126) = raw29476 := by
      apply Matrix.ext; unfold tripleCharges sourceA2126 sourceB2126 sourceC2126 difference raw29476; decide +kernel
    rw [ha]
    exact (canonical29476 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2126 + sourceB2126) sourceC2126) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2126 + sourceB2126) sourceC2126) = raw29319 := by
      apply Matrix.ext; unfold doubleCharges sourceA2126 sourceB2126 sourceC2126 raw29319; decide +kernel
    rw [ha]
    exact (canonical29319 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2126 sourceB2126 sourceC2126
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2126, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2127 : Charge := ![1, 1, -1, 1, -2, 0]
def sourceB2127 : Charge := ![2, 0, 1, -1, 0, -2]
def sourceC2127 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceForm2127 : Integer.Sparse Master := [(Sum.inr 1997, 1), (Sum.inr 3369, 1), (Sum.inr 3433, 1), (Sum.inr 3516, 1), (Sum.inr 3520, 1), (Sum.inr 3522, 1), (Sum.inr 4082, -1)]

theorem sourceEq2127 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2127 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2127 + difference 4 0) (sourceB2127 + difference 0 4) sourceC2127) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1997) := by
    have ha : (tripleCharges (sourceA2127 + difference 4 0) (sourceB2127 + difference 0 4) sourceC2127) = raw29477 := by
      apply Matrix.ext; unfold tripleCharges sourceA2127 sourceB2127 sourceC2127 difference raw29477; decide +kernel
    rw [ha]
    exact (canonical29477 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2127 + difference 4 1) (sourceB2127 + difference 1 4) sourceC2127) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3433) := by
    have ha : (tripleCharges (sourceA2127 + difference 4 1) (sourceB2127 + difference 1 4) sourceC2127) = raw29478 := by
      apply Matrix.ext; unfold tripleCharges sourceA2127 sourceB2127 sourceC2127 difference raw29478; decide +kernel
    rw [ha]
    exact (canonical29478 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2127 + difference 4 2) (sourceB2127 + difference 2 4) sourceC2127) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3369) := by
    have ha : (tripleCharges (sourceA2127 + difference 4 2) (sourceB2127 + difference 2 4) sourceC2127) = raw29479 := by
      apply Matrix.ext; unfold tripleCharges sourceA2127 sourceB2127 sourceC2127 difference raw29479; decide +kernel
    rw [ha]
    exact (canonical29479 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2127 + difference 4 3) (sourceB2127 + difference 3 4) sourceC2127) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3522) := by
    have ha : (tripleCharges (sourceA2127 + difference 4 3) (sourceB2127 + difference 3 4) sourceC2127) = raw29454 := by
      apply Matrix.ext; unfold tripleCharges sourceA2127 sourceB2127 sourceC2127 difference raw29454; decide +kernel
    rw [ha]
    exact (canonical29454 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2127 + difference 4 4) (sourceB2127 + difference 4 4) sourceC2127) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3516) := by
    have ha : (tripleCharges (sourceA2127 + difference 4 4) (sourceB2127 + difference 4 4) sourceC2127) = raw29453 := by
      apply Matrix.ext; unfold tripleCharges sourceA2127 sourceB2127 sourceC2127 difference raw29453; decide +kernel
    rw [ha]
    exact (canonical29453 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2127 + difference 4 5) (sourceB2127 + difference 5 4) sourceC2127) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3520) := by
    have ha : (tripleCharges (sourceA2127 + difference 4 5) (sourceB2127 + difference 5 4) sourceC2127) = raw29480 := by
      apply Matrix.ext; unfold tripleCharges sourceA2127 sourceB2127 sourceC2127 difference raw29480; decide +kernel
    rw [ha]
    exact (canonical29480 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2127 + sourceB2127) sourceC2127) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2127 + sourceB2127) sourceC2127) = raw29319 := by
      apply Matrix.ext; unfold doubleCharges sourceA2127 sourceB2127 sourceC2127 raw29319; decide +kernel
    rw [ha]
    exact (canonical29319 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2127 sourceB2127 sourceC2127
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2127, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2128 : Charge := ![1, 1, -1, 1, -2, 0]
def sourceB2128 : Charge := ![2, 0, 1, -1, 0, -2]
def sourceC2128 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceForm2128 : Integer.Sparse Master := [(Sum.inr 3433, 1), (Sum.inr 3516, 1), (Sum.inr 3518, 1), (Sum.inr 3520, 1), (Sum.inr 3536, 1), (Sum.inr 3612, 1), (Sum.inr 4082, -1)]

theorem sourceEq2128 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2128 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2128 + difference 0 5) (sourceB2128 + difference 5 0) sourceC2128) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3433) := by
    have ha : (tripleCharges (sourceA2128 + difference 0 5) (sourceB2128 + difference 5 0) sourceC2128) = raw29476 := by
      apply Matrix.ext; unfold tripleCharges sourceA2128 sourceB2128 sourceC2128 difference raw29476; decide +kernel
    rw [ha]
    exact (canonical29476 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2128 + difference 1 5) (sourceB2128 + difference 5 1) sourceC2128) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3536) := by
    have ha : (tripleCharges (sourceA2128 + difference 1 5) (sourceB2128 + difference 5 1) sourceC2128) = raw29351 := by
      apply Matrix.ext; unfold tripleCharges sourceA2128 sourceB2128 sourceC2128 difference raw29351; decide +kernel
    rw [ha]
    exact (canonical29351 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2128 + difference 2 5) (sourceB2128 + difference 5 2) sourceC2128) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3612) := by
    have ha : (tripleCharges (sourceA2128 + difference 2 5) (sourceB2128 + difference 5 2) sourceC2128) = raw29313 := by
      apply Matrix.ext; unfold tripleCharges sourceA2128 sourceB2128 sourceC2128 difference raw29313; decide +kernel
    rw [ha]
    exact (canonical29313 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2128 + difference 3 5) (sourceB2128 + difference 5 3) sourceC2128) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3518) := by
    have ha : (tripleCharges (sourceA2128 + difference 3 5) (sourceB2128 + difference 5 3) sourceC2128) = raw29481 := by
      apply Matrix.ext; unfold tripleCharges sourceA2128 sourceB2128 sourceC2128 difference raw29481; decide +kernel
    rw [ha]
    exact (canonical29481 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2128 + difference 4 5) (sourceB2128 + difference 5 4) sourceC2128) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3520) := by
    have ha : (tripleCharges (sourceA2128 + difference 4 5) (sourceB2128 + difference 5 4) sourceC2128) = raw29480 := by
      apply Matrix.ext; unfold tripleCharges sourceA2128 sourceB2128 sourceC2128 difference raw29480; decide +kernel
    rw [ha]
    exact (canonical29480 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2128 + difference 5 5) (sourceB2128 + difference 5 5) sourceC2128) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3516) := by
    have ha : (tripleCharges (sourceA2128 + difference 5 5) (sourceB2128 + difference 5 5) sourceC2128) = raw29453 := by
      apply Matrix.ext; unfold tripleCharges sourceA2128 sourceB2128 sourceC2128 difference raw29453; decide +kernel
    rw [ha]
    exact (canonical29453 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2128 + sourceB2128) sourceC2128) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2128 + sourceB2128) sourceC2128) = raw29319 := by
      apply Matrix.ext; unfold doubleCharges sourceA2128 sourceB2128 sourceC2128 raw29319; decide +kernel
    rw [ha]
    exact (canonical29319 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2128 sourceB2128 sourceC2128
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2128, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2129 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2129 : Charge := ![1, 1, -1, 1, -1, -1]
def sourceC2129 : Charge := ![2, 0, 1, -1, -1, -1]
def sourceForm2129 : Integer.Sparse Master := [(Sum.inr 2422, 2), (Sum.inr 2432, 1), (Sum.inr 2489, 1), (Sum.inr 2546, 1), (Sum.inr 3779, 1), (Sum.inr 4091, -1)]

theorem sourceEq2129 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2129 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2129 + difference 0 2) (sourceB2129 + difference 2 0) sourceC2129) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3779) := by
    have ha : (tripleCharges (sourceA2129 + difference 0 2) (sourceB2129 + difference 2 0) sourceC2129) = raw29482 := by
      apply Matrix.ext; unfold tripleCharges sourceA2129 sourceB2129 sourceC2129 difference raw29482; decide +kernel
    rw [ha]
    exact (canonical29482 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2129 + difference 1 2) (sourceB2129 + difference 2 1) sourceC2129) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2489) := by
    have ha : (tripleCharges (sourceA2129 + difference 1 2) (sourceB2129 + difference 2 1) sourceC2129) = raw29483 := by
      apply Matrix.ext; unfold tripleCharges sourceA2129 sourceB2129 sourceC2129 difference raw29483; decide +kernel
    rw [ha]
    exact (canonical29483 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2129 + difference 2 2) (sourceB2129 + difference 2 2) sourceC2129) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2546) := by
    have ha : (tripleCharges (sourceA2129 + difference 2 2) (sourceB2129 + difference 2 2) sourceC2129) = raw29484 := by
      apply Matrix.ext; unfold tripleCharges sourceA2129 sourceB2129 sourceC2129 difference raw29484; decide +kernel
    rw [ha]
    exact (canonical29484 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2129 + difference 3 2) (sourceB2129 + difference 2 3) sourceC2129) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2432) := by
    have ha : (tripleCharges (sourceA2129 + difference 3 2) (sourceB2129 + difference 2 3) sourceC2129) = raw29485 := by
      apply Matrix.ext; unfold tripleCharges sourceA2129 sourceB2129 sourceC2129 difference raw29485; decide +kernel
    rw [ha]
    exact (canonical29485 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2129 + difference 4 2) (sourceB2129 + difference 2 4) sourceC2129) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2422) := by
    have ha : (tripleCharges (sourceA2129 + difference 4 2) (sourceB2129 + difference 2 4) sourceC2129) = raw29486 := by
      apply Matrix.ext; unfold tripleCharges sourceA2129 sourceB2129 sourceC2129 difference raw29486; decide +kernel
    rw [ha]
    exact (canonical29486 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2129 + difference 5 2) (sourceB2129 + difference 2 5) sourceC2129) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2422) := by
    have ha : (tripleCharges (sourceA2129 + difference 5 2) (sourceB2129 + difference 2 5) sourceC2129) = raw27529 := by
      apply Matrix.ext; unfold tripleCharges sourceA2129 sourceB2129 sourceC2129 difference raw27529; decide +kernel
    rw [ha]
    exact (canonical27529 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2129 + sourceB2129) sourceC2129) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA2129 + sourceB2129) sourceC2129) = raw24552 := by
      apply Matrix.ext; unfold doubleCharges sourceA2129 sourceB2129 sourceC2129 raw24552; decide +kernel
    rw [ha]
    exact (canonical24552 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2129 sourceB2129 sourceC2129
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2129, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2130 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2130 : Charge := ![1, 1, -1, 1, -1, -1]
def sourceC2130 : Charge := ![2, 0, 1, -1, -1, -1]
def sourceForm2130 : Integer.Sparse Master := [(Sum.inr 1152, 1), (Sum.inr 2351, 1), (Sum.inr 2432, 1), (Sum.inr 2546, 1), (Sum.inr 2556, 2), (Sum.inr 4091, -1)]

theorem sourceEq2130 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2130 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2130 + difference 3 0) (sourceB2130 + difference 0 3) sourceC2130) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1152) := by
    have ha : (tripleCharges (sourceA2130 + difference 3 0) (sourceB2130 + difference 0 3) sourceC2130) = raw24556 := by
      apply Matrix.ext; unfold tripleCharges sourceA2130 sourceB2130 sourceC2130 difference raw24556; decide +kernel
    rw [ha]
    exact (canonical24556 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2130 + difference 3 1) (sourceB2130 + difference 1 3) sourceC2130) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2351) := by
    have ha : (tripleCharges (sourceA2130 + difference 3 1) (sourceB2130 + difference 1 3) sourceC2130) = raw29487 := by
      apply Matrix.ext; unfold tripleCharges sourceA2130 sourceB2130 sourceC2130 difference raw29487; decide +kernel
    rw [ha]
    exact (canonical29487 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2130 + difference 3 2) (sourceB2130 + difference 2 3) sourceC2130) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2432) := by
    have ha : (tripleCharges (sourceA2130 + difference 3 2) (sourceB2130 + difference 2 3) sourceC2130) = raw29485 := by
      apply Matrix.ext; unfold tripleCharges sourceA2130 sourceB2130 sourceC2130 difference raw29485; decide +kernel
    rw [ha]
    exact (canonical29485 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2130 + difference 3 3) (sourceB2130 + difference 3 3) sourceC2130) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2546) := by
    have ha : (tripleCharges (sourceA2130 + difference 3 3) (sourceB2130 + difference 3 3) sourceC2130) = raw29484 := by
      apply Matrix.ext; unfold tripleCharges sourceA2130 sourceB2130 sourceC2130 difference raw29484; decide +kernel
    rw [ha]
    exact (canonical29484 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2130 + difference 3 4) (sourceB2130 + difference 4 3) sourceC2130) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2556) := by
    have ha : (tripleCharges (sourceA2130 + difference 3 4) (sourceB2130 + difference 4 3) sourceC2130) = raw24553 := by
      apply Matrix.ext; unfold tripleCharges sourceA2130 sourceB2130 sourceC2130 difference raw24553; decide +kernel
    rw [ha]
    exact (canonical24553 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2130 + difference 3 5) (sourceB2130 + difference 5 3) sourceC2130) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2556) := by
    have ha : (tripleCharges (sourceA2130 + difference 3 5) (sourceB2130 + difference 5 3) sourceC2130) = raw29488 := by
      apply Matrix.ext; unfold tripleCharges sourceA2130 sourceB2130 sourceC2130 difference raw29488; decide +kernel
    rw [ha]
    exact (canonical29488 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2130 + sourceB2130) sourceC2130) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA2130 + sourceB2130) sourceC2130) = raw24552 := by
      apply Matrix.ext; unfold doubleCharges sourceA2130 sourceB2130 sourceC2130 raw24552; decide +kernel
    rw [ha]
    exact (canonical24552 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2130 sourceB2130 sourceC2130
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2130, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2131 : Charge := ![1, 1, -1, 1, -1, -1]
def sourceB2131 : Charge := ![2, 0, 1, -1, -1, -1]
def sourceC2131 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceForm2131 : Integer.Sparse Master := [(Sum.inr 3433, 2), (Sum.inr 3438, 1), (Sum.inr 3482, 1), (Sum.inr 3520, 2), (Sum.inr 4082, -1)]

theorem sourceEq2131 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2131 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2131 + difference 0 0) (sourceB2131 + difference 0 0) sourceC2131) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3520) := by
    have ha : (tripleCharges (sourceA2131 + difference 0 0) (sourceB2131 + difference 0 0) sourceC2131) = raw29480 := by
      apply Matrix.ext; unfold tripleCharges sourceA2131 sourceB2131 sourceC2131 difference raw29480; decide +kernel
    rw [ha]
    exact (canonical29480 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2131 + difference 0 1) (sourceB2131 + difference 1 0) sourceC2131) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3520) := by
    have ha : (tripleCharges (sourceA2131 + difference 0 1) (sourceB2131 + difference 1 0) sourceC2131) = raw29489 := by
      apply Matrix.ext; unfold tripleCharges sourceA2131 sourceB2131 sourceC2131 difference raw29489; decide +kernel
    rw [ha]
    exact (canonical29489 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2131 + difference 0 2) (sourceB2131 + difference 2 0) sourceC2131) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3438) := by
    have ha : (tripleCharges (sourceA2131 + difference 0 2) (sourceB2131 + difference 2 0) sourceC2131) = raw29490 := by
      apply Matrix.ext; unfold tripleCharges sourceA2131 sourceB2131 sourceC2131 difference raw29490; decide +kernel
    rw [ha]
    exact (canonical29490 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2131 + difference 0 3) (sourceB2131 + difference 3 0) sourceC2131) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3482) := by
    have ha : (tripleCharges (sourceA2131 + difference 0 3) (sourceB2131 + difference 3 0) sourceC2131) = raw29491 := by
      apply Matrix.ext; unfold tripleCharges sourceA2131 sourceB2131 sourceC2131 difference raw29491; decide +kernel
    rw [ha]
    exact (canonical29491 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2131 + difference 0 4) (sourceB2131 + difference 4 0) sourceC2131) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3433) := by
    have ha : (tripleCharges (sourceA2131 + difference 0 4) (sourceB2131 + difference 4 0) sourceC2131) = raw29476 := by
      apply Matrix.ext; unfold tripleCharges sourceA2131 sourceB2131 sourceC2131 difference raw29476; decide +kernel
    rw [ha]
    exact (canonical29476 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2131 + difference 0 5) (sourceB2131 + difference 5 0) sourceC2131) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3433) := by
    have ha : (tripleCharges (sourceA2131 + difference 0 5) (sourceB2131 + difference 5 0) sourceC2131) = raw29492 := by
      apply Matrix.ext; unfold tripleCharges sourceA2131 sourceB2131 sourceC2131 difference raw29492; decide +kernel
    rw [ha]
    exact (canonical29492 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2131 + sourceB2131) sourceC2131) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2131 + sourceB2131) sourceC2131) = raw29319 := by
      apply Matrix.ext; unfold doubleCharges sourceA2131 sourceB2131 sourceC2131 raw29319; decide +kernel
    rw [ha]
    exact (canonical29319 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2131 sourceB2131 sourceC2131
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2131, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2132 : Charge := ![1, 1, -1, 1, -1, -1]
def sourceB2132 : Charge := ![2, 0, 1, -1, -1, -1]
def sourceC2132 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceForm2132 : Integer.Sparse Master := [(Sum.inr 1997, 2), (Sum.inr 2002, 1), (Sum.inr 2044, 1), (Sum.inr 2225, 1), (Sum.inr 3520, 1), (Sum.inr 4082, -1)]

theorem sourceEq2132 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2132 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2132 + difference 0 0) (sourceB2132 + difference 0 0) sourceC2132) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3520) := by
    have ha : (tripleCharges (sourceA2132 + difference 0 0) (sourceB2132 + difference 0 0) sourceC2132) = raw29480 := by
      apply Matrix.ext; unfold tripleCharges sourceA2132 sourceB2132 sourceC2132 difference raw29480; decide +kernel
    rw [ha]
    exact (canonical29480 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2132 + difference 1 0) (sourceB2132 + difference 0 1) sourceC2132) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2044) := by
    have ha : (tripleCharges (sourceA2132 + difference 1 0) (sourceB2132 + difference 0 1) sourceC2132) = raw29493 := by
      apply Matrix.ext; unfold tripleCharges sourceA2132 sourceB2132 sourceC2132 difference raw29493; decide +kernel
    rw [ha]
    exact (canonical29493 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2132 + difference 2 0) (sourceB2132 + difference 0 2) sourceC2132) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2225) := by
    have ha : (tripleCharges (sourceA2132 + difference 2 0) (sourceB2132 + difference 0 2) sourceC2132) = raw29317 := by
      apply Matrix.ext; unfold tripleCharges sourceA2132 sourceB2132 sourceC2132 difference raw29317; decide +kernel
    rw [ha]
    exact (canonical29317 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2132 + difference 3 0) (sourceB2132 + difference 0 3) sourceC2132) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2002) := by
    have ha : (tripleCharges (sourceA2132 + difference 3 0) (sourceB2132 + difference 0 3) sourceC2132) = raw29494 := by
      apply Matrix.ext; unfold tripleCharges sourceA2132 sourceB2132 sourceC2132 difference raw29494; decide +kernel
    rw [ha]
    exact (canonical29494 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2132 + difference 4 0) (sourceB2132 + difference 0 4) sourceC2132) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1997) := by
    have ha : (tripleCharges (sourceA2132 + difference 4 0) (sourceB2132 + difference 0 4) sourceC2132) = raw29495 := by
      apply Matrix.ext; unfold tripleCharges sourceA2132 sourceB2132 sourceC2132 difference raw29495; decide +kernel
    rw [ha]
    exact (canonical29495 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2132 + difference 5 0) (sourceB2132 + difference 0 5) sourceC2132) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1997) := by
    have ha : (tripleCharges (sourceA2132 + difference 5 0) (sourceB2132 + difference 0 5) sourceC2132) = raw29477 := by
      apply Matrix.ext; unfold tripleCharges sourceA2132 sourceB2132 sourceC2132 difference raw29477; decide +kernel
    rw [ha]
    exact (canonical29477 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2132 + sourceB2132) sourceC2132) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2132 + sourceB2132) sourceC2132) = raw29319 := by
      apply Matrix.ext; unfold doubleCharges sourceA2132 sourceB2132 sourceC2132 raw29319; decide +kernel
    rw [ha]
    exact (canonical29319 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2132 sourceB2132 sourceC2132
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2132, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2133 : Charge := ![1, 1, -1, 1, -1, -1]
def sourceB2133 : Charge := ![2, 0, 1, -1, -1, -1]
def sourceC2133 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceForm2133 : Integer.Sparse Master := [(Sum.inr 3482, 1), (Sum.inr 3520, 1), (Sum.inr 3522, 2), (Sum.inr 3542, 1), (Sum.inr 3616, 1), (Sum.inr 4082, -1)]

theorem sourceEq2133 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2133 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2133 + difference 0 3) (sourceB2133 + difference 3 0) sourceC2133) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3482) := by
    have ha : (tripleCharges (sourceA2133 + difference 0 3) (sourceB2133 + difference 3 0) sourceC2133) = raw29491 := by
      apply Matrix.ext; unfold tripleCharges sourceA2133 sourceB2133 sourceC2133 difference raw29491; decide +kernel
    rw [ha]
    exact (canonical29491 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2133 + difference 1 3) (sourceB2133 + difference 3 1) sourceC2133) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3542) := by
    have ha : (tripleCharges (sourceA2133 + difference 1 3) (sourceB2133 + difference 3 1) sourceC2133) = raw29496 := by
      apply Matrix.ext; unfold tripleCharges sourceA2133 sourceB2133 sourceC2133 difference raw29496; decide +kernel
    rw [ha]
    exact (canonical29496 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2133 + difference 2 3) (sourceB2133 + difference 3 2) sourceC2133) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3616) := by
    have ha : (tripleCharges (sourceA2133 + difference 2 3) (sourceB2133 + difference 3 2) sourceC2133) = raw29497 := by
      apply Matrix.ext; unfold tripleCharges sourceA2133 sourceB2133 sourceC2133 difference raw29497; decide +kernel
    rw [ha]
    exact (canonical29497 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2133 + difference 3 3) (sourceB2133 + difference 3 3) sourceC2133) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3520) := by
    have ha : (tripleCharges (sourceA2133 + difference 3 3) (sourceB2133 + difference 3 3) sourceC2133) = raw29480 := by
      apply Matrix.ext; unfold tripleCharges sourceA2133 sourceB2133 sourceC2133 difference raw29480; decide +kernel
    rw [ha]
    exact (canonical29480 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2133 + difference 4 3) (sourceB2133 + difference 3 4) sourceC2133) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3522) := by
    have ha : (tripleCharges (sourceA2133 + difference 4 3) (sourceB2133 + difference 3 4) sourceC2133) = raw29498 := by
      apply Matrix.ext; unfold tripleCharges sourceA2133 sourceB2133 sourceC2133 difference raw29498; decide +kernel
    rw [ha]
    exact (canonical29498 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2133 + difference 5 3) (sourceB2133 + difference 3 5) sourceC2133) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3522) := by
    have ha : (tripleCharges (sourceA2133 + difference 5 3) (sourceB2133 + difference 3 5) sourceC2133) = raw29454 := by
      apply Matrix.ext; unfold tripleCharges sourceA2133 sourceB2133 sourceC2133 difference raw29454; decide +kernel
    rw [ha]
    exact (canonical29454 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2133 + sourceB2133) sourceC2133) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2133 + sourceB2133) sourceC2133) = raw29319 := by
      apply Matrix.ext; unfold doubleCharges sourceA2133 sourceB2133 sourceC2133 raw29319; decide +kernel
    rw [ha]
    exact (canonical29319 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2133 sourceB2133 sourceC2133
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2133, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2134 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2134 : Charge := ![2, 0, 1, -2, 0, -1]
def sourceC2134 : Charge := ![1, 1, -1, 2, -2, -1]
def sourceForm2134 : Integer.Sparse Master := [(Sum.inr 2905, 1), (Sum.inr 3680, 1), (Sum.inr 3683, 1), (Sum.inr 3696, 1), (Sum.inr 3796, 1), (Sum.inr 3873, 1), (Sum.inr 4090, -1)]

theorem sourceEq2134 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2134 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2134 + difference 0 0) (sourceB2134 + difference 0 0) sourceC2134) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2905) := by
    have ha : (tripleCharges (sourceA2134 + difference 0 0) (sourceB2134 + difference 0 0) sourceC2134) = raw29499 := by
      apply Matrix.ext; unfold tripleCharges sourceA2134 sourceB2134 sourceC2134 difference raw29499; decide +kernel
    rw [ha]
    exact (canonical29499 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2134 + difference 0 1) (sourceB2134 + difference 1 0) sourceC2134) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3680) := by
    have ha : (tripleCharges (sourceA2134 + difference 0 1) (sourceB2134 + difference 1 0) sourceC2134) = raw29500 := by
      apply Matrix.ext; unfold tripleCharges sourceA2134 sourceB2134 sourceC2134 difference raw29500; decide +kernel
    rw [ha]
    exact (canonical29500 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2134 + difference 0 2) (sourceB2134 + difference 2 0) sourceC2134) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3696) := by
    have ha : (tripleCharges (sourceA2134 + difference 0 2) (sourceB2134 + difference 2 0) sourceC2134) = raw29501 := by
      apply Matrix.ext; unfold tripleCharges sourceA2134 sourceB2134 sourceC2134 difference raw29501; decide +kernel
    rw [ha]
    exact (canonical29501 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2134 + difference 0 3) (sourceB2134 + difference 3 0) sourceC2134) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3683) := by
    have ha : (tripleCharges (sourceA2134 + difference 0 3) (sourceB2134 + difference 3 0) sourceC2134) = raw29502 := by
      apply Matrix.ext; unfold tripleCharges sourceA2134 sourceB2134 sourceC2134 difference raw29502; decide +kernel
    rw [ha]
    exact (canonical29502 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2134 + difference 0 4) (sourceB2134 + difference 4 0) sourceC2134) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3873) := by
    have ha : (tripleCharges (sourceA2134 + difference 0 4) (sourceB2134 + difference 4 0) sourceC2134) = raw29503 := by
      apply Matrix.ext; unfold tripleCharges sourceA2134 sourceB2134 sourceC2134 difference raw29503; decide +kernel
    rw [ha]
    exact (canonical29503 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2134 + difference 0 5) (sourceB2134 + difference 5 0) sourceC2134) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3796) := by
    have ha : (tripleCharges (sourceA2134 + difference 0 5) (sourceB2134 + difference 5 0) sourceC2134) = raw29504 := by
      apply Matrix.ext; unfold tripleCharges sourceA2134 sourceB2134 sourceC2134 difference raw29504; decide +kernel
    rw [ha]
    exact (canonical29504 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2134 + sourceB2134) sourceC2134) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (doubleCharges (sourceA2134 + sourceB2134) sourceC2134) = raw29505 := by
      apply Matrix.ext; unfold doubleCharges sourceA2134 sourceB2134 sourceC2134 raw29505; decide +kernel
    rw [ha]
    exact (canonical29505 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2134 sourceB2134 sourceC2134
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2134, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2135 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2135 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC2135 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceForm2135 : Integer.Sparse Master := [(Sum.inr 4553, 2), (Sum.inr 4557, 1), (Sum.inr 4559, 1), (Sum.inr 4627, 1), (Sum.inr 4686, 2), (Sum.inr 4693, 1), (Sum.inr 4871, 1), (Sum.inr 4970, 2), (Sum.inr 4973, 2), (Sum.inr 4979, 1), (Sum.inr 5114, 2), (Sum.inr 5168, 2), (Sum.inr 5170, 2), (Sum.inr 5171, 1), (Sum.inr 5176, 2), (Sum.inr 5308, 1), (Sum.inr 5310, 1), (Sum.inr 5387, 2), (Sum.inr 5389, 1), (Sum.inr 5441, 1), (Sum.inr 5443, 1)]

theorem sourceEq2135 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2135 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2135 + difference 0 1) (sourceB2135 + difference 1 0) sourceC2135) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5389) := by
    have ha : (tripleCharges (sourceA2135 + difference 0 1) (sourceB2135 + difference 1 0) sourceC2135) = raw18306 := by
      apply Matrix.ext; unfold tripleCharges sourceA2135 sourceB2135 sourceC2135 difference raw18306; decide +kernel
    rw [ha]
    exact (canonical18306 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2135 + difference 0 2) (sourceB2135 + difference 2 0) sourceC2135) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5387) := by
    have ha : (tripleCharges (sourceA2135 + difference 0 2) (sourceB2135 + difference 2 0) sourceC2135) = raw18307 := by
      apply Matrix.ext; unfold tripleCharges sourceA2135 sourceB2135 sourceC2135 difference raw18307; decide +kernel
    rw [ha]
    exact (canonical18307 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2135 + difference 0 3) (sourceB2135 + difference 3 0) sourceC2135) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5387) := by
    have ha : (tripleCharges (sourceA2135 + difference 0 3) (sourceB2135 + difference 3 0) sourceC2135) = raw18308 := by
      apply Matrix.ext; unfold tripleCharges sourceA2135 sourceB2135 sourceC2135 difference raw18308; decide +kernel
    rw [ha]
    exact (canonical18308 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2135 + difference 0 4) (sourceB2135 + difference 4 0) sourceC2135) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5441) := by
    have ha : (tripleCharges (sourceA2135 + difference 0 4) (sourceB2135 + difference 4 0) sourceC2135) = raw10216 := by
      apply Matrix.ext; unfold tripleCharges sourceA2135 sourceB2135 sourceC2135 difference raw10216; decide +kernel
    rw [ha]
    exact (canonical10216 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2135 + difference 0 5) (sourceB2135 + difference 5 0) sourceC2135) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA2135 + difference 0 5) (sourceB2135 + difference 5 0) sourceC2135) = raw18309 := by
      apply Matrix.ext; unfold tripleCharges sourceA2135 sourceB2135 sourceC2135 difference raw18309; decide +kernel
    rw [ha]
    exact (canonical18309 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2135 + difference 1 0) (sourceB2135 + difference 0 1) sourceC2135) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4627) := by
    have ha : (tripleCharges (sourceA2135 + difference 1 0) (sourceB2135 + difference 0 1) sourceC2135) = raw10232 := by
      apply Matrix.ext; unfold tripleCharges sourceA2135 sourceB2135 sourceC2135 difference raw10232; decide +kernel
    rw [ha]
    exact (canonical10232 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2135 + difference 1 2) (sourceB2135 + difference 2 1) sourceC2135) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5176) := by
    have ha : (tripleCharges (sourceA2135 + difference 1 2) (sourceB2135 + difference 2 1) sourceC2135) = raw10234 := by
      apply Matrix.ext; unfold tripleCharges sourceA2135 sourceB2135 sourceC2135 difference raw10234; decide +kernel
    rw [ha]
    exact (canonical10234 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2135 + difference 1 3) (sourceB2135 + difference 3 1) sourceC2135) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5176) := by
    have ha : (tripleCharges (sourceA2135 + difference 1 3) (sourceB2135 + difference 3 1) sourceC2135) = raw10235 := by
      apply Matrix.ext; unfold tripleCharges sourceA2135 sourceB2135 sourceC2135 difference raw10235; decide +kernel
    rw [ha]
    exact (canonical10235 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2135 + difference 1 4) (sourceB2135 + difference 4 1) sourceC2135) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5308) := by
    have ha : (tripleCharges (sourceA2135 + difference 1 4) (sourceB2135 + difference 4 1) sourceC2135) = raw5082 := by
      apply Matrix.ext; unfold tripleCharges sourceA2135 sourceB2135 sourceC2135 difference raw5082; decide +kernel
    rw [ha]
    exact (canonical5082 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2135 + difference 1 5) (sourceB2135 + difference 5 1) sourceC2135) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5310) := by
    have ha : (tripleCharges (sourceA2135 + difference 1 5) (sourceB2135 + difference 5 1) sourceC2135) = raw10236 := by
      apply Matrix.ext; unfold tripleCharges sourceA2135 sourceB2135 sourceC2135 difference raw10236; decide +kernel
    rw [ha]
    exact (canonical10236 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2135 + difference 2 0) (sourceB2135 + difference 0 2) sourceC2135) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4553) := by
    have ha : (tripleCharges (sourceA2135 + difference 2 0) (sourceB2135 + difference 0 2) sourceC2135) = raw22476 := by
      apply Matrix.ext; unfold tripleCharges sourceA2135 sourceB2135 sourceC2135 difference raw22476; decide +kernel
    rw [ha]
    exact (canonical22476 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2135 + difference 2 1) (sourceB2135 + difference 1 2) sourceC2135) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4973) := by
    have ha : (tripleCharges (sourceA2135 + difference 2 1) (sourceB2135 + difference 1 2) sourceC2135) = raw29506 := by
      apply Matrix.ext; unfold tripleCharges sourceA2135 sourceB2135 sourceC2135 difference raw29506; decide +kernel
    rw [ha]
    exact (canonical29506 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2135 + difference 2 3) (sourceB2135 + difference 3 2) sourceC2135) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5114) := by
    have ha : (tripleCharges (sourceA2135 + difference 2 3) (sourceB2135 + difference 3 2) sourceC2135) = raw29507 := by
      apply Matrix.ext; unfold tripleCharges sourceA2135 sourceB2135 sourceC2135 difference raw29507; decide +kernel
    rw [ha]
    exact (canonical29507 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2135 + difference 2 4) (sourceB2135 + difference 4 2) sourceC2135) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5168) := by
    have ha : (tripleCharges (sourceA2135 + difference 2 4) (sourceB2135 + difference 4 2) sourceC2135) = raw10225 := by
      apply Matrix.ext; unfold tripleCharges sourceA2135 sourceB2135 sourceC2135 difference raw10225; decide +kernel
    rw [ha]
    exact (canonical10225 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2135 + difference 2 5) (sourceB2135 + difference 5 2) sourceC2135) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5170) := by
    have ha : (tripleCharges (sourceA2135 + difference 2 5) (sourceB2135 + difference 5 2) sourceC2135) = raw29508 := by
      apply Matrix.ext; unfold tripleCharges sourceA2135 sourceB2135 sourceC2135 difference raw29508; decide +kernel
    rw [ha]
    exact (canonical29508 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2135 + difference 3 0) (sourceB2135 + difference 0 3) sourceC2135) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4553) := by
    have ha : (tripleCharges (sourceA2135 + difference 3 0) (sourceB2135 + difference 0 3) sourceC2135) = raw22480 := by
      apply Matrix.ext; unfold tripleCharges sourceA2135 sourceB2135 sourceC2135 difference raw22480; decide +kernel
    rw [ha]
    exact (canonical22480 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2135 + difference 3 1) (sourceB2135 + difference 1 3) sourceC2135) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4973) := by
    have ha : (tripleCharges (sourceA2135 + difference 3 1) (sourceB2135 + difference 1 3) sourceC2135) = raw29509 := by
      apply Matrix.ext; unfold tripleCharges sourceA2135 sourceB2135 sourceC2135 difference raw29509; decide +kernel
    rw [ha]
    exact (canonical29509 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2135 + difference 3 2) (sourceB2135 + difference 2 3) sourceC2135) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5114) := by
    have ha : (tripleCharges (sourceA2135 + difference 3 2) (sourceB2135 + difference 2 3) sourceC2135) = raw29510 := by
      apply Matrix.ext; unfold tripleCharges sourceA2135 sourceB2135 sourceC2135 difference raw29510; decide +kernel
    rw [ha]
    exact (canonical29510 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2135 + difference 3 4) (sourceB2135 + difference 4 3) sourceC2135) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5168) := by
    have ha : (tripleCharges (sourceA2135 + difference 3 4) (sourceB2135 + difference 4 3) sourceC2135) = raw10229 := by
      apply Matrix.ext; unfold tripleCharges sourceA2135 sourceB2135 sourceC2135 difference raw10229; decide +kernel
    rw [ha]
    exact (canonical10229 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2135 + difference 3 5) (sourceB2135 + difference 5 3) sourceC2135) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5170) := by
    have ha : (tripleCharges (sourceA2135 + difference 3 5) (sourceB2135 + difference 5 3) sourceC2135) = raw12098 := by
      apply Matrix.ext; unfold tripleCharges sourceA2135 sourceB2135 sourceC2135 difference raw12098; decide +kernel
    rw [ha]
    exact (canonical12098 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2135 + difference 4 0) (sourceB2135 + difference 0 4) sourceC2135) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4557) := by
    have ha : (tripleCharges (sourceA2135 + difference 4 0) (sourceB2135 + difference 0 4) sourceC2135) = raw22483 := by
      apply Matrix.ext; unfold tripleCharges sourceA2135 sourceB2135 sourceC2135 difference raw22483; decide +kernel
    rw [ha]
    exact (canonical22483 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2135 + difference 4 1) (sourceB2135 + difference 1 4) sourceC2135) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4693) := by
    have ha : (tripleCharges (sourceA2135 + difference 4 1) (sourceB2135 + difference 1 4) sourceC2135) = raw29511 := by
      apply Matrix.ext; unfold tripleCharges sourceA2135 sourceB2135 sourceC2135 difference raw29511; decide +kernel
    rw [ha]
    exact (canonical29511 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2135 + difference 4 2) (sourceB2135 + difference 2 4) sourceC2135) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4686) := by
    have ha : (tripleCharges (sourceA2135 + difference 4 2) (sourceB2135 + difference 2 4) sourceC2135) = raw29512 := by
      apply Matrix.ext; unfold tripleCharges sourceA2135 sourceB2135 sourceC2135 difference raw29512; decide +kernel
    rw [ha]
    exact (canonical29512 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2135 + difference 4 3) (sourceB2135 + difference 3 4) sourceC2135) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4686) := by
    have ha : (tripleCharges (sourceA2135 + difference 4 3) (sourceB2135 + difference 3 4) sourceC2135) = raw29513 := by
      apply Matrix.ext; unfold tripleCharges sourceA2135 sourceB2135 sourceC2135 difference raw29513; decide +kernel
    rw [ha]
    exact (canonical29513 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2135 + difference 4 5) (sourceB2135 + difference 5 4) sourceC2135) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4871) := by
    have ha : (tripleCharges (sourceA2135 + difference 4 5) (sourceB2135 + difference 5 4) sourceC2135) = raw29514 := by
      apply Matrix.ext; unfold tripleCharges sourceA2135 sourceB2135 sourceC2135 difference raw29514; decide +kernel
    rw [ha]
    exact (canonical29514 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2135 + difference 5 0) (sourceB2135 + difference 0 5) sourceC2135) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4559) := by
    have ha : (tripleCharges (sourceA2135 + difference 5 0) (sourceB2135 + difference 0 5) sourceC2135) = raw20361 := by
      apply Matrix.ext; unfold tripleCharges sourceA2135 sourceB2135 sourceC2135 difference raw20361; decide +kernel
    rw [ha]
    exact (canonical20361 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2135 + difference 5 1) (sourceB2135 + difference 1 5) sourceC2135) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4979) := by
    have ha : (tripleCharges (sourceA2135 + difference 5 1) (sourceB2135 + difference 1 5) sourceC2135) = raw27562 := by
      apply Matrix.ext; unfold tripleCharges sourceA2135 sourceB2135 sourceC2135 difference raw27562; decide +kernel
    rw [ha]
    exact (canonical27562 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2135 + difference 5 2) (sourceB2135 + difference 2 5) sourceC2135) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4970) := by
    have ha : (tripleCharges (sourceA2135 + difference 5 2) (sourceB2135 + difference 2 5) sourceC2135) = raw27563 := by
      apply Matrix.ext; unfold tripleCharges sourceA2135 sourceB2135 sourceC2135 difference raw27563; decide +kernel
    rw [ha]
    exact (canonical27563 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2135 + difference 5 3) (sourceB2135 + difference 3 5) sourceC2135) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4970) := by
    have ha : (tripleCharges (sourceA2135 + difference 5 3) (sourceB2135 + difference 3 5) sourceC2135) = raw27564 := by
      apply Matrix.ext; unfold tripleCharges sourceA2135 sourceB2135 sourceC2135 difference raw27564; decide +kernel
    rw [ha]
    exact (canonical27564 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2135 + difference 5 4) (sourceB2135 + difference 4 5) sourceC2135) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5171) := by
    have ha : (tripleCharges (sourceA2135 + difference 5 4) (sourceB2135 + difference 4 5) sourceC2135) = raw5079 := by
      apply Matrix.ext; unfold tripleCharges sourceA2135 sourceB2135 sourceC2135 difference raw5079; decide +kernel
    rw [ha]
    exact (canonical5079 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2135 sourceB2135 sourceC2135
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2135, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2136 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2136 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC2136 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceForm2136 : Integer.Sparse Master := [(Sum.inr 1138, 2), (Sum.inr 1143, 1), (Sum.inr 1145, 1), (Sum.inr 1311, 1), (Sum.inr 1812, 2), (Sum.inr 1819, 1), (Sum.inr 2112, 1), (Sum.inr 2815, 2), (Sum.inr 2817, 2), (Sum.inr 2820, 1), (Sum.inr 2896, 2), (Sum.inr 2954, 2), (Sum.inr 2963, 2), (Sum.inr 2965, 1), (Sum.inr 2968, 2), (Sum.inr 3121, 1), (Sum.inr 3124, 1), (Sum.inr 3739, 2), (Sum.inr 3740, 1), (Sum.inr 3889, 1), (Sum.inr 4037, 1)]

theorem sourceEq2136 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2136 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2136 + difference 0 1) (sourceB2136 + difference 1 0) sourceC2136) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3740) := by
    have ha : (tripleCharges (sourceA2136 + difference 0 1) (sourceB2136 + difference 1 0) sourceC2136) = raw29515 := by
      apply Matrix.ext; unfold tripleCharges sourceA2136 sourceB2136 sourceC2136 difference raw29515; decide +kernel
    rw [ha]
    exact (canonical29515 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2136 + difference 0 2) (sourceB2136 + difference 2 0) sourceC2136) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3739) := by
    have ha : (tripleCharges (sourceA2136 + difference 0 2) (sourceB2136 + difference 2 0) sourceC2136) = raw29516 := by
      apply Matrix.ext; unfold tripleCharges sourceA2136 sourceB2136 sourceC2136 difference raw29516; decide +kernel
    rw [ha]
    exact (canonical29516 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2136 + difference 0 3) (sourceB2136 + difference 3 0) sourceC2136) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3739) := by
    have ha : (tripleCharges (sourceA2136 + difference 0 3) (sourceB2136 + difference 3 0) sourceC2136) = raw29517 := by
      apply Matrix.ext; unfold tripleCharges sourceA2136 sourceB2136 sourceC2136 difference raw29517; decide +kernel
    rw [ha]
    exact (canonical29517 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2136 + difference 0 4) (sourceB2136 + difference 4 0) sourceC2136) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4037) := by
    have ha : (tripleCharges (sourceA2136 + difference 0 4) (sourceB2136 + difference 4 0) sourceC2136) = raw27572 := by
      apply Matrix.ext; unfold tripleCharges sourceA2136 sourceB2136 sourceC2136 difference raw27572; decide +kernel
    rw [ha]
    exact (canonical27572 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2136 + difference 0 5) (sourceB2136 + difference 5 0) sourceC2136) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3889) := by
    have ha : (tripleCharges (sourceA2136 + difference 0 5) (sourceB2136 + difference 5 0) sourceC2136) = raw29518 := by
      apply Matrix.ext; unfold tripleCharges sourceA2136 sourceB2136 sourceC2136 difference raw29518; decide +kernel
    rw [ha]
    exact (canonical29518 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2136 + difference 1 0) (sourceB2136 + difference 0 1) sourceC2136) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1311) := by
    have ha : (tripleCharges (sourceA2136 + difference 1 0) (sourceB2136 + difference 0 1) sourceC2136) = raw20382 := by
      apply Matrix.ext; unfold tripleCharges sourceA2136 sourceB2136 sourceC2136 difference raw20382; decide +kernel
    rw [ha]
    exact (canonical20382 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2136 + difference 1 2) (sourceB2136 + difference 2 1) sourceC2136) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2968) := by
    have ha : (tripleCharges (sourceA2136 + difference 1 2) (sourceB2136 + difference 2 1) sourceC2136) = raw22488 := by
      apply Matrix.ext; unfold tripleCharges sourceA2136 sourceB2136 sourceC2136 difference raw22488; decide +kernel
    rw [ha]
    exact (canonical22488 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2136 + difference 1 3) (sourceB2136 + difference 3 1) sourceC2136) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2968) := by
    have ha : (tripleCharges (sourceA2136 + difference 1 3) (sourceB2136 + difference 3 1) sourceC2136) = raw22489 := by
      apply Matrix.ext; unfold tripleCharges sourceA2136 sourceB2136 sourceC2136 difference raw22489; decide +kernel
    rw [ha]
    exact (canonical22489 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2136 + difference 1 4) (sourceB2136 + difference 4 1) sourceC2136) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3124) := by
    have ha : (tripleCharges (sourceA2136 + difference 1 4) (sourceB2136 + difference 4 1) sourceC2136) = raw12129 := by
      apply Matrix.ext; unfold tripleCharges sourceA2136 sourceB2136 sourceC2136 difference raw12129; decide +kernel
    rw [ha]
    exact (canonical12129 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2136 + difference 1 5) (sourceB2136 + difference 5 1) sourceC2136) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3121) := by
    have ha : (tripleCharges (sourceA2136 + difference 1 5) (sourceB2136 + difference 5 1) sourceC2136) = raw12124 := by
      apply Matrix.ext; unfold tripleCharges sourceA2136 sourceB2136 sourceC2136 difference raw12124; decide +kernel
    rw [ha]
    exact (canonical12124 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2136 + difference 2 0) (sourceB2136 + difference 0 2) sourceC2136) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1138) := by
    have ha : (tripleCharges (sourceA2136 + difference 2 0) (sourceB2136 + difference 0 2) sourceC2136) = raw22495 := by
      apply Matrix.ext; unfold tripleCharges sourceA2136 sourceB2136 sourceC2136 difference raw22495; decide +kernel
    rw [ha]
    exact (canonical22495 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2136 + difference 2 1) (sourceB2136 + difference 1 2) sourceC2136) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2817) := by
    have ha : (tripleCharges (sourceA2136 + difference 2 1) (sourceB2136 + difference 1 2) sourceC2136) = raw29519 := by
      apply Matrix.ext; unfold tripleCharges sourceA2136 sourceB2136 sourceC2136 difference raw29519; decide +kernel
    rw [ha]
    exact (canonical29519 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2136 + difference 2 3) (sourceB2136 + difference 3 2) sourceC2136) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2896) := by
    have ha : (tripleCharges (sourceA2136 + difference 2 3) (sourceB2136 + difference 3 2) sourceC2136) = raw29520 := by
      apply Matrix.ext; unfold tripleCharges sourceA2136 sourceB2136 sourceC2136 difference raw29520; decide +kernel
    rw [ha]
    exact (canonical29520 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2136 + difference 2 4) (sourceB2136 + difference 4 2) sourceC2136) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2963) := by
    have ha : (tripleCharges (sourceA2136 + difference 2 4) (sourceB2136 + difference 4 2) sourceC2136) = raw27576 := by
      apply Matrix.ext; unfold tripleCharges sourceA2136 sourceB2136 sourceC2136 difference raw27576; decide +kernel
    rw [ha]
    exact (canonical27576 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2136 + difference 2 5) (sourceB2136 + difference 5 2) sourceC2136) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2954) := by
    have ha : (tripleCharges (sourceA2136 + difference 2 5) (sourceB2136 + difference 5 2) sourceC2136) = raw29521 := by
      apply Matrix.ext; unfold tripleCharges sourceA2136 sourceB2136 sourceC2136 difference raw29521; decide +kernel
    rw [ha]
    exact (canonical29521 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2136 + difference 3 0) (sourceB2136 + difference 0 3) sourceC2136) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1138) := by
    have ha : (tripleCharges (sourceA2136 + difference 3 0) (sourceB2136 + difference 0 3) sourceC2136) = raw22499 := by
      apply Matrix.ext; unfold tripleCharges sourceA2136 sourceB2136 sourceC2136 difference raw22499; decide +kernel
    rw [ha]
    exact (canonical22499 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2136 + difference 3 1) (sourceB2136 + difference 1 3) sourceC2136) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2817) := by
    have ha : (tripleCharges (sourceA2136 + difference 3 1) (sourceB2136 + difference 1 3) sourceC2136) = raw29522 := by
      apply Matrix.ext; unfold tripleCharges sourceA2136 sourceB2136 sourceC2136 difference raw29522; decide +kernel
    rw [ha]
    exact (canonical29522 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2136 + difference 3 2) (sourceB2136 + difference 2 3) sourceC2136) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2896) := by
    have ha : (tripleCharges (sourceA2136 + difference 3 2) (sourceB2136 + difference 2 3) sourceC2136) = raw29523 := by
      apply Matrix.ext; unfold tripleCharges sourceA2136 sourceB2136 sourceC2136 difference raw29523; decide +kernel
    rw [ha]
    exact (canonical29523 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2136 + difference 3 4) (sourceB2136 + difference 4 3) sourceC2136) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2963) := by
    have ha : (tripleCharges (sourceA2136 + difference 3 4) (sourceB2136 + difference 4 3) sourceC2136) = raw12127 := by
      apply Matrix.ext; unfold tripleCharges sourceA2136 sourceB2136 sourceC2136 difference raw12127; decide +kernel
    rw [ha]
    exact (canonical12127 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2136 + difference 3 5) (sourceB2136 + difference 5 3) sourceC2136) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2954) := by
    have ha : (tripleCharges (sourceA2136 + difference 3 5) (sourceB2136 + difference 5 3) sourceC2136) = raw12122 := by
      apply Matrix.ext; unfold tripleCharges sourceA2136 sourceB2136 sourceC2136 difference raw12122; decide +kernel
    rw [ha]
    exact (canonical12122 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2136 + difference 4 0) (sourceB2136 + difference 0 4) sourceC2136) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1143) := by
    have ha : (tripleCharges (sourceA2136 + difference 4 0) (sourceB2136 + difference 0 4) sourceC2136) = raw22502 := by
      apply Matrix.ext; unfold tripleCharges sourceA2136 sourceB2136 sourceC2136 difference raw22502; decide +kernel
    rw [ha]
    exact (canonical22502 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2136 + difference 4 1) (sourceB2136 + difference 1 4) sourceC2136) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1819) := by
    have ha : (tripleCharges (sourceA2136 + difference 4 1) (sourceB2136 + difference 1 4) sourceC2136) = raw29524 := by
      apply Matrix.ext; unfold tripleCharges sourceA2136 sourceB2136 sourceC2136 difference raw29524; decide +kernel
    rw [ha]
    exact (canonical29524 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2136 + difference 4 2) (sourceB2136 + difference 2 4) sourceC2136) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1812) := by
    have ha : (tripleCharges (sourceA2136 + difference 4 2) (sourceB2136 + difference 2 4) sourceC2136) = raw29525 := by
      apply Matrix.ext; unfold tripleCharges sourceA2136 sourceB2136 sourceC2136 difference raw29525; decide +kernel
    rw [ha]
    exact (canonical29525 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2136 + difference 4 3) (sourceB2136 + difference 3 4) sourceC2136) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1812) := by
    have ha : (tripleCharges (sourceA2136 + difference 4 3) (sourceB2136 + difference 3 4) sourceC2136) = raw29526 := by
      apply Matrix.ext; unfold tripleCharges sourceA2136 sourceB2136 sourceC2136 difference raw29526; decide +kernel
    rw [ha]
    exact (canonical29526 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2136 + difference 4 5) (sourceB2136 + difference 5 4) sourceC2136) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2112) := by
    have ha : (tripleCharges (sourceA2136 + difference 4 5) (sourceB2136 + difference 5 4) sourceC2136) = raw29527 := by
      apply Matrix.ext; unfold tripleCharges sourceA2136 sourceB2136 sourceC2136 difference raw29527; decide +kernel
    rw [ha]
    exact (canonical29527 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2136 + difference 5 0) (sourceB2136 + difference 0 5) sourceC2136) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1145) := by
    have ha : (tripleCharges (sourceA2136 + difference 5 0) (sourceB2136 + difference 0 5) sourceC2136) = raw20379 := by
      apply Matrix.ext; unfold tripleCharges sourceA2136 sourceB2136 sourceC2136 difference raw20379; decide +kernel
    rw [ha]
    exact (canonical20379 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2136 + difference 5 1) (sourceB2136 + difference 1 5) sourceC2136) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2820) := by
    have ha : (tripleCharges (sourceA2136 + difference 5 1) (sourceB2136 + difference 1 5) sourceC2136) = raw27580 := by
      apply Matrix.ext; unfold tripleCharges sourceA2136 sourceB2136 sourceC2136 difference raw27580; decide +kernel
    rw [ha]
    exact (canonical27580 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2136 + difference 5 2) (sourceB2136 + difference 2 5) sourceC2136) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2815) := by
    have ha : (tripleCharges (sourceA2136 + difference 5 2) (sourceB2136 + difference 2 5) sourceC2136) = raw27581 := by
      apply Matrix.ext; unfold tripleCharges sourceA2136 sourceB2136 sourceC2136 difference raw27581; decide +kernel
    rw [ha]
    exact (canonical27581 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2136 + difference 5 3) (sourceB2136 + difference 3 5) sourceC2136) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2815) := by
    have ha : (tripleCharges (sourceA2136 + difference 5 3) (sourceB2136 + difference 3 5) sourceC2136) = raw27582 := by
      apply Matrix.ext; unfold tripleCharges sourceA2136 sourceB2136 sourceC2136 difference raw27582; decide +kernel
    rw [ha]
    exact (canonical27582 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2136 + difference 5 4) (sourceB2136 + difference 4 5) sourceC2136) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2965) := by
    have ha : (tripleCharges (sourceA2136 + difference 5 4) (sourceB2136 + difference 4 5) sourceC2136) = raw20364 := by
      apply Matrix.ext; unfold tripleCharges sourceA2136 sourceB2136 sourceC2136 difference raw20364; decide +kernel
    rw [ha]
    exact (canonical20364 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2136 sourceB2136 sourceC2136
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2136, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2137 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2137 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC2137 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceForm2137 : Integer.Sparse Master := [(Sum.inr 4354, 2), (Sum.inr 4359, 1), (Sum.inr 4361, 1), (Sum.inr 4466, 1), (Sum.inr 4681, 2), (Sum.inr 4692, 1), (Sum.inr 4868, 1), (Sum.inr 4949, 2), (Sum.inr 4953, 1), (Sum.inr 4972, 2), (Sum.inr 5038, 2), (Sum.inr 5080, 2), (Sum.inr 5163, 2), (Sum.inr 5172, 2), (Sum.inr 5174, 1), (Sum.inr 5291, 1), (Sum.inr 5294, 1), (Sum.inr 5388, 2), (Sum.inr 5390, 1), (Sum.inr 5442, 1), (Sum.inr 5451, 1)]

theorem sourceEq2137 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2137 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2137 + difference 0 1) (sourceB2137 + difference 1 0) sourceC2137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5390) := by
    have ha : (tripleCharges (sourceA2137 + difference 0 1) (sourceB2137 + difference 1 0) sourceC2137) = raw29528 := by
      apply Matrix.ext; unfold tripleCharges sourceA2137 sourceB2137 sourceC2137 difference raw29528; decide +kernel
    rw [ha]
    exact (canonical29528 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2137 + difference 0 2) (sourceB2137 + difference 2 0) sourceC2137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5388) := by
    have ha : (tripleCharges (sourceA2137 + difference 0 2) (sourceB2137 + difference 2 0) sourceC2137) = raw29529 := by
      apply Matrix.ext; unfold tripleCharges sourceA2137 sourceB2137 sourceC2137 difference raw29529; decide +kernel
    rw [ha]
    exact (canonical29529 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2137 + difference 0 3) (sourceB2137 + difference 3 0) sourceC2137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5388) := by
    have ha : (tripleCharges (sourceA2137 + difference 0 3) (sourceB2137 + difference 3 0) sourceC2137) = raw29530 := by
      apply Matrix.ext; unfold tripleCharges sourceA2137 sourceB2137 sourceC2137 difference raw29530; decide +kernel
    rw [ha]
    exact (canonical29530 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2137 + difference 0 4) (sourceB2137 + difference 4 0) sourceC2137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA2137 + difference 0 4) (sourceB2137 + difference 4 0) sourceC2137) = raw9592 := by
      apply Matrix.ext; unfold tripleCharges sourceA2137 sourceB2137 sourceC2137 difference raw9592; decide +kernel
    rw [ha]
    exact (canonical9592 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2137 + difference 0 5) (sourceB2137 + difference 5 0) sourceC2137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5442) := by
    have ha : (tripleCharges (sourceA2137 + difference 0 5) (sourceB2137 + difference 5 0) sourceC2137) = raw29531 := by
      apply Matrix.ext; unfold tripleCharges sourceA2137 sourceB2137 sourceC2137 difference raw29531; decide +kernel
    rw [ha]
    exact (canonical29531 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2137 + difference 1 0) (sourceB2137 + difference 0 1) sourceC2137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4466) := by
    have ha : (tripleCharges (sourceA2137 + difference 1 0) (sourceB2137 + difference 0 1) sourceC2137) = raw9612 := by
      apply Matrix.ext; unfold tripleCharges sourceA2137 sourceB2137 sourceC2137 difference raw9612; decide +kernel
    rw [ha]
    exact (canonical9612 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2137 + difference 1 2) (sourceB2137 + difference 2 1) sourceC2137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5080) := by
    have ha : (tripleCharges (sourceA2137 + difference 1 2) (sourceB2137 + difference 2 1) sourceC2137) = raw9614 := by
      apply Matrix.ext; unfold tripleCharges sourceA2137 sourceB2137 sourceC2137 difference raw9614; decide +kernel
    rw [ha]
    exact (canonical9614 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2137 + difference 1 3) (sourceB2137 + difference 3 1) sourceC2137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5080) := by
    have ha : (tripleCharges (sourceA2137 + difference 1 3) (sourceB2137 + difference 3 1) sourceC2137) = raw9615 := by
      apply Matrix.ext; unfold tripleCharges sourceA2137 sourceB2137 sourceC2137 difference raw9615; decide +kernel
    rw [ha]
    exact (canonical9615 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2137 + difference 1 4) (sourceB2137 + difference 4 1) sourceC2137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5291) := by
    have ha : (tripleCharges (sourceA2137 + difference 1 4) (sourceB2137 + difference 4 1) sourceC2137) = raw28619 := by
      apply Matrix.ext; unfold tripleCharges sourceA2137 sourceB2137 sourceC2137 difference raw28619; decide +kernel
    rw [ha]
    exact (canonical28619 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2137 + difference 1 5) (sourceB2137 + difference 5 1) sourceC2137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA2137 + difference 1 5) (sourceB2137 + difference 5 1) sourceC2137) = raw9616 := by
      apply Matrix.ext; unfold tripleCharges sourceA2137 sourceB2137 sourceC2137 difference raw9616; decide +kernel
    rw [ha]
    exact (canonical9616 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2137 + difference 2 0) (sourceB2137 + difference 0 2) sourceC2137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4354) := by
    have ha : (tripleCharges (sourceA2137 + difference 2 0) (sourceB2137 + difference 0 2) sourceC2137) = raw29532 := by
      apply Matrix.ext; unfold tripleCharges sourceA2137 sourceB2137 sourceC2137 difference raw29532; decide +kernel
    rw [ha]
    exact (canonical29532 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2137 + difference 2 1) (sourceB2137 + difference 1 2) sourceC2137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4949) := by
    have ha : (tripleCharges (sourceA2137 + difference 2 1) (sourceB2137 + difference 1 2) sourceC2137) = raw29533 := by
      apply Matrix.ext; unfold tripleCharges sourceA2137 sourceB2137 sourceC2137 difference raw29533; decide +kernel
    rw [ha]
    exact (canonical29533 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2137 + difference 2 3) (sourceB2137 + difference 3 2) sourceC2137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5038) := by
    have ha : (tripleCharges (sourceA2137 + difference 2 3) (sourceB2137 + difference 3 2) sourceC2137) = raw29534 := by
      apply Matrix.ext; unfold tripleCharges sourceA2137 sourceB2137 sourceC2137 difference raw29534; decide +kernel
    rw [ha]
    exact (canonical29534 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2137 + difference 2 4) (sourceB2137 + difference 4 2) sourceC2137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5163) := by
    have ha : (tripleCharges (sourceA2137 + difference 2 4) (sourceB2137 + difference 4 2) sourceC2137) = raw9603 := by
      apply Matrix.ext; unfold tripleCharges sourceA2137 sourceB2137 sourceC2137 difference raw9603; decide +kernel
    rw [ha]
    exact (canonical9603 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2137 + difference 2 5) (sourceB2137 + difference 5 2) sourceC2137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5172) := by
    have ha : (tripleCharges (sourceA2137 + difference 2 5) (sourceB2137 + difference 5 2) sourceC2137) = raw29535 := by
      apply Matrix.ext; unfold tripleCharges sourceA2137 sourceB2137 sourceC2137 difference raw29535; decide +kernel
    rw [ha]
    exact (canonical29535 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2137 + difference 3 0) (sourceB2137 + difference 0 3) sourceC2137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4354) := by
    have ha : (tripleCharges (sourceA2137 + difference 3 0) (sourceB2137 + difference 0 3) sourceC2137) = raw29536 := by
      apply Matrix.ext; unfold tripleCharges sourceA2137 sourceB2137 sourceC2137 difference raw29536; decide +kernel
    rw [ha]
    exact (canonical29536 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2137 + difference 3 1) (sourceB2137 + difference 1 3) sourceC2137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4949) := by
    have ha : (tripleCharges (sourceA2137 + difference 3 1) (sourceB2137 + difference 1 3) sourceC2137) = raw29537 := by
      apply Matrix.ext; unfold tripleCharges sourceA2137 sourceB2137 sourceC2137 difference raw29537; decide +kernel
    rw [ha]
    exact (canonical29537 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2137 + difference 3 2) (sourceB2137 + difference 2 3) sourceC2137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5038) := by
    have ha : (tripleCharges (sourceA2137 + difference 3 2) (sourceB2137 + difference 2 3) sourceC2137) = raw29538 := by
      apply Matrix.ext; unfold tripleCharges sourceA2137 sourceB2137 sourceC2137 difference raw29538; decide +kernel
    rw [ha]
    exact (canonical29538 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2137 + difference 3 4) (sourceB2137 + difference 4 3) sourceC2137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5163) := by
    have ha : (tripleCharges (sourceA2137 + difference 3 4) (sourceB2137 + difference 4 3) sourceC2137) = raw9608 := by
      apply Matrix.ext; unfold tripleCharges sourceA2137 sourceB2137 sourceC2137 difference raw9608; decide +kernel
    rw [ha]
    exact (canonical9608 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2137 + difference 3 5) (sourceB2137 + difference 5 3) sourceC2137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5172) := by
    have ha : (tripleCharges (sourceA2137 + difference 3 5) (sourceB2137 + difference 5 3) sourceC2137) = raw29539 := by
      apply Matrix.ext; unfold tripleCharges sourceA2137 sourceB2137 sourceC2137 difference raw29539; decide +kernel
    rw [ha]
    exact (canonical29539 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2137 + difference 4 0) (sourceB2137 + difference 0 4) sourceC2137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4361) := by
    have ha : (tripleCharges (sourceA2137 + difference 4 0) (sourceB2137 + difference 0 4) sourceC2137) = raw29540 := by
      apply Matrix.ext; unfold tripleCharges sourceA2137 sourceB2137 sourceC2137 difference raw29540; decide +kernel
    rw [ha]
    exact (canonical29540 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2137 + difference 4 1) (sourceB2137 + difference 1 4) sourceC2137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4953) := by
    have ha : (tripleCharges (sourceA2137 + difference 4 1) (sourceB2137 + difference 1 4) sourceC2137) = raw29541 := by
      apply Matrix.ext; unfold tripleCharges sourceA2137 sourceB2137 sourceC2137 difference raw29541; decide +kernel
    rw [ha]
    exact (canonical29541 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2137 + difference 4 2) (sourceB2137 + difference 2 4) sourceC2137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4972) := by
    have ha : (tripleCharges (sourceA2137 + difference 4 2) (sourceB2137 + difference 2 4) sourceC2137) = raw29542 := by
      apply Matrix.ext; unfold tripleCharges sourceA2137 sourceB2137 sourceC2137 difference raw29542; decide +kernel
    rw [ha]
    exact (canonical29542 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2137 + difference 4 3) (sourceB2137 + difference 3 4) sourceC2137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4972) := by
    have ha : (tripleCharges (sourceA2137 + difference 4 3) (sourceB2137 + difference 3 4) sourceC2137) = raw29543 := by
      apply Matrix.ext; unfold tripleCharges sourceA2137 sourceB2137 sourceC2137 difference raw29543; decide +kernel
    rw [ha]
    exact (canonical29543 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2137 + difference 4 5) (sourceB2137 + difference 5 4) sourceC2137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5174) := by
    have ha : (tripleCharges (sourceA2137 + difference 4 5) (sourceB2137 + difference 5 4) sourceC2137) = raw29544 := by
      apply Matrix.ext; unfold tripleCharges sourceA2137 sourceB2137 sourceC2137 difference raw29544; decide +kernel
    rw [ha]
    exact (canonical29544 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2137 + difference 5 0) (sourceB2137 + difference 0 5) sourceC2137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4359) := by
    have ha : (tripleCharges (sourceA2137 + difference 5 0) (sourceB2137 + difference 0 5) sourceC2137) = raw28628 := by
      apply Matrix.ext; unfold tripleCharges sourceA2137 sourceB2137 sourceC2137 difference raw28628; decide +kernel
    rw [ha]
    exact (canonical28628 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2137 + difference 5 1) (sourceB2137 + difference 1 5) sourceC2137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4692) := by
    have ha : (tripleCharges (sourceA2137 + difference 5 1) (sourceB2137 + difference 1 5) sourceC2137) = raw28629 := by
      apply Matrix.ext; unfold tripleCharges sourceA2137 sourceB2137 sourceC2137 difference raw28629; decide +kernel
    rw [ha]
    exact (canonical28629 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2137 + difference 5 2) (sourceB2137 + difference 2 5) sourceC2137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4681) := by
    have ha : (tripleCharges (sourceA2137 + difference 5 2) (sourceB2137 + difference 2 5) sourceC2137) = raw28630 := by
      apply Matrix.ext; unfold tripleCharges sourceA2137 sourceB2137 sourceC2137 difference raw28630; decide +kernel
    rw [ha]
    exact (canonical28630 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2137 + difference 5 3) (sourceB2137 + difference 3 5) sourceC2137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4681) := by
    have ha : (tripleCharges (sourceA2137 + difference 5 3) (sourceB2137 + difference 3 5) sourceC2137) = raw28631 := by
      apply Matrix.ext; unfold tripleCharges sourceA2137 sourceB2137 sourceC2137 difference raw28631; decide +kernel
    rw [ha]
    exact (canonical28631 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2137 + difference 5 4) (sourceB2137 + difference 4 5) sourceC2137) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4868) := by
    have ha : (tripleCharges (sourceA2137 + difference 5 4) (sourceB2137 + difference 4 5) sourceC2137) = raw9618 := by
      apply Matrix.ext; unfold tripleCharges sourceA2137 sourceB2137 sourceC2137 difference raw9618; decide +kernel
    rw [ha]
    exact (canonical9618 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2137 sourceB2137 sourceC2137
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2137, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2138 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2138 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC2138 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceForm2138 : Integer.Sparse Master := [(Sum.inr 932, 2), (Sum.inr 937, 1), (Sum.inr 939, 1), (Sum.inr 1049, 1), (Sum.inr 1807, 2), (Sum.inr 1818, 1), (Sum.inr 2109, 1), (Sum.inr 2341, 2), (Sum.inr 2345, 1), (Sum.inr 2431, 2), (Sum.inr 2434, 2), (Sum.inr 2488, 2), (Sum.inr 2590, 2), (Sum.inr 2599, 2), (Sum.inr 2601, 1), (Sum.inr 2765, 1), (Sum.inr 2768, 1), (Sum.inr 3737, 2), (Sum.inr 3741, 1), (Sum.inr 3888, 1), (Sum.inr 4001, 1)]

theorem sourceEq2138 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2138 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2138 + difference 0 1) (sourceB2138 + difference 1 0) sourceC2138) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3741) := by
    have ha : (tripleCharges (sourceA2138 + difference 0 1) (sourceB2138 + difference 1 0) sourceC2138) = raw29545 := by
      apply Matrix.ext; unfold tripleCharges sourceA2138 sourceB2138 sourceC2138 difference raw29545; decide +kernel
    rw [ha]
    exact (canonical29545 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2138 + difference 0 2) (sourceB2138 + difference 2 0) sourceC2138) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3737) := by
    have ha : (tripleCharges (sourceA2138 + difference 0 2) (sourceB2138 + difference 2 0) sourceC2138) = raw29546 := by
      apply Matrix.ext; unfold tripleCharges sourceA2138 sourceB2138 sourceC2138 difference raw29546; decide +kernel
    rw [ha]
    exact (canonical29546 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2138 + difference 0 3) (sourceB2138 + difference 3 0) sourceC2138) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3737) := by
    have ha : (tripleCharges (sourceA2138 + difference 0 3) (sourceB2138 + difference 3 0) sourceC2138) = raw29547 := by
      apply Matrix.ext; unfold tripleCharges sourceA2138 sourceB2138 sourceC2138 difference raw29547; decide +kernel
    rw [ha]
    exact (canonical29547 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2138 + difference 0 4) (sourceB2138 + difference 4 0) sourceC2138) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3888) := by
    have ha : (tripleCharges (sourceA2138 + difference 0 4) (sourceB2138 + difference 4 0) sourceC2138) = raw9622 := by
      apply Matrix.ext; unfold tripleCharges sourceA2138 sourceB2138 sourceC2138 difference raw9622; decide +kernel
    rw [ha]
    exact (canonical9622 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2138 + difference 0 5) (sourceB2138 + difference 5 0) sourceC2138) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4001) := by
    have ha : (tripleCharges (sourceA2138 + difference 0 5) (sourceB2138 + difference 5 0) sourceC2138) = raw29548 := by
      apply Matrix.ext; unfold tripleCharges sourceA2138 sourceB2138 sourceC2138 difference raw29548; decide +kernel
    rw [ha]
    exact (canonical29548 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2138 + difference 1 0) (sourceB2138 + difference 0 1) sourceC2138) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1049) := by
    have ha : (tripleCharges (sourceA2138 + difference 1 0) (sourceB2138 + difference 0 1) sourceC2138) = raw9642 := by
      apply Matrix.ext; unfold tripleCharges sourceA2138 sourceB2138 sourceC2138 difference raw9642; decide +kernel
    rw [ha]
    exact (canonical9642 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2138 + difference 1 2) (sourceB2138 + difference 2 1) sourceC2138) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2488) := by
    have ha : (tripleCharges (sourceA2138 + difference 1 2) (sourceB2138 + difference 2 1) sourceC2138) = raw9644 := by
      apply Matrix.ext; unfold tripleCharges sourceA2138 sourceB2138 sourceC2138 difference raw9644; decide +kernel
    rw [ha]
    exact (canonical9644 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2138 + difference 1 3) (sourceB2138 + difference 3 1) sourceC2138) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2488) := by
    have ha : (tripleCharges (sourceA2138 + difference 1 3) (sourceB2138 + difference 3 1) sourceC2138) = raw9645 := by
      apply Matrix.ext; unfold tripleCharges sourceA2138 sourceB2138 sourceC2138 difference raw9645; decide +kernel
    rw [ha]
    exact (canonical9645 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2138 + difference 1 4) (sourceB2138 + difference 4 1) sourceC2138) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2765) := by
    have ha : (tripleCharges (sourceA2138 + difference 1 4) (sourceB2138 + difference 4 1) sourceC2138) = raw28641 := by
      apply Matrix.ext; unfold tripleCharges sourceA2138 sourceB2138 sourceC2138 difference raw28641; decide +kernel
    rw [ha]
    exact (canonical28641 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2138 + difference 1 5) (sourceB2138 + difference 5 1) sourceC2138) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2768) := by
    have ha : (tripleCharges (sourceA2138 + difference 1 5) (sourceB2138 + difference 5 1) sourceC2138) = raw9646 := by
      apply Matrix.ext; unfold tripleCharges sourceA2138 sourceB2138 sourceC2138 difference raw9646; decide +kernel
    rw [ha]
    exact (canonical9646 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2138 + difference 2 0) (sourceB2138 + difference 0 2) sourceC2138) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 932) := by
    have ha : (tripleCharges (sourceA2138 + difference 2 0) (sourceB2138 + difference 0 2) sourceC2138) = raw29549 := by
      apply Matrix.ext; unfold tripleCharges sourceA2138 sourceB2138 sourceC2138 difference raw29549; decide +kernel
    rw [ha]
    exact (canonical29549 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2138 + difference 2 1) (sourceB2138 + difference 1 2) sourceC2138) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2341) := by
    have ha : (tripleCharges (sourceA2138 + difference 2 1) (sourceB2138 + difference 1 2) sourceC2138) = raw29550 := by
      apply Matrix.ext; unfold tripleCharges sourceA2138 sourceB2138 sourceC2138 difference raw29550; decide +kernel
    rw [ha]
    exact (canonical29550 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2138 + difference 2 3) (sourceB2138 + difference 3 2) sourceC2138) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2431) := by
    have ha : (tripleCharges (sourceA2138 + difference 2 3) (sourceB2138 + difference 3 2) sourceC2138) = raw29551 := by
      apply Matrix.ext; unfold tripleCharges sourceA2138 sourceB2138 sourceC2138 difference raw29551; decide +kernel
    rw [ha]
    exact (canonical29551 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2138 + difference 2 4) (sourceB2138 + difference 4 2) sourceC2138) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2590) := by
    have ha : (tripleCharges (sourceA2138 + difference 2 4) (sourceB2138 + difference 4 2) sourceC2138) = raw9633 := by
      apply Matrix.ext; unfold tripleCharges sourceA2138 sourceB2138 sourceC2138 difference raw9633; decide +kernel
    rw [ha]
    exact (canonical9633 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2138 + difference 2 5) (sourceB2138 + difference 5 2) sourceC2138) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2599) := by
    have ha : (tripleCharges (sourceA2138 + difference 2 5) (sourceB2138 + difference 5 2) sourceC2138) = raw29552 := by
      apply Matrix.ext; unfold tripleCharges sourceA2138 sourceB2138 sourceC2138 difference raw29552; decide +kernel
    rw [ha]
    exact (canonical29552 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2138 + difference 3 0) (sourceB2138 + difference 0 3) sourceC2138) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 932) := by
    have ha : (tripleCharges (sourceA2138 + difference 3 0) (sourceB2138 + difference 0 3) sourceC2138) = raw29553 := by
      apply Matrix.ext; unfold tripleCharges sourceA2138 sourceB2138 sourceC2138 difference raw29553; decide +kernel
    rw [ha]
    exact (canonical29553 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2138 + difference 3 1) (sourceB2138 + difference 1 3) sourceC2138) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2341) := by
    have ha : (tripleCharges (sourceA2138 + difference 3 1) (sourceB2138 + difference 1 3) sourceC2138) = raw29554 := by
      apply Matrix.ext; unfold tripleCharges sourceA2138 sourceB2138 sourceC2138 difference raw29554; decide +kernel
    rw [ha]
    exact (canonical29554 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2138 + difference 3 2) (sourceB2138 + difference 2 3) sourceC2138) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2431) := by
    have ha : (tripleCharges (sourceA2138 + difference 3 2) (sourceB2138 + difference 2 3) sourceC2138) = raw29555 := by
      apply Matrix.ext; unfold tripleCharges sourceA2138 sourceB2138 sourceC2138 difference raw29555; decide +kernel
    rw [ha]
    exact (canonical29555 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2138 + difference 3 4) (sourceB2138 + difference 4 3) sourceC2138) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2590) := by
    have ha : (tripleCharges (sourceA2138 + difference 3 4) (sourceB2138 + difference 4 3) sourceC2138) = raw9638 := by
      apply Matrix.ext; unfold tripleCharges sourceA2138 sourceB2138 sourceC2138 difference raw9638; decide +kernel
    rw [ha]
    exact (canonical9638 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2138 + difference 3 5) (sourceB2138 + difference 5 3) sourceC2138) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2599) := by
    have ha : (tripleCharges (sourceA2138 + difference 3 5) (sourceB2138 + difference 5 3) sourceC2138) = raw29556 := by
      apply Matrix.ext; unfold tripleCharges sourceA2138 sourceB2138 sourceC2138 difference raw29556; decide +kernel
    rw [ha]
    exact (canonical29556 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2138 + difference 4 0) (sourceB2138 + difference 0 4) sourceC2138) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 939) := by
    have ha : (tripleCharges (sourceA2138 + difference 4 0) (sourceB2138 + difference 0 4) sourceC2138) = raw29557 := by
      apply Matrix.ext; unfold tripleCharges sourceA2138 sourceB2138 sourceC2138 difference raw29557; decide +kernel
    rw [ha]
    exact (canonical29557 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2138 + difference 4 1) (sourceB2138 + difference 1 4) sourceC2138) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2345) := by
    have ha : (tripleCharges (sourceA2138 + difference 4 1) (sourceB2138 + difference 1 4) sourceC2138) = raw29558 := by
      apply Matrix.ext; unfold tripleCharges sourceA2138 sourceB2138 sourceC2138 difference raw29558; decide +kernel
    rw [ha]
    exact (canonical29558 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2138 + difference 4 2) (sourceB2138 + difference 2 4) sourceC2138) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2434) := by
    have ha : (tripleCharges (sourceA2138 + difference 4 2) (sourceB2138 + difference 2 4) sourceC2138) = raw29559 := by
      apply Matrix.ext; unfold tripleCharges sourceA2138 sourceB2138 sourceC2138 difference raw29559; decide +kernel
    rw [ha]
    exact (canonical29559 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2138 + difference 4 3) (sourceB2138 + difference 3 4) sourceC2138) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2434) := by
    have ha : (tripleCharges (sourceA2138 + difference 4 3) (sourceB2138 + difference 3 4) sourceC2138) = raw29560 := by
      apply Matrix.ext; unfold tripleCharges sourceA2138 sourceB2138 sourceC2138 difference raw29560; decide +kernel
    rw [ha]
    exact (canonical29560 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2138 + difference 4 5) (sourceB2138 + difference 5 4) sourceC2138) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2601) := by
    have ha : (tripleCharges (sourceA2138 + difference 4 5) (sourceB2138 + difference 5 4) sourceC2138) = raw29561 := by
      apply Matrix.ext; unfold tripleCharges sourceA2138 sourceB2138 sourceC2138 difference raw29561; decide +kernel
    rw [ha]
    exact (canonical29561 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2138 + difference 5 0) (sourceB2138 + difference 0 5) sourceC2138) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 937) := by
    have ha : (tripleCharges (sourceA2138 + difference 5 0) (sourceB2138 + difference 0 5) sourceC2138) = raw28650 := by
      apply Matrix.ext; unfold tripleCharges sourceA2138 sourceB2138 sourceC2138 difference raw28650; decide +kernel
    rw [ha]
    exact (canonical28650 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2138 + difference 5 1) (sourceB2138 + difference 1 5) sourceC2138) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1818) := by
    have ha : (tripleCharges (sourceA2138 + difference 5 1) (sourceB2138 + difference 1 5) sourceC2138) = raw28651 := by
      apply Matrix.ext; unfold tripleCharges sourceA2138 sourceB2138 sourceC2138 difference raw28651; decide +kernel
    rw [ha]
    exact (canonical28651 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2138 + difference 5 2) (sourceB2138 + difference 2 5) sourceC2138) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1807) := by
    have ha : (tripleCharges (sourceA2138 + difference 5 2) (sourceB2138 + difference 2 5) sourceC2138) = raw28652 := by
      apply Matrix.ext; unfold tripleCharges sourceA2138 sourceB2138 sourceC2138 difference raw28652; decide +kernel
    rw [ha]
    exact (canonical28652 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2138 + difference 5 3) (sourceB2138 + difference 3 5) sourceC2138) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1807) := by
    have ha : (tripleCharges (sourceA2138 + difference 5 3) (sourceB2138 + difference 3 5) sourceC2138) = raw28653 := by
      apply Matrix.ext; unfold tripleCharges sourceA2138 sourceB2138 sourceC2138 difference raw28653; decide +kernel
    rw [ha]
    exact (canonical28653 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2138 + difference 5 4) (sourceB2138 + difference 4 5) sourceC2138) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2109) := by
    have ha : (tripleCharges (sourceA2138 + difference 5 4) (sourceB2138 + difference 4 5) sourceC2138) = raw9648 := by
      apply Matrix.ext; unfold tripleCharges sourceA2138 sourceB2138 sourceC2138 difference raw9648; decide +kernel
    rw [ha]
    exact (canonical9648 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2138 sourceB2138 sourceC2138
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2138, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2139 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceB2139 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC2139 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceForm2139 : Integer.Sparse Master := [(Sum.inr 4810, 2), (Sum.inr 4845, 1), (Sum.inr 4846, 1), (Sum.inr 4874, 1), (Sum.inr 5080, 4), (Sum.inr 5110, 2), (Sum.inr 5111, 2), (Sum.inr 5129, 2), (Sum.inr 5140, 2), (Sum.inr 5141, 2), (Sum.inr 5151, 2), (Sum.inr 5152, 2), (Sum.inr 5175, 1), (Sum.inr 5176, 1), (Sum.inr 5177, 1), (Sum.inr 5188, 2), (Sum.inr 5206, 1), (Sum.inr 5207, 1)]

theorem sourceEq2139 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2139 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2139 + difference 0 1) (sourceB2139 + difference 1 0) sourceC2139) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5176) := by
    have ha : (tripleCharges (sourceA2139 + difference 0 1) (sourceB2139 + difference 1 0) sourceC2139) = raw29562 := by
      apply Matrix.ext; unfold tripleCharges sourceA2139 sourceB2139 sourceC2139 difference raw29562; decide +kernel
    rw [ha]
    exact (canonical29562 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2139 + difference 0 2) (sourceB2139 + difference 2 0) sourceC2139) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5080) := by
    have ha : (tripleCharges (sourceA2139 + difference 0 2) (sourceB2139 + difference 2 0) sourceC2139) = raw29563 := by
      apply Matrix.ext; unfold tripleCharges sourceA2139 sourceB2139 sourceC2139 difference raw29563; decide +kernel
    rw [ha]
    exact (canonical29563 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2139 + difference 0 3) (sourceB2139 + difference 3 0) sourceC2139) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5080) := by
    have ha : (tripleCharges (sourceA2139 + difference 0 3) (sourceB2139 + difference 3 0) sourceC2139) = raw29564 := by
      apply Matrix.ext; unfold tripleCharges sourceA2139 sourceB2139 sourceC2139 difference raw29564; decide +kernel
    rw [ha]
    exact (canonical29564 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2139 + difference 0 4) (sourceB2139 + difference 4 0) sourceC2139) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5110) := by
    have ha : (tripleCharges (sourceA2139 + difference 0 4) (sourceB2139 + difference 4 0) sourceC2139) = raw29565 := by
      apply Matrix.ext; unfold tripleCharges sourceA2139 sourceB2139 sourceC2139 difference raw29565; decide +kernel
    rw [ha]
    exact (canonical29565 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2139 + difference 0 5) (sourceB2139 + difference 5 0) sourceC2139) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5111) := by
    have ha : (tripleCharges (sourceA2139 + difference 0 5) (sourceB2139 + difference 5 0) sourceC2139) = raw29566 := by
      apply Matrix.ext; unfold tripleCharges sourceA2139 sourceB2139 sourceC2139 difference raw29566; decide +kernel
    rw [ha]
    exact (canonical29566 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2139 + difference 1 0) (sourceB2139 + difference 0 1) sourceC2139) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4874) := by
    have ha : (tripleCharges (sourceA2139 + difference 1 0) (sourceB2139 + difference 0 1) sourceC2139) = raw29567 := by
      apply Matrix.ext; unfold tripleCharges sourceA2139 sourceB2139 sourceC2139 difference raw29567; decide +kernel
    rw [ha]
    exact (canonical29567 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2139 + difference 1 2) (sourceB2139 + difference 2 1) sourceC2139) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5188) := by
    have ha : (tripleCharges (sourceA2139 + difference 1 2) (sourceB2139 + difference 2 1) sourceC2139) = raw29568 := by
      apply Matrix.ext; unfold tripleCharges sourceA2139 sourceB2139 sourceC2139 difference raw29568; decide +kernel
    rw [ha]
    exact (canonical29568 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2139 + difference 1 3) (sourceB2139 + difference 3 1) sourceC2139) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5188) := by
    have ha : (tripleCharges (sourceA2139 + difference 1 3) (sourceB2139 + difference 3 1) sourceC2139) = raw29569 := by
      apply Matrix.ext; unfold tripleCharges sourceA2139 sourceB2139 sourceC2139 difference raw29569; decide +kernel
    rw [ha]
    exact (canonical29569 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2139 + difference 1 4) (sourceB2139 + difference 4 1) sourceC2139) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5206) := by
    have ha : (tripleCharges (sourceA2139 + difference 1 4) (sourceB2139 + difference 4 1) sourceC2139) = raw29570 := by
      apply Matrix.ext; unfold tripleCharges sourceA2139 sourceB2139 sourceC2139 difference raw29570; decide +kernel
    rw [ha]
    exact (canonical29570 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2139 + difference 1 5) (sourceB2139 + difference 5 1) sourceC2139) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5207) := by
    have ha : (tripleCharges (sourceA2139 + difference 1 5) (sourceB2139 + difference 5 1) sourceC2139) = raw29571 := by
      apply Matrix.ext; unfold tripleCharges sourceA2139 sourceB2139 sourceC2139 difference raw29571; decide +kernel
    rw [ha]
    exact (canonical29571 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2139 + difference 2 0) (sourceB2139 + difference 0 2) sourceC2139) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4810) := by
    have ha : (tripleCharges (sourceA2139 + difference 2 0) (sourceB2139 + difference 0 2) sourceC2139) = raw29572 := by
      apply Matrix.ext; unfold tripleCharges sourceA2139 sourceB2139 sourceC2139 difference raw29572; decide +kernel
    rw [ha]
    exact (canonical29572 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2139 + difference 2 1) (sourceB2139 + difference 1 2) sourceC2139) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5080) := by
    have ha : (tripleCharges (sourceA2139 + difference 2 1) (sourceB2139 + difference 1 2) sourceC2139) = raw29573 := by
      apply Matrix.ext; unfold tripleCharges sourceA2139 sourceB2139 sourceC2139 difference raw29573; decide +kernel
    rw [ha]
    exact (canonical29573 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2139 + difference 2 3) (sourceB2139 + difference 3 2) sourceC2139) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5129) := by
    have ha : (tripleCharges (sourceA2139 + difference 2 3) (sourceB2139 + difference 3 2) sourceC2139) = raw29574 := by
      apply Matrix.ext; unfold tripleCharges sourceA2139 sourceB2139 sourceC2139 difference raw29574; decide +kernel
    rw [ha]
    exact (canonical29574 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2139 + difference 2 4) (sourceB2139 + difference 4 2) sourceC2139) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5151) := by
    have ha : (tripleCharges (sourceA2139 + difference 2 4) (sourceB2139 + difference 4 2) sourceC2139) = raw29575 := by
      apply Matrix.ext; unfold tripleCharges sourceA2139 sourceB2139 sourceC2139 difference raw29575; decide +kernel
    rw [ha]
    exact (canonical29575 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2139 + difference 2 5) (sourceB2139 + difference 5 2) sourceC2139) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5152) := by
    have ha : (tripleCharges (sourceA2139 + difference 2 5) (sourceB2139 + difference 5 2) sourceC2139) = raw29576 := by
      apply Matrix.ext; unfold tripleCharges sourceA2139 sourceB2139 sourceC2139 difference raw29576; decide +kernel
    rw [ha]
    exact (canonical29576 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2139 + difference 3 0) (sourceB2139 + difference 0 3) sourceC2139) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4810) := by
    have ha : (tripleCharges (sourceA2139 + difference 3 0) (sourceB2139 + difference 0 3) sourceC2139) = raw29577 := by
      apply Matrix.ext; unfold tripleCharges sourceA2139 sourceB2139 sourceC2139 difference raw29577; decide +kernel
    rw [ha]
    exact (canonical29577 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2139 + difference 3 1) (sourceB2139 + difference 1 3) sourceC2139) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5080) := by
    have ha : (tripleCharges (sourceA2139 + difference 3 1) (sourceB2139 + difference 1 3) sourceC2139) = raw29578 := by
      apply Matrix.ext; unfold tripleCharges sourceA2139 sourceB2139 sourceC2139 difference raw29578; decide +kernel
    rw [ha]
    exact (canonical29578 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2139 + difference 3 2) (sourceB2139 + difference 2 3) sourceC2139) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5129) := by
    have ha : (tripleCharges (sourceA2139 + difference 3 2) (sourceB2139 + difference 2 3) sourceC2139) = raw29579 := by
      apply Matrix.ext; unfold tripleCharges sourceA2139 sourceB2139 sourceC2139 difference raw29579; decide +kernel
    rw [ha]
    exact (canonical29579 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2139 + difference 3 4) (sourceB2139 + difference 4 3) sourceC2139) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5151) := by
    have ha : (tripleCharges (sourceA2139 + difference 3 4) (sourceB2139 + difference 4 3) sourceC2139) = raw29580 := by
      apply Matrix.ext; unfold tripleCharges sourceA2139 sourceB2139 sourceC2139 difference raw29580; decide +kernel
    rw [ha]
    exact (canonical29580 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2139 + difference 3 5) (sourceB2139 + difference 5 3) sourceC2139) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5152) := by
    have ha : (tripleCharges (sourceA2139 + difference 3 5) (sourceB2139 + difference 5 3) sourceC2139) = raw29581 := by
      apply Matrix.ext; unfold tripleCharges sourceA2139 sourceB2139 sourceC2139 difference raw29581; decide +kernel
    rw [ha]
    exact (canonical29581 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2139 + difference 4 0) (sourceB2139 + difference 0 4) sourceC2139) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4846) := by
    have ha : (tripleCharges (sourceA2139 + difference 4 0) (sourceB2139 + difference 0 4) sourceC2139) = raw29582 := by
      apply Matrix.ext; unfold tripleCharges sourceA2139 sourceB2139 sourceC2139 difference raw29582; decide +kernel
    rw [ha]
    exact (canonical29582 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2139 + difference 4 1) (sourceB2139 + difference 1 4) sourceC2139) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5111) := by
    have ha : (tripleCharges (sourceA2139 + difference 4 1) (sourceB2139 + difference 1 4) sourceC2139) = raw29583 := by
      apply Matrix.ext; unfold tripleCharges sourceA2139 sourceB2139 sourceC2139 difference raw29583; decide +kernel
    rw [ha]
    exact (canonical29583 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2139 + difference 4 2) (sourceB2139 + difference 2 4) sourceC2139) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA2139 + difference 4 2) (sourceB2139 + difference 2 4) sourceC2139) = raw29584 := by
      apply Matrix.ext; unfold tripleCharges sourceA2139 sourceB2139 sourceC2139 difference raw29584; decide +kernel
    rw [ha]
    exact (canonical29584 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2139 + difference 4 3) (sourceB2139 + difference 3 4) sourceC2139) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA2139 + difference 4 3) (sourceB2139 + difference 3 4) sourceC2139) = raw29585 := by
      apply Matrix.ext; unfold tripleCharges sourceA2139 sourceB2139 sourceC2139 difference raw29585; decide +kernel
    rw [ha]
    exact (canonical29585 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2139 + difference 4 5) (sourceB2139 + difference 5 4) sourceC2139) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5177) := by
    have ha : (tripleCharges (sourceA2139 + difference 4 5) (sourceB2139 + difference 5 4) sourceC2139) = raw29586 := by
      apply Matrix.ext; unfold tripleCharges sourceA2139 sourceB2139 sourceC2139 difference raw29586; decide +kernel
    rw [ha]
    exact (canonical29586 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2139 + difference 5 0) (sourceB2139 + difference 0 5) sourceC2139) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4845) := by
    have ha : (tripleCharges (sourceA2139 + difference 5 0) (sourceB2139 + difference 0 5) sourceC2139) = raw29587 := by
      apply Matrix.ext; unfold tripleCharges sourceA2139 sourceB2139 sourceC2139 difference raw29587; decide +kernel
    rw [ha]
    exact (canonical29587 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2139 + difference 5 1) (sourceB2139 + difference 1 5) sourceC2139) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5110) := by
    have ha : (tripleCharges (sourceA2139 + difference 5 1) (sourceB2139 + difference 1 5) sourceC2139) = raw29588 := by
      apply Matrix.ext; unfold tripleCharges sourceA2139 sourceB2139 sourceC2139 difference raw29588; decide +kernel
    rw [ha]
    exact (canonical29588 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2139 + difference 5 2) (sourceB2139 + difference 2 5) sourceC2139) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5140) := by
    have ha : (tripleCharges (sourceA2139 + difference 5 2) (sourceB2139 + difference 2 5) sourceC2139) = raw29589 := by
      apply Matrix.ext; unfold tripleCharges sourceA2139 sourceB2139 sourceC2139 difference raw29589; decide +kernel
    rw [ha]
    exact (canonical29589 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2139 + difference 5 3) (sourceB2139 + difference 3 5) sourceC2139) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5140) := by
    have ha : (tripleCharges (sourceA2139 + difference 5 3) (sourceB2139 + difference 3 5) sourceC2139) = raw29590 := by
      apply Matrix.ext; unfold tripleCharges sourceA2139 sourceB2139 sourceC2139 difference raw29590; decide +kernel
    rw [ha]
    exact (canonical29590 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2139 + difference 5 4) (sourceB2139 + difference 4 5) sourceC2139) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5175) := by
    have ha : (tripleCharges (sourceA2139 + difference 5 4) (sourceB2139 + difference 4 5) sourceC2139) = raw29591 := by
      apply Matrix.ext; unfold tripleCharges sourceA2139 sourceB2139 sourceC2139 difference raw29591; decide +kernel
    rw [ha]
    exact (canonical29591 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2139 sourceB2139 sourceC2139
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2139, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2140 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceB2140 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC2140 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceForm2140 : Integer.Sparse Master := [(Sum.inr 2488, 2), (Sum.inr 2522, 1), (Sum.inr 2523, 1), (Sum.inr 2604, 1), (Sum.inr 2867, 2), (Sum.inr 2888, 1), (Sum.inr 2889, 1), (Sum.inr 2916, 2), (Sum.inr 2930, 2), (Sum.inr 2931, 2), (Sum.inr 2942, 2), (Sum.inr 2943, 2), (Sum.inr 2967, 1), (Sum.inr 2969, 1), (Sum.inr 2990, 2), (Sum.inr 3005, 1), (Sum.inr 3006, 1), (Sum.inr 3095, 1), (Sum.inr 3187, 1), (Sum.inr 3206, 2), (Sum.inr 3216, 1)]

theorem sourceEq2140 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2140 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2140 + difference 0 1) (sourceB2140 + difference 1 0) sourceC2140) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2604) := by
    have ha : (tripleCharges (sourceA2140 + difference 0 1) (sourceB2140 + difference 1 0) sourceC2140) = raw29592 := by
      apply Matrix.ext; unfold tripleCharges sourceA2140 sourceB2140 sourceC2140 difference raw29592; decide +kernel
    rw [ha]
    exact (canonical29592 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2140 + difference 0 2) (sourceB2140 + difference 2 0) sourceC2140) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2488) := by
    have ha : (tripleCharges (sourceA2140 + difference 0 2) (sourceB2140 + difference 2 0) sourceC2140) = raw29593 := by
      apply Matrix.ext; unfold tripleCharges sourceA2140 sourceB2140 sourceC2140 difference raw29593; decide +kernel
    rw [ha]
    exact (canonical29593 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2140 + difference 0 3) (sourceB2140 + difference 3 0) sourceC2140) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2488) := by
    have ha : (tripleCharges (sourceA2140 + difference 0 3) (sourceB2140 + difference 3 0) sourceC2140) = raw29594 := by
      apply Matrix.ext; unfold tripleCharges sourceA2140 sourceB2140 sourceC2140 difference raw29594; decide +kernel
    rw [ha]
    exact (canonical29594 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2140 + difference 0 4) (sourceB2140 + difference 4 0) sourceC2140) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2522) := by
    have ha : (tripleCharges (sourceA2140 + difference 0 4) (sourceB2140 + difference 4 0) sourceC2140) = raw29595 := by
      apply Matrix.ext; unfold tripleCharges sourceA2140 sourceB2140 sourceC2140 difference raw29595; decide +kernel
    rw [ha]
    exact (canonical29595 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2140 + difference 0 5) (sourceB2140 + difference 5 0) sourceC2140) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2523) := by
    have ha : (tripleCharges (sourceA2140 + difference 0 5) (sourceB2140 + difference 5 0) sourceC2140) = raw29596 := by
      apply Matrix.ext; unfold tripleCharges sourceA2140 sourceB2140 sourceC2140 difference raw29596; decide +kernel
    rw [ha]
    exact (canonical29596 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2140 + difference 1 0) (sourceB2140 + difference 0 1) sourceC2140) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3187) := by
    have ha : (tripleCharges (sourceA2140 + difference 1 0) (sourceB2140 + difference 0 1) sourceC2140) = raw29597 := by
      apply Matrix.ext; unfold tripleCharges sourceA2140 sourceB2140 sourceC2140 difference raw29597; decide +kernel
    rw [ha]
    exact (canonical29597 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2140 + difference 1 2) (sourceB2140 + difference 2 1) sourceC2140) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2867) := by
    have ha : (tripleCharges (sourceA2140 + difference 1 2) (sourceB2140 + difference 2 1) sourceC2140) = raw29598 := by
      apply Matrix.ext; unfold tripleCharges sourceA2140 sourceB2140 sourceC2140 difference raw29598; decide +kernel
    rw [ha]
    exact (canonical29598 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2140 + difference 1 3) (sourceB2140 + difference 3 1) sourceC2140) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2867) := by
    have ha : (tripleCharges (sourceA2140 + difference 1 3) (sourceB2140 + difference 3 1) sourceC2140) = raw29599 := by
      apply Matrix.ext; unfold tripleCharges sourceA2140 sourceB2140 sourceC2140 difference raw29599; decide +kernel
    rw [ha]
    exact (canonical29599 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2140 + difference 1 4) (sourceB2140 + difference 4 1) sourceC2140) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2888) := by
    have ha : (tripleCharges (sourceA2140 + difference 1 4) (sourceB2140 + difference 4 1) sourceC2140) = raw29600 := by
      apply Matrix.ext; unfold tripleCharges sourceA2140 sourceB2140 sourceC2140 difference raw29600; decide +kernel
    rw [ha]
    exact (canonical29600 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2140 + difference 1 5) (sourceB2140 + difference 5 1) sourceC2140) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2889) := by
    have ha : (tripleCharges (sourceA2140 + difference 1 5) (sourceB2140 + difference 5 1) sourceC2140) = raw29601 := by
      apply Matrix.ext; unfold tripleCharges sourceA2140 sourceB2140 sourceC2140 difference raw29601; decide +kernel
    rw [ha]
    exact (canonical29601 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2140 + difference 2 0) (sourceB2140 + difference 0 2) sourceC2140) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3206) := by
    have ha : (tripleCharges (sourceA2140 + difference 2 0) (sourceB2140 + difference 0 2) sourceC2140) = raw29602 := by
      apply Matrix.ext; unfold tripleCharges sourceA2140 sourceB2140 sourceC2140 difference raw29602; decide +kernel
    rw [ha]
    exact (canonical29602 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2140 + difference 2 1) (sourceB2140 + difference 1 2) sourceC2140) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2990) := by
    have ha : (tripleCharges (sourceA2140 + difference 2 1) (sourceB2140 + difference 1 2) sourceC2140) = raw29603 := by
      apply Matrix.ext; unfold tripleCharges sourceA2140 sourceB2140 sourceC2140 difference raw29603; decide +kernel
    rw [ha]
    exact (canonical29603 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2140 + difference 2 3) (sourceB2140 + difference 3 2) sourceC2140) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2916) := by
    have ha : (tripleCharges (sourceA2140 + difference 2 3) (sourceB2140 + difference 3 2) sourceC2140) = raw29604 := by
      apply Matrix.ext; unfold tripleCharges sourceA2140 sourceB2140 sourceC2140 difference raw29604; decide +kernel
    rw [ha]
    exact (canonical29604 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2140 + difference 2 4) (sourceB2140 + difference 4 2) sourceC2140) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2930) := by
    have ha : (tripleCharges (sourceA2140 + difference 2 4) (sourceB2140 + difference 4 2) sourceC2140) = raw29605 := by
      apply Matrix.ext; unfold tripleCharges sourceA2140 sourceB2140 sourceC2140 difference raw29605; decide +kernel
    rw [ha]
    exact (canonical29605 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2140 + difference 2 5) (sourceB2140 + difference 5 2) sourceC2140) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2931) := by
    have ha : (tripleCharges (sourceA2140 + difference 2 5) (sourceB2140 + difference 5 2) sourceC2140) = raw29606 := by
      apply Matrix.ext; unfold tripleCharges sourceA2140 sourceB2140 sourceC2140 difference raw29606; decide +kernel
    rw [ha]
    exact (canonical29606 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2140 + difference 3 0) (sourceB2140 + difference 0 3) sourceC2140) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3206) := by
    have ha : (tripleCharges (sourceA2140 + difference 3 0) (sourceB2140 + difference 0 3) sourceC2140) = raw29607 := by
      apply Matrix.ext; unfold tripleCharges sourceA2140 sourceB2140 sourceC2140 difference raw29607; decide +kernel
    rw [ha]
    exact (canonical29607 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2140 + difference 3 1) (sourceB2140 + difference 1 3) sourceC2140) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2990) := by
    have ha : (tripleCharges (sourceA2140 + difference 3 1) (sourceB2140 + difference 1 3) sourceC2140) = raw29608 := by
      apply Matrix.ext; unfold tripleCharges sourceA2140 sourceB2140 sourceC2140 difference raw29608; decide +kernel
    rw [ha]
    exact (canonical29608 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2140 + difference 3 2) (sourceB2140 + difference 2 3) sourceC2140) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2916) := by
    have ha : (tripleCharges (sourceA2140 + difference 3 2) (sourceB2140 + difference 2 3) sourceC2140) = raw29609 := by
      apply Matrix.ext; unfold tripleCharges sourceA2140 sourceB2140 sourceC2140 difference raw29609; decide +kernel
    rw [ha]
    exact (canonical29609 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2140 + difference 3 4) (sourceB2140 + difference 4 3) sourceC2140) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2930) := by
    have ha : (tripleCharges (sourceA2140 + difference 3 4) (sourceB2140 + difference 4 3) sourceC2140) = raw29610 := by
      apply Matrix.ext; unfold tripleCharges sourceA2140 sourceB2140 sourceC2140 difference raw29610; decide +kernel
    rw [ha]
    exact (canonical29610 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2140 + difference 3 5) (sourceB2140 + difference 5 3) sourceC2140) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2931) := by
    have ha : (tripleCharges (sourceA2140 + difference 3 5) (sourceB2140 + difference 5 3) sourceC2140) = raw29611 := by
      apply Matrix.ext; unfold tripleCharges sourceA2140 sourceB2140 sourceC2140 difference raw29611; decide +kernel
    rw [ha]
    exact (canonical29611 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2140 + difference 4 0) (sourceB2140 + difference 0 4) sourceC2140) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3216) := by
    have ha : (tripleCharges (sourceA2140 + difference 4 0) (sourceB2140 + difference 0 4) sourceC2140) = raw29612 := by
      apply Matrix.ext; unfold tripleCharges sourceA2140 sourceB2140 sourceC2140 difference raw29612; decide +kernel
    rw [ha]
    exact (canonical29612 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2140 + difference 4 1) (sourceB2140 + difference 1 4) sourceC2140) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3006) := by
    have ha : (tripleCharges (sourceA2140 + difference 4 1) (sourceB2140 + difference 1 4) sourceC2140) = raw29613 := by
      apply Matrix.ext; unfold tripleCharges sourceA2140 sourceB2140 sourceC2140 difference raw29613; decide +kernel
    rw [ha]
    exact (canonical29613 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2140 + difference 4 2) (sourceB2140 + difference 2 4) sourceC2140) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2943) := by
    have ha : (tripleCharges (sourceA2140 + difference 4 2) (sourceB2140 + difference 2 4) sourceC2140) = raw29614 := by
      apply Matrix.ext; unfold tripleCharges sourceA2140 sourceB2140 sourceC2140 difference raw29614; decide +kernel
    rw [ha]
    exact (canonical29614 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2140 + difference 4 3) (sourceB2140 + difference 3 4) sourceC2140) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2943) := by
    have ha : (tripleCharges (sourceA2140 + difference 4 3) (sourceB2140 + difference 3 4) sourceC2140) = raw29615 := by
      apply Matrix.ext; unfold tripleCharges sourceA2140 sourceB2140 sourceC2140 difference raw29615; decide +kernel
    rw [ha]
    exact (canonical29615 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2140 + difference 4 5) (sourceB2140 + difference 5 4) sourceC2140) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2969) := by
    have ha : (tripleCharges (sourceA2140 + difference 4 5) (sourceB2140 + difference 5 4) sourceC2140) = raw29616 := by
      apply Matrix.ext; unfold tripleCharges sourceA2140 sourceB2140 sourceC2140 difference raw29616; decide +kernel
    rw [ha]
    exact (canonical29616 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2140 + difference 5 0) (sourceB2140 + difference 0 5) sourceC2140) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3095) := by
    have ha : (tripleCharges (sourceA2140 + difference 5 0) (sourceB2140 + difference 0 5) sourceC2140) = raw29617 := by
      apply Matrix.ext; unfold tripleCharges sourceA2140 sourceB2140 sourceC2140 difference raw29617; decide +kernel
    rw [ha]
    exact (canonical29617 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2140 + difference 5 1) (sourceB2140 + difference 1 5) sourceC2140) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3005) := by
    have ha : (tripleCharges (sourceA2140 + difference 5 1) (sourceB2140 + difference 1 5) sourceC2140) = raw29618 := by
      apply Matrix.ext; unfold tripleCharges sourceA2140 sourceB2140 sourceC2140 difference raw29618; decide +kernel
    rw [ha]
    exact (canonical29618 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2140 + difference 5 2) (sourceB2140 + difference 2 5) sourceC2140) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2942) := by
    have ha : (tripleCharges (sourceA2140 + difference 5 2) (sourceB2140 + difference 2 5) sourceC2140) = raw29619 := by
      apply Matrix.ext; unfold tripleCharges sourceA2140 sourceB2140 sourceC2140 difference raw29619; decide +kernel
    rw [ha]
    exact (canonical29619 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2140 + difference 5 3) (sourceB2140 + difference 3 5) sourceC2140) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2942) := by
    have ha : (tripleCharges (sourceA2140 + difference 5 3) (sourceB2140 + difference 3 5) sourceC2140) = raw29620 := by
      apply Matrix.ext; unfold tripleCharges sourceA2140 sourceB2140 sourceC2140 difference raw29620; decide +kernel
    rw [ha]
    exact (canonical29620 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2140 + difference 5 4) (sourceB2140 + difference 4 5) sourceC2140) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2967) := by
    have ha : (tripleCharges (sourceA2140 + difference 5 4) (sourceB2140 + difference 4 5) sourceC2140) = raw29621 := by
      apply Matrix.ext; unfold tripleCharges sourceA2140 sourceB2140 sourceC2140 difference raw29621; decide +kernel
    rw [ha]
    exact (canonical29621 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2140 sourceB2140 sourceC2140
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2140, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2141 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2141 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC2141 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceForm2141 : Integer.Sparse Master := [(Sum.inr 4554, 2), (Sum.inr 4558, 2), (Sum.inr 4628, 1), (Sum.inr 4948, 4), (Sum.inr 4953, 2), (Sum.inr 4974, 2), (Sum.inr 5115, 2), (Sum.inr 5169, 4), (Sum.inr 5174, 2), (Sum.inr 5177, 2), (Sum.inr 5309, 2), (Sum.inr 5390, 1), (Sum.inr 5418, 2), (Sum.inr 5442, 2)]

theorem sourceEq2141 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2141 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2141 + difference 0 1) (sourceB2141 + difference 1 0) sourceC2141) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5390) := by
    have ha : (tripleCharges (sourceA2141 + difference 0 1) (sourceB2141 + difference 1 0) sourceC2141) = raw29622 := by
      apply Matrix.ext; unfold tripleCharges sourceA2141 sourceB2141 sourceC2141 difference raw29622; decide +kernel
    rw [ha]
    exact (canonical29622 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2141 + difference 0 2) (sourceB2141 + difference 2 0) sourceC2141) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5418) := by
    have ha : (tripleCharges (sourceA2141 + difference 0 2) (sourceB2141 + difference 2 0) sourceC2141) = raw29623 := by
      apply Matrix.ext; unfold tripleCharges sourceA2141 sourceB2141 sourceC2141 difference raw29623; decide +kernel
    rw [ha]
    exact (canonical29623 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2141 + difference 0 3) (sourceB2141 + difference 3 0) sourceC2141) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5418) := by
    have ha : (tripleCharges (sourceA2141 + difference 0 3) (sourceB2141 + difference 3 0) sourceC2141) = raw29624 := by
      apply Matrix.ext; unfold tripleCharges sourceA2141 sourceB2141 sourceC2141 difference raw29624; decide +kernel
    rw [ha]
    exact (canonical29624 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2141 + difference 0 4) (sourceB2141 + difference 4 0) sourceC2141) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5442) := by
    have ha : (tripleCharges (sourceA2141 + difference 0 4) (sourceB2141 + difference 4 0) sourceC2141) = raw10194 := by
      apply Matrix.ext; unfold tripleCharges sourceA2141 sourceB2141 sourceC2141 difference raw10194; decide +kernel
    rw [ha]
    exact (canonical10194 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2141 + difference 0 5) (sourceB2141 + difference 5 0) sourceC2141) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5442) := by
    have ha : (tripleCharges (sourceA2141 + difference 0 5) (sourceB2141 + difference 5 0) sourceC2141) = raw29625 := by
      apply Matrix.ext; unfold tripleCharges sourceA2141 sourceB2141 sourceC2141 difference raw29625; decide +kernel
    rw [ha]
    exact (canonical29625 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2141 + difference 1 0) (sourceB2141 + difference 0 1) sourceC2141) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4628) := by
    have ha : (tripleCharges (sourceA2141 + difference 1 0) (sourceB2141 + difference 0 1) sourceC2141) = raw10210 := by
      apply Matrix.ext; unfold tripleCharges sourceA2141 sourceB2141 sourceC2141 difference raw10210; decide +kernel
    rw [ha]
    exact (canonical10210 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2141 + difference 1 2) (sourceB2141 + difference 2 1) sourceC2141) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5177) := by
    have ha : (tripleCharges (sourceA2141 + difference 1 2) (sourceB2141 + difference 2 1) sourceC2141) = raw10212 := by
      apply Matrix.ext; unfold tripleCharges sourceA2141 sourceB2141 sourceC2141 difference raw10212; decide +kernel
    rw [ha]
    exact (canonical10212 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2141 + difference 1 3) (sourceB2141 + difference 3 1) sourceC2141) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5177) := by
    have ha : (tripleCharges (sourceA2141 + difference 1 3) (sourceB2141 + difference 3 1) sourceC2141) = raw10213 := by
      apply Matrix.ext; unfold tripleCharges sourceA2141 sourceB2141 sourceC2141 difference raw10213; decide +kernel
    rw [ha]
    exact (canonical10213 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2141 + difference 1 4) (sourceB2141 + difference 4 1) sourceC2141) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5309) := by
    have ha : (tripleCharges (sourceA2141 + difference 1 4) (sourceB2141 + difference 4 1) sourceC2141) = raw4306 := by
      apply Matrix.ext; unfold tripleCharges sourceA2141 sourceB2141 sourceC2141 difference raw4306; decide +kernel
    rw [ha]
    exact (canonical4306 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2141 + difference 1 5) (sourceB2141 + difference 5 1) sourceC2141) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5309) := by
    have ha : (tripleCharges (sourceA2141 + difference 1 5) (sourceB2141 + difference 5 1) sourceC2141) = raw10214 := by
      apply Matrix.ext; unfold tripleCharges sourceA2141 sourceB2141 sourceC2141 difference raw10214; decide +kernel
    rw [ha]
    exact (canonical10214 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2141 + difference 2 0) (sourceB2141 + difference 0 2) sourceC2141) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4554) := by
    have ha : (tripleCharges (sourceA2141 + difference 2 0) (sourceB2141 + difference 0 2) sourceC2141) = raw22574 := by
      apply Matrix.ext; unfold tripleCharges sourceA2141 sourceB2141 sourceC2141 difference raw22574; decide +kernel
    rw [ha]
    exact (canonical22574 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2141 + difference 2 1) (sourceB2141 + difference 1 2) sourceC2141) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4974) := by
    have ha : (tripleCharges (sourceA2141 + difference 2 1) (sourceB2141 + difference 1 2) sourceC2141) = raw29626 := by
      apply Matrix.ext; unfold tripleCharges sourceA2141 sourceB2141 sourceC2141 difference raw29626; decide +kernel
    rw [ha]
    exact (canonical29626 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2141 + difference 2 3) (sourceB2141 + difference 3 2) sourceC2141) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5115) := by
    have ha : (tripleCharges (sourceA2141 + difference 2 3) (sourceB2141 + difference 3 2) sourceC2141) = raw29627 := by
      apply Matrix.ext; unfold tripleCharges sourceA2141 sourceB2141 sourceC2141 difference raw29627; decide +kernel
    rw [ha]
    exact (canonical29627 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2141 + difference 2 4) (sourceB2141 + difference 4 2) sourceC2141) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA2141 + difference 2 4) (sourceB2141 + difference 4 2) sourceC2141) = raw10203 := by
      apply Matrix.ext; unfold tripleCharges sourceA2141 sourceB2141 sourceC2141 difference raw10203; decide +kernel
    rw [ha]
    exact (canonical10203 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2141 + difference 2 5) (sourceB2141 + difference 5 2) sourceC2141) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA2141 + difference 2 5) (sourceB2141 + difference 5 2) sourceC2141) = raw29628 := by
      apply Matrix.ext; unfold tripleCharges sourceA2141 sourceB2141 sourceC2141 difference raw29628; decide +kernel
    rw [ha]
    exact (canonical29628 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2141 + difference 3 0) (sourceB2141 + difference 0 3) sourceC2141) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4554) := by
    have ha : (tripleCharges (sourceA2141 + difference 3 0) (sourceB2141 + difference 0 3) sourceC2141) = raw22578 := by
      apply Matrix.ext; unfold tripleCharges sourceA2141 sourceB2141 sourceC2141 difference raw22578; decide +kernel
    rw [ha]
    exact (canonical22578 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2141 + difference 3 1) (sourceB2141 + difference 1 3) sourceC2141) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4974) := by
    have ha : (tripleCharges (sourceA2141 + difference 3 1) (sourceB2141 + difference 1 3) sourceC2141) = raw29629 := by
      apply Matrix.ext; unfold tripleCharges sourceA2141 sourceB2141 sourceC2141 difference raw29629; decide +kernel
    rw [ha]
    exact (canonical29629 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2141 + difference 3 2) (sourceB2141 + difference 2 3) sourceC2141) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5115) := by
    have ha : (tripleCharges (sourceA2141 + difference 3 2) (sourceB2141 + difference 2 3) sourceC2141) = raw29630 := by
      apply Matrix.ext; unfold tripleCharges sourceA2141 sourceB2141 sourceC2141 difference raw29630; decide +kernel
    rw [ha]
    exact (canonical29630 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2141 + difference 3 4) (sourceB2141 + difference 4 3) sourceC2141) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA2141 + difference 3 4) (sourceB2141 + difference 4 3) sourceC2141) = raw10207 := by
      apply Matrix.ext; unfold tripleCharges sourceA2141 sourceB2141 sourceC2141 difference raw10207; decide +kernel
    rw [ha]
    exact (canonical10207 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2141 + difference 3 5) (sourceB2141 + difference 5 3) sourceC2141) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA2141 + difference 3 5) (sourceB2141 + difference 5 3) sourceC2141) = raw29631 := by
      apply Matrix.ext; unfold tripleCharges sourceA2141 sourceB2141 sourceC2141 difference raw29631; decide +kernel
    rw [ha]
    exact (canonical29631 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2141 + difference 4 0) (sourceB2141 + difference 0 4) sourceC2141) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4558) := by
    have ha : (tripleCharges (sourceA2141 + difference 4 0) (sourceB2141 + difference 0 4) sourceC2141) = raw22582 := by
      apply Matrix.ext; unfold tripleCharges sourceA2141 sourceB2141 sourceC2141 difference raw22582; decide +kernel
    rw [ha]
    exact (canonical22582 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2141 + difference 4 1) (sourceB2141 + difference 1 4) sourceC2141) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4953) := by
    have ha : (tripleCharges (sourceA2141 + difference 4 1) (sourceB2141 + difference 1 4) sourceC2141) = raw29632 := by
      apply Matrix.ext; unfold tripleCharges sourceA2141 sourceB2141 sourceC2141 difference raw29632; decide +kernel
    rw [ha]
    exact (canonical29632 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2141 + difference 4 2) (sourceB2141 + difference 2 4) sourceC2141) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4948) := by
    have ha : (tripleCharges (sourceA2141 + difference 4 2) (sourceB2141 + difference 2 4) sourceC2141) = raw29633 := by
      apply Matrix.ext; unfold tripleCharges sourceA2141 sourceB2141 sourceC2141 difference raw29633; decide +kernel
    rw [ha]
    exact (canonical29633 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2141 + difference 4 3) (sourceB2141 + difference 3 4) sourceC2141) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4948) := by
    have ha : (tripleCharges (sourceA2141 + difference 4 3) (sourceB2141 + difference 3 4) sourceC2141) = raw29634 := by
      apply Matrix.ext; unfold tripleCharges sourceA2141 sourceB2141 sourceC2141 difference raw29634; decide +kernel
    rw [ha]
    exact (canonical29634 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2141 + difference 4 5) (sourceB2141 + difference 5 4) sourceC2141) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5174) := by
    have ha : (tripleCharges (sourceA2141 + difference 4 5) (sourceB2141 + difference 5 4) sourceC2141) = raw29635 := by
      apply Matrix.ext; unfold tripleCharges sourceA2141 sourceB2141 sourceC2141 difference raw29635; decide +kernel
    rw [ha]
    exact (canonical29635 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2141 + difference 5 0) (sourceB2141 + difference 0 5) sourceC2141) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4558) := by
    have ha : (tripleCharges (sourceA2141 + difference 5 0) (sourceB2141 + difference 0 5) sourceC2141) = raw20394 := by
      apply Matrix.ext; unfold tripleCharges sourceA2141 sourceB2141 sourceC2141 difference raw20394; decide +kernel
    rw [ha]
    exact (canonical20394 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2141 + difference 5 1) (sourceB2141 + difference 1 5) sourceC2141) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4953) := by
    have ha : (tripleCharges (sourceA2141 + difference 5 1) (sourceB2141 + difference 1 5) sourceC2141) = raw27617 := by
      apply Matrix.ext; unfold tripleCharges sourceA2141 sourceB2141 sourceC2141 difference raw27617; decide +kernel
    rw [ha]
    exact (canonical27617 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2141 + difference 5 2) (sourceB2141 + difference 2 5) sourceC2141) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4948) := by
    have ha : (tripleCharges (sourceA2141 + difference 5 2) (sourceB2141 + difference 2 5) sourceC2141) = raw27618 := by
      apply Matrix.ext; unfold tripleCharges sourceA2141 sourceB2141 sourceC2141 difference raw27618; decide +kernel
    rw [ha]
    exact (canonical27618 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2141 + difference 5 3) (sourceB2141 + difference 3 5) sourceC2141) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4948) := by
    have ha : (tripleCharges (sourceA2141 + difference 5 3) (sourceB2141 + difference 3 5) sourceC2141) = raw27619 := by
      apply Matrix.ext; unfold tripleCharges sourceA2141 sourceB2141 sourceC2141 difference raw27619; decide +kernel
    rw [ha]
    exact (canonical27619 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2141 + difference 5 4) (sourceB2141 + difference 4 5) sourceC2141) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5174) := by
    have ha : (tripleCharges (sourceA2141 + difference 5 4) (sourceB2141 + difference 4 5) sourceC2141) = raw4303 := by
      apply Matrix.ext; unfold tripleCharges sourceA2141 sourceB2141 sourceC2141 difference raw4303; decide +kernel
    rw [ha]
    exact (canonical4303 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2141 sourceB2141 sourceC2141
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2141, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2142 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2142 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC2142 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceForm2142 : Integer.Sparse Master := [(Sum.inr 1139, 2), (Sum.inr 1144, 2), (Sum.inr 1312, 1), (Sum.inr 2339, 4), (Sum.inr 2345, 2), (Sum.inr 2601, 2), (Sum.inr 2818, 2), (Sum.inr 2897, 2), (Sum.inr 2960, 4), (Sum.inr 2969, 2), (Sum.inr 3123, 2), (Sum.inr 3741, 1), (Sum.inr 3933, 2), (Sum.inr 4001, 2)]

theorem sourceEq2142 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2142 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2142 + difference 0 1) (sourceB2142 + difference 1 0) sourceC2142) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3741) := by
    have ha : (tripleCharges (sourceA2142 + difference 0 1) (sourceB2142 + difference 1 0) sourceC2142) = raw29636 := by
      apply Matrix.ext; unfold tripleCharges sourceA2142 sourceB2142 sourceC2142 difference raw29636; decide +kernel
    rw [ha]
    exact (canonical29636 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2142 + difference 0 2) (sourceB2142 + difference 2 0) sourceC2142) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3933) := by
    have ha : (tripleCharges (sourceA2142 + difference 0 2) (sourceB2142 + difference 2 0) sourceC2142) = raw29637 := by
      apply Matrix.ext; unfold tripleCharges sourceA2142 sourceB2142 sourceC2142 difference raw29637; decide +kernel
    rw [ha]
    exact (canonical29637 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2142 + difference 0 3) (sourceB2142 + difference 3 0) sourceC2142) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3933) := by
    have ha : (tripleCharges (sourceA2142 + difference 0 3) (sourceB2142 + difference 3 0) sourceC2142) = raw29638 := by
      apply Matrix.ext; unfold tripleCharges sourceA2142 sourceB2142 sourceC2142 difference raw29638; decide +kernel
    rw [ha]
    exact (canonical29638 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2142 + difference 0 4) (sourceB2142 + difference 4 0) sourceC2142) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4001) := by
    have ha : (tripleCharges (sourceA2142 + difference 0 4) (sourceB2142 + difference 4 0) sourceC2142) = raw27626 := by
      apply Matrix.ext; unfold tripleCharges sourceA2142 sourceB2142 sourceC2142 difference raw27626; decide +kernel
    rw [ha]
    exact (canonical27626 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2142 + difference 0 5) (sourceB2142 + difference 5 0) sourceC2142) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4001) := by
    have ha : (tripleCharges (sourceA2142 + difference 0 5) (sourceB2142 + difference 5 0) sourceC2142) = raw29639 := by
      apply Matrix.ext; unfold tripleCharges sourceA2142 sourceB2142 sourceC2142 difference raw29639; decide +kernel
    rw [ha]
    exact (canonical29639 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2142 + difference 1 0) (sourceB2142 + difference 0 1) sourceC2142) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1312) := by
    have ha : (tripleCharges (sourceA2142 + difference 1 0) (sourceB2142 + difference 0 1) sourceC2142) = raw20413 := by
      apply Matrix.ext; unfold tripleCharges sourceA2142 sourceB2142 sourceC2142 difference raw20413; decide +kernel
    rw [ha]
    exact (canonical20413 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2142 + difference 1 2) (sourceB2142 + difference 2 1) sourceC2142) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2969) := by
    have ha : (tripleCharges (sourceA2142 + difference 1 2) (sourceB2142 + difference 2 1) sourceC2142) = raw22587 := by
      apply Matrix.ext; unfold tripleCharges sourceA2142 sourceB2142 sourceC2142 difference raw22587; decide +kernel
    rw [ha]
    exact (canonical22587 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2142 + difference 1 3) (sourceB2142 + difference 3 1) sourceC2142) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2969) := by
    have ha : (tripleCharges (sourceA2142 + difference 1 3) (sourceB2142 + difference 3 1) sourceC2142) = raw22588 := by
      apply Matrix.ext; unfold tripleCharges sourceA2142 sourceB2142 sourceC2142 difference raw22588; decide +kernel
    rw [ha]
    exact (canonical22588 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2142 + difference 1 4) (sourceB2142 + difference 4 1) sourceC2142) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3123) := by
    have ha : (tripleCharges (sourceA2142 + difference 1 4) (sourceB2142 + difference 4 1) sourceC2142) = raw4336 := by
      apply Matrix.ext; unfold tripleCharges sourceA2142 sourceB2142 sourceC2142 difference raw4336; decide +kernel
    rw [ha]
    exact (canonical4336 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2142 + difference 1 5) (sourceB2142 + difference 5 1) sourceC2142) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3123) := by
    have ha : (tripleCharges (sourceA2142 + difference 1 5) (sourceB2142 + difference 5 1) sourceC2142) = raw22589 := by
      apply Matrix.ext; unfold tripleCharges sourceA2142 sourceB2142 sourceC2142 difference raw22589; decide +kernel
    rw [ha]
    exact (canonical22589 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2142 + difference 2 0) (sourceB2142 + difference 0 2) sourceC2142) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1139) := by
    have ha : (tripleCharges (sourceA2142 + difference 2 0) (sourceB2142 + difference 0 2) sourceC2142) = raw22595 := by
      apply Matrix.ext; unfold tripleCharges sourceA2142 sourceB2142 sourceC2142 difference raw22595; decide +kernel
    rw [ha]
    exact (canonical22595 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2142 + difference 2 1) (sourceB2142 + difference 1 2) sourceC2142) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2818) := by
    have ha : (tripleCharges (sourceA2142 + difference 2 1) (sourceB2142 + difference 1 2) sourceC2142) = raw29640 := by
      apply Matrix.ext; unfold tripleCharges sourceA2142 sourceB2142 sourceC2142 difference raw29640; decide +kernel
    rw [ha]
    exact (canonical29640 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2142 + difference 2 3) (sourceB2142 + difference 3 2) sourceC2142) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2897) := by
    have ha : (tripleCharges (sourceA2142 + difference 2 3) (sourceB2142 + difference 3 2) sourceC2142) = raw29641 := by
      apply Matrix.ext; unfold tripleCharges sourceA2142 sourceB2142 sourceC2142 difference raw29641; decide +kernel
    rw [ha]
    exact (canonical29641 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2142 + difference 2 4) (sourceB2142 + difference 4 2) sourceC2142) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2960) := by
    have ha : (tripleCharges (sourceA2142 + difference 2 4) (sourceB2142 + difference 4 2) sourceC2142) = raw27629 := by
      apply Matrix.ext; unfold tripleCharges sourceA2142 sourceB2142 sourceC2142 difference raw27629; decide +kernel
    rw [ha]
    exact (canonical27629 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2142 + difference 2 5) (sourceB2142 + difference 5 2) sourceC2142) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2960) := by
    have ha : (tripleCharges (sourceA2142 + difference 2 5) (sourceB2142 + difference 5 2) sourceC2142) = raw29642 := by
      apply Matrix.ext; unfold tripleCharges sourceA2142 sourceB2142 sourceC2142 difference raw29642; decide +kernel
    rw [ha]
    exact (canonical29642 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2142 + difference 3 0) (sourceB2142 + difference 0 3) sourceC2142) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1139) := by
    have ha : (tripleCharges (sourceA2142 + difference 3 0) (sourceB2142 + difference 0 3) sourceC2142) = raw22599 := by
      apply Matrix.ext; unfold tripleCharges sourceA2142 sourceB2142 sourceC2142 difference raw22599; decide +kernel
    rw [ha]
    exact (canonical22599 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2142 + difference 3 1) (sourceB2142 + difference 1 3) sourceC2142) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2818) := by
    have ha : (tripleCharges (sourceA2142 + difference 3 1) (sourceB2142 + difference 1 3) sourceC2142) = raw29643 := by
      apply Matrix.ext; unfold tripleCharges sourceA2142 sourceB2142 sourceC2142 difference raw29643; decide +kernel
    rw [ha]
    exact (canonical29643 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2142 + difference 3 2) (sourceB2142 + difference 2 3) sourceC2142) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2897) := by
    have ha : (tripleCharges (sourceA2142 + difference 3 2) (sourceB2142 + difference 2 3) sourceC2142) = raw29644 := by
      apply Matrix.ext; unfold tripleCharges sourceA2142 sourceB2142 sourceC2142 difference raw29644; decide +kernel
    rw [ha]
    exact (canonical29644 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2142 + difference 3 4) (sourceB2142 + difference 4 3) sourceC2142) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2960) := by
    have ha : (tripleCharges (sourceA2142 + difference 3 4) (sourceB2142 + difference 4 3) sourceC2142) = raw24232 := by
      apply Matrix.ext; unfold tripleCharges sourceA2142 sourceB2142 sourceC2142 difference raw24232; decide +kernel
    rw [ha]
    exact (canonical24232 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2142 + difference 3 5) (sourceB2142 + difference 5 3) sourceC2142) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2960) := by
    have ha : (tripleCharges (sourceA2142 + difference 3 5) (sourceB2142 + difference 5 3) sourceC2142) = raw29645 := by
      apply Matrix.ext; unfold tripleCharges sourceA2142 sourceB2142 sourceC2142 difference raw29645; decide +kernel
    rw [ha]
    exact (canonical29645 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2142 + difference 4 0) (sourceB2142 + difference 0 4) sourceC2142) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1144) := by
    have ha : (tripleCharges (sourceA2142 + difference 4 0) (sourceB2142 + difference 0 4) sourceC2142) = raw22603 := by
      apply Matrix.ext; unfold tripleCharges sourceA2142 sourceB2142 sourceC2142 difference raw22603; decide +kernel
    rw [ha]
    exact (canonical22603 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2142 + difference 4 1) (sourceB2142 + difference 1 4) sourceC2142) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2345) := by
    have ha : (tripleCharges (sourceA2142 + difference 4 1) (sourceB2142 + difference 1 4) sourceC2142) = raw29646 := by
      apply Matrix.ext; unfold tripleCharges sourceA2142 sourceB2142 sourceC2142 difference raw29646; decide +kernel
    rw [ha]
    exact (canonical29646 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2142 + difference 4 2) (sourceB2142 + difference 2 4) sourceC2142) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2339) := by
    have ha : (tripleCharges (sourceA2142 + difference 4 2) (sourceB2142 + difference 2 4) sourceC2142) = raw29647 := by
      apply Matrix.ext; unfold tripleCharges sourceA2142 sourceB2142 sourceC2142 difference raw29647; decide +kernel
    rw [ha]
    exact (canonical29647 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2142 + difference 4 3) (sourceB2142 + difference 3 4) sourceC2142) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2339) := by
    have ha : (tripleCharges (sourceA2142 + difference 4 3) (sourceB2142 + difference 3 4) sourceC2142) = raw29648 := by
      apply Matrix.ext; unfold tripleCharges sourceA2142 sourceB2142 sourceC2142 difference raw29648; decide +kernel
    rw [ha]
    exact (canonical29648 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2142 + difference 4 5) (sourceB2142 + difference 5 4) sourceC2142) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2601) := by
    have ha : (tripleCharges (sourceA2142 + difference 4 5) (sourceB2142 + difference 5 4) sourceC2142) = raw29649 := by
      apply Matrix.ext; unfold tripleCharges sourceA2142 sourceB2142 sourceC2142 difference raw29649; decide +kernel
    rw [ha]
    exact (canonical29649 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2142 + difference 5 0) (sourceB2142 + difference 0 5) sourceC2142) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1144) := by
    have ha : (tripleCharges (sourceA2142 + difference 5 0) (sourceB2142 + difference 0 5) sourceC2142) = raw20410 := by
      apply Matrix.ext; unfold tripleCharges sourceA2142 sourceB2142 sourceC2142 difference raw20410; decide +kernel
    rw [ha]
    exact (canonical20410 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2142 + difference 5 1) (sourceB2142 + difference 1 5) sourceC2142) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2345) := by
    have ha : (tripleCharges (sourceA2142 + difference 5 1) (sourceB2142 + difference 1 5) sourceC2142) = raw27632 := by
      apply Matrix.ext; unfold tripleCharges sourceA2142 sourceB2142 sourceC2142 difference raw27632; decide +kernel
    rw [ha]
    exact (canonical27632 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2142 + difference 5 2) (sourceB2142 + difference 2 5) sourceC2142) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2339) := by
    have ha : (tripleCharges (sourceA2142 + difference 5 2) (sourceB2142 + difference 2 5) sourceC2142) = raw27633 := by
      apply Matrix.ext; unfold tripleCharges sourceA2142 sourceB2142 sourceC2142 difference raw27633; decide +kernel
    rw [ha]
    exact (canonical27633 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2142 + difference 5 3) (sourceB2142 + difference 3 5) sourceC2142) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2339) := by
    have ha : (tripleCharges (sourceA2142 + difference 5 3) (sourceB2142 + difference 3 5) sourceC2142) = raw27634 := by
      apply Matrix.ext; unfold tripleCharges sourceA2142 sourceB2142 sourceC2142 difference raw27634; decide +kernel
    rw [ha]
    exact (canonical27634 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2142 + difference 5 4) (sourceB2142 + difference 4 5) sourceC2142) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2601) := by
    have ha : (tripleCharges (sourceA2142 + difference 5 4) (sourceB2142 + difference 4 5) sourceC2142) = raw4333 := by
      apply Matrix.ext; unfold tripleCharges sourceA2142 sourceB2142 sourceC2142 difference raw4333; decide +kernel
    rw [ha]
    exact (canonical4333 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2142 sourceB2142 sourceC2142
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2142, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2143 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2143 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC2143 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceForm2143 : Integer.Sparse Master := [(Sum.inr 4355, 2), (Sum.inr 4360, 2), (Sum.inr 4467, 1), (Sum.inr 4943, 4), (Sum.inr 4950, 2), (Sum.inr 4952, 2), (Sum.inr 5039, 2), (Sum.inr 5081, 2), (Sum.inr 5169, 4), (Sum.inr 5171, 2), (Sum.inr 5293, 2), (Sum.inr 5465, 2), (Sum.inr 5466, 1), (Sum.inr 5487, 2)]

theorem sourceEq2143 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2143 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2143 + difference 0 1) (sourceB2143 + difference 1 0) sourceC2143) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5466) := by
    have ha : (tripleCharges (sourceA2143 + difference 0 1) (sourceB2143 + difference 1 0) sourceC2143) = raw17676 := by
      apply Matrix.ext; unfold tripleCharges sourceA2143 sourceB2143 sourceC2143 difference raw17676; decide +kernel
    rw [ha]
    exact (canonical17676 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2143 + difference 0 2) (sourceB2143 + difference 2 0) sourceC2143) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5465) := by
    have ha : (tripleCharges (sourceA2143 + difference 0 2) (sourceB2143 + difference 2 0) sourceC2143) = raw17677 := by
      apply Matrix.ext; unfold tripleCharges sourceA2143 sourceB2143 sourceC2143 difference raw17677; decide +kernel
    rw [ha]
    exact (canonical17677 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2143 + difference 0 3) (sourceB2143 + difference 3 0) sourceC2143) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5465) := by
    have ha : (tripleCharges (sourceA2143 + difference 0 3) (sourceB2143 + difference 3 0) sourceC2143) = raw17678 := by
      apply Matrix.ext; unfold tripleCharges sourceA2143 sourceB2143 sourceC2143 difference raw17678; decide +kernel
    rw [ha]
    exact (canonical17678 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2143 + difference 0 4) (sourceB2143 + difference 4 0) sourceC2143) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5487) := by
    have ha : (tripleCharges (sourceA2143 + difference 0 4) (sourceB2143 + difference 4 0) sourceC2143) = raw2772 := by
      apply Matrix.ext; unfold tripleCharges sourceA2143 sourceB2143 sourceC2143 difference raw2772; decide +kernel
    rw [ha]
    exact (canonical2772 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2143 + difference 0 5) (sourceB2143 + difference 5 0) sourceC2143) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5487) := by
    have ha : (tripleCharges (sourceA2143 + difference 0 5) (sourceB2143 + difference 5 0) sourceC2143) = raw17679 := by
      apply Matrix.ext; unfold tripleCharges sourceA2143 sourceB2143 sourceC2143 difference raw17679; decide +kernel
    rw [ha]
    exact (canonical17679 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2143 + difference 1 0) (sourceB2143 + difference 0 1) sourceC2143) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4467) := by
    have ha : (tripleCharges (sourceA2143 + difference 1 0) (sourceB2143 + difference 0 1) sourceC2143) = raw21494 := by
      apply Matrix.ext; unfold tripleCharges sourceA2143 sourceB2143 sourceC2143 difference raw21494; decide +kernel
    rw [ha]
    exact (canonical21494 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2143 + difference 1 2) (sourceB2143 + difference 2 1) sourceC2143) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5081) := by
    have ha : (tripleCharges (sourceA2143 + difference 1 2) (sourceB2143 + difference 2 1) sourceC2143) = raw23219 := by
      apply Matrix.ext; unfold tripleCharges sourceA2143 sourceB2143 sourceC2143 difference raw23219; decide +kernel
    rw [ha]
    exact (canonical23219 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2143 + difference 1 3) (sourceB2143 + difference 3 1) sourceC2143) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5081) := by
    have ha : (tripleCharges (sourceA2143 + difference 1 3) (sourceB2143 + difference 3 1) sourceC2143) = raw23220 := by
      apply Matrix.ext; unfold tripleCharges sourceA2143 sourceB2143 sourceC2143 difference raw23220; decide +kernel
    rw [ha]
    exact (canonical23220 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2143 + difference 1 4) (sourceB2143 + difference 4 1) sourceC2143) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA2143 + difference 1 4) (sourceB2143 + difference 4 1) sourceC2143) = raw2771 := by
      apply Matrix.ext; unfold tripleCharges sourceA2143 sourceB2143 sourceC2143 difference raw2771; decide +kernel
    rw [ha]
    exact (canonical2771 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2143 + difference 1 5) (sourceB2143 + difference 5 1) sourceC2143) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA2143 + difference 1 5) (sourceB2143 + difference 5 1) sourceC2143) = raw23221 := by
      apply Matrix.ext; unfold tripleCharges sourceA2143 sourceB2143 sourceC2143 difference raw23221; decide +kernel
    rw [ha]
    exact (canonical23221 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2143 + difference 2 0) (sourceB2143 + difference 0 2) sourceC2143) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4355) := by
    have ha : (tripleCharges (sourceA2143 + difference 2 0) (sourceB2143 + difference 0 2) sourceC2143) = raw23227 := by
      apply Matrix.ext; unfold tripleCharges sourceA2143 sourceB2143 sourceC2143 difference raw23227; decide +kernel
    rw [ha]
    exact (canonical23227 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2143 + difference 2 1) (sourceB2143 + difference 1 2) sourceC2143) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4950) := by
    have ha : (tripleCharges (sourceA2143 + difference 2 1) (sourceB2143 + difference 1 2) sourceC2143) = raw29650 := by
      apply Matrix.ext; unfold tripleCharges sourceA2143 sourceB2143 sourceC2143 difference raw29650; decide +kernel
    rw [ha]
    exact (canonical29650 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2143 + difference 2 3) (sourceB2143 + difference 3 2) sourceC2143) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5039) := by
    have ha : (tripleCharges (sourceA2143 + difference 2 3) (sourceB2143 + difference 3 2) sourceC2143) = raw29651 := by
      apply Matrix.ext; unfold tripleCharges sourceA2143 sourceB2143 sourceC2143 difference raw29651; decide +kernel
    rw [ha]
    exact (canonical29651 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2143 + difference 2 4) (sourceB2143 + difference 4 2) sourceC2143) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA2143 + difference 2 4) (sourceB2143 + difference 4 2) sourceC2143) = raw17667 := by
      apply Matrix.ext; unfold tripleCharges sourceA2143 sourceB2143 sourceC2143 difference raw17667; decide +kernel
    rw [ha]
    exact (canonical17667 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2143 + difference 2 5) (sourceB2143 + difference 5 2) sourceC2143) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA2143 + difference 2 5) (sourceB2143 + difference 5 2) sourceC2143) = raw29652 := by
      apply Matrix.ext; unfold tripleCharges sourceA2143 sourceB2143 sourceC2143 difference raw29652; decide +kernel
    rw [ha]
    exact (canonical29652 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2143 + difference 3 0) (sourceB2143 + difference 0 3) sourceC2143) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4355) := by
    have ha : (tripleCharges (sourceA2143 + difference 3 0) (sourceB2143 + difference 0 3) sourceC2143) = raw23231 := by
      apply Matrix.ext; unfold tripleCharges sourceA2143 sourceB2143 sourceC2143 difference raw23231; decide +kernel
    rw [ha]
    exact (canonical23231 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2143 + difference 3 1) (sourceB2143 + difference 1 3) sourceC2143) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4950) := by
    have ha : (tripleCharges (sourceA2143 + difference 3 1) (sourceB2143 + difference 1 3) sourceC2143) = raw29653 := by
      apply Matrix.ext; unfold tripleCharges sourceA2143 sourceB2143 sourceC2143 difference raw29653; decide +kernel
    rw [ha]
    exact (canonical29653 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2143 + difference 3 2) (sourceB2143 + difference 2 3) sourceC2143) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5039) := by
    have ha : (tripleCharges (sourceA2143 + difference 3 2) (sourceB2143 + difference 2 3) sourceC2143) = raw29654 := by
      apply Matrix.ext; unfold tripleCharges sourceA2143 sourceB2143 sourceC2143 difference raw29654; decide +kernel
    rw [ha]
    exact (canonical29654 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2143 + difference 3 4) (sourceB2143 + difference 4 3) sourceC2143) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA2143 + difference 3 4) (sourceB2143 + difference 4 3) sourceC2143) = raw17671 := by
      apply Matrix.ext; unfold tripleCharges sourceA2143 sourceB2143 sourceC2143 difference raw17671; decide +kernel
    rw [ha]
    exact (canonical17671 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2143 + difference 3 5) (sourceB2143 + difference 5 3) sourceC2143) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA2143 + difference 3 5) (sourceB2143 + difference 5 3) sourceC2143) = raw29655 := by
      apply Matrix.ext; unfold tripleCharges sourceA2143 sourceB2143 sourceC2143 difference raw29655; decide +kernel
    rw [ha]
    exact (canonical29655 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2143 + difference 4 0) (sourceB2143 + difference 0 4) sourceC2143) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4360) := by
    have ha : (tripleCharges (sourceA2143 + difference 4 0) (sourceB2143 + difference 0 4) sourceC2143) = raw23235 := by
      apply Matrix.ext; unfold tripleCharges sourceA2143 sourceB2143 sourceC2143 difference raw23235; decide +kernel
    rw [ha]
    exact (canonical23235 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2143 + difference 4 1) (sourceB2143 + difference 1 4) sourceC2143) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4952) := by
    have ha : (tripleCharges (sourceA2143 + difference 4 1) (sourceB2143 + difference 1 4) sourceC2143) = raw29656 := by
      apply Matrix.ext; unfold tripleCharges sourceA2143 sourceB2143 sourceC2143 difference raw29656; decide +kernel
    rw [ha]
    exact (canonical29656 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2143 + difference 4 2) (sourceB2143 + difference 2 4) sourceC2143) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4943) := by
    have ha : (tripleCharges (sourceA2143 + difference 4 2) (sourceB2143 + difference 2 4) sourceC2143) = raw29657 := by
      apply Matrix.ext; unfold tripleCharges sourceA2143 sourceB2143 sourceC2143 difference raw29657; decide +kernel
    rw [ha]
    exact (canonical29657 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2143 + difference 4 3) (sourceB2143 + difference 3 4) sourceC2143) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4943) := by
    have ha : (tripleCharges (sourceA2143 + difference 4 3) (sourceB2143 + difference 3 4) sourceC2143) = raw29658 := by
      apply Matrix.ext; unfold tripleCharges sourceA2143 sourceB2143 sourceC2143 difference raw29658; decide +kernel
    rw [ha]
    exact (canonical29658 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2143 + difference 4 5) (sourceB2143 + difference 5 4) sourceC2143) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5171) := by
    have ha : (tripleCharges (sourceA2143 + difference 4 5) (sourceB2143 + difference 5 4) sourceC2143) = raw29659 := by
      apply Matrix.ext; unfold tripleCharges sourceA2143 sourceB2143 sourceC2143 difference raw29659; decide +kernel
    rw [ha]
    exact (canonical29659 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2143 + difference 5 0) (sourceB2143 + difference 0 5) sourceC2143) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4360) := by
    have ha : (tripleCharges (sourceA2143 + difference 5 0) (sourceB2143 + difference 0 5) sourceC2143) = raw21491 := by
      apply Matrix.ext; unfold tripleCharges sourceA2143 sourceB2143 sourceC2143 difference raw21491; decide +kernel
    rw [ha]
    exact (canonical21491 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2143 + difference 5 1) (sourceB2143 + difference 1 5) sourceC2143) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4952) := by
    have ha : (tripleCharges (sourceA2143 + difference 5 1) (sourceB2143 + difference 1 5) sourceC2143) = raw27590 := by
      apply Matrix.ext; unfold tripleCharges sourceA2143 sourceB2143 sourceC2143 difference raw27590; decide +kernel
    rw [ha]
    exact (canonical27590 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2143 + difference 5 2) (sourceB2143 + difference 2 5) sourceC2143) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4943) := by
    have ha : (tripleCharges (sourceA2143 + difference 5 2) (sourceB2143 + difference 2 5) sourceC2143) = raw27591 := by
      apply Matrix.ext; unfold tripleCharges sourceA2143 sourceB2143 sourceC2143 difference raw27591; decide +kernel
    rw [ha]
    exact (canonical27591 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2143 + difference 5 3) (sourceB2143 + difference 3 5) sourceC2143) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4943) := by
    have ha : (tripleCharges (sourceA2143 + difference 5 3) (sourceB2143 + difference 3 5) sourceC2143) = raw27592 := by
      apply Matrix.ext; unfold tripleCharges sourceA2143 sourceB2143 sourceC2143 difference raw27592; decide +kernel
    rw [ha]
    exact (canonical27592 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2143 + difference 5 4) (sourceB2143 + difference 4 5) sourceC2143) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5171) := by
    have ha : (tripleCharges (sourceA2143 + difference 5 4) (sourceB2143 + difference 4 5) sourceC2143) = raw4936 := by
      apply Matrix.ext; unfold tripleCharges sourceA2143 sourceB2143 sourceC2143 difference raw4936; decide +kernel
    rw [ha]
    exact (canonical4936 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2143 sourceB2143 sourceC2143
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2143, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
