import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical91
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical93
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical94
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical95
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical97
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical98
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical100
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical101
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical102
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical103
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical104
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical105
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical106
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical107

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA800 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB800 : Charge := ![1, 1, 1, -2, -1, 0]
def sourceC800 : Charge := ![2, -1, -1, 1, 0, -1]
def sourceForm800 : Integer.Sparse Master := [(Sum.inr 2622, 1), (Sum.inr 2623, 1), (Sum.inr 2625, 1), (Sum.inr 2631, 1), (Sum.inr 2750, 1), (Sum.inr 3880, 1), (Sum.inr 4091, -1)]

theorem sourceEq800 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm800 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA800 + difference 0 1) (sourceB800 + difference 1 0) sourceC800) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3880) := by
    have ha : (tripleCharges (sourceA800 + difference 0 1) (sourceB800 + difference 1 0) sourceC800) = raw13190 := by
      apply Matrix.ext; unfold tripleCharges sourceA800 sourceB800 sourceC800 difference raw13190; decide +kernel
    rw [ha]
    exact (canonical13190 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA800 + difference 1 1) (sourceB800 + difference 1 1) sourceC800) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2750) := by
    have ha : (tripleCharges (sourceA800 + difference 1 1) (sourceB800 + difference 1 1) sourceC800) = raw13189 := by
      apply Matrix.ext; unfold tripleCharges sourceA800 sourceB800 sourceC800 difference raw13189; decide +kernel
    rw [ha]
    exact (canonical13189 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA800 + difference 2 1) (sourceB800 + difference 1 2) sourceC800) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2631) := by
    have ha : (tripleCharges (sourceA800 + difference 2 1) (sourceB800 + difference 1 2) sourceC800) = raw13205 := by
      apply Matrix.ext; unfold tripleCharges sourceA800 sourceB800 sourceC800 difference raw13205; decide +kernel
    rw [ha]
    exact (canonical13205 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA800 + difference 3 1) (sourceB800 + difference 1 3) sourceC800) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2625) := by
    have ha : (tripleCharges (sourceA800 + difference 3 1) (sourceB800 + difference 1 3) sourceC800) = raw13206 := by
      apply Matrix.ext; unfold tripleCharges sourceA800 sourceB800 sourceC800 difference raw13206; decide +kernel
    rw [ha]
    exact (canonical13206 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA800 + difference 4 1) (sourceB800 + difference 1 4) sourceC800) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2623) := by
    have ha : (tripleCharges (sourceA800 + difference 4 1) (sourceB800 + difference 1 4) sourceC800) = raw13207 := by
      apply Matrix.ext; unfold tripleCharges sourceA800 sourceB800 sourceC800 difference raw13207; decide +kernel
    rw [ha]
    exact (canonical13207 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA800 + difference 5 1) (sourceB800 + difference 1 5) sourceC800) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2622) := by
    have ha : (tripleCharges (sourceA800 + difference 5 1) (sourceB800 + difference 1 5) sourceC800) = raw13208 := by
      apply Matrix.ext; unfold tripleCharges sourceA800 sourceB800 sourceC800 difference raw13208; decide +kernel
    rw [ha]
    exact (canonical13208 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA800 + sourceB800) sourceC800) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA800 + sourceB800) sourceC800) = raw13195 := by
      apply Matrix.ext; unfold doubleCharges sourceA800 sourceB800 sourceC800 raw13195; decide +kernel
    rw [ha]
    exact (canonical13195 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA800 sourceB800 sourceC800
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm800, Integer.Sparse.eval]
  linarith only [hs]

def sourceA801 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB801 : Charge := ![2, -1, -1, 1, 0, -1]
def sourceC801 : Charge := ![1, 1, 1, -2, -1, 0]
def sourceForm801 : Integer.Sparse Master := [(Sum.inr 4435, 1), (Sum.inr 4436, 1), (Sum.inr 4439, 1), (Sum.inr 4449, 2), (Sum.inr 5144, 2), (Sum.inr 5145, 2), (Sum.inr 5149, 2), (Sum.inr 5160, 2), (Sum.inr 5219, 1), (Sum.inr 5220, 1), (Sum.inr 5226, 2), (Sum.inr 5249, 1), (Sum.inr 5251, 1), (Sum.inr 5255, 2), (Sum.inr 5282, 1), (Sum.inr 5284, 1), (Sum.inr 5289, 2), (Sum.inr 5431, 1), (Sum.inr 5478, 2), (Sum.inr 5481, 1), (Sum.inr 5485, 1)]

theorem sourceEq801 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm801 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA801 + difference 0 1) (sourceB801 + difference 1 0) sourceC801) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5478) := by
    have ha : (tripleCharges (sourceA801 + difference 0 1) (sourceB801 + difference 1 0) sourceC801) = raw13209 := by
      apply Matrix.ext; unfold tripleCharges sourceA801 sourceB801 sourceC801 difference raw13209; decide +kernel
    rw [ha]
    exact (canonical13209 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA801 + difference 0 2) (sourceB801 + difference 2 0) sourceC801) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5478) := by
    have ha : (tripleCharges (sourceA801 + difference 0 2) (sourceB801 + difference 2 0) sourceC801) = raw13210 := by
      apply Matrix.ext; unfold tripleCharges sourceA801 sourceB801 sourceC801 difference raw13210; decide +kernel
    rw [ha]
    exact (canonical13210 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA801 + difference 0 3) (sourceB801 + difference 3 0) sourceC801) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA801 + difference 0 3) (sourceB801 + difference 3 0) sourceC801) = raw13211 := by
      apply Matrix.ext; unfold tripleCharges sourceA801 sourceB801 sourceC801 difference raw13211; decide +kernel
    rw [ha]
    exact (canonical13211 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA801 + difference 0 4) (sourceB801 + difference 4 0) sourceC801) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5481) := by
    have ha : (tripleCharges (sourceA801 + difference 0 4) (sourceB801 + difference 4 0) sourceC801) = raw13212 := by
      apply Matrix.ext; unfold tripleCharges sourceA801 sourceB801 sourceC801 difference raw13212; decide +kernel
    rw [ha]
    exact (canonical13212 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA801 + difference 0 5) (sourceB801 + difference 5 0) sourceC801) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA801 + difference 0 5) (sourceB801 + difference 5 0) sourceC801) = raw13213 := by
      apply Matrix.ext; unfold tripleCharges sourceA801 sourceB801 sourceC801 difference raw13213; decide +kernel
    rw [ha]
    exact (canonical13213 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA801 + difference 1 0) (sourceB801 + difference 0 1) sourceC801) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4449) := by
    have ha : (tripleCharges (sourceA801 + difference 1 0) (sourceB801 + difference 0 1) sourceC801) = raw13214 := by
      apply Matrix.ext; unfold tripleCharges sourceA801 sourceB801 sourceC801 difference raw13214; decide +kernel
    rw [ha]
    exact (canonical13214 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA801 + difference 1 2) (sourceB801 + difference 2 1) sourceC801) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5160) := by
    have ha : (tripleCharges (sourceA801 + difference 1 2) (sourceB801 + difference 2 1) sourceC801) = raw13215 := by
      apply Matrix.ext; unfold tripleCharges sourceA801 sourceB801 sourceC801 difference raw13215; decide +kernel
    rw [ha]
    exact (canonical13215 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA801 + difference 1 3) (sourceB801 + difference 3 1) sourceC801) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5226) := by
    have ha : (tripleCharges (sourceA801 + difference 1 3) (sourceB801 + difference 3 1) sourceC801) = raw13216 := by
      apply Matrix.ext; unfold tripleCharges sourceA801 sourceB801 sourceC801 difference raw13216; decide +kernel
    rw [ha]
    exact (canonical13216 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA801 + difference 1 4) (sourceB801 + difference 4 1) sourceC801) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5255) := by
    have ha : (tripleCharges (sourceA801 + difference 1 4) (sourceB801 + difference 4 1) sourceC801) = raw13217 := by
      apply Matrix.ext; unfold tripleCharges sourceA801 sourceB801 sourceC801 difference raw13217; decide +kernel
    rw [ha]
    exact (canonical13217 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA801 + difference 1 5) (sourceB801 + difference 5 1) sourceC801) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA801 + difference 1 5) (sourceB801 + difference 5 1) sourceC801) = raw13218 := by
      apply Matrix.ext; unfold tripleCharges sourceA801 sourceB801 sourceC801 difference raw13218; decide +kernel
    rw [ha]
    exact (canonical13218 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA801 + difference 2 0) (sourceB801 + difference 0 2) sourceC801) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4449) := by
    have ha : (tripleCharges (sourceA801 + difference 2 0) (sourceB801 + difference 0 2) sourceC801) = raw13219 := by
      apply Matrix.ext; unfold tripleCharges sourceA801 sourceB801 sourceC801 difference raw13219; decide +kernel
    rw [ha]
    exact (canonical13219 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA801 + difference 2 1) (sourceB801 + difference 1 2) sourceC801) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5160) := by
    have ha : (tripleCharges (sourceA801 + difference 2 1) (sourceB801 + difference 1 2) sourceC801) = raw13220 := by
      apply Matrix.ext; unfold tripleCharges sourceA801 sourceB801 sourceC801 difference raw13220; decide +kernel
    rw [ha]
    exact (canonical13220 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA801 + difference 2 3) (sourceB801 + difference 3 2) sourceC801) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5226) := by
    have ha : (tripleCharges (sourceA801 + difference 2 3) (sourceB801 + difference 3 2) sourceC801) = raw13221 := by
      apply Matrix.ext; unfold tripleCharges sourceA801 sourceB801 sourceC801 difference raw13221; decide +kernel
    rw [ha]
    exact (canonical13221 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA801 + difference 2 4) (sourceB801 + difference 4 2) sourceC801) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5255) := by
    have ha : (tripleCharges (sourceA801 + difference 2 4) (sourceB801 + difference 4 2) sourceC801) = raw13222 := by
      apply Matrix.ext; unfold tripleCharges sourceA801 sourceB801 sourceC801 difference raw13222; decide +kernel
    rw [ha]
    exact (canonical13222 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA801 + difference 2 5) (sourceB801 + difference 5 2) sourceC801) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA801 + difference 2 5) (sourceB801 + difference 5 2) sourceC801) = raw13223 := by
      apply Matrix.ext; unfold tripleCharges sourceA801 sourceB801 sourceC801 difference raw13223; decide +kernel
    rw [ha]
    exact (canonical13223 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA801 + difference 3 0) (sourceB801 + difference 0 3) sourceC801) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4439) := by
    have ha : (tripleCharges (sourceA801 + difference 3 0) (sourceB801 + difference 0 3) sourceC801) = raw13224 := by
      apply Matrix.ext; unfold tripleCharges sourceA801 sourceB801 sourceC801 difference raw13224; decide +kernel
    rw [ha]
    exact (canonical13224 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA801 + difference 3 1) (sourceB801 + difference 1 3) sourceC801) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5149) := by
    have ha : (tripleCharges (sourceA801 + difference 3 1) (sourceB801 + difference 1 3) sourceC801) = raw13225 := by
      apply Matrix.ext; unfold tripleCharges sourceA801 sourceB801 sourceC801 difference raw13225; decide +kernel
    rw [ha]
    exact (canonical13225 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA801 + difference 3 2) (sourceB801 + difference 2 3) sourceC801) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5149) := by
    have ha : (tripleCharges (sourceA801 + difference 3 2) (sourceB801 + difference 2 3) sourceC801) = raw13226 := by
      apply Matrix.ext; unfold tripleCharges sourceA801 sourceB801 sourceC801 difference raw13226; decide +kernel
    rw [ha]
    exact (canonical13226 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA801 + difference 3 4) (sourceB801 + difference 4 3) sourceC801) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5251) := by
    have ha : (tripleCharges (sourceA801 + difference 3 4) (sourceB801 + difference 4 3) sourceC801) = raw13227 := by
      apply Matrix.ext; unfold tripleCharges sourceA801 sourceB801 sourceC801 difference raw13227; decide +kernel
    rw [ha]
    exact (canonical13227 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA801 + difference 3 5) (sourceB801 + difference 5 3) sourceC801) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA801 + difference 3 5) (sourceB801 + difference 5 3) sourceC801) = raw13228 := by
      apply Matrix.ext; unfold tripleCharges sourceA801 sourceB801 sourceC801 difference raw13228; decide +kernel
    rw [ha]
    exact (canonical13228 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA801 + difference 4 0) (sourceB801 + difference 0 4) sourceC801) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4436) := by
    have ha : (tripleCharges (sourceA801 + difference 4 0) (sourceB801 + difference 0 4) sourceC801) = raw13229 := by
      apply Matrix.ext; unfold tripleCharges sourceA801 sourceB801 sourceC801 difference raw13229; decide +kernel
    rw [ha]
    exact (canonical13229 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA801 + difference 4 1) (sourceB801 + difference 1 4) sourceC801) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5145) := by
    have ha : (tripleCharges (sourceA801 + difference 4 1) (sourceB801 + difference 1 4) sourceC801) = raw13230 := by
      apply Matrix.ext; unfold tripleCharges sourceA801 sourceB801 sourceC801 difference raw13230; decide +kernel
    rw [ha]
    exact (canonical13230 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA801 + difference 4 2) (sourceB801 + difference 2 4) sourceC801) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5145) := by
    have ha : (tripleCharges (sourceA801 + difference 4 2) (sourceB801 + difference 2 4) sourceC801) = raw13231 := by
      apply Matrix.ext; unfold tripleCharges sourceA801 sourceB801 sourceC801 difference raw13231; decide +kernel
    rw [ha]
    exact (canonical13231 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA801 + difference 4 3) (sourceB801 + difference 3 4) sourceC801) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5220) := by
    have ha : (tripleCharges (sourceA801 + difference 4 3) (sourceB801 + difference 3 4) sourceC801) = raw13232 := by
      apply Matrix.ext; unfold tripleCharges sourceA801 sourceB801 sourceC801 difference raw13232; decide +kernel
    rw [ha]
    exact (canonical13232 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA801 + difference 4 5) (sourceB801 + difference 5 4) sourceC801) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5282) := by
    have ha : (tripleCharges (sourceA801 + difference 4 5) (sourceB801 + difference 5 4) sourceC801) = raw13233 := by
      apply Matrix.ext; unfold tripleCharges sourceA801 sourceB801 sourceC801 difference raw13233; decide +kernel
    rw [ha]
    exact (canonical13233 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA801 + difference 5 0) (sourceB801 + difference 0 5) sourceC801) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4435) := by
    have ha : (tripleCharges (sourceA801 + difference 5 0) (sourceB801 + difference 0 5) sourceC801) = raw13234 := by
      apply Matrix.ext; unfold tripleCharges sourceA801 sourceB801 sourceC801 difference raw13234; decide +kernel
    rw [ha]
    exact (canonical13234 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA801 + difference 5 1) (sourceB801 + difference 1 5) sourceC801) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5144) := by
    have ha : (tripleCharges (sourceA801 + difference 5 1) (sourceB801 + difference 1 5) sourceC801) = raw13235 := by
      apply Matrix.ext; unfold tripleCharges sourceA801 sourceB801 sourceC801 difference raw13235; decide +kernel
    rw [ha]
    exact (canonical13235 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA801 + difference 5 2) (sourceB801 + difference 2 5) sourceC801) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5144) := by
    have ha : (tripleCharges (sourceA801 + difference 5 2) (sourceB801 + difference 2 5) sourceC801) = raw13236 := by
      apply Matrix.ext; unfold tripleCharges sourceA801 sourceB801 sourceC801 difference raw13236; decide +kernel
    rw [ha]
    exact (canonical13236 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA801 + difference 5 3) (sourceB801 + difference 3 5) sourceC801) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5219) := by
    have ha : (tripleCharges (sourceA801 + difference 5 3) (sourceB801 + difference 3 5) sourceC801) = raw13237 := by
      apply Matrix.ext; unfold tripleCharges sourceA801 sourceB801 sourceC801 difference raw13237; decide +kernel
    rw [ha]
    exact (canonical13237 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA801 + difference 5 4) (sourceB801 + difference 4 5) sourceC801) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5249) := by
    have ha : (tripleCharges (sourceA801 + difference 5 4) (sourceB801 + difference 4 5) sourceC801) = raw13238 := by
      apply Matrix.ext; unfold tripleCharges sourceA801 sourceB801 sourceC801 difference raw13238; decide +kernel
    rw [ha]
    exact (canonical13238 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA801 sourceB801 sourceC801
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm801, Integer.Sparse.eval]
  linarith only [hs]

def sourceA802 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB802 : Charge := ![2, -1, -1, 1, 0, -1]
def sourceC802 : Charge := ![1, 1, 1, -2, -1, 0]
def sourceForm802 : Integer.Sparse Master := [(Sum.inr 1017, 1), (Sum.inr 1018, 1), (Sum.inr 1021, 1), (Sum.inr 1032, 2), (Sum.inr 2566, 2), (Sum.inr 2567, 2), (Sum.inr 2570, 2), (Sum.inr 2587, 2), (Sum.inr 2661, 1), (Sum.inr 2662, 1), (Sum.inr 2669, 2), (Sum.inr 2708, 1), (Sum.inr 2710, 1), (Sum.inr 2718, 2), (Sum.inr 2751, 1), (Sum.inr 2753, 1), (Sum.inr 2763, 2), (Sum.inr 3849, 1), (Sum.inr 3979, 1), (Sum.inr 3994, 2), (Sum.inr 3998, 1)]

theorem sourceEq802 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm802 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA802 + difference 0 1) (sourceB802 + difference 1 0) sourceC802) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3994) := by
    have ha : (tripleCharges (sourceA802 + difference 0 1) (sourceB802 + difference 1 0) sourceC802) = raw13239 := by
      apply Matrix.ext; unfold tripleCharges sourceA802 sourceB802 sourceC802 difference raw13239; decide +kernel
    rw [ha]
    exact (canonical13239 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA802 + difference 0 2) (sourceB802 + difference 2 0) sourceC802) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3994) := by
    have ha : (tripleCharges (sourceA802 + difference 0 2) (sourceB802 + difference 2 0) sourceC802) = raw13240 := by
      apply Matrix.ext; unfold tripleCharges sourceA802 sourceB802 sourceC802 difference raw13240; decide +kernel
    rw [ha]
    exact (canonical13240 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA802 + difference 0 3) (sourceB802 + difference 3 0) sourceC802) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3849) := by
    have ha : (tripleCharges (sourceA802 + difference 0 3) (sourceB802 + difference 3 0) sourceC802) = raw13241 := by
      apply Matrix.ext; unfold tripleCharges sourceA802 sourceB802 sourceC802 difference raw13241; decide +kernel
    rw [ha]
    exact (canonical13241 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA802 + difference 0 4) (sourceB802 + difference 4 0) sourceC802) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3979) := by
    have ha : (tripleCharges (sourceA802 + difference 0 4) (sourceB802 + difference 4 0) sourceC802) = raw13242 := by
      apply Matrix.ext; unfold tripleCharges sourceA802 sourceB802 sourceC802 difference raw13242; decide +kernel
    rw [ha]
    exact (canonical13242 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA802 + difference 0 5) (sourceB802 + difference 5 0) sourceC802) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3998) := by
    have ha : (tripleCharges (sourceA802 + difference 0 5) (sourceB802 + difference 5 0) sourceC802) = raw13243 := by
      apply Matrix.ext; unfold tripleCharges sourceA802 sourceB802 sourceC802 difference raw13243; decide +kernel
    rw [ha]
    exact (canonical13243 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA802 + difference 1 0) (sourceB802 + difference 0 1) sourceC802) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1032) := by
    have ha : (tripleCharges (sourceA802 + difference 1 0) (sourceB802 + difference 0 1) sourceC802) = raw13244 := by
      apply Matrix.ext; unfold tripleCharges sourceA802 sourceB802 sourceC802 difference raw13244; decide +kernel
    rw [ha]
    exact (canonical13244 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA802 + difference 1 2) (sourceB802 + difference 2 1) sourceC802) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2587) := by
    have ha : (tripleCharges (sourceA802 + difference 1 2) (sourceB802 + difference 2 1) sourceC802) = raw13245 := by
      apply Matrix.ext; unfold tripleCharges sourceA802 sourceB802 sourceC802 difference raw13245; decide +kernel
    rw [ha]
    exact (canonical13245 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA802 + difference 1 3) (sourceB802 + difference 3 1) sourceC802) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2669) := by
    have ha : (tripleCharges (sourceA802 + difference 1 3) (sourceB802 + difference 3 1) sourceC802) = raw13246 := by
      apply Matrix.ext; unfold tripleCharges sourceA802 sourceB802 sourceC802 difference raw13246; decide +kernel
    rw [ha]
    exact (canonical13246 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA802 + difference 1 4) (sourceB802 + difference 4 1) sourceC802) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2718) := by
    have ha : (tripleCharges (sourceA802 + difference 1 4) (sourceB802 + difference 4 1) sourceC802) = raw13247 := by
      apply Matrix.ext; unfold tripleCharges sourceA802 sourceB802 sourceC802 difference raw13247; decide +kernel
    rw [ha]
    exact (canonical13247 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA802 + difference 1 5) (sourceB802 + difference 5 1) sourceC802) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2763) := by
    have ha : (tripleCharges (sourceA802 + difference 1 5) (sourceB802 + difference 5 1) sourceC802) = raw13248 := by
      apply Matrix.ext; unfold tripleCharges sourceA802 sourceB802 sourceC802 difference raw13248; decide +kernel
    rw [ha]
    exact (canonical13248 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA802 + difference 2 0) (sourceB802 + difference 0 2) sourceC802) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1032) := by
    have ha : (tripleCharges (sourceA802 + difference 2 0) (sourceB802 + difference 0 2) sourceC802) = raw13249 := by
      apply Matrix.ext; unfold tripleCharges sourceA802 sourceB802 sourceC802 difference raw13249; decide +kernel
    rw [ha]
    exact (canonical13249 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA802 + difference 2 1) (sourceB802 + difference 1 2) sourceC802) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2587) := by
    have ha : (tripleCharges (sourceA802 + difference 2 1) (sourceB802 + difference 1 2) sourceC802) = raw13250 := by
      apply Matrix.ext; unfold tripleCharges sourceA802 sourceB802 sourceC802 difference raw13250; decide +kernel
    rw [ha]
    exact (canonical13250 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA802 + difference 2 3) (sourceB802 + difference 3 2) sourceC802) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2669) := by
    have ha : (tripleCharges (sourceA802 + difference 2 3) (sourceB802 + difference 3 2) sourceC802) = raw13251 := by
      apply Matrix.ext; unfold tripleCharges sourceA802 sourceB802 sourceC802 difference raw13251; decide +kernel
    rw [ha]
    exact (canonical13251 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA802 + difference 2 4) (sourceB802 + difference 4 2) sourceC802) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2718) := by
    have ha : (tripleCharges (sourceA802 + difference 2 4) (sourceB802 + difference 4 2) sourceC802) = raw13252 := by
      apply Matrix.ext; unfold tripleCharges sourceA802 sourceB802 sourceC802 difference raw13252; decide +kernel
    rw [ha]
    exact (canonical13252 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA802 + difference 2 5) (sourceB802 + difference 5 2) sourceC802) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2763) := by
    have ha : (tripleCharges (sourceA802 + difference 2 5) (sourceB802 + difference 5 2) sourceC802) = raw13253 := by
      apply Matrix.ext; unfold tripleCharges sourceA802 sourceB802 sourceC802 difference raw13253; decide +kernel
    rw [ha]
    exact (canonical13253 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA802 + difference 3 0) (sourceB802 + difference 0 3) sourceC802) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1021) := by
    have ha : (tripleCharges (sourceA802 + difference 3 0) (sourceB802 + difference 0 3) sourceC802) = raw13254 := by
      apply Matrix.ext; unfold tripleCharges sourceA802 sourceB802 sourceC802 difference raw13254; decide +kernel
    rw [ha]
    exact (canonical13254 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA802 + difference 3 1) (sourceB802 + difference 1 3) sourceC802) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2570) := by
    have ha : (tripleCharges (sourceA802 + difference 3 1) (sourceB802 + difference 1 3) sourceC802) = raw13255 := by
      apply Matrix.ext; unfold tripleCharges sourceA802 sourceB802 sourceC802 difference raw13255; decide +kernel
    rw [ha]
    exact (canonical13255 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA802 + difference 3 2) (sourceB802 + difference 2 3) sourceC802) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2570) := by
    have ha : (tripleCharges (sourceA802 + difference 3 2) (sourceB802 + difference 2 3) sourceC802) = raw13256 := by
      apply Matrix.ext; unfold tripleCharges sourceA802 sourceB802 sourceC802 difference raw13256; decide +kernel
    rw [ha]
    exact (canonical13256 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA802 + difference 3 4) (sourceB802 + difference 4 3) sourceC802) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2710) := by
    have ha : (tripleCharges (sourceA802 + difference 3 4) (sourceB802 + difference 4 3) sourceC802) = raw13257 := by
      apply Matrix.ext; unfold tripleCharges sourceA802 sourceB802 sourceC802 difference raw13257; decide +kernel
    rw [ha]
    exact (canonical13257 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA802 + difference 3 5) (sourceB802 + difference 5 3) sourceC802) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2753) := by
    have ha : (tripleCharges (sourceA802 + difference 3 5) (sourceB802 + difference 5 3) sourceC802) = raw13258 := by
      apply Matrix.ext; unfold tripleCharges sourceA802 sourceB802 sourceC802 difference raw13258; decide +kernel
    rw [ha]
    exact (canonical13258 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA802 + difference 4 0) (sourceB802 + difference 0 4) sourceC802) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1018) := by
    have ha : (tripleCharges (sourceA802 + difference 4 0) (sourceB802 + difference 0 4) sourceC802) = raw13259 := by
      apply Matrix.ext; unfold tripleCharges sourceA802 sourceB802 sourceC802 difference raw13259; decide +kernel
    rw [ha]
    exact (canonical13259 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA802 + difference 4 1) (sourceB802 + difference 1 4) sourceC802) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2567) := by
    have ha : (tripleCharges (sourceA802 + difference 4 1) (sourceB802 + difference 1 4) sourceC802) = raw13260 := by
      apply Matrix.ext; unfold tripleCharges sourceA802 sourceB802 sourceC802 difference raw13260; decide +kernel
    rw [ha]
    exact (canonical13260 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA802 + difference 4 2) (sourceB802 + difference 2 4) sourceC802) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2567) := by
    have ha : (tripleCharges (sourceA802 + difference 4 2) (sourceB802 + difference 2 4) sourceC802) = raw13261 := by
      apply Matrix.ext; unfold tripleCharges sourceA802 sourceB802 sourceC802 difference raw13261; decide +kernel
    rw [ha]
    exact (canonical13261 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA802 + difference 4 3) (sourceB802 + difference 3 4) sourceC802) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2662) := by
    have ha : (tripleCharges (sourceA802 + difference 4 3) (sourceB802 + difference 3 4) sourceC802) = raw13262 := by
      apply Matrix.ext; unfold tripleCharges sourceA802 sourceB802 sourceC802 difference raw13262; decide +kernel
    rw [ha]
    exact (canonical13262 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA802 + difference 4 5) (sourceB802 + difference 5 4) sourceC802) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2751) := by
    have ha : (tripleCharges (sourceA802 + difference 4 5) (sourceB802 + difference 5 4) sourceC802) = raw13263 := by
      apply Matrix.ext; unfold tripleCharges sourceA802 sourceB802 sourceC802 difference raw13263; decide +kernel
    rw [ha]
    exact (canonical13263 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA802 + difference 5 0) (sourceB802 + difference 0 5) sourceC802) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1017) := by
    have ha : (tripleCharges (sourceA802 + difference 5 0) (sourceB802 + difference 0 5) sourceC802) = raw13264 := by
      apply Matrix.ext; unfold tripleCharges sourceA802 sourceB802 sourceC802 difference raw13264; decide +kernel
    rw [ha]
    exact (canonical13264 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA802 + difference 5 1) (sourceB802 + difference 1 5) sourceC802) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2566) := by
    have ha : (tripleCharges (sourceA802 + difference 5 1) (sourceB802 + difference 1 5) sourceC802) = raw13265 := by
      apply Matrix.ext; unfold tripleCharges sourceA802 sourceB802 sourceC802 difference raw13265; decide +kernel
    rw [ha]
    exact (canonical13265 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA802 + difference 5 2) (sourceB802 + difference 2 5) sourceC802) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2566) := by
    have ha : (tripleCharges (sourceA802 + difference 5 2) (sourceB802 + difference 2 5) sourceC802) = raw13266 := by
      apply Matrix.ext; unfold tripleCharges sourceA802 sourceB802 sourceC802 difference raw13266; decide +kernel
    rw [ha]
    exact (canonical13266 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA802 + difference 5 3) (sourceB802 + difference 3 5) sourceC802) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2661) := by
    have ha : (tripleCharges (sourceA802 + difference 5 3) (sourceB802 + difference 3 5) sourceC802) = raw13267 := by
      apply Matrix.ext; unfold tripleCharges sourceA802 sourceB802 sourceC802 difference raw13267; decide +kernel
    rw [ha]
    exact (canonical13267 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA802 + difference 5 4) (sourceB802 + difference 4 5) sourceC802) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2708) := by
    have ha : (tripleCharges (sourceA802 + difference 5 4) (sourceB802 + difference 4 5) sourceC802) = raw13268 := by
      apply Matrix.ext; unfold tripleCharges sourceA802 sourceB802 sourceC802 difference raw13268; decide +kernel
    rw [ha]
    exact (canonical13268 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA802 sourceB802 sourceC802
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm802, Integer.Sparse.eval]
  linarith only [hs]

def sourceA803 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB803 : Charge := ![2, -1, -1, 1, 0, -1]
def sourceC803 : Charge := ![1, 1, 1, -2, -1, 0]
def sourceForm803 : Integer.Sparse Master := [(Sum.inr 1635, 1), (Sum.inr 1636, 2), (Sum.inr 1642, 1), (Sum.inr 1713, 1), (Sum.inr 3375, 1), (Sum.inr 3376, 2), (Sum.inr 3388, 1), (Sum.inr 3502, 1), (Sum.inr 3503, 2), (Sum.inr 3539, 1), (Sum.inr 3557, 2), (Sum.inr 3558, 2), (Sum.inr 3562, 2), (Sum.inr 3572, 2), (Sum.inr 3580, 1), (Sum.inr 3605, 2), (Sum.inr 3625, 1), (Sum.inr 3974, 2), (Sum.inr 3984, 1), (Sum.inr 3991, 1), (Sum.inr 4026, 1)]

theorem sourceEq803 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm803 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA803 + difference 0 1) (sourceB803 + difference 1 0) sourceC803) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3974) := by
    have ha : (tripleCharges (sourceA803 + difference 0 1) (sourceB803 + difference 1 0) sourceC803) = raw13269 := by
      apply Matrix.ext; unfold tripleCharges sourceA803 sourceB803 sourceC803 difference raw13269; decide +kernel
    rw [ha]
    exact (canonical13269 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA803 + difference 0 2) (sourceB803 + difference 2 0) sourceC803) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3974) := by
    have ha : (tripleCharges (sourceA803 + difference 0 2) (sourceB803 + difference 2 0) sourceC803) = raw13270 := by
      apply Matrix.ext; unfold tripleCharges sourceA803 sourceB803 sourceC803 difference raw13270; decide +kernel
    rw [ha]
    exact (canonical13270 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA803 + difference 0 3) (sourceB803 + difference 3 0) sourceC803) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4026) := by
    have ha : (tripleCharges (sourceA803 + difference 0 3) (sourceB803 + difference 3 0) sourceC803) = raw13271 := by
      apply Matrix.ext; unfold tripleCharges sourceA803 sourceB803 sourceC803 difference raw13271; decide +kernel
    rw [ha]
    exact (canonical13271 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA803 + difference 0 4) (sourceB803 + difference 4 0) sourceC803) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3991) := by
    have ha : (tripleCharges (sourceA803 + difference 0 4) (sourceB803 + difference 4 0) sourceC803) = raw13272 := by
      apply Matrix.ext; unfold tripleCharges sourceA803 sourceB803 sourceC803 difference raw13272; decide +kernel
    rw [ha]
    exact (canonical13272 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA803 + difference 0 5) (sourceB803 + difference 5 0) sourceC803) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3984) := by
    have ha : (tripleCharges (sourceA803 + difference 0 5) (sourceB803 + difference 5 0) sourceC803) = raw13273 := by
      apply Matrix.ext; unfold tripleCharges sourceA803 sourceB803 sourceC803 difference raw13273; decide +kernel
    rw [ha]
    exact (canonical13273 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA803 + difference 1 0) (sourceB803 + difference 0 1) sourceC803) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1636) := by
    have ha : (tripleCharges (sourceA803 + difference 1 0) (sourceB803 + difference 0 1) sourceC803) = raw13274 := by
      apply Matrix.ext; unfold tripleCharges sourceA803 sourceB803 sourceC803 difference raw13274; decide +kernel
    rw [ha]
    exact (canonical13274 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA803 + difference 1 2) (sourceB803 + difference 2 1) sourceC803) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3558) := by
    have ha : (tripleCharges (sourceA803 + difference 1 2) (sourceB803 + difference 2 1) sourceC803) = raw13275 := by
      apply Matrix.ext; unfold tripleCharges sourceA803 sourceB803 sourceC803 difference raw13275; decide +kernel
    rw [ha]
    exact (canonical13275 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA803 + difference 1 3) (sourceB803 + difference 3 1) sourceC803) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3376) := by
    have ha : (tripleCharges (sourceA803 + difference 1 3) (sourceB803 + difference 3 1) sourceC803) = raw13276 := by
      apply Matrix.ext; unfold tripleCharges sourceA803 sourceB803 sourceC803 difference raw13276; decide +kernel
    rw [ha]
    exact (canonical13276 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA803 + difference 1 4) (sourceB803 + difference 4 1) sourceC803) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3503) := by
    have ha : (tripleCharges (sourceA803 + difference 1 4) (sourceB803 + difference 4 1) sourceC803) = raw13277 := by
      apply Matrix.ext; unfold tripleCharges sourceA803 sourceB803 sourceC803 difference raw13277; decide +kernel
    rw [ha]
    exact (canonical13277 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA803 + difference 1 5) (sourceB803 + difference 5 1) sourceC803) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA803 + difference 1 5) (sourceB803 + difference 5 1) sourceC803) = raw13278 := by
      apply Matrix.ext; unfold tripleCharges sourceA803 sourceB803 sourceC803 difference raw13278; decide +kernel
    rw [ha]
    exact (canonical13278 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA803 + difference 2 0) (sourceB803 + difference 0 2) sourceC803) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1636) := by
    have ha : (tripleCharges (sourceA803 + difference 2 0) (sourceB803 + difference 0 2) sourceC803) = raw13279 := by
      apply Matrix.ext; unfold tripleCharges sourceA803 sourceB803 sourceC803 difference raw13279; decide +kernel
    rw [ha]
    exact (canonical13279 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA803 + difference 2 1) (sourceB803 + difference 1 2) sourceC803) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3558) := by
    have ha : (tripleCharges (sourceA803 + difference 2 1) (sourceB803 + difference 1 2) sourceC803) = raw13280 := by
      apply Matrix.ext; unfold tripleCharges sourceA803 sourceB803 sourceC803 difference raw13280; decide +kernel
    rw [ha]
    exact (canonical13280 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA803 + difference 2 3) (sourceB803 + difference 3 2) sourceC803) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3376) := by
    have ha : (tripleCharges (sourceA803 + difference 2 3) (sourceB803 + difference 3 2) sourceC803) = raw13281 := by
      apply Matrix.ext; unfold tripleCharges sourceA803 sourceB803 sourceC803 difference raw13281; decide +kernel
    rw [ha]
    exact (canonical13281 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA803 + difference 2 4) (sourceB803 + difference 4 2) sourceC803) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3503) := by
    have ha : (tripleCharges (sourceA803 + difference 2 4) (sourceB803 + difference 4 2) sourceC803) = raw13282 := by
      apply Matrix.ext; unfold tripleCharges sourceA803 sourceB803 sourceC803 difference raw13282; decide +kernel
    rw [ha]
    exact (canonical13282 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA803 + difference 2 5) (sourceB803 + difference 5 2) sourceC803) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA803 + difference 2 5) (sourceB803 + difference 5 2) sourceC803) = raw13283 := by
      apply Matrix.ext; unfold tripleCharges sourceA803 sourceB803 sourceC803 difference raw13283; decide +kernel
    rw [ha]
    exact (canonical13283 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA803 + difference 3 0) (sourceB803 + difference 0 3) sourceC803) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1713) := by
    have ha : (tripleCharges (sourceA803 + difference 3 0) (sourceB803 + difference 0 3) sourceC803) = raw13284 := by
      apply Matrix.ext; unfold tripleCharges sourceA803 sourceB803 sourceC803 difference raw13284; decide +kernel
    rw [ha]
    exact (canonical13284 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA803 + difference 3 1) (sourceB803 + difference 1 3) sourceC803) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3605) := by
    have ha : (tripleCharges (sourceA803 + difference 3 1) (sourceB803 + difference 1 3) sourceC803) = raw13285 := by
      apply Matrix.ext; unfold tripleCharges sourceA803 sourceB803 sourceC803 difference raw13285; decide +kernel
    rw [ha]
    exact (canonical13285 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA803 + difference 3 2) (sourceB803 + difference 2 3) sourceC803) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3605) := by
    have ha : (tripleCharges (sourceA803 + difference 3 2) (sourceB803 + difference 2 3) sourceC803) = raw13286 := by
      apply Matrix.ext; unfold tripleCharges sourceA803 sourceB803 sourceC803 difference raw13286; decide +kernel
    rw [ha]
    exact (canonical13286 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA803 + difference 3 4) (sourceB803 + difference 4 3) sourceC803) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3539) := by
    have ha : (tripleCharges (sourceA803 + difference 3 4) (sourceB803 + difference 4 3) sourceC803) = raw13287 := by
      apply Matrix.ext; unfold tripleCharges sourceA803 sourceB803 sourceC803 difference raw13287; decide +kernel
    rw [ha]
    exact (canonical13287 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA803 + difference 3 5) (sourceB803 + difference 5 3) sourceC803) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3625) := by
    have ha : (tripleCharges (sourceA803 + difference 3 5) (sourceB803 + difference 5 3) sourceC803) = raw13288 := by
      apply Matrix.ext; unfold tripleCharges sourceA803 sourceB803 sourceC803 difference raw13288; decide +kernel
    rw [ha]
    exact (canonical13288 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA803 + difference 4 0) (sourceB803 + difference 0 4) sourceC803) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1642) := by
    have ha : (tripleCharges (sourceA803 + difference 4 0) (sourceB803 + difference 0 4) sourceC803) = raw13289 := by
      apply Matrix.ext; unfold tripleCharges sourceA803 sourceB803 sourceC803 difference raw13289; decide +kernel
    rw [ha]
    exact (canonical13289 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA803 + difference 4 1) (sourceB803 + difference 1 4) sourceC803) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3562) := by
    have ha : (tripleCharges (sourceA803 + difference 4 1) (sourceB803 + difference 1 4) sourceC803) = raw13290 := by
      apply Matrix.ext; unfold tripleCharges sourceA803 sourceB803 sourceC803 difference raw13290; decide +kernel
    rw [ha]
    exact (canonical13290 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA803 + difference 4 2) (sourceB803 + difference 2 4) sourceC803) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3562) := by
    have ha : (tripleCharges (sourceA803 + difference 4 2) (sourceB803 + difference 2 4) sourceC803) = raw13291 := by
      apply Matrix.ext; unfold tripleCharges sourceA803 sourceB803 sourceC803 difference raw13291; decide +kernel
    rw [ha]
    exact (canonical13291 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA803 + difference 4 3) (sourceB803 + difference 3 4) sourceC803) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3388) := by
    have ha : (tripleCharges (sourceA803 + difference 4 3) (sourceB803 + difference 3 4) sourceC803) = raw13292 := by
      apply Matrix.ext; unfold tripleCharges sourceA803 sourceB803 sourceC803 difference raw13292; decide +kernel
    rw [ha]
    exact (canonical13292 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA803 + difference 4 5) (sourceB803 + difference 5 4) sourceC803) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3580) := by
    have ha : (tripleCharges (sourceA803 + difference 4 5) (sourceB803 + difference 5 4) sourceC803) = raw13293 := by
      apply Matrix.ext; unfold tripleCharges sourceA803 sourceB803 sourceC803 difference raw13293; decide +kernel
    rw [ha]
    exact (canonical13293 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA803 + difference 5 0) (sourceB803 + difference 0 5) sourceC803) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1635) := by
    have ha : (tripleCharges (sourceA803 + difference 5 0) (sourceB803 + difference 0 5) sourceC803) = raw13294 := by
      apply Matrix.ext; unfold tripleCharges sourceA803 sourceB803 sourceC803 difference raw13294; decide +kernel
    rw [ha]
    exact (canonical13294 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA803 + difference 5 1) (sourceB803 + difference 1 5) sourceC803) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3557) := by
    have ha : (tripleCharges (sourceA803 + difference 5 1) (sourceB803 + difference 1 5) sourceC803) = raw13295 := by
      apply Matrix.ext; unfold tripleCharges sourceA803 sourceB803 sourceC803 difference raw13295; decide +kernel
    rw [ha]
    exact (canonical13295 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA803 + difference 5 2) (sourceB803 + difference 2 5) sourceC803) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3557) := by
    have ha : (tripleCharges (sourceA803 + difference 5 2) (sourceB803 + difference 2 5) sourceC803) = raw13296 := by
      apply Matrix.ext; unfold tripleCharges sourceA803 sourceB803 sourceC803 difference raw13296; decide +kernel
    rw [ha]
    exact (canonical13296 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA803 + difference 5 3) (sourceB803 + difference 3 5) sourceC803) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3375) := by
    have ha : (tripleCharges (sourceA803 + difference 5 3) (sourceB803 + difference 3 5) sourceC803) = raw13297 := by
      apply Matrix.ext; unfold tripleCharges sourceA803 sourceB803 sourceC803 difference raw13297; decide +kernel
    rw [ha]
    exact (canonical13297 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA803 + difference 5 4) (sourceB803 + difference 4 5) sourceC803) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3502) := by
    have ha : (tripleCharges (sourceA803 + difference 5 4) (sourceB803 + difference 4 5) sourceC803) = raw13298 := by
      apply Matrix.ext; unfold tripleCharges sourceA803 sourceB803 sourceC803 difference raw13298; decide +kernel
    rw [ha]
    exact (canonical13298 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA803 sourceB803 sourceC803
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm803, Integer.Sparse.eval]
  linarith only [hs]

def sourceA804 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB804 : Charge := ![2, -1, -1, 1, 0, -1]
def sourceC804 : Charge := ![1, 1, 1, -2, -1, 0]
def sourceForm804 : Integer.Sparse Master := [(Sum.inr 3074, 1), (Sum.inr 3875, 1), (Sum.inr 3974, 2), (Sum.inr 4008, 1), (Sum.inr 4010, 1), (Sum.inr 4091, -1)]

theorem sourceEq804 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm804 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA804 + difference 0 0) (sourceB804 + difference 0 0) sourceC804) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3074) := by
    have ha : (tripleCharges (sourceA804 + difference 0 0) (sourceB804 + difference 0 0) sourceC804) = raw13299 := by
      apply Matrix.ext; unfold tripleCharges sourceA804 sourceB804 sourceC804 difference raw13299; decide +kernel
    rw [ha]
    exact (canonical13299 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA804 + difference 0 1) (sourceB804 + difference 1 0) sourceC804) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3974) := by
    have ha : (tripleCharges (sourceA804 + difference 0 1) (sourceB804 + difference 1 0) sourceC804) = raw13300 := by
      apply Matrix.ext; unfold tripleCharges sourceA804 sourceB804 sourceC804 difference raw13300; decide +kernel
    rw [ha]
    exact (canonical13300 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA804 + difference 0 2) (sourceB804 + difference 2 0) sourceC804) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3974) := by
    have ha : (tripleCharges (sourceA804 + difference 0 2) (sourceB804 + difference 2 0) sourceC804) = raw13301 := by
      apply Matrix.ext; unfold tripleCharges sourceA804 sourceB804 sourceC804 difference raw13301; decide +kernel
    rw [ha]
    exact (canonical13301 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA804 + difference 0 3) (sourceB804 + difference 3 0) sourceC804) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3875) := by
    have ha : (tripleCharges (sourceA804 + difference 0 3) (sourceB804 + difference 3 0) sourceC804) = raw13302 := by
      apply Matrix.ext; unfold tripleCharges sourceA804 sourceB804 sourceC804 difference raw13302; decide +kernel
    rw [ha]
    exact (canonical13302 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA804 + difference 0 4) (sourceB804 + difference 4 0) sourceC804) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4008) := by
    have ha : (tripleCharges (sourceA804 + difference 0 4) (sourceB804 + difference 4 0) sourceC804) = raw13303 := by
      apply Matrix.ext; unfold tripleCharges sourceA804 sourceB804 sourceC804 difference raw13303; decide +kernel
    rw [ha]
    exact (canonical13303 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA804 + difference 0 5) (sourceB804 + difference 5 0) sourceC804) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4010) := by
    have ha : (tripleCharges (sourceA804 + difference 0 5) (sourceB804 + difference 5 0) sourceC804) = raw13304 := by
      apply Matrix.ext; unfold tripleCharges sourceA804 sourceB804 sourceC804 difference raw13304; decide +kernel
    rw [ha]
    exact (canonical13304 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA804 + sourceB804) sourceC804) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA804 + sourceB804) sourceC804) = raw13305 := by
      apply Matrix.ext; unfold doubleCharges sourceA804 sourceB804 sourceC804 raw13305; decide +kernel
    rw [ha]
    exact (canonical13305 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA804 sourceB804 sourceC804
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm804, Integer.Sparse.eval]
  linarith only [hs]

def sourceA805 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB805 : Charge := ![2, -1, -1, 1, 0, -1]
def sourceC805 : Charge := ![1, 1, 1, -2, -1, 0]
def sourceForm805 : Integer.Sparse Master := [(Sum.inr 1383, 1), (Sum.inr 1384, 1), (Sum.inr 1387, 1), (Sum.inr 1403, 2), (Sum.inr 3074, 1), (Sum.inr 4091, -1)]

theorem sourceEq805 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm805 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA805 + difference 0 0) (sourceB805 + difference 0 0) sourceC805) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3074) := by
    have ha : (tripleCharges (sourceA805 + difference 0 0) (sourceB805 + difference 0 0) sourceC805) = raw13299 := by
      apply Matrix.ext; unfold tripleCharges sourceA805 sourceB805 sourceC805 difference raw13299; decide +kernel
    rw [ha]
    exact (canonical13299 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA805 + difference 1 0) (sourceB805 + difference 0 1) sourceC805) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1403) := by
    have ha : (tripleCharges (sourceA805 + difference 1 0) (sourceB805 + difference 0 1) sourceC805) = raw13306 := by
      apply Matrix.ext; unfold tripleCharges sourceA805 sourceB805 sourceC805 difference raw13306; decide +kernel
    rw [ha]
    exact (canonical13306 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA805 + difference 2 0) (sourceB805 + difference 0 2) sourceC805) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1403) := by
    have ha : (tripleCharges (sourceA805 + difference 2 0) (sourceB805 + difference 0 2) sourceC805) = raw13307 := by
      apply Matrix.ext; unfold tripleCharges sourceA805 sourceB805 sourceC805 difference raw13307; decide +kernel
    rw [ha]
    exact (canonical13307 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA805 + difference 3 0) (sourceB805 + difference 0 3) sourceC805) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1383) := by
    have ha : (tripleCharges (sourceA805 + difference 3 0) (sourceB805 + difference 0 3) sourceC805) = raw13308 := by
      apply Matrix.ext; unfold tripleCharges sourceA805 sourceB805 sourceC805 difference raw13308; decide +kernel
    rw [ha]
    exact (canonical13308 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA805 + difference 4 0) (sourceB805 + difference 0 4) sourceC805) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1384) := by
    have ha : (tripleCharges (sourceA805 + difference 4 0) (sourceB805 + difference 0 4) sourceC805) = raw13309 := by
      apply Matrix.ext; unfold tripleCharges sourceA805 sourceB805 sourceC805 difference raw13309; decide +kernel
    rw [ha]
    exact (canonical13309 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA805 + difference 5 0) (sourceB805 + difference 0 5) sourceC805) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1387) := by
    have ha : (tripleCharges (sourceA805 + difference 5 0) (sourceB805 + difference 0 5) sourceC805) = raw13310 := by
      apply Matrix.ext; unfold tripleCharges sourceA805 sourceB805 sourceC805 difference raw13310; decide +kernel
    rw [ha]
    exact (canonical13310 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA805 + sourceB805) sourceC805) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA805 + sourceB805) sourceC805) = raw13305 := by
      apply Matrix.ext; unfold doubleCharges sourceA805 sourceB805 sourceC805 raw13305; decide +kernel
    rw [ha]
    exact (canonical13305 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA805 sourceB805 sourceC805
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm805, Integer.Sparse.eval]
  linarith only [hs]

def sourceA806 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB806 : Charge := ![2, -1, -1, 1, 0, -1]
def sourceC806 : Charge := ![1, 1, 1, -2, -1, 0]
def sourceForm806 : Integer.Sparse Master := [(Sum.inr 2924, 1), (Sum.inr 2925, 1), (Sum.inr 2928, 1), (Sum.inr 2951, 1), (Sum.inr 3074, 1), (Sum.inr 3974, 1), (Sum.inr 4091, -1)]

theorem sourceEq806 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm806 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA806 + difference 0 1) (sourceB806 + difference 1 0) sourceC806) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3974) := by
    have ha : (tripleCharges (sourceA806 + difference 0 1) (sourceB806 + difference 1 0) sourceC806) = raw13300 := by
      apply Matrix.ext; unfold tripleCharges sourceA806 sourceB806 sourceC806 difference raw13300; decide +kernel
    rw [ha]
    exact (canonical13300 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA806 + difference 1 1) (sourceB806 + difference 1 1) sourceC806) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3074) := by
    have ha : (tripleCharges (sourceA806 + difference 1 1) (sourceB806 + difference 1 1) sourceC806) = raw13299 := by
      apply Matrix.ext; unfold tripleCharges sourceA806 sourceB806 sourceC806 difference raw13299; decide +kernel
    rw [ha]
    exact (canonical13299 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA806 + difference 2 1) (sourceB806 + difference 1 2) sourceC806) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2951) := by
    have ha : (tripleCharges (sourceA806 + difference 2 1) (sourceB806 + difference 1 2) sourceC806) = raw13311 := by
      apply Matrix.ext; unfold tripleCharges sourceA806 sourceB806 sourceC806 difference raw13311; decide +kernel
    rw [ha]
    exact (canonical13311 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA806 + difference 3 1) (sourceB806 + difference 1 3) sourceC806) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2924) := by
    have ha : (tripleCharges (sourceA806 + difference 3 1) (sourceB806 + difference 1 3) sourceC806) = raw13312 := by
      apply Matrix.ext; unfold tripleCharges sourceA806 sourceB806 sourceC806 difference raw13312; decide +kernel
    rw [ha]
    exact (canonical13312 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA806 + difference 4 1) (sourceB806 + difference 1 4) sourceC806) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2925) := by
    have ha : (tripleCharges (sourceA806 + difference 4 1) (sourceB806 + difference 1 4) sourceC806) = raw13313 := by
      apply Matrix.ext; unfold tripleCharges sourceA806 sourceB806 sourceC806 difference raw13313; decide +kernel
    rw [ha]
    exact (canonical13313 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA806 + difference 5 1) (sourceB806 + difference 1 5) sourceC806) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2928) := by
    have ha : (tripleCharges (sourceA806 + difference 5 1) (sourceB806 + difference 1 5) sourceC806) = raw13314 := by
      apply Matrix.ext; unfold tripleCharges sourceA806 sourceB806 sourceC806 difference raw13314; decide +kernel
    rw [ha]
    exact (canonical13314 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA806 + sourceB806) sourceC806) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA806 + sourceB806) sourceC806) = raw13305 := by
      apply Matrix.ext; unfold doubleCharges sourceA806 sourceB806 sourceC806 raw13305; decide +kernel
    rw [ha]
    exact (canonical13305 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA806 sourceB806 sourceC806
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm806, Integer.Sparse.eval]
  linarith only [hs]

def sourceA807 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB807 : Charge := ![2, -1, -1, 1, 0, -1]
def sourceC807 : Charge := ![1, 1, 1, -2, -1, 0]
def sourceForm807 : Integer.Sparse Master := [(Sum.inr 3068, 1), (Sum.inr 3069, 1), (Sum.inr 3074, 1), (Sum.inr 3091, 2), (Sum.inr 3875, 1), (Sum.inr 4091, -1)]

theorem sourceEq807 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm807 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA807 + difference 0 3) (sourceB807 + difference 3 0) sourceC807) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3875) := by
    have ha : (tripleCharges (sourceA807 + difference 0 3) (sourceB807 + difference 3 0) sourceC807) = raw13302 := by
      apply Matrix.ext; unfold tripleCharges sourceA807 sourceB807 sourceC807 difference raw13302; decide +kernel
    rw [ha]
    exact (canonical13302 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA807 + difference 1 3) (sourceB807 + difference 3 1) sourceC807) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3091) := by
    have ha : (tripleCharges (sourceA807 + difference 1 3) (sourceB807 + difference 3 1) sourceC807) = raw13315 := by
      apply Matrix.ext; unfold tripleCharges sourceA807 sourceB807 sourceC807 difference raw13315; decide +kernel
    rw [ha]
    exact (canonical13315 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA807 + difference 2 3) (sourceB807 + difference 3 2) sourceC807) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3091) := by
    have ha : (tripleCharges (sourceA807 + difference 2 3) (sourceB807 + difference 3 2) sourceC807) = raw13316 := by
      apply Matrix.ext; unfold tripleCharges sourceA807 sourceB807 sourceC807 difference raw13316; decide +kernel
    rw [ha]
    exact (canonical13316 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA807 + difference 3 3) (sourceB807 + difference 3 3) sourceC807) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3074) := by
    have ha : (tripleCharges (sourceA807 + difference 3 3) (sourceB807 + difference 3 3) sourceC807) = raw13299 := by
      apply Matrix.ext; unfold tripleCharges sourceA807 sourceB807 sourceC807 difference raw13299; decide +kernel
    rw [ha]
    exact (canonical13299 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA807 + difference 4 3) (sourceB807 + difference 3 4) sourceC807) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3068) := by
    have ha : (tripleCharges (sourceA807 + difference 4 3) (sourceB807 + difference 3 4) sourceC807) = raw13317 := by
      apply Matrix.ext; unfold tripleCharges sourceA807 sourceB807 sourceC807 difference raw13317; decide +kernel
    rw [ha]
    exact (canonical13317 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA807 + difference 5 3) (sourceB807 + difference 3 5) sourceC807) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3069) := by
    have ha : (tripleCharges (sourceA807 + difference 5 3) (sourceB807 + difference 3 5) sourceC807) = raw13318 := by
      apply Matrix.ext; unfold tripleCharges sourceA807 sourceB807 sourceC807 difference raw13318; decide +kernel
    rw [ha]
    exact (canonical13318 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA807 + sourceB807) sourceC807) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA807 + sourceB807) sourceC807) = raw13305 := by
      apply Matrix.ext; unfold doubleCharges sourceA807 sourceB807 sourceC807 raw13305; decide +kernel
    rw [ha]
    exact (canonical13305 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA807 sourceB807 sourceC807
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm807, Integer.Sparse.eval]
  linarith only [hs]

def sourceA808 : Charge := ![1, 1, 1, -2, -1, 0]
def sourceB808 : Charge := ![2, -1, -1, 1, 0, -1]
def sourceC808 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceForm808 : Integer.Sparse Master := [(Sum.inr 4851, 1), (Sum.inr 4852, 2), (Sum.inr 4864, 1), (Sum.inr 4887, 1), (Sum.inr 5143, 2), (Sum.inr 5150, 1), (Sum.inr 5157, 1), (Sum.inr 5246, 1), (Sum.inr 5247, 1), (Sum.inr 5271, 2), (Sum.inr 5278, 1), (Sum.inr 5280, 1), (Sum.inr 5281, 2), (Sum.inr 5283, 1), (Sum.inr 5285, 2), (Sum.inr 5286, 2), (Sum.inr 5289, 2), (Sum.inr 5290, 2), (Sum.inr 5292, 2), (Sum.inr 5299, 2)]

theorem sourceEq808 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm808 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA808 + difference 0 1) (sourceB808 + difference 1 0) sourceC808) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA808 + difference 0 1) (sourceB808 + difference 1 0) sourceC808) = raw12463 := by
      apply Matrix.ext; unfold tripleCharges sourceA808 sourceB808 sourceC808 difference raw12463; decide +kernel
    rw [ha]
    exact (canonical12463 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA808 + difference 0 2) (sourceB808 + difference 2 0) sourceC808) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA808 + difference 0 2) (sourceB808 + difference 2 0) sourceC808) = raw13319 := by
      apply Matrix.ext; unfold tripleCharges sourceA808 sourceB808 sourceC808 difference raw13319; decide +kernel
    rw [ha]
    exact (canonical13319 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA808 + difference 0 3) (sourceB808 + difference 3 0) sourceC808) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5150) := by
    have ha : (tripleCharges (sourceA808 + difference 0 3) (sourceB808 + difference 3 0) sourceC808) = raw13320 := by
      apply Matrix.ext; unfold tripleCharges sourceA808 sourceB808 sourceC808 difference raw13320; decide +kernel
    rw [ha]
    exact (canonical13320 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA808 + difference 0 4) (sourceB808 + difference 4 0) sourceC808) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5246) := by
    have ha : (tripleCharges (sourceA808 + difference 0 4) (sourceB808 + difference 4 0) sourceC808) = raw13321 := by
      apply Matrix.ext; unfold tripleCharges sourceA808 sourceB808 sourceC808 difference raw13321; decide +kernel
    rw [ha]
    exact (canonical13321 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA808 + difference 0 5) (sourceB808 + difference 5 0) sourceC808) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5247) := by
    have ha : (tripleCharges (sourceA808 + difference 0 5) (sourceB808 + difference 5 0) sourceC808) = raw13322 := by
      apply Matrix.ext; unfold tripleCharges sourceA808 sourceB808 sourceC808 difference raw13322; decide +kernel
    rw [ha]
    exact (canonical13322 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA808 + difference 1 0) (sourceB808 + difference 0 1) sourceC808) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4852) := by
    have ha : (tripleCharges (sourceA808 + difference 1 0) (sourceB808 + difference 0 1) sourceC808) = raw13323 := by
      apply Matrix.ext; unfold tripleCharges sourceA808 sourceB808 sourceC808 difference raw13323; decide +kernel
    rw [ha]
    exact (canonical13323 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA808 + difference 1 2) (sourceB808 + difference 2 1) sourceC808) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA808 + difference 1 2) (sourceB808 + difference 2 1) sourceC808) = raw13324 := by
      apply Matrix.ext; unfold tripleCharges sourceA808 sourceB808 sourceC808 difference raw13324; decide +kernel
    rw [ha]
    exact (canonical13324 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA808 + difference 1 3) (sourceB808 + difference 3 1) sourceC808) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5143) := by
    have ha : (tripleCharges (sourceA808 + difference 1 3) (sourceB808 + difference 3 1) sourceC808) = raw13325 := by
      apply Matrix.ext; unfold tripleCharges sourceA808 sourceB808 sourceC808 difference raw13325; decide +kernel
    rw [ha]
    exact (canonical13325 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA808 + difference 1 4) (sourceB808 + difference 4 1) sourceC808) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5285) := by
    have ha : (tripleCharges (sourceA808 + difference 1 4) (sourceB808 + difference 4 1) sourceC808) = raw13326 := by
      apply Matrix.ext; unfold tripleCharges sourceA808 sourceB808 sourceC808 difference raw13326; decide +kernel
    rw [ha]
    exact (canonical13326 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA808 + difference 1 5) (sourceB808 + difference 5 1) sourceC808) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5286) := by
    have ha : (tripleCharges (sourceA808 + difference 1 5) (sourceB808 + difference 5 1) sourceC808) = raw13327 := by
      apply Matrix.ext; unfold tripleCharges sourceA808 sourceB808 sourceC808 difference raw13327; decide +kernel
    rw [ha]
    exact (canonical13327 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA808 + difference 2 0) (sourceB808 + difference 0 2) sourceC808) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4852) := by
    have ha : (tripleCharges (sourceA808 + difference 2 0) (sourceB808 + difference 0 2) sourceC808) = raw12884 := by
      apply Matrix.ext; unfold tripleCharges sourceA808 sourceB808 sourceC808 difference raw12884; decide +kernel
    rw [ha]
    exact (canonical12884 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA808 + difference 2 1) (sourceB808 + difference 1 2) sourceC808) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA808 + difference 2 1) (sourceB808 + difference 1 2) sourceC808) = raw12003 := by
      apply Matrix.ext; unfold tripleCharges sourceA808 sourceB808 sourceC808 difference raw12003; decide +kernel
    rw [ha]
    exact (canonical12003 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA808 + difference 2 3) (sourceB808 + difference 3 2) sourceC808) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5143) := by
    have ha : (tripleCharges (sourceA808 + difference 2 3) (sourceB808 + difference 3 2) sourceC808) = raw12885 := by
      apply Matrix.ext; unfold tripleCharges sourceA808 sourceB808 sourceC808 difference raw12885; decide +kernel
    rw [ha]
    exact (canonical12885 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA808 + difference 2 4) (sourceB808 + difference 4 2) sourceC808) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5285) := by
    have ha : (tripleCharges (sourceA808 + difference 2 4) (sourceB808 + difference 4 2) sourceC808) = raw12886 := by
      apply Matrix.ext; unfold tripleCharges sourceA808 sourceB808 sourceC808 difference raw12886; decide +kernel
    rw [ha]
    exact (canonical12886 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA808 + difference 2 5) (sourceB808 + difference 5 2) sourceC808) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5286) := by
    have ha : (tripleCharges (sourceA808 + difference 2 5) (sourceB808 + difference 5 2) sourceC808) = raw12887 := by
      apply Matrix.ext; unfold tripleCharges sourceA808 sourceB808 sourceC808 difference raw12887; decide +kernel
    rw [ha]
    exact (canonical12887 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA808 + difference 3 0) (sourceB808 + difference 0 3) sourceC808) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4887) := by
    have ha : (tripleCharges (sourceA808 + difference 3 0) (sourceB808 + difference 0 3) sourceC808) = raw12653 := by
      apply Matrix.ext; unfold tripleCharges sourceA808 sourceB808 sourceC808 difference raw12653; decide +kernel
    rw [ha]
    exact (canonical12653 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA808 + difference 3 1) (sourceB808 + difference 1 3) sourceC808) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA808 + difference 3 1) (sourceB808 + difference 1 3) sourceC808) = raw11669 := by
      apply Matrix.ext; unfold tripleCharges sourceA808 sourceB808 sourceC808 difference raw11669; decide +kernel
    rw [ha]
    exact (canonical11669 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA808 + difference 3 2) (sourceB808 + difference 2 3) sourceC808) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA808 + difference 3 2) (sourceB808 + difference 2 3) sourceC808) = raw12191 := by
      apply Matrix.ext; unfold tripleCharges sourceA808 sourceB808 sourceC808 difference raw12191; decide +kernel
    rw [ha]
    exact (canonical12191 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA808 + difference 3 4) (sourceB808 + difference 4 3) sourceC808) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5281) := by
    have ha : (tripleCharges (sourceA808 + difference 3 4) (sourceB808 + difference 4 3) sourceC808) = raw12654 := by
      apply Matrix.ext; unfold tripleCharges sourceA808 sourceB808 sourceC808 difference raw12654; decide +kernel
    rw [ha]
    exact (canonical12654 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA808 + difference 3 5) (sourceB808 + difference 5 3) sourceC808) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5283) := by
    have ha : (tripleCharges (sourceA808 + difference 3 5) (sourceB808 + difference 5 3) sourceC808) = raw12655 := by
      apply Matrix.ext; unfold tripleCharges sourceA808 sourceB808 sourceC808 difference raw12655; decide +kernel
    rw [ha]
    exact (canonical12655 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA808 + difference 4 0) (sourceB808 + difference 0 4) sourceC808) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4864) := by
    have ha : (tripleCharges (sourceA808 + difference 4 0) (sourceB808 + difference 0 4) sourceC808) = raw13328 := by
      apply Matrix.ext; unfold tripleCharges sourceA808 sourceB808 sourceC808 difference raw13328; decide +kernel
    rw [ha]
    exact (canonical13328 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA808 + difference 4 1) (sourceB808 + difference 1 4) sourceC808) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA808 + difference 4 1) (sourceB808 + difference 1 4) sourceC808) = raw12473 := by
      apply Matrix.ext; unfold tripleCharges sourceA808 sourceB808 sourceC808 difference raw12473; decide +kernel
    rw [ha]
    exact (canonical12473 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA808 + difference 4 2) (sourceB808 + difference 2 4) sourceC808) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA808 + difference 4 2) (sourceB808 + difference 2 4) sourceC808) = raw13329 := by
      apply Matrix.ext; unfold tripleCharges sourceA808 sourceB808 sourceC808 difference raw13329; decide +kernel
    rw [ha]
    exact (canonical13329 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA808 + difference 4 3) (sourceB808 + difference 3 4) sourceC808) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5278) := by
    have ha : (tripleCharges (sourceA808 + difference 4 3) (sourceB808 + difference 3 4) sourceC808) = raw13330 := by
      apply Matrix.ext; unfold tripleCharges sourceA808 sourceB808 sourceC808 difference raw13330; decide +kernel
    rw [ha]
    exact (canonical13330 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA808 + difference 4 5) (sourceB808 + difference 5 4) sourceC808) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5281) := by
    have ha : (tripleCharges (sourceA808 + difference 4 5) (sourceB808 + difference 5 4) sourceC808) = raw13331 := by
      apply Matrix.ext; unfold tripleCharges sourceA808 sourceB808 sourceC808 difference raw13331; decide +kernel
    rw [ha]
    exact (canonical13331 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA808 + difference 5 0) (sourceB808 + difference 0 5) sourceC808) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4851) := by
    have ha : (tripleCharges (sourceA808 + difference 5 0) (sourceB808 + difference 0 5) sourceC808) = raw12464 := by
      apply Matrix.ext; unfold tripleCharges sourceA808 sourceB808 sourceC808 difference raw12464; decide +kernel
    rw [ha]
    exact (canonical12464 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA808 + difference 5 1) (sourceB808 + difference 1 5) sourceC808) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA808 + difference 5 1) (sourceB808 + difference 1 5) sourceC808) = raw11667 := by
      apply Matrix.ext; unfold tripleCharges sourceA808 sourceB808 sourceC808 difference raw11667; decide +kernel
    rw [ha]
    exact (canonical11667 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA808 + difference 5 2) (sourceB808 + difference 2 5) sourceC808) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA808 + difference 5 2) (sourceB808 + difference 2 5) sourceC808) = raw12189 := by
      apply Matrix.ext; unfold tripleCharges sourceA808 sourceB808 sourceC808 difference raw12189; decide +kernel
    rw [ha]
    exact (canonical12189 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA808 + difference 5 3) (sourceB808 + difference 3 5) sourceC808) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5157) := by
    have ha : (tripleCharges (sourceA808 + difference 5 3) (sourceB808 + difference 3 5) sourceC808) = raw12465 := by
      apply Matrix.ext; unfold tripleCharges sourceA808 sourceB808 sourceC808 difference raw12465; decide +kernel
    rw [ha]
    exact (canonical12465 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA808 + difference 5 4) (sourceB808 + difference 4 5) sourceC808) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5280) := by
    have ha : (tripleCharges (sourceA808 + difference 5 4) (sourceB808 + difference 4 5) sourceC808) = raw12466 := by
      apply Matrix.ext; unfold tripleCharges sourceA808 sourceB808 sourceC808 difference raw12466; decide +kernel
    rw [ha]
    exact (canonical12466 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA808 sourceB808 sourceC808
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm808, Integer.Sparse.eval]
  linarith only [hs]

def sourceA809 : Charge := ![1, 1, 1, -2, -1, 0]
def sourceB809 : Charge := ![2, -1, -1, 1, 0, -1]
def sourceC809 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceForm809 : Integer.Sparse Master := [(Sum.inr 2240, 1), (Sum.inr 2241, 1), (Sum.inr 2243, 1), (Sum.inr 2250, 2), (Sum.inr 2565, 2), (Sum.inr 2573, 1), (Sum.inr 2583, 1), (Sum.inr 2747, 1), (Sum.inr 2749, 1), (Sum.inr 2750, 2), (Sum.inr 2752, 1), (Sum.inr 2756, 2), (Sum.inr 2757, 2), (Sum.inr 2763, 2), (Sum.inr 2764, 2), (Sum.inr 2766, 2), (Sum.inr 2773, 2), (Sum.inr 3104, 1), (Sum.inr 3105, 1), (Sum.inr 3109, 2)]

theorem sourceEq809 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm809 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA809 + difference 0 1) (sourceB809 + difference 1 0) sourceC809) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3109) := by
    have ha : (tripleCharges (sourceA809 + difference 0 1) (sourceB809 + difference 1 0) sourceC809) = raw12480 := by
      apply Matrix.ext; unfold tripleCharges sourceA809 sourceB809 sourceC809 difference raw12480; decide +kernel
    rw [ha]
    exact (canonical12480 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA809 + difference 0 2) (sourceB809 + difference 2 0) sourceC809) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3109) := by
    have ha : (tripleCharges (sourceA809 + difference 0 2) (sourceB809 + difference 2 0) sourceC809) = raw13332 := by
      apply Matrix.ext; unfold tripleCharges sourceA809 sourceB809 sourceC809 difference raw13332; decide +kernel
    rw [ha]
    exact (canonical13332 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA809 + difference 0 3) (sourceB809 + difference 3 0) sourceC809) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2573) := by
    have ha : (tripleCharges (sourceA809 + difference 0 3) (sourceB809 + difference 3 0) sourceC809) = raw13333 := by
      apply Matrix.ext; unfold tripleCharges sourceA809 sourceB809 sourceC809 difference raw13333; decide +kernel
    rw [ha]
    exact (canonical13333 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA809 + difference 0 4) (sourceB809 + difference 4 0) sourceC809) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3104) := by
    have ha : (tripleCharges (sourceA809 + difference 0 4) (sourceB809 + difference 4 0) sourceC809) = raw13334 := by
      apply Matrix.ext; unfold tripleCharges sourceA809 sourceB809 sourceC809 difference raw13334; decide +kernel
    rw [ha]
    exact (canonical13334 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA809 + difference 0 5) (sourceB809 + difference 5 0) sourceC809) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3105) := by
    have ha : (tripleCharges (sourceA809 + difference 0 5) (sourceB809 + difference 5 0) sourceC809) = raw13335 := by
      apply Matrix.ext; unfold tripleCharges sourceA809 sourceB809 sourceC809 difference raw13335; decide +kernel
    rw [ha]
    exact (canonical13335 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA809 + difference 1 0) (sourceB809 + difference 0 1) sourceC809) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2250) := by
    have ha : (tripleCharges (sourceA809 + difference 1 0) (sourceB809 + difference 0 1) sourceC809) = raw13336 := by
      apply Matrix.ext; unfold tripleCharges sourceA809 sourceB809 sourceC809 difference raw13336; decide +kernel
    rw [ha]
    exact (canonical13336 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA809 + difference 1 2) (sourceB809 + difference 2 1) sourceC809) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2773) := by
    have ha : (tripleCharges (sourceA809 + difference 1 2) (sourceB809 + difference 2 1) sourceC809) = raw13337 := by
      apply Matrix.ext; unfold tripleCharges sourceA809 sourceB809 sourceC809 difference raw13337; decide +kernel
    rw [ha]
    exact (canonical13337 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA809 + difference 1 3) (sourceB809 + difference 3 1) sourceC809) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2565) := by
    have ha : (tripleCharges (sourceA809 + difference 1 3) (sourceB809 + difference 3 1) sourceC809) = raw13338 := by
      apply Matrix.ext; unfold tripleCharges sourceA809 sourceB809 sourceC809 difference raw13338; decide +kernel
    rw [ha]
    exact (canonical13338 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA809 + difference 1 4) (sourceB809 + difference 4 1) sourceC809) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2756) := by
    have ha : (tripleCharges (sourceA809 + difference 1 4) (sourceB809 + difference 4 1) sourceC809) = raw13339 := by
      apply Matrix.ext; unfold tripleCharges sourceA809 sourceB809 sourceC809 difference raw13339; decide +kernel
    rw [ha]
    exact (canonical13339 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA809 + difference 1 5) (sourceB809 + difference 5 1) sourceC809) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2757) := by
    have ha : (tripleCharges (sourceA809 + difference 1 5) (sourceB809 + difference 5 1) sourceC809) = raw13340 := by
      apply Matrix.ext; unfold tripleCharges sourceA809 sourceB809 sourceC809 difference raw13340; decide +kernel
    rw [ha]
    exact (canonical13340 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA809 + difference 2 0) (sourceB809 + difference 0 2) sourceC809) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2250) := by
    have ha : (tripleCharges (sourceA809 + difference 2 0) (sourceB809 + difference 0 2) sourceC809) = raw12898 := by
      apply Matrix.ext; unfold tripleCharges sourceA809 sourceB809 sourceC809 difference raw12898; decide +kernel
    rw [ha]
    exact (canonical12898 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA809 + difference 2 1) (sourceB809 + difference 1 2) sourceC809) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2773) := by
    have ha : (tripleCharges (sourceA809 + difference 2 1) (sourceB809 + difference 1 2) sourceC809) = raw12025 := by
      apply Matrix.ext; unfold tripleCharges sourceA809 sourceB809 sourceC809 difference raw12025; decide +kernel
    rw [ha]
    exact (canonical12025 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA809 + difference 2 3) (sourceB809 + difference 3 2) sourceC809) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2565) := by
    have ha : (tripleCharges (sourceA809 + difference 2 3) (sourceB809 + difference 3 2) sourceC809) = raw12899 := by
      apply Matrix.ext; unfold tripleCharges sourceA809 sourceB809 sourceC809 difference raw12899; decide +kernel
    rw [ha]
    exact (canonical12899 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA809 + difference 2 4) (sourceB809 + difference 4 2) sourceC809) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2756) := by
    have ha : (tripleCharges (sourceA809 + difference 2 4) (sourceB809 + difference 4 2) sourceC809) = raw12900 := by
      apply Matrix.ext; unfold tripleCharges sourceA809 sourceB809 sourceC809 difference raw12900; decide +kernel
    rw [ha]
    exact (canonical12900 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA809 + difference 2 5) (sourceB809 + difference 5 2) sourceC809) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2757) := by
    have ha : (tripleCharges (sourceA809 + difference 2 5) (sourceB809 + difference 5 2) sourceC809) = raw12901 := by
      apply Matrix.ext; unfold tripleCharges sourceA809 sourceB809 sourceC809 difference raw12901; decide +kernel
    rw [ha]
    exact (canonical12901 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA809 + difference 3 0) (sourceB809 + difference 0 3) sourceC809) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2243) := by
    have ha : (tripleCharges (sourceA809 + difference 3 0) (sourceB809 + difference 0 3) sourceC809) = raw13341 := by
      apply Matrix.ext; unfold tripleCharges sourceA809 sourceB809 sourceC809 difference raw13341; decide +kernel
    rw [ha]
    exact (canonical13341 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA809 + difference 3 1) (sourceB809 + difference 1 3) sourceC809) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2766) := by
    have ha : (tripleCharges (sourceA809 + difference 3 1) (sourceB809 + difference 1 3) sourceC809) = raw11699 := by
      apply Matrix.ext; unfold tripleCharges sourceA809 sourceB809 sourceC809 difference raw11699; decide +kernel
    rw [ha]
    exact (canonical11699 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA809 + difference 3 2) (sourceB809 + difference 2 3) sourceC809) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2766) := by
    have ha : (tripleCharges (sourceA809 + difference 3 2) (sourceB809 + difference 2 3) sourceC809) = raw13342 := by
      apply Matrix.ext; unfold tripleCharges sourceA809 sourceB809 sourceC809 difference raw13342; decide +kernel
    rw [ha]
    exact (canonical13342 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA809 + difference 3 4) (sourceB809 + difference 4 3) sourceC809) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2750) := by
    have ha : (tripleCharges (sourceA809 + difference 3 4) (sourceB809 + difference 4 3) sourceC809) = raw13343 := by
      apply Matrix.ext; unfold tripleCharges sourceA809 sourceB809 sourceC809 difference raw13343; decide +kernel
    rw [ha]
    exact (canonical13343 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA809 + difference 3 5) (sourceB809 + difference 5 3) sourceC809) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2752) := by
    have ha : (tripleCharges (sourceA809 + difference 3 5) (sourceB809 + difference 5 3) sourceC809) = raw13344 := by
      apply Matrix.ext; unfold tripleCharges sourceA809 sourceB809 sourceC809 difference raw13344; decide +kernel
    rw [ha]
    exact (canonical13344 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA809 + difference 4 0) (sourceB809 + difference 0 4) sourceC809) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2241) := by
    have ha : (tripleCharges (sourceA809 + difference 4 0) (sourceB809 + difference 0 4) sourceC809) = raw13345 := by
      apply Matrix.ext; unfold tripleCharges sourceA809 sourceB809 sourceC809 difference raw13345; decide +kernel
    rw [ha]
    exact (canonical13345 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA809 + difference 4 1) (sourceB809 + difference 1 4) sourceC809) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2764) := by
    have ha : (tripleCharges (sourceA809 + difference 4 1) (sourceB809 + difference 1 4) sourceC809) = raw12492 := by
      apply Matrix.ext; unfold tripleCharges sourceA809 sourceB809 sourceC809 difference raw12492; decide +kernel
    rw [ha]
    exact (canonical12492 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA809 + difference 4 2) (sourceB809 + difference 2 4) sourceC809) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2764) := by
    have ha : (tripleCharges (sourceA809 + difference 4 2) (sourceB809 + difference 2 4) sourceC809) = raw13346 := by
      apply Matrix.ext; unfold tripleCharges sourceA809 sourceB809 sourceC809 difference raw13346; decide +kernel
    rw [ha]
    exact (canonical13346 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA809 + difference 4 3) (sourceB809 + difference 3 4) sourceC809) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2747) := by
    have ha : (tripleCharges (sourceA809 + difference 4 3) (sourceB809 + difference 3 4) sourceC809) = raw13347 := by
      apply Matrix.ext; unfold tripleCharges sourceA809 sourceB809 sourceC809 difference raw13347; decide +kernel
    rw [ha]
    exact (canonical13347 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA809 + difference 4 5) (sourceB809 + difference 5 4) sourceC809) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2750) := by
    have ha : (tripleCharges (sourceA809 + difference 4 5) (sourceB809 + difference 5 4) sourceC809) = raw13348 := by
      apply Matrix.ext; unfold tripleCharges sourceA809 sourceB809 sourceC809 difference raw13348; decide +kernel
    rw [ha]
    exact (canonical13348 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA809 + difference 5 0) (sourceB809 + difference 0 5) sourceC809) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2240) := by
    have ha : (tripleCharges (sourceA809 + difference 5 0) (sourceB809 + difference 0 5) sourceC809) = raw12481 := by
      apply Matrix.ext; unfold tripleCharges sourceA809 sourceB809 sourceC809 difference raw12481; decide +kernel
    rw [ha]
    exact (canonical12481 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA809 + difference 5 1) (sourceB809 + difference 1 5) sourceC809) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2763) := by
    have ha : (tripleCharges (sourceA809 + difference 5 1) (sourceB809 + difference 1 5) sourceC809) = raw11697 := by
      apply Matrix.ext; unfold tripleCharges sourceA809 sourceB809 sourceC809 difference raw11697; decide +kernel
    rw [ha]
    exact (canonical11697 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA809 + difference 5 2) (sourceB809 + difference 2 5) sourceC809) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2763) := by
    have ha : (tripleCharges (sourceA809 + difference 5 2) (sourceB809 + difference 2 5) sourceC809) = raw12482 := by
      apply Matrix.ext; unfold tripleCharges sourceA809 sourceB809 sourceC809 difference raw12482; decide +kernel
    rw [ha]
    exact (canonical12482 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA809 + difference 5 3) (sourceB809 + difference 3 5) sourceC809) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2583) := by
    have ha : (tripleCharges (sourceA809 + difference 5 3) (sourceB809 + difference 3 5) sourceC809) = raw12483 := by
      apply Matrix.ext; unfold tripleCharges sourceA809 sourceB809 sourceC809 difference raw12483; decide +kernel
    rw [ha]
    exact (canonical12483 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA809 + difference 5 4) (sourceB809 + difference 4 5) sourceC809) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2749) := by
    have ha : (tripleCharges (sourceA809 + difference 5 4) (sourceB809 + difference 4 5) sourceC809) = raw12484 := by
      apply Matrix.ext; unfold tripleCharges sourceA809 sourceB809 sourceC809 difference raw12484; decide +kernel
    rw [ha]
    exact (canonical12484 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA809 sourceB809 sourceC809
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm809, Integer.Sparse.eval]
  linarith only [hs]

def sourceA810 : Charge := ![1, 1, 1, -2, -1, 0]
def sourceB810 : Charge := ![2, -1, -1, 1, 0, -1]
def sourceC810 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceForm810 : Integer.Sparse Master := [(Sum.inr 2700, 1), (Sum.inr 2701, 1), (Sum.inr 2703, 1), (Sum.inr 2739, 2), (Sum.inr 3020, 2), (Sum.inr 3021, 2), (Sum.inr 3023, 2), (Sum.inr 3051, 2), (Sum.inr 3070, 1), (Sum.inr 3071, 1), (Sum.inr 3073, 1), (Sum.inr 3074, 2), (Sum.inr 3076, 1), (Sum.inr 3097, 2), (Sum.inr 3099, 2), (Sum.inr 3100, 2), (Sum.inr 3170, 2), (Sum.inr 3172, 1), (Sum.inr 3182, 1), (Sum.inr 3226, 1)]

theorem sourceEq810 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm810 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA810 + difference 0 1) (sourceB810 + difference 1 0) sourceC810) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2739) := by
    have ha : (tripleCharges (sourceA810 + difference 0 1) (sourceB810 + difference 1 0) sourceC810) = raw12499 := by
      apply Matrix.ext; unfold tripleCharges sourceA810 sourceB810 sourceC810 difference raw12499; decide +kernel
    rw [ha]
    exact (canonical12499 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA810 + difference 0 2) (sourceB810 + difference 2 0) sourceC810) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2739) := by
    have ha : (tripleCharges (sourceA810 + difference 0 2) (sourceB810 + difference 2 0) sourceC810) = raw13349 := by
      apply Matrix.ext; unfold tripleCharges sourceA810 sourceB810 sourceC810 difference raw13349; decide +kernel
    rw [ha]
    exact (canonical13349 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA810 + difference 0 3) (sourceB810 + difference 3 0) sourceC810) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2700) := by
    have ha : (tripleCharges (sourceA810 + difference 0 3) (sourceB810 + difference 3 0) sourceC810) = raw13350 := by
      apply Matrix.ext; unfold tripleCharges sourceA810 sourceB810 sourceC810 difference raw13350; decide +kernel
    rw [ha]
    exact (canonical13350 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA810 + difference 0 4) (sourceB810 + difference 4 0) sourceC810) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2701) := by
    have ha : (tripleCharges (sourceA810 + difference 0 4) (sourceB810 + difference 4 0) sourceC810) = raw13351 := by
      apply Matrix.ext; unfold tripleCharges sourceA810 sourceB810 sourceC810 difference raw13351; decide +kernel
    rw [ha]
    exact (canonical13351 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA810 + difference 0 5) (sourceB810 + difference 5 0) sourceC810) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2703) := by
    have ha : (tripleCharges (sourceA810 + difference 0 5) (sourceB810 + difference 5 0) sourceC810) = raw13352 := by
      apply Matrix.ext; unfold tripleCharges sourceA810 sourceB810 sourceC810 difference raw13352; decide +kernel
    rw [ha]
    exact (canonical13352 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA810 + difference 1 0) (sourceB810 + difference 0 1) sourceC810) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3170) := by
    have ha : (tripleCharges (sourceA810 + difference 1 0) (sourceB810 + difference 0 1) sourceC810) = raw13353 := by
      apply Matrix.ext; unfold tripleCharges sourceA810 sourceB810 sourceC810 difference raw13353; decide +kernel
    rw [ha]
    exact (canonical13353 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA810 + difference 1 2) (sourceB810 + difference 2 1) sourceC810) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3051) := by
    have ha : (tripleCharges (sourceA810 + difference 1 2) (sourceB810 + difference 2 1) sourceC810) = raw13354 := by
      apply Matrix.ext; unfold tripleCharges sourceA810 sourceB810 sourceC810 difference raw13354; decide +kernel
    rw [ha]
    exact (canonical13354 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA810 + difference 1 3) (sourceB810 + difference 3 1) sourceC810) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3020) := by
    have ha : (tripleCharges (sourceA810 + difference 1 3) (sourceB810 + difference 3 1) sourceC810) = raw13355 := by
      apply Matrix.ext; unfold tripleCharges sourceA810 sourceB810 sourceC810 difference raw13355; decide +kernel
    rw [ha]
    exact (canonical13355 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA810 + difference 1 4) (sourceB810 + difference 4 1) sourceC810) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3021) := by
    have ha : (tripleCharges (sourceA810 + difference 1 4) (sourceB810 + difference 4 1) sourceC810) = raw13356 := by
      apply Matrix.ext; unfold tripleCharges sourceA810 sourceB810 sourceC810 difference raw13356; decide +kernel
    rw [ha]
    exact (canonical13356 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA810 + difference 1 5) (sourceB810 + difference 5 1) sourceC810) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3023) := by
    have ha : (tripleCharges (sourceA810 + difference 1 5) (sourceB810 + difference 5 1) sourceC810) = raw13357 := by
      apply Matrix.ext; unfold tripleCharges sourceA810 sourceB810 sourceC810 difference raw13357; decide +kernel
    rw [ha]
    exact (canonical13357 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA810 + difference 2 0) (sourceB810 + difference 0 2) sourceC810) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3170) := by
    have ha : (tripleCharges (sourceA810 + difference 2 0) (sourceB810 + difference 0 2) sourceC810) = raw12912 := by
      apply Matrix.ext; unfold tripleCharges sourceA810 sourceB810 sourceC810 difference raw12912; decide +kernel
    rw [ha]
    exact (canonical12912 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA810 + difference 2 1) (sourceB810 + difference 1 2) sourceC810) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3051) := by
    have ha : (tripleCharges (sourceA810 + difference 2 1) (sourceB810 + difference 1 2) sourceC810) = raw12047 := by
      apply Matrix.ext; unfold tripleCharges sourceA810 sourceB810 sourceC810 difference raw12047; decide +kernel
    rw [ha]
    exact (canonical12047 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA810 + difference 2 3) (sourceB810 + difference 3 2) sourceC810) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3020) := by
    have ha : (tripleCharges (sourceA810 + difference 2 3) (sourceB810 + difference 3 2) sourceC810) = raw12913 := by
      apply Matrix.ext; unfold tripleCharges sourceA810 sourceB810 sourceC810 difference raw12913; decide +kernel
    rw [ha]
    exact (canonical12913 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA810 + difference 2 4) (sourceB810 + difference 4 2) sourceC810) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3021) := by
    have ha : (tripleCharges (sourceA810 + difference 2 4) (sourceB810 + difference 4 2) sourceC810) = raw12914 := by
      apply Matrix.ext; unfold tripleCharges sourceA810 sourceB810 sourceC810 difference raw12914; decide +kernel
    rw [ha]
    exact (canonical12914 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA810 + difference 2 5) (sourceB810 + difference 5 2) sourceC810) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3023) := by
    have ha : (tripleCharges (sourceA810 + difference 2 5) (sourceB810 + difference 5 2) sourceC810) = raw12915 := by
      apply Matrix.ext; unfold tripleCharges sourceA810 sourceB810 sourceC810 difference raw12915; decide +kernel
    rw [ha]
    exact (canonical12915 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA810 + difference 3 0) (sourceB810 + difference 0 3) sourceC810) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3226) := by
    have ha : (tripleCharges (sourceA810 + difference 3 0) (sourceB810 + difference 0 3) sourceC810) = raw13358 := by
      apply Matrix.ext; unfold tripleCharges sourceA810 sourceB810 sourceC810 difference raw13358; decide +kernel
    rw [ha]
    exact (canonical13358 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA810 + difference 3 1) (sourceB810 + difference 1 3) sourceC810) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3100) := by
    have ha : (tripleCharges (sourceA810 + difference 3 1) (sourceB810 + difference 1 3) sourceC810) = raw11729 := by
      apply Matrix.ext; unfold tripleCharges sourceA810 sourceB810 sourceC810 difference raw11729; decide +kernel
    rw [ha]
    exact (canonical11729 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA810 + difference 3 2) (sourceB810 + difference 2 3) sourceC810) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3100) := by
    have ha : (tripleCharges (sourceA810 + difference 3 2) (sourceB810 + difference 2 3) sourceC810) = raw12212 := by
      apply Matrix.ext; unfold tripleCharges sourceA810 sourceB810 sourceC810 difference raw12212; decide +kernel
    rw [ha]
    exact (canonical12212 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA810 + difference 3 4) (sourceB810 + difference 4 3) sourceC810) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3074) := by
    have ha : (tripleCharges (sourceA810 + difference 3 4) (sourceB810 + difference 4 3) sourceC810) = raw13359 := by
      apply Matrix.ext; unfold tripleCharges sourceA810 sourceB810 sourceC810 difference raw13359; decide +kernel
    rw [ha]
    exact (canonical13359 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA810 + difference 3 5) (sourceB810 + difference 5 3) sourceC810) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3076) := by
    have ha : (tripleCharges (sourceA810 + difference 3 5) (sourceB810 + difference 5 3) sourceC810) = raw13086 := by
      apply Matrix.ext; unfold tripleCharges sourceA810 sourceB810 sourceC810 difference raw13086; decide +kernel
    rw [ha]
    exact (canonical13086 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA810 + difference 4 0) (sourceB810 + difference 0 4) sourceC810) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3182) := by
    have ha : (tripleCharges (sourceA810 + difference 4 0) (sourceB810 + difference 0 4) sourceC810) = raw13360 := by
      apply Matrix.ext; unfold tripleCharges sourceA810 sourceB810 sourceC810 difference raw13360; decide +kernel
    rw [ha]
    exact (canonical13360 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA810 + difference 4 1) (sourceB810 + difference 1 4) sourceC810) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3099) := by
    have ha : (tripleCharges (sourceA810 + difference 4 1) (sourceB810 + difference 1 4) sourceC810) = raw12509 := by
      apply Matrix.ext; unfold tripleCharges sourceA810 sourceB810 sourceC810 difference raw12509; decide +kernel
    rw [ha]
    exact (canonical12509 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA810 + difference 4 2) (sourceB810 + difference 2 4) sourceC810) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3099) := by
    have ha : (tripleCharges (sourceA810 + difference 4 2) (sourceB810 + difference 2 4) sourceC810) = raw13361 := by
      apply Matrix.ext; unfold tripleCharges sourceA810 sourceB810 sourceC810 difference raw13361; decide +kernel
    rw [ha]
    exact (canonical13361 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA810 + difference 4 3) (sourceB810 + difference 3 4) sourceC810) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3073) := by
    have ha : (tripleCharges (sourceA810 + difference 4 3) (sourceB810 + difference 3 4) sourceC810) = raw13362 := by
      apply Matrix.ext; unfold tripleCharges sourceA810 sourceB810 sourceC810 difference raw13362; decide +kernel
    rw [ha]
    exact (canonical13362 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA810 + difference 4 5) (sourceB810 + difference 5 4) sourceC810) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3074) := by
    have ha : (tripleCharges (sourceA810 + difference 4 5) (sourceB810 + difference 5 4) sourceC810) = raw13363 := by
      apply Matrix.ext; unfold tripleCharges sourceA810 sourceB810 sourceC810 difference raw13363; decide +kernel
    rw [ha]
    exact (canonical13363 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA810 + difference 5 0) (sourceB810 + difference 0 5) sourceC810) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3172) := by
    have ha : (tripleCharges (sourceA810 + difference 5 0) (sourceB810 + difference 0 5) sourceC810) = raw12500 := by
      apply Matrix.ext; unfold tripleCharges sourceA810 sourceB810 sourceC810 difference raw12500; decide +kernel
    rw [ha]
    exact (canonical12500 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA810 + difference 5 1) (sourceB810 + difference 1 5) sourceC810) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3097) := by
    have ha : (tripleCharges (sourceA810 + difference 5 1) (sourceB810 + difference 1 5) sourceC810) = raw11727 := by
      apply Matrix.ext; unfold tripleCharges sourceA810 sourceB810 sourceC810 difference raw11727; decide +kernel
    rw [ha]
    exact (canonical11727 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA810 + difference 5 2) (sourceB810 + difference 2 5) sourceC810) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3097) := by
    have ha : (tripleCharges (sourceA810 + difference 5 2) (sourceB810 + difference 2 5) sourceC810) = raw12210 := by
      apply Matrix.ext; unfold tripleCharges sourceA810 sourceB810 sourceC810 difference raw12210; decide +kernel
    rw [ha]
    exact (canonical12210 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA810 + difference 5 3) (sourceB810 + difference 3 5) sourceC810) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3070) := by
    have ha : (tripleCharges (sourceA810 + difference 5 3) (sourceB810 + difference 3 5) sourceC810) = raw12501 := by
      apply Matrix.ext; unfold tripleCharges sourceA810 sourceB810 sourceC810 difference raw12501; decide +kernel
    rw [ha]
    exact (canonical12501 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA810 + difference 5 4) (sourceB810 + difference 4 5) sourceC810) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3071) := by
    have ha : (tripleCharges (sourceA810 + difference 5 4) (sourceB810 + difference 4 5) sourceC810) = raw12502 := by
      apply Matrix.ext; unfold tripleCharges sourceA810 sourceB810 sourceC810 difference raw12502; decide +kernel
    rw [ha]
    exact (canonical12502 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA810 sourceB810 sourceC810
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm810, Integer.Sparse.eval]
  linarith only [hs]

def sourceA811 : Charge := ![1, 1, 1, -2, -1, 0]
def sourceB811 : Charge := ![2, -1, -1, 1, 0, -1]
def sourceC811 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceForm811 : Integer.Sparse Master := [(Sum.inr 2923, 1), (Sum.inr 3489, 1), (Sum.inr 3496, 1), (Sum.inr 3534, 2), (Sum.inr 3571, 1), (Sum.inr 4083, -1)]

theorem sourceEq811 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm811 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA811 + difference 0 0) (sourceB811 + difference 0 0) sourceC811) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3571) := by
    have ha : (tripleCharges (sourceA811 + difference 0 0) (sourceB811 + difference 0 0) sourceC811) = raw12520 := by
      apply Matrix.ext; unfold tripleCharges sourceA811 sourceB811 sourceC811 difference raw12520; decide +kernel
    rw [ha]
    exact (canonical12520 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA811 + difference 0 1) (sourceB811 + difference 1 0) sourceC811) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3534) := by
    have ha : (tripleCharges (sourceA811 + difference 0 1) (sourceB811 + difference 1 0) sourceC811) = raw12515 := by
      apply Matrix.ext; unfold tripleCharges sourceA811 sourceB811 sourceC811 difference raw12515; decide +kernel
    rw [ha]
    exact (canonical12515 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA811 + difference 0 2) (sourceB811 + difference 2 0) sourceC811) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3534) := by
    have ha : (tripleCharges (sourceA811 + difference 0 2) (sourceB811 + difference 2 0) sourceC811) = raw13364 := by
      apply Matrix.ext; unfold tripleCharges sourceA811 sourceB811 sourceC811 difference raw13364; decide +kernel
    rw [ha]
    exact (canonical13364 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA811 + difference 0 3) (sourceB811 + difference 3 0) sourceC811) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2923) := by
    have ha : (tripleCharges (sourceA811 + difference 0 3) (sourceB811 + difference 3 0) sourceC811) = raw13365 := by
      apply Matrix.ext; unfold tripleCharges sourceA811 sourceB811 sourceC811 difference raw13365; decide +kernel
    rw [ha]
    exact (canonical13365 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA811 + difference 0 4) (sourceB811 + difference 4 0) sourceC811) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3489) := by
    have ha : (tripleCharges (sourceA811 + difference 0 4) (sourceB811 + difference 4 0) sourceC811) = raw13366 := by
      apply Matrix.ext; unfold tripleCharges sourceA811 sourceB811 sourceC811 difference raw13366; decide +kernel
    rw [ha]
    exact (canonical13366 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA811 + difference 0 5) (sourceB811 + difference 5 0) sourceC811) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3496) := by
    have ha : (tripleCharges (sourceA811 + difference 0 5) (sourceB811 + difference 5 0) sourceC811) = raw13367 := by
      apply Matrix.ext; unfold tripleCharges sourceA811 sourceB811 sourceC811 difference raw13367; decide +kernel
    rw [ha]
    exact (canonical13367 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA811 + sourceB811) sourceC811) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA811 + sourceB811) sourceC811) = raw11756 := by
      apply Matrix.ext; unfold doubleCharges sourceA811 sourceB811 sourceC811 raw11756; decide +kernel
    rw [ha]
    exact (canonical11756 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA811 sourceB811 sourceC811
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm811, Integer.Sparse.eval]
  linarith only [hs]

def sourceA812 : Charge := ![1, 1, 1, -2, -1, 0]
def sourceB812 : Charge := ![2, -1, -1, 1, 0, -1]
def sourceC812 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceForm812 : Integer.Sparse Master := [(Sum.inr 2088, 1), (Sum.inr 2089, 2), (Sum.inr 2105, 1), (Sum.inr 2243, 1), (Sum.inr 3571, 1), (Sum.inr 4083, -1)]

theorem sourceEq812 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm812 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA812 + difference 0 0) (sourceB812 + difference 0 0) sourceC812) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3571) := by
    have ha : (tripleCharges (sourceA812 + difference 0 0) (sourceB812 + difference 0 0) sourceC812) = raw12520 := by
      apply Matrix.ext; unfold tripleCharges sourceA812 sourceB812 sourceC812 difference raw12520; decide +kernel
    rw [ha]
    exact (canonical12520 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA812 + difference 1 0) (sourceB812 + difference 0 1) sourceC812) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2089) := by
    have ha : (tripleCharges (sourceA812 + difference 1 0) (sourceB812 + difference 0 1) sourceC812) = raw13368 := by
      apply Matrix.ext; unfold tripleCharges sourceA812 sourceB812 sourceC812 difference raw13368; decide +kernel
    rw [ha]
    exact (canonical13368 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA812 + difference 2 0) (sourceB812 + difference 0 2) sourceC812) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2089) := by
    have ha : (tripleCharges (sourceA812 + difference 2 0) (sourceB812 + difference 0 2) sourceC812) = raw12926 := by
      apply Matrix.ext; unfold tripleCharges sourceA812 sourceB812 sourceC812 difference raw12926; decide +kernel
    rw [ha]
    exact (canonical12926 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA812 + difference 3 0) (sourceB812 + difference 0 3) sourceC812) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2243) := by
    have ha : (tripleCharges (sourceA812 + difference 3 0) (sourceB812 + difference 0 3) sourceC812) = raw12664 := by
      apply Matrix.ext; unfold tripleCharges sourceA812 sourceB812 sourceC812 difference raw12664; decide +kernel
    rw [ha]
    exact (canonical12664 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA812 + difference 4 0) (sourceB812 + difference 0 4) sourceC812) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2105) := by
    have ha : (tripleCharges (sourceA812 + difference 4 0) (sourceB812 + difference 0 4) sourceC812) = raw13369 := by
      apply Matrix.ext; unfold tripleCharges sourceA812 sourceB812 sourceC812 difference raw13369; decide +kernel
    rw [ha]
    exact (canonical13369 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA812 + difference 5 0) (sourceB812 + difference 0 5) sourceC812) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2088) := by
    have ha : (tripleCharges (sourceA812 + difference 5 0) (sourceB812 + difference 0 5) sourceC812) = raw12516 := by
      apply Matrix.ext; unfold tripleCharges sourceA812 sourceB812 sourceC812 difference raw12516; decide +kernel
    rw [ha]
    exact (canonical12516 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA812 + sourceB812) sourceC812) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA812 + sourceB812) sourceC812) = raw11756 := by
      apply Matrix.ext; unfold doubleCharges sourceA812 sourceB812 sourceC812 raw11756; decide +kernel
    rw [ha]
    exact (canonical11756 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA812 sourceB812 sourceC812
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm812, Integer.Sparse.eval]
  linarith only [hs]

def sourceA813 : Charge := ![1, 1, 1, -2, -1, 0]
def sourceB813 : Charge := ![2, -1, -1, 1, 0, -1]
def sourceC813 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceForm813 : Integer.Sparse Master := [(Sum.inr 2923, 1), (Sum.inr 2926, 2), (Sum.inr 2950, 1), (Sum.inr 3073, 1), (Sum.inr 3571, 1), (Sum.inr 4083, -1)]

theorem sourceEq813 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm813 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA813 + difference 0 3) (sourceB813 + difference 3 0) sourceC813) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2923) := by
    have ha : (tripleCharges (sourceA813 + difference 0 3) (sourceB813 + difference 3 0) sourceC813) = raw13365 := by
      apply Matrix.ext; unfold tripleCharges sourceA813 sourceB813 sourceC813 difference raw13365; decide +kernel
    rw [ha]
    exact (canonical13365 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA813 + difference 1 3) (sourceB813 + difference 3 1) sourceC813) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2926) := by
    have ha : (tripleCharges (sourceA813 + difference 1 3) (sourceB813 + difference 3 1) sourceC813) = raw13370 := by
      apply Matrix.ext; unfold tripleCharges sourceA813 sourceB813 sourceC813 difference raw13370; decide +kernel
    rw [ha]
    exact (canonical13370 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA813 + difference 2 3) (sourceB813 + difference 3 2) sourceC813) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2926) := by
    have ha : (tripleCharges (sourceA813 + difference 2 3) (sourceB813 + difference 3 2) sourceC813) = raw12927 := by
      apply Matrix.ext; unfold tripleCharges sourceA813 sourceB813 sourceC813 difference raw12927; decide +kernel
    rw [ha]
    exact (canonical12927 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA813 + difference 3 3) (sourceB813 + difference 3 3) sourceC813) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3571) := by
    have ha : (tripleCharges (sourceA813 + difference 3 3) (sourceB813 + difference 3 3) sourceC813) = raw12520 := by
      apply Matrix.ext; unfold tripleCharges sourceA813 sourceB813 sourceC813 difference raw12520; decide +kernel
    rw [ha]
    exact (canonical12520 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA813 + difference 4 3) (sourceB813 + difference 3 4) sourceC813) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3073) := by
    have ha : (tripleCharges (sourceA813 + difference 4 3) (sourceB813 + difference 3 4) sourceC813) = raw13371 := by
      apply Matrix.ext; unfold tripleCharges sourceA813 sourceB813 sourceC813 difference raw13371; decide +kernel
    rw [ha]
    exact (canonical13371 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA813 + difference 5 3) (sourceB813 + difference 3 5) sourceC813) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2950) := by
    have ha : (tripleCharges (sourceA813 + difference 5 3) (sourceB813 + difference 3 5) sourceC813) = raw12518 := by
      apply Matrix.ext; unfold tripleCharges sourceA813 sourceB813 sourceC813 difference raw12518; decide +kernel
    rw [ha]
    exact (canonical12518 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA813 + sourceB813) sourceC813) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA813 + sourceB813) sourceC813) = raw11756 := by
      apply Matrix.ext; unfold doubleCharges sourceA813 sourceB813 sourceC813 raw11756; decide +kernel
    rw [ha]
    exact (canonical11756 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA813 sourceB813 sourceC813
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm813, Integer.Sparse.eval]
  linarith only [hs]

def sourceA814 : Charge := ![1, 1, 1, -2, -1, 0]
def sourceB814 : Charge := ![2, -1, -1, 1, 0, -1]
def sourceC814 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceForm814 : Integer.Sparse Master := [(Sum.inr 2105, 1), (Sum.inr 3073, 1), (Sum.inr 3571, 2), (Sum.inr 3581, 2), (Sum.inr 4083, -1)]

theorem sourceEq814 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm814 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA814 + difference 4 0) (sourceB814 + difference 0 4) sourceC814) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2105) := by
    have ha : (tripleCharges (sourceA814 + difference 4 0) (sourceB814 + difference 0 4) sourceC814) = raw13369 := by
      apply Matrix.ext; unfold tripleCharges sourceA814 sourceB814 sourceC814 difference raw13369; decide +kernel
    rw [ha]
    exact (canonical13369 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA814 + difference 4 1) (sourceB814 + difference 1 4) sourceC814) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3581) := by
    have ha : (tripleCharges (sourceA814 + difference 4 1) (sourceB814 + difference 1 4) sourceC814) = raw12528 := by
      apply Matrix.ext; unfold tripleCharges sourceA814 sourceB814 sourceC814 difference raw12528; decide +kernel
    rw [ha]
    exact (canonical12528 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA814 + difference 4 2) (sourceB814 + difference 2 4) sourceC814) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3581) := by
    have ha : (tripleCharges (sourceA814 + difference 4 2) (sourceB814 + difference 2 4) sourceC814) = raw13372 := by
      apply Matrix.ext; unfold tripleCharges sourceA814 sourceB814 sourceC814 difference raw13372; decide +kernel
    rw [ha]
    exact (canonical13372 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA814 + difference 4 3) (sourceB814 + difference 3 4) sourceC814) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3073) := by
    have ha : (tripleCharges (sourceA814 + difference 4 3) (sourceB814 + difference 3 4) sourceC814) = raw13371 := by
      apply Matrix.ext; unfold tripleCharges sourceA814 sourceB814 sourceC814 difference raw13371; decide +kernel
    rw [ha]
    exact (canonical13371 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA814 + difference 4 4) (sourceB814 + difference 4 4) sourceC814) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3571) := by
    have ha : (tripleCharges (sourceA814 + difference 4 4) (sourceB814 + difference 4 4) sourceC814) = raw12520 := by
      apply Matrix.ext; unfold tripleCharges sourceA814 sourceB814 sourceC814 difference raw12520; decide +kernel
    rw [ha]
    exact (canonical12520 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA814 + difference 4 5) (sourceB814 + difference 5 4) sourceC814) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3571) := by
    have ha : (tripleCharges (sourceA814 + difference 4 5) (sourceB814 + difference 5 4) sourceC814) = raw13373 := by
      apply Matrix.ext; unfold tripleCharges sourceA814 sourceB814 sourceC814 difference raw13373; decide +kernel
    rw [ha]
    exact (canonical13373 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA814 + sourceB814) sourceC814) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA814 + sourceB814) sourceC814) = raw11756 := by
      apply Matrix.ext; unfold doubleCharges sourceA814 sourceB814 sourceC814 raw11756; decide +kernel
    rw [ha]
    exact (canonical11756 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA814 sourceB814 sourceC814
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm814, Integer.Sparse.eval]
  linarith only [hs]

def sourceA815 : Charge := ![1, 1, 1, -2, -1, 0]
def sourceB815 : Charge := ![2, -1, -1, 1, 0, -1]
def sourceC815 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceForm815 : Integer.Sparse Master := [(Sum.inr 3489, 1), (Sum.inr 3550, 1), (Sum.inr 3551, 2), (Sum.inr 3571, 2), (Sum.inr 4083, -1)]

theorem sourceEq815 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm815 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA815 + difference 0 4) (sourceB815 + difference 4 0) sourceC815) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3489) := by
    have ha : (tripleCharges (sourceA815 + difference 0 4) (sourceB815 + difference 4 0) sourceC815) = raw13366 := by
      apply Matrix.ext; unfold tripleCharges sourceA815 sourceB815 sourceC815 difference raw13366; decide +kernel
    rw [ha]
    exact (canonical13366 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA815 + difference 1 4) (sourceB815 + difference 4 1) sourceC815) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3551) := by
    have ha : (tripleCharges (sourceA815 + difference 1 4) (sourceB815 + difference 4 1) sourceC815) = raw13374 := by
      apply Matrix.ext; unfold tripleCharges sourceA815 sourceB815 sourceC815 difference raw13374; decide +kernel
    rw [ha]
    exact (canonical13374 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA815 + difference 2 4) (sourceB815 + difference 4 2) sourceC815) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3551) := by
    have ha : (tripleCharges (sourceA815 + difference 2 4) (sourceB815 + difference 4 2) sourceC815) = raw12928 := by
      apply Matrix.ext; unfold tripleCharges sourceA815 sourceB815 sourceC815 difference raw12928; decide +kernel
    rw [ha]
    exact (canonical12928 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA815 + difference 3 4) (sourceB815 + difference 4 3) sourceC815) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3571) := by
    have ha : (tripleCharges (sourceA815 + difference 3 4) (sourceB815 + difference 4 3) sourceC815) = raw12666 := by
      apply Matrix.ext; unfold tripleCharges sourceA815 sourceB815 sourceC815 difference raw12666; decide +kernel
    rw [ha]
    exact (canonical12666 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA815 + difference 4 4) (sourceB815 + difference 4 4) sourceC815) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3571) := by
    have ha : (tripleCharges (sourceA815 + difference 4 4) (sourceB815 + difference 4 4) sourceC815) = raw12520 := by
      apply Matrix.ext; unfold tripleCharges sourceA815 sourceB815 sourceC815 difference raw12520; decide +kernel
    rw [ha]
    exact (canonical12520 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA815 + difference 5 4) (sourceB815 + difference 4 5) sourceC815) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3550) := by
    have ha : (tripleCharges (sourceA815 + difference 5 4) (sourceB815 + difference 4 5) sourceC815) = raw12519 := by
      apply Matrix.ext; unfold tripleCharges sourceA815 sourceB815 sourceC815 difference raw12519; decide +kernel
    rw [ha]
    exact (canonical12519 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA815 + sourceB815) sourceC815) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA815 + sourceB815) sourceC815) = raw11756 := by
      apply Matrix.ext; unfold doubleCharges sourceA815 sourceB815 sourceC815 raw11756; decide +kernel
    rw [ha]
    exact (canonical11756 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA815 sourceB815 sourceC815
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm815, Integer.Sparse.eval]
  linarith only [hs]

def sourceA816 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB816 : Charge := ![1, 1, 1, -1, -1, -1]
def sourceC816 : Charge := ![2, -1, -1, 0, 0, 0]
def sourceForm816 : Integer.Sparse Master := [(Sum.inr 4581, 3), (Sum.inr 4601, 2), (Sum.inr 5192, 6), (Sum.inr 5202, 2), (Sum.inr 5284, 6), (Sum.inr 5292, 6), (Sum.inr 5447, 2), (Sum.inr 5452, 3)]

theorem sourceEq816 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm816 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA816 + difference 0 1) (sourceB816 + difference 1 0) sourceC816) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5447) := by
    have ha : (tripleCharges (sourceA816 + difference 0 1) (sourceB816 + difference 1 0) sourceC816) = raw13375 := by
      apply Matrix.ext; unfold tripleCharges sourceA816 sourceB816 sourceC816 difference raw13375; decide +kernel
    rw [ha]
    exact (canonical13375 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA816 + difference 0 2) (sourceB816 + difference 2 0) sourceC816) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5447) := by
    have ha : (tripleCharges (sourceA816 + difference 0 2) (sourceB816 + difference 2 0) sourceC816) = raw13376 := by
      apply Matrix.ext; unfold tripleCharges sourceA816 sourceB816 sourceC816 difference raw13376; decide +kernel
    rw [ha]
    exact (canonical13376 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA816 + difference 0 3) (sourceB816 + difference 3 0) sourceC816) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5452) := by
    have ha : (tripleCharges (sourceA816 + difference 0 3) (sourceB816 + difference 3 0) sourceC816) = raw13377 := by
      apply Matrix.ext; unfold tripleCharges sourceA816 sourceB816 sourceC816 difference raw13377; decide +kernel
    rw [ha]
    exact (canonical13377 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA816 + difference 0 4) (sourceB816 + difference 4 0) sourceC816) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5452) := by
    have ha : (tripleCharges (sourceA816 + difference 0 4) (sourceB816 + difference 4 0) sourceC816) = raw13378 := by
      apply Matrix.ext; unfold tripleCharges sourceA816 sourceB816 sourceC816 difference raw13378; decide +kernel
    rw [ha]
    exact (canonical13378 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA816 + difference 0 5) (sourceB816 + difference 5 0) sourceC816) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5452) := by
    have ha : (tripleCharges (sourceA816 + difference 0 5) (sourceB816 + difference 5 0) sourceC816) = raw13379 := by
      apply Matrix.ext; unfold tripleCharges sourceA816 sourceB816 sourceC816 difference raw13379; decide +kernel
    rw [ha]
    exact (canonical13379 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA816 + difference 1 0) (sourceB816 + difference 0 1) sourceC816) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4601) := by
    have ha : (tripleCharges (sourceA816 + difference 1 0) (sourceB816 + difference 0 1) sourceC816) = raw13380 := by
      apply Matrix.ext; unfold tripleCharges sourceA816 sourceB816 sourceC816 difference raw13380; decide +kernel
    rw [ha]
    exact (canonical13380 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA816 + difference 1 2) (sourceB816 + difference 2 1) sourceC816) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5202) := by
    have ha : (tripleCharges (sourceA816 + difference 1 2) (sourceB816 + difference 2 1) sourceC816) = raw13381 := by
      apply Matrix.ext; unfold tripleCharges sourceA816 sourceB816 sourceC816 difference raw13381; decide +kernel
    rw [ha]
    exact (canonical13381 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA816 + difference 1 3) (sourceB816 + difference 3 1) sourceC816) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA816 + difference 1 3) (sourceB816 + difference 3 1) sourceC816) = raw13382 := by
      apply Matrix.ext; unfold tripleCharges sourceA816 sourceB816 sourceC816 difference raw13382; decide +kernel
    rw [ha]
    exact (canonical13382 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA816 + difference 1 4) (sourceB816 + difference 4 1) sourceC816) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA816 + difference 1 4) (sourceB816 + difference 4 1) sourceC816) = raw13383 := by
      apply Matrix.ext; unfold tripleCharges sourceA816 sourceB816 sourceC816 difference raw13383; decide +kernel
    rw [ha]
    exact (canonical13383 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA816 + difference 1 5) (sourceB816 + difference 5 1) sourceC816) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA816 + difference 1 5) (sourceB816 + difference 5 1) sourceC816) = raw13384 := by
      apply Matrix.ext; unfold tripleCharges sourceA816 sourceB816 sourceC816 difference raw13384; decide +kernel
    rw [ha]
    exact (canonical13384 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA816 + difference 2 0) (sourceB816 + difference 0 2) sourceC816) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4601) := by
    have ha : (tripleCharges (sourceA816 + difference 2 0) (sourceB816 + difference 0 2) sourceC816) = raw13385 := by
      apply Matrix.ext; unfold tripleCharges sourceA816 sourceB816 sourceC816 difference raw13385; decide +kernel
    rw [ha]
    exact (canonical13385 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA816 + difference 2 1) (sourceB816 + difference 1 2) sourceC816) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5202) := by
    have ha : (tripleCharges (sourceA816 + difference 2 1) (sourceB816 + difference 1 2) sourceC816) = raw13386 := by
      apply Matrix.ext; unfold tripleCharges sourceA816 sourceB816 sourceC816 difference raw13386; decide +kernel
    rw [ha]
    exact (canonical13386 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA816 + difference 2 3) (sourceB816 + difference 3 2) sourceC816) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA816 + difference 2 3) (sourceB816 + difference 3 2) sourceC816) = raw13387 := by
      apply Matrix.ext; unfold tripleCharges sourceA816 sourceB816 sourceC816 difference raw13387; decide +kernel
    rw [ha]
    exact (canonical13387 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA816 + difference 2 4) (sourceB816 + difference 4 2) sourceC816) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA816 + difference 2 4) (sourceB816 + difference 4 2) sourceC816) = raw13388 := by
      apply Matrix.ext; unfold tripleCharges sourceA816 sourceB816 sourceC816 difference raw13388; decide +kernel
    rw [ha]
    exact (canonical13388 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA816 + difference 2 5) (sourceB816 + difference 5 2) sourceC816) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA816 + difference 2 5) (sourceB816 + difference 5 2) sourceC816) = raw13389 := by
      apply Matrix.ext; unfold tripleCharges sourceA816 sourceB816 sourceC816 difference raw13389; decide +kernel
    rw [ha]
    exact (canonical13389 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA816 + difference 3 0) (sourceB816 + difference 0 3) sourceC816) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4581) := by
    have ha : (tripleCharges (sourceA816 + difference 3 0) (sourceB816 + difference 0 3) sourceC816) = raw13390 := by
      apply Matrix.ext; unfold tripleCharges sourceA816 sourceB816 sourceC816 difference raw13390; decide +kernel
    rw [ha]
    exact (canonical13390 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA816 + difference 3 1) (sourceB816 + difference 1 3) sourceC816) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5192) := by
    have ha : (tripleCharges (sourceA816 + difference 3 1) (sourceB816 + difference 1 3) sourceC816) = raw13391 := by
      apply Matrix.ext; unfold tripleCharges sourceA816 sourceB816 sourceC816 difference raw13391; decide +kernel
    rw [ha]
    exact (canonical13391 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA816 + difference 3 2) (sourceB816 + difference 2 3) sourceC816) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5192) := by
    have ha : (tripleCharges (sourceA816 + difference 3 2) (sourceB816 + difference 2 3) sourceC816) = raw13392 := by
      apply Matrix.ext; unfold tripleCharges sourceA816 sourceB816 sourceC816 difference raw13392; decide +kernel
    rw [ha]
    exact (canonical13392 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA816 + difference 3 4) (sourceB816 + difference 4 3) sourceC816) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA816 + difference 3 4) (sourceB816 + difference 4 3) sourceC816) = raw13393 := by
      apply Matrix.ext; unfold tripleCharges sourceA816 sourceB816 sourceC816 difference raw13393; decide +kernel
    rw [ha]
    exact (canonical13393 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA816 + difference 3 5) (sourceB816 + difference 5 3) sourceC816) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA816 + difference 3 5) (sourceB816 + difference 5 3) sourceC816) = raw13394 := by
      apply Matrix.ext; unfold tripleCharges sourceA816 sourceB816 sourceC816 difference raw13394; decide +kernel
    rw [ha]
    exact (canonical13394 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA816 + difference 4 0) (sourceB816 + difference 0 4) sourceC816) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4581) := by
    have ha : (tripleCharges (sourceA816 + difference 4 0) (sourceB816 + difference 0 4) sourceC816) = raw13395 := by
      apply Matrix.ext; unfold tripleCharges sourceA816 sourceB816 sourceC816 difference raw13395; decide +kernel
    rw [ha]
    exact (canonical13395 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA816 + difference 4 1) (sourceB816 + difference 1 4) sourceC816) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5192) := by
    have ha : (tripleCharges (sourceA816 + difference 4 1) (sourceB816 + difference 1 4) sourceC816) = raw13396 := by
      apply Matrix.ext; unfold tripleCharges sourceA816 sourceB816 sourceC816 difference raw13396; decide +kernel
    rw [ha]
    exact (canonical13396 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA816 + difference 4 2) (sourceB816 + difference 2 4) sourceC816) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5192) := by
    have ha : (tripleCharges (sourceA816 + difference 4 2) (sourceB816 + difference 2 4) sourceC816) = raw13397 := by
      apply Matrix.ext; unfold tripleCharges sourceA816 sourceB816 sourceC816 difference raw13397; decide +kernel
    rw [ha]
    exact (canonical13397 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA816 + difference 4 3) (sourceB816 + difference 3 4) sourceC816) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA816 + difference 4 3) (sourceB816 + difference 3 4) sourceC816) = raw13398 := by
      apply Matrix.ext; unfold tripleCharges sourceA816 sourceB816 sourceC816 difference raw13398; decide +kernel
    rw [ha]
    exact (canonical13398 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA816 + difference 4 5) (sourceB816 + difference 5 4) sourceC816) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA816 + difference 4 5) (sourceB816 + difference 5 4) sourceC816) = raw13399 := by
      apply Matrix.ext; unfold tripleCharges sourceA816 sourceB816 sourceC816 difference raw13399; decide +kernel
    rw [ha]
    exact (canonical13399 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA816 + difference 5 0) (sourceB816 + difference 0 5) sourceC816) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4581) := by
    have ha : (tripleCharges (sourceA816 + difference 5 0) (sourceB816 + difference 0 5) sourceC816) = raw13400 := by
      apply Matrix.ext; unfold tripleCharges sourceA816 sourceB816 sourceC816 difference raw13400; decide +kernel
    rw [ha]
    exact (canonical13400 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA816 + difference 5 1) (sourceB816 + difference 1 5) sourceC816) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5192) := by
    have ha : (tripleCharges (sourceA816 + difference 5 1) (sourceB816 + difference 1 5) sourceC816) = raw13401 := by
      apply Matrix.ext; unfold tripleCharges sourceA816 sourceB816 sourceC816 difference raw13401; decide +kernel
    rw [ha]
    exact (canonical13401 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA816 + difference 5 2) (sourceB816 + difference 2 5) sourceC816) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5192) := by
    have ha : (tripleCharges (sourceA816 + difference 5 2) (sourceB816 + difference 2 5) sourceC816) = raw13402 := by
      apply Matrix.ext; unfold tripleCharges sourceA816 sourceB816 sourceC816 difference raw13402; decide +kernel
    rw [ha]
    exact (canonical13402 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA816 + difference 5 3) (sourceB816 + difference 3 5) sourceC816) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA816 + difference 5 3) (sourceB816 + difference 3 5) sourceC816) = raw13403 := by
      apply Matrix.ext; unfold tripleCharges sourceA816 sourceB816 sourceC816 difference raw13403; decide +kernel
    rw [ha]
    exact (canonical13403 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA816 + difference 5 4) (sourceB816 + difference 4 5) sourceC816) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA816 + difference 5 4) (sourceB816 + difference 4 5) sourceC816) = raw13404 := by
      apply Matrix.ext; unfold tripleCharges sourceA816 sourceB816 sourceC816 difference raw13404; decide +kernel
    rw [ha]
    exact (canonical13404 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA816 sourceB816 sourceC816
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm816, Integer.Sparse.eval]
  linarith only [hs]

def sourceA817 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB817 : Charge := ![1, 1, 1, -1, -1, -1]
def sourceC817 : Charge := ![2, -1, -1, 0, 0, 0]
def sourceForm817 : Integer.Sparse Master := [(Sum.inr 1200, 3), (Sum.inr 1235, 2), (Sum.inr 2853, 6), (Sum.inr 2880, 2), (Sum.inr 3077, 6), (Sum.inr 3100, 6), (Sum.inr 4025, 2), (Sum.inr 4039, 3)]

theorem sourceEq817 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm817 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA817 + difference 0 1) (sourceB817 + difference 1 0) sourceC817) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4025) := by
    have ha : (tripleCharges (sourceA817 + difference 0 1) (sourceB817 + difference 1 0) sourceC817) = raw13405 := by
      apply Matrix.ext; unfold tripleCharges sourceA817 sourceB817 sourceC817 difference raw13405; decide +kernel
    rw [ha]
    exact (canonical13405 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA817 + difference 0 2) (sourceB817 + difference 2 0) sourceC817) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4025) := by
    have ha : (tripleCharges (sourceA817 + difference 0 2) (sourceB817 + difference 2 0) sourceC817) = raw13406 := by
      apply Matrix.ext; unfold tripleCharges sourceA817 sourceB817 sourceC817 difference raw13406; decide +kernel
    rw [ha]
    exact (canonical13406 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA817 + difference 0 3) (sourceB817 + difference 3 0) sourceC817) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4039) := by
    have ha : (tripleCharges (sourceA817 + difference 0 3) (sourceB817 + difference 3 0) sourceC817) = raw13407 := by
      apply Matrix.ext; unfold tripleCharges sourceA817 sourceB817 sourceC817 difference raw13407; decide +kernel
    rw [ha]
    exact (canonical13407 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA817 + difference 0 4) (sourceB817 + difference 4 0) sourceC817) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4039) := by
    have ha : (tripleCharges (sourceA817 + difference 0 4) (sourceB817 + difference 4 0) sourceC817) = raw13408 := by
      apply Matrix.ext; unfold tripleCharges sourceA817 sourceB817 sourceC817 difference raw13408; decide +kernel
    rw [ha]
    exact (canonical13408 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA817 + difference 0 5) (sourceB817 + difference 5 0) sourceC817) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4039) := by
    have ha : (tripleCharges (sourceA817 + difference 0 5) (sourceB817 + difference 5 0) sourceC817) = raw13409 := by
      apply Matrix.ext; unfold tripleCharges sourceA817 sourceB817 sourceC817 difference raw13409; decide +kernel
    rw [ha]
    exact (canonical13409 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA817 + difference 1 0) (sourceB817 + difference 0 1) sourceC817) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1235) := by
    have ha : (tripleCharges (sourceA817 + difference 1 0) (sourceB817 + difference 0 1) sourceC817) = raw13410 := by
      apply Matrix.ext; unfold tripleCharges sourceA817 sourceB817 sourceC817 difference raw13410; decide +kernel
    rw [ha]
    exact (canonical13410 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA817 + difference 1 2) (sourceB817 + difference 2 1) sourceC817) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2880) := by
    have ha : (tripleCharges (sourceA817 + difference 1 2) (sourceB817 + difference 2 1) sourceC817) = raw13411 := by
      apply Matrix.ext; unfold tripleCharges sourceA817 sourceB817 sourceC817 difference raw13411; decide +kernel
    rw [ha]
    exact (canonical13411 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA817 + difference 1 3) (sourceB817 + difference 3 1) sourceC817) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3100) := by
    have ha : (tripleCharges (sourceA817 + difference 1 3) (sourceB817 + difference 3 1) sourceC817) = raw13412 := by
      apply Matrix.ext; unfold tripleCharges sourceA817 sourceB817 sourceC817 difference raw13412; decide +kernel
    rw [ha]
    exact (canonical13412 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA817 + difference 1 4) (sourceB817 + difference 4 1) sourceC817) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3100) := by
    have ha : (tripleCharges (sourceA817 + difference 1 4) (sourceB817 + difference 4 1) sourceC817) = raw13413 := by
      apply Matrix.ext; unfold tripleCharges sourceA817 sourceB817 sourceC817 difference raw13413; decide +kernel
    rw [ha]
    exact (canonical13413 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA817 + difference 1 5) (sourceB817 + difference 5 1) sourceC817) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3100) := by
    have ha : (tripleCharges (sourceA817 + difference 1 5) (sourceB817 + difference 5 1) sourceC817) = raw13414 := by
      apply Matrix.ext; unfold tripleCharges sourceA817 sourceB817 sourceC817 difference raw13414; decide +kernel
    rw [ha]
    exact (canonical13414 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA817 + difference 2 0) (sourceB817 + difference 0 2) sourceC817) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1235) := by
    have ha : (tripleCharges (sourceA817 + difference 2 0) (sourceB817 + difference 0 2) sourceC817) = raw13415 := by
      apply Matrix.ext; unfold tripleCharges sourceA817 sourceB817 sourceC817 difference raw13415; decide +kernel
    rw [ha]
    exact (canonical13415 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA817 + difference 2 1) (sourceB817 + difference 1 2) sourceC817) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2880) := by
    have ha : (tripleCharges (sourceA817 + difference 2 1) (sourceB817 + difference 1 2) sourceC817) = raw13416 := by
      apply Matrix.ext; unfold tripleCharges sourceA817 sourceB817 sourceC817 difference raw13416; decide +kernel
    rw [ha]
    exact (canonical13416 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA817 + difference 2 3) (sourceB817 + difference 3 2) sourceC817) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3100) := by
    have ha : (tripleCharges (sourceA817 + difference 2 3) (sourceB817 + difference 3 2) sourceC817) = raw13417 := by
      apply Matrix.ext; unfold tripleCharges sourceA817 sourceB817 sourceC817 difference raw13417; decide +kernel
    rw [ha]
    exact (canonical13417 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA817 + difference 2 4) (sourceB817 + difference 4 2) sourceC817) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3100) := by
    have ha : (tripleCharges (sourceA817 + difference 2 4) (sourceB817 + difference 4 2) sourceC817) = raw13418 := by
      apply Matrix.ext; unfold tripleCharges sourceA817 sourceB817 sourceC817 difference raw13418; decide +kernel
    rw [ha]
    exact (canonical13418 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA817 + difference 2 5) (sourceB817 + difference 5 2) sourceC817) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3100) := by
    have ha : (tripleCharges (sourceA817 + difference 2 5) (sourceB817 + difference 5 2) sourceC817) = raw13419 := by
      apply Matrix.ext; unfold tripleCharges sourceA817 sourceB817 sourceC817 difference raw13419; decide +kernel
    rw [ha]
    exact (canonical13419 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA817 + difference 3 0) (sourceB817 + difference 0 3) sourceC817) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1200) := by
    have ha : (tripleCharges (sourceA817 + difference 3 0) (sourceB817 + difference 0 3) sourceC817) = raw13420 := by
      apply Matrix.ext; unfold tripleCharges sourceA817 sourceB817 sourceC817 difference raw13420; decide +kernel
    rw [ha]
    exact (canonical13420 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA817 + difference 3 1) (sourceB817 + difference 1 3) sourceC817) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2853) := by
    have ha : (tripleCharges (sourceA817 + difference 3 1) (sourceB817 + difference 1 3) sourceC817) = raw13421 := by
      apply Matrix.ext; unfold tripleCharges sourceA817 sourceB817 sourceC817 difference raw13421; decide +kernel
    rw [ha]
    exact (canonical13421 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA817 + difference 3 2) (sourceB817 + difference 2 3) sourceC817) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2853) := by
    have ha : (tripleCharges (sourceA817 + difference 3 2) (sourceB817 + difference 2 3) sourceC817) = raw13422 := by
      apply Matrix.ext; unfold tripleCharges sourceA817 sourceB817 sourceC817 difference raw13422; decide +kernel
    rw [ha]
    exact (canonical13422 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA817 + difference 3 4) (sourceB817 + difference 4 3) sourceC817) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3077) := by
    have ha : (tripleCharges (sourceA817 + difference 3 4) (sourceB817 + difference 4 3) sourceC817) = raw13423 := by
      apply Matrix.ext; unfold tripleCharges sourceA817 sourceB817 sourceC817 difference raw13423; decide +kernel
    rw [ha]
    exact (canonical13423 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA817 + difference 3 5) (sourceB817 + difference 5 3) sourceC817) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3077) := by
    have ha : (tripleCharges (sourceA817 + difference 3 5) (sourceB817 + difference 5 3) sourceC817) = raw13424 := by
      apply Matrix.ext; unfold tripleCharges sourceA817 sourceB817 sourceC817 difference raw13424; decide +kernel
    rw [ha]
    exact (canonical13424 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA817 + difference 4 0) (sourceB817 + difference 0 4) sourceC817) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1200) := by
    have ha : (tripleCharges (sourceA817 + difference 4 0) (sourceB817 + difference 0 4) sourceC817) = raw13425 := by
      apply Matrix.ext; unfold tripleCharges sourceA817 sourceB817 sourceC817 difference raw13425; decide +kernel
    rw [ha]
    exact (canonical13425 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA817 + difference 4 1) (sourceB817 + difference 1 4) sourceC817) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2853) := by
    have ha : (tripleCharges (sourceA817 + difference 4 1) (sourceB817 + difference 1 4) sourceC817) = raw13426 := by
      apply Matrix.ext; unfold tripleCharges sourceA817 sourceB817 sourceC817 difference raw13426; decide +kernel
    rw [ha]
    exact (canonical13426 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA817 + difference 4 2) (sourceB817 + difference 2 4) sourceC817) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2853) := by
    have ha : (tripleCharges (sourceA817 + difference 4 2) (sourceB817 + difference 2 4) sourceC817) = raw13427 := by
      apply Matrix.ext; unfold tripleCharges sourceA817 sourceB817 sourceC817 difference raw13427; decide +kernel
    rw [ha]
    exact (canonical13427 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA817 + difference 4 3) (sourceB817 + difference 3 4) sourceC817) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3077) := by
    have ha : (tripleCharges (sourceA817 + difference 4 3) (sourceB817 + difference 3 4) sourceC817) = raw13428 := by
      apply Matrix.ext; unfold tripleCharges sourceA817 sourceB817 sourceC817 difference raw13428; decide +kernel
    rw [ha]
    exact (canonical13428 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA817 + difference 4 5) (sourceB817 + difference 5 4) sourceC817) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3077) := by
    have ha : (tripleCharges (sourceA817 + difference 4 5) (sourceB817 + difference 5 4) sourceC817) = raw13429 := by
      apply Matrix.ext; unfold tripleCharges sourceA817 sourceB817 sourceC817 difference raw13429; decide +kernel
    rw [ha]
    exact (canonical13429 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA817 + difference 5 0) (sourceB817 + difference 0 5) sourceC817) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1200) := by
    have ha : (tripleCharges (sourceA817 + difference 5 0) (sourceB817 + difference 0 5) sourceC817) = raw13430 := by
      apply Matrix.ext; unfold tripleCharges sourceA817 sourceB817 sourceC817 difference raw13430; decide +kernel
    rw [ha]
    exact (canonical13430 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA817 + difference 5 1) (sourceB817 + difference 1 5) sourceC817) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2853) := by
    have ha : (tripleCharges (sourceA817 + difference 5 1) (sourceB817 + difference 1 5) sourceC817) = raw13431 := by
      apply Matrix.ext; unfold tripleCharges sourceA817 sourceB817 sourceC817 difference raw13431; decide +kernel
    rw [ha]
    exact (canonical13431 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA817 + difference 5 2) (sourceB817 + difference 2 5) sourceC817) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2853) := by
    have ha : (tripleCharges (sourceA817 + difference 5 2) (sourceB817 + difference 2 5) sourceC817) = raw13432 := by
      apply Matrix.ext; unfold tripleCharges sourceA817 sourceB817 sourceC817 difference raw13432; decide +kernel
    rw [ha]
    exact (canonical13432 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA817 + difference 5 3) (sourceB817 + difference 3 5) sourceC817) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3077) := by
    have ha : (tripleCharges (sourceA817 + difference 5 3) (sourceB817 + difference 3 5) sourceC817) = raw13433 := by
      apply Matrix.ext; unfold tripleCharges sourceA817 sourceB817 sourceC817 difference raw13433; decide +kernel
    rw [ha]
    exact (canonical13433 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA817 + difference 5 4) (sourceB817 + difference 4 5) sourceC817) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3077) := by
    have ha : (tripleCharges (sourceA817 + difference 5 4) (sourceB817 + difference 4 5) sourceC817) = raw13434 := by
      apply Matrix.ext; unfold tripleCharges sourceA817 sourceB817 sourceC817 difference raw13434; decide +kernel
    rw [ha]
    exact (canonical13434 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA817 sourceB817 sourceC817
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm817, Integer.Sparse.eval]
  linarith only [hs]

def sourceA818 : Charge := ![1, 1, 1, -1, -1, -1]
def sourceB818 : Charge := ![2, -1, -1, 0, 0, 0]
def sourceC818 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceForm818 : Integer.Sparse Master := [(Sum.inr 4885, 2), (Sum.inr 4887, 3), (Sum.inr 5247, 3), (Sum.inr 5273, 2), (Sum.inr 5281, 6), (Sum.inr 5286, 6), (Sum.inr 5292, 6), (Sum.inr 5301, 2)]

theorem sourceEq818 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm818 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA818 + difference 0 1) (sourceB818 + difference 1 0) sourceC818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5273) := by
    have ha : (tripleCharges (sourceA818 + difference 0 1) (sourceB818 + difference 1 0) sourceC818) = raw12652 := by
      apply Matrix.ext; unfold tripleCharges sourceA818 sourceB818 sourceC818 difference raw12652; decide +kernel
    rw [ha]
    exact (canonical12652 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA818 + difference 0 2) (sourceB818 + difference 2 0) sourceC818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5273) := by
    have ha : (tripleCharges (sourceA818 + difference 0 2) (sourceB818 + difference 2 0) sourceC818) = raw13435 := by
      apply Matrix.ext; unfold tripleCharges sourceA818 sourceB818 sourceC818 difference raw13435; decide +kernel
    rw [ha]
    exact (canonical13435 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA818 + difference 0 3) (sourceB818 + difference 3 0) sourceC818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5247) := by
    have ha : (tripleCharges (sourceA818 + difference 0 3) (sourceB818 + difference 3 0) sourceC818) = raw13322 := by
      apply Matrix.ext; unfold tripleCharges sourceA818 sourceB818 sourceC818 difference raw13322; decide +kernel
    rw [ha]
    exact (canonical13322 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA818 + difference 0 4) (sourceB818 + difference 4 0) sourceC818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5247) := by
    have ha : (tripleCharges (sourceA818 + difference 0 4) (sourceB818 + difference 4 0) sourceC818) = raw13436 := by
      apply Matrix.ext; unfold tripleCharges sourceA818 sourceB818 sourceC818 difference raw13436; decide +kernel
    rw [ha]
    exact (canonical13436 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA818 + difference 0 5) (sourceB818 + difference 5 0) sourceC818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5247) := by
    have ha : (tripleCharges (sourceA818 + difference 0 5) (sourceB818 + difference 5 0) sourceC818) = raw13437 := by
      apply Matrix.ext; unfold tripleCharges sourceA818 sourceB818 sourceC818 difference raw13437; decide +kernel
    rw [ha]
    exact (canonical13437 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA818 + difference 1 0) (sourceB818 + difference 0 1) sourceC818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4885) := by
    have ha : (tripleCharges (sourceA818 + difference 1 0) (sourceB818 + difference 0 1) sourceC818) = raw13438 := by
      apply Matrix.ext; unfold tripleCharges sourceA818 sourceB818 sourceC818 difference raw13438; decide +kernel
    rw [ha]
    exact (canonical13438 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA818 + difference 1 2) (sourceB818 + difference 2 1) sourceC818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5301) := by
    have ha : (tripleCharges (sourceA818 + difference 1 2) (sourceB818 + difference 2 1) sourceC818) = raw13439 := by
      apply Matrix.ext; unfold tripleCharges sourceA818 sourceB818 sourceC818 difference raw13439; decide +kernel
    rw [ha]
    exact (canonical13439 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA818 + difference 1 3) (sourceB818 + difference 3 1) sourceC818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5286) := by
    have ha : (tripleCharges (sourceA818 + difference 1 3) (sourceB818 + difference 3 1) sourceC818) = raw13327 := by
      apply Matrix.ext; unfold tripleCharges sourceA818 sourceB818 sourceC818 difference raw13327; decide +kernel
    rw [ha]
    exact (canonical13327 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA818 + difference 1 4) (sourceB818 + difference 4 1) sourceC818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5286) := by
    have ha : (tripleCharges (sourceA818 + difference 1 4) (sourceB818 + difference 4 1) sourceC818) = raw13440 := by
      apply Matrix.ext; unfold tripleCharges sourceA818 sourceB818 sourceC818 difference raw13440; decide +kernel
    rw [ha]
    exact (canonical13440 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA818 + difference 1 5) (sourceB818 + difference 5 1) sourceC818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5286) := by
    have ha : (tripleCharges (sourceA818 + difference 1 5) (sourceB818 + difference 5 1) sourceC818) = raw13441 := by
      apply Matrix.ext; unfold tripleCharges sourceA818 sourceB818 sourceC818 difference raw13441; decide +kernel
    rw [ha]
    exact (canonical13441 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA818 + difference 2 0) (sourceB818 + difference 0 2) sourceC818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4885) := by
    have ha : (tripleCharges (sourceA818 + difference 2 0) (sourceB818 + difference 0 2) sourceC818) = raw13071 := by
      apply Matrix.ext; unfold tripleCharges sourceA818 sourceB818 sourceC818 difference raw13071; decide +kernel
    rw [ha]
    exact (canonical13071 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA818 + difference 2 1) (sourceB818 + difference 1 2) sourceC818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5301) := by
    have ha : (tripleCharges (sourceA818 + difference 2 1) (sourceB818 + difference 1 2) sourceC818) = raw12005 := by
      apply Matrix.ext; unfold tripleCharges sourceA818 sourceB818 sourceC818 difference raw12005; decide +kernel
    rw [ha]
    exact (canonical12005 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA818 + difference 2 3) (sourceB818 + difference 3 2) sourceC818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5286) := by
    have ha : (tripleCharges (sourceA818 + difference 2 3) (sourceB818 + difference 3 2) sourceC818) = raw12887 := by
      apply Matrix.ext; unfold tripleCharges sourceA818 sourceB818 sourceC818 difference raw12887; decide +kernel
    rw [ha]
    exact (canonical12887 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA818 + difference 2 4) (sourceB818 + difference 4 2) sourceC818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5286) := by
    have ha : (tripleCharges (sourceA818 + difference 2 4) (sourceB818 + difference 4 2) sourceC818) = raw13072 := by
      apply Matrix.ext; unfold tripleCharges sourceA818 sourceB818 sourceC818 difference raw13072; decide +kernel
    rw [ha]
    exact (canonical13072 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA818 + difference 2 5) (sourceB818 + difference 5 2) sourceC818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5286) := by
    have ha : (tripleCharges (sourceA818 + difference 2 5) (sourceB818 + difference 5 2) sourceC818) = raw13073 := by
      apply Matrix.ext; unfold tripleCharges sourceA818 sourceB818 sourceC818 difference raw13073; decide +kernel
    rw [ha]
    exact (canonical13073 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA818 + difference 3 0) (sourceB818 + difference 0 3) sourceC818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4887) := by
    have ha : (tripleCharges (sourceA818 + difference 3 0) (sourceB818 + difference 0 3) sourceC818) = raw13442 := by
      apply Matrix.ext; unfold tripleCharges sourceA818 sourceB818 sourceC818 difference raw13442; decide +kernel
    rw [ha]
    exact (canonical13442 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA818 + difference 3 1) (sourceB818 + difference 1 3) sourceC818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA818 + difference 3 1) (sourceB818 + difference 1 3) sourceC818) = raw12658 := by
      apply Matrix.ext; unfold tripleCharges sourceA818 sourceB818 sourceC818 difference raw12658; decide +kernel
    rw [ha]
    exact (canonical12658 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA818 + difference 3 2) (sourceB818 + difference 2 3) sourceC818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA818 + difference 3 2) (sourceB818 + difference 2 3) sourceC818) = raw13443 := by
      apply Matrix.ext; unfold tripleCharges sourceA818 sourceB818 sourceC818 difference raw13443; decide +kernel
    rw [ha]
    exact (canonical13443 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA818 + difference 3 4) (sourceB818 + difference 4 3) sourceC818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5281) := by
    have ha : (tripleCharges (sourceA818 + difference 3 4) (sourceB818 + difference 4 3) sourceC818) = raw13444 := by
      apply Matrix.ext; unfold tripleCharges sourceA818 sourceB818 sourceC818 difference raw13444; decide +kernel
    rw [ha]
    exact (canonical13444 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA818 + difference 3 5) (sourceB818 + difference 5 3) sourceC818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5281) := by
    have ha : (tripleCharges (sourceA818 + difference 3 5) (sourceB818 + difference 5 3) sourceC818) = raw13445 := by
      apply Matrix.ext; unfold tripleCharges sourceA818 sourceB818 sourceC818 difference raw13445; decide +kernel
    rw [ha]
    exact (canonical13445 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA818 + difference 4 0) (sourceB818 + difference 0 4) sourceC818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4887) := by
    have ha : (tripleCharges (sourceA818 + difference 4 0) (sourceB818 + difference 0 4) sourceC818) = raw13446 := by
      apply Matrix.ext; unfold tripleCharges sourceA818 sourceB818 sourceC818 difference raw13446; decide +kernel
    rw [ha]
    exact (canonical13446 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA818 + difference 4 1) (sourceB818 + difference 1 4) sourceC818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA818 + difference 4 1) (sourceB818 + difference 1 4) sourceC818) = raw12660 := by
      apply Matrix.ext; unfold tripleCharges sourceA818 sourceB818 sourceC818 difference raw12660; decide +kernel
    rw [ha]
    exact (canonical12660 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA818 + difference 4 2) (sourceB818 + difference 2 4) sourceC818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA818 + difference 4 2) (sourceB818 + difference 2 4) sourceC818) = raw13447 := by
      apply Matrix.ext; unfold tripleCharges sourceA818 sourceB818 sourceC818 difference raw13447; decide +kernel
    rw [ha]
    exact (canonical13447 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA818 + difference 4 3) (sourceB818 + difference 3 4) sourceC818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5281) := by
    have ha : (tripleCharges (sourceA818 + difference 4 3) (sourceB818 + difference 3 4) sourceC818) = raw13331 := by
      apply Matrix.ext; unfold tripleCharges sourceA818 sourceB818 sourceC818 difference raw13331; decide +kernel
    rw [ha]
    exact (canonical13331 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA818 + difference 4 5) (sourceB818 + difference 5 4) sourceC818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5281) := by
    have ha : (tripleCharges (sourceA818 + difference 4 5) (sourceB818 + difference 5 4) sourceC818) = raw13448 := by
      apply Matrix.ext; unfold tripleCharges sourceA818 sourceB818 sourceC818 difference raw13448; decide +kernel
    rw [ha]
    exact (canonical13448 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA818 + difference 5 0) (sourceB818 + difference 0 5) sourceC818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4887) := by
    have ha : (tripleCharges (sourceA818 + difference 5 0) (sourceB818 + difference 0 5) sourceC818) = raw12653 := by
      apply Matrix.ext; unfold tripleCharges sourceA818 sourceB818 sourceC818 difference raw12653; decide +kernel
    rw [ha]
    exact (canonical12653 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA818 + difference 5 1) (sourceB818 + difference 1 5) sourceC818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA818 + difference 5 1) (sourceB818 + difference 1 5) sourceC818) = raw11669 := by
      apply Matrix.ext; unfold tripleCharges sourceA818 sourceB818 sourceC818 difference raw11669; decide +kernel
    rw [ha]
    exact (canonical11669 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA818 + difference 5 2) (sourceB818 + difference 2 5) sourceC818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA818 + difference 5 2) (sourceB818 + difference 2 5) sourceC818) = raw12191 := by
      apply Matrix.ext; unfold tripleCharges sourceA818 sourceB818 sourceC818 difference raw12191; decide +kernel
    rw [ha]
    exact (canonical12191 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA818 + difference 5 3) (sourceB818 + difference 3 5) sourceC818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5281) := by
    have ha : (tripleCharges (sourceA818 + difference 5 3) (sourceB818 + difference 3 5) sourceC818) = raw12467 := by
      apply Matrix.ext; unfold tripleCharges sourceA818 sourceB818 sourceC818 difference raw12467; decide +kernel
    rw [ha]
    exact (canonical12467 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA818 + difference 5 4) (sourceB818 + difference 4 5) sourceC818) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5281) := by
    have ha : (tripleCharges (sourceA818 + difference 5 4) (sourceB818 + difference 4 5) sourceC818) = raw12654 := by
      apply Matrix.ext; unfold tripleCharges sourceA818 sourceB818 sourceC818 difference raw12654; decide +kernel
    rw [ha]
    exact (canonical12654 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA818 sourceB818 sourceC818
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm818, Integer.Sparse.eval]
  linarith only [hs]

def sourceA819 : Charge := ![1, 1, 1, -1, -1, -1]
def sourceB819 : Charge := ![2, -1, -1, 0, 0, 0]
def sourceC819 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceForm819 : Integer.Sparse Master := [(Sum.inr 2703, 3), (Sum.inr 2741, 2), (Sum.inr 3023, 6), (Sum.inr 3053, 2), (Sum.inr 3074, 6), (Sum.inr 3100, 6), (Sum.inr 3221, 2), (Sum.inr 3226, 3)]

theorem sourceEq819 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm819 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA819 + difference 0 1) (sourceB819 + difference 1 0) sourceC819) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2741) := by
    have ha : (tripleCharges (sourceA819 + difference 0 1) (sourceB819 + difference 1 0) sourceC819) = raw13082 := by
      apply Matrix.ext; unfold tripleCharges sourceA819 sourceB819 sourceC819 difference raw13082; decide +kernel
    rw [ha]
    exact (canonical13082 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA819 + difference 0 2) (sourceB819 + difference 2 0) sourceC819) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2741) := by
    have ha : (tripleCharges (sourceA819 + difference 0 2) (sourceB819 + difference 2 0) sourceC819) = raw13449 := by
      apply Matrix.ext; unfold tripleCharges sourceA819 sourceB819 sourceC819 difference raw13449; decide +kernel
    rw [ha]
    exact (canonical13449 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA819 + difference 0 3) (sourceB819 + difference 3 0) sourceC819) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2703) := by
    have ha : (tripleCharges (sourceA819 + difference 0 3) (sourceB819 + difference 3 0) sourceC819) = raw13352 := by
      apply Matrix.ext; unfold tripleCharges sourceA819 sourceB819 sourceC819 difference raw13352; decide +kernel
    rw [ha]
    exact (canonical13352 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA819 + difference 0 4) (sourceB819 + difference 4 0) sourceC819) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2703) := by
    have ha : (tripleCharges (sourceA819 + difference 0 4) (sourceB819 + difference 4 0) sourceC819) = raw13450 := by
      apply Matrix.ext; unfold tripleCharges sourceA819 sourceB819 sourceC819 difference raw13450; decide +kernel
    rw [ha]
    exact (canonical13450 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA819 + difference 0 5) (sourceB819 + difference 5 0) sourceC819) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2703) := by
    have ha : (tripleCharges (sourceA819 + difference 0 5) (sourceB819 + difference 5 0) sourceC819) = raw13451 := by
      apply Matrix.ext; unfold tripleCharges sourceA819 sourceB819 sourceC819 difference raw13451; decide +kernel
    rw [ha]
    exact (canonical13451 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA819 + difference 1 0) (sourceB819 + difference 0 1) sourceC819) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3221) := by
    have ha : (tripleCharges (sourceA819 + difference 1 0) (sourceB819 + difference 0 1) sourceC819) = raw13452 := by
      apply Matrix.ext; unfold tripleCharges sourceA819 sourceB819 sourceC819 difference raw13452; decide +kernel
    rw [ha]
    exact (canonical13452 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA819 + difference 1 2) (sourceB819 + difference 2 1) sourceC819) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3053) := by
    have ha : (tripleCharges (sourceA819 + difference 1 2) (sourceB819 + difference 2 1) sourceC819) = raw13453 := by
      apply Matrix.ext; unfold tripleCharges sourceA819 sourceB819 sourceC819 difference raw13453; decide +kernel
    rw [ha]
    exact (canonical13453 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA819 + difference 1 3) (sourceB819 + difference 3 1) sourceC819) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3023) := by
    have ha : (tripleCharges (sourceA819 + difference 1 3) (sourceB819 + difference 3 1) sourceC819) = raw13357 := by
      apply Matrix.ext; unfold tripleCharges sourceA819 sourceB819 sourceC819 difference raw13357; decide +kernel
    rw [ha]
    exact (canonical13357 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA819 + difference 1 4) (sourceB819 + difference 4 1) sourceC819) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3023) := by
    have ha : (tripleCharges (sourceA819 + difference 1 4) (sourceB819 + difference 4 1) sourceC819) = raw13454 := by
      apply Matrix.ext; unfold tripleCharges sourceA819 sourceB819 sourceC819 difference raw13454; decide +kernel
    rw [ha]
    exact (canonical13454 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA819 + difference 1 5) (sourceB819 + difference 5 1) sourceC819) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3023) := by
    have ha : (tripleCharges (sourceA819 + difference 1 5) (sourceB819 + difference 5 1) sourceC819) = raw13455 := by
      apply Matrix.ext; unfold tripleCharges sourceA819 sourceB819 sourceC819 difference raw13455; decide +kernel
    rw [ha]
    exact (canonical13455 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA819 + difference 2 0) (sourceB819 + difference 0 2) sourceC819) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3221) := by
    have ha : (tripleCharges (sourceA819 + difference 2 0) (sourceB819 + difference 0 2) sourceC819) = raw13085 := by
      apply Matrix.ext; unfold tripleCharges sourceA819 sourceB819 sourceC819 difference raw13085; decide +kernel
    rw [ha]
    exact (canonical13085 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA819 + difference 2 1) (sourceB819 + difference 1 2) sourceC819) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3053) := by
    have ha : (tripleCharges (sourceA819 + difference 2 1) (sourceB819 + difference 1 2) sourceC819) = raw12049 := by
      apply Matrix.ext; unfold tripleCharges sourceA819 sourceB819 sourceC819 difference raw12049; decide +kernel
    rw [ha]
    exact (canonical12049 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA819 + difference 2 3) (sourceB819 + difference 3 2) sourceC819) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3023) := by
    have ha : (tripleCharges (sourceA819 + difference 2 3) (sourceB819 + difference 3 2) sourceC819) = raw12915 := by
      apply Matrix.ext; unfold tripleCharges sourceA819 sourceB819 sourceC819 difference raw12915; decide +kernel
    rw [ha]
    exact (canonical12915 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA819 + difference 2 4) (sourceB819 + difference 4 2) sourceC819) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3023) := by
    have ha : (tripleCharges (sourceA819 + difference 2 4) (sourceB819 + difference 4 2) sourceC819) = raw13087 := by
      apply Matrix.ext; unfold tripleCharges sourceA819 sourceB819 sourceC819 difference raw13087; decide +kernel
    rw [ha]
    exact (canonical13087 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA819 + difference 2 5) (sourceB819 + difference 5 2) sourceC819) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3023) := by
    have ha : (tripleCharges (sourceA819 + difference 2 5) (sourceB819 + difference 5 2) sourceC819) = raw13088 := by
      apply Matrix.ext; unfold tripleCharges sourceA819 sourceB819 sourceC819 difference raw13088; decide +kernel
    rw [ha]
    exact (canonical13088 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA819 + difference 3 0) (sourceB819 + difference 0 3) sourceC819) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3226) := by
    have ha : (tripleCharges (sourceA819 + difference 3 0) (sourceB819 + difference 0 3) sourceC819) = raw13456 := by
      apply Matrix.ext; unfold tripleCharges sourceA819 sourceB819 sourceC819 difference raw13456; decide +kernel
    rw [ha]
    exact (canonical13456 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA819 + difference 3 1) (sourceB819 + difference 1 3) sourceC819) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3100) := by
    have ha : (tripleCharges (sourceA819 + difference 3 1) (sourceB819 + difference 1 3) sourceC819) = raw13093 := by
      apply Matrix.ext; unfold tripleCharges sourceA819 sourceB819 sourceC819 difference raw13093; decide +kernel
    rw [ha]
    exact (canonical13093 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA819 + difference 3 2) (sourceB819 + difference 2 3) sourceC819) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3100) := by
    have ha : (tripleCharges (sourceA819 + difference 3 2) (sourceB819 + difference 2 3) sourceC819) = raw13457 := by
      apply Matrix.ext; unfold tripleCharges sourceA819 sourceB819 sourceC819 difference raw13457; decide +kernel
    rw [ha]
    exact (canonical13457 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA819 + difference 3 4) (sourceB819 + difference 4 3) sourceC819) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3074) := by
    have ha : (tripleCharges (sourceA819 + difference 3 4) (sourceB819 + difference 4 3) sourceC819) = raw13458 := by
      apply Matrix.ext; unfold tripleCharges sourceA819 sourceB819 sourceC819 difference raw13458; decide +kernel
    rw [ha]
    exact (canonical13458 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA819 + difference 3 5) (sourceB819 + difference 5 3) sourceC819) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3074) := by
    have ha : (tripleCharges (sourceA819 + difference 3 5) (sourceB819 + difference 5 3) sourceC819) = raw13459 := by
      apply Matrix.ext; unfold tripleCharges sourceA819 sourceB819 sourceC819 difference raw13459; decide +kernel
    rw [ha]
    exact (canonical13459 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA819 + difference 4 0) (sourceB819 + difference 0 4) sourceC819) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3226) := by
    have ha : (tripleCharges (sourceA819 + difference 4 0) (sourceB819 + difference 0 4) sourceC819) = raw13460 := by
      apply Matrix.ext; unfold tripleCharges sourceA819 sourceB819 sourceC819 difference raw13460; decide +kernel
    rw [ha]
    exact (canonical13460 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA819 + difference 4 1) (sourceB819 + difference 1 4) sourceC819) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3100) := by
    have ha : (tripleCharges (sourceA819 + difference 4 1) (sourceB819 + difference 1 4) sourceC819) = raw13097 := by
      apply Matrix.ext; unfold tripleCharges sourceA819 sourceB819 sourceC819 difference raw13097; decide +kernel
    rw [ha]
    exact (canonical13097 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA819 + difference 4 2) (sourceB819 + difference 2 4) sourceC819) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3100) := by
    have ha : (tripleCharges (sourceA819 + difference 4 2) (sourceB819 + difference 2 4) sourceC819) = raw13461 := by
      apply Matrix.ext; unfold tripleCharges sourceA819 sourceB819 sourceC819 difference raw13461; decide +kernel
    rw [ha]
    exact (canonical13461 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA819 + difference 4 3) (sourceB819 + difference 3 4) sourceC819) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3074) := by
    have ha : (tripleCharges (sourceA819 + difference 4 3) (sourceB819 + difference 3 4) sourceC819) = raw13363 := by
      apply Matrix.ext; unfold tripleCharges sourceA819 sourceB819 sourceC819 difference raw13363; decide +kernel
    rw [ha]
    exact (canonical13363 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA819 + difference 4 5) (sourceB819 + difference 5 4) sourceC819) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3074) := by
    have ha : (tripleCharges (sourceA819 + difference 4 5) (sourceB819 + difference 5 4) sourceC819) = raw13462 := by
      apply Matrix.ext; unfold tripleCharges sourceA819 sourceB819 sourceC819 difference raw13462; decide +kernel
    rw [ha]
    exact (canonical13462 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA819 + difference 5 0) (sourceB819 + difference 0 5) sourceC819) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3226) := by
    have ha : (tripleCharges (sourceA819 + difference 5 0) (sourceB819 + difference 0 5) sourceC819) = raw13358 := by
      apply Matrix.ext; unfold tripleCharges sourceA819 sourceB819 sourceC819 difference raw13358; decide +kernel
    rw [ha]
    exact (canonical13358 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA819 + difference 5 1) (sourceB819 + difference 1 5) sourceC819) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3100) := by
    have ha : (tripleCharges (sourceA819 + difference 5 1) (sourceB819 + difference 1 5) sourceC819) = raw11729 := by
      apply Matrix.ext; unfold tripleCharges sourceA819 sourceB819 sourceC819 difference raw11729; decide +kernel
    rw [ha]
    exact (canonical11729 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA819 + difference 5 2) (sourceB819 + difference 2 5) sourceC819) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3100) := by
    have ha : (tripleCharges (sourceA819 + difference 5 2) (sourceB819 + difference 2 5) sourceC819) = raw12212 := by
      apply Matrix.ext; unfold tripleCharges sourceA819 sourceB819 sourceC819 difference raw12212; decide +kernel
    rw [ha]
    exact (canonical12212 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA819 + difference 5 3) (sourceB819 + difference 3 5) sourceC819) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3074) := by
    have ha : (tripleCharges (sourceA819 + difference 5 3) (sourceB819 + difference 3 5) sourceC819) = raw12503 := by
      apply Matrix.ext; unfold tripleCharges sourceA819 sourceB819 sourceC819 difference raw12503; decide +kernel
    rw [ha]
    exact (canonical12503 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA819 + difference 5 4) (sourceB819 + difference 4 5) sourceC819) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3074) := by
    have ha : (tripleCharges (sourceA819 + difference 5 4) (sourceB819 + difference 4 5) sourceC819) = raw13359 := by
      apply Matrix.ext; unfold tripleCharges sourceA819 sourceB819 sourceC819 difference raw13359; decide +kernel
    rw [ha]
    exact (canonical13359 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA819 sourceB819 sourceC819
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm819, Integer.Sparse.eval]
  linarith only [hs]

def sourceA820 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB820 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC820 : Charge := ![2, -1, 0, -1, -1, 1]
def sourceForm820 : Integer.Sparse Master := [(Sum.inr 4599, 1), (Sum.inr 4600, 1), (Sum.inr 4603, 2), (Sum.inr 4618, 1), (Sum.inr 5145, 2), (Sum.inr 5150, 1), (Sum.inr 5162, 1), (Sum.inr 5197, 1), (Sum.inr 5199, 2), (Sum.inr 5205, 1), (Sum.inr 5257, 1), (Sum.inr 5259, 2), (Sum.inr 5270, 2), (Sum.inr 5273, 1), (Sum.inr 5281, 2), (Sum.inr 5282, 2), (Sum.inr 5290, 2), (Sum.inr 5431, 1), (Sum.inr 5440, 1), (Sum.inr 5448, 1), (Sum.inr 5450, 2)]

theorem sourceEq820 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm820 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA820 + difference 0 1) (sourceB820 + difference 1 0) sourceC820) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5448) := by
    have ha : (tripleCharges (sourceA820 + difference 0 1) (sourceB820 + difference 1 0) sourceC820) = raw13463 := by
      apply Matrix.ext; unfold tripleCharges sourceA820 sourceB820 sourceC820 difference raw13463; decide +kernel
    rw [ha]
    exact (canonical13463 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA820 + difference 0 2) (sourceB820 + difference 2 0) sourceC820) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA820 + difference 0 2) (sourceB820 + difference 2 0) sourceC820) = raw13464 := by
      apply Matrix.ext; unfold tripleCharges sourceA820 sourceB820 sourceC820 difference raw13464; decide +kernel
    rw [ha]
    exact (canonical13464 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA820 + difference 0 3) (sourceB820 + difference 3 0) sourceC820) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA820 + difference 0 3) (sourceB820 + difference 3 0) sourceC820) = raw13465 := by
      apply Matrix.ext; unfold tripleCharges sourceA820 sourceB820 sourceC820 difference raw13465; decide +kernel
    rw [ha]
    exact (canonical13465 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA820 + difference 0 4) (sourceB820 + difference 4 0) sourceC820) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA820 + difference 0 4) (sourceB820 + difference 4 0) sourceC820) = raw13466 := by
      apply Matrix.ext; unfold tripleCharges sourceA820 sourceB820 sourceC820 difference raw13466; decide +kernel
    rw [ha]
    exact (canonical13466 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA820 + difference 0 5) (sourceB820 + difference 5 0) sourceC820) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5440) := by
    have ha : (tripleCharges (sourceA820 + difference 0 5) (sourceB820 + difference 5 0) sourceC820) = raw13467 := by
      apply Matrix.ext; unfold tripleCharges sourceA820 sourceB820 sourceC820 difference raw13467; decide +kernel
    rw [ha]
    exact (canonical13467 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA820 + difference 1 0) (sourceB820 + difference 0 1) sourceC820) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4618) := by
    have ha : (tripleCharges (sourceA820 + difference 1 0) (sourceB820 + difference 0 1) sourceC820) = raw13468 := by
      apply Matrix.ext; unfold tripleCharges sourceA820 sourceB820 sourceC820 difference raw13468; decide +kernel
    rw [ha]
    exact (canonical13468 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA820 + difference 1 2) (sourceB820 + difference 2 1) sourceC820) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5162) := by
    have ha : (tripleCharges (sourceA820 + difference 1 2) (sourceB820 + difference 2 1) sourceC820) = raw13469 := by
      apply Matrix.ext; unfold tripleCharges sourceA820 sourceB820 sourceC820 difference raw13469; decide +kernel
    rw [ha]
    exact (canonical13469 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA820 + difference 1 3) (sourceB820 + difference 3 1) sourceC820) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA820 + difference 1 3) (sourceB820 + difference 3 1) sourceC820) = raw13470 := by
      apply Matrix.ext; unfold tripleCharges sourceA820 sourceB820 sourceC820 difference raw13470; decide +kernel
    rw [ha]
    exact (canonical13470 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA820 + difference 1 4) (sourceB820 + difference 4 1) sourceC820) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA820 + difference 1 4) (sourceB820 + difference 4 1) sourceC820) = raw13471 := by
      apply Matrix.ext; unfold tripleCharges sourceA820 sourceB820 sourceC820 difference raw13471; decide +kernel
    rw [ha]
    exact (canonical13471 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA820 + difference 1 5) (sourceB820 + difference 5 1) sourceC820) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5273) := by
    have ha : (tripleCharges (sourceA820 + difference 1 5) (sourceB820 + difference 5 1) sourceC820) = raw13472 := by
      apply Matrix.ext; unfold tripleCharges sourceA820 sourceB820 sourceC820 difference raw13472; decide +kernel
    rw [ha]
    exact (canonical13472 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA820 + difference 2 0) (sourceB820 + difference 0 2) sourceC820) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4599) := by
    have ha : (tripleCharges (sourceA820 + difference 2 0) (sourceB820 + difference 0 2) sourceC820) = raw13473 := by
      apply Matrix.ext; unfold tripleCharges sourceA820 sourceB820 sourceC820 difference raw13473; decide +kernel
    rw [ha]
    exact (canonical13473 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA820 + difference 2 1) (sourceB820 + difference 1 2) sourceC820) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5197) := by
    have ha : (tripleCharges (sourceA820 + difference 2 1) (sourceB820 + difference 1 2) sourceC820) = raw13474 := by
      apply Matrix.ext; unfold tripleCharges sourceA820 sourceB820 sourceC820 difference raw13474; decide +kernel
    rw [ha]
    exact (canonical13474 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA820 + difference 2 3) (sourceB820 + difference 3 2) sourceC820) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5281) := by
    have ha : (tripleCharges (sourceA820 + difference 2 3) (sourceB820 + difference 3 2) sourceC820) = raw13475 := by
      apply Matrix.ext; unfold tripleCharges sourceA820 sourceB820 sourceC820 difference raw13475; decide +kernel
    rw [ha]
    exact (canonical13475 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA820 + difference 2 4) (sourceB820 + difference 4 2) sourceC820) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5281) := by
    have ha : (tripleCharges (sourceA820 + difference 2 4) (sourceB820 + difference 4 2) sourceC820) = raw13476 := by
      apply Matrix.ext; unfold tripleCharges sourceA820 sourceB820 sourceC820 difference raw13476; decide +kernel
    rw [ha]
    exact (canonical13476 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA820 + difference 2 5) (sourceB820 + difference 5 2) sourceC820) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA820 + difference 2 5) (sourceB820 + difference 5 2) sourceC820) = raw13477 := by
      apply Matrix.ext; unfold tripleCharges sourceA820 sourceB820 sourceC820 difference raw13477; decide +kernel
    rw [ha]
    exact (canonical13477 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA820 + difference 3 0) (sourceB820 + difference 0 3) sourceC820) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4603) := by
    have ha : (tripleCharges (sourceA820 + difference 3 0) (sourceB820 + difference 0 3) sourceC820) = raw13478 := by
      apply Matrix.ext; unfold tripleCharges sourceA820 sourceB820 sourceC820 difference raw13478; decide +kernel
    rw [ha]
    exact (canonical13478 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA820 + difference 3 1) (sourceB820 + difference 1 3) sourceC820) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5199) := by
    have ha : (tripleCharges (sourceA820 + difference 3 1) (sourceB820 + difference 1 3) sourceC820) = raw13479 := by
      apply Matrix.ext; unfold tripleCharges sourceA820 sourceB820 sourceC820 difference raw13479; decide +kernel
    rw [ha]
    exact (canonical13479 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA820 + difference 3 2) (sourceB820 + difference 2 3) sourceC820) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5145) := by
    have ha : (tripleCharges (sourceA820 + difference 3 2) (sourceB820 + difference 2 3) sourceC820) = raw13480 := by
      apply Matrix.ext; unfold tripleCharges sourceA820 sourceB820 sourceC820 difference raw13480; decide +kernel
    rw [ha]
    exact (canonical13480 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA820 + difference 3 4) (sourceB820 + difference 4 3) sourceC820) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5282) := by
    have ha : (tripleCharges (sourceA820 + difference 3 4) (sourceB820 + difference 4 3) sourceC820) = raw13481 := by
      apply Matrix.ext; unfold tripleCharges sourceA820 sourceB820 sourceC820 difference raw13481; decide +kernel
    rw [ha]
    exact (canonical13481 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA820 + difference 3 5) (sourceB820 + difference 5 3) sourceC820) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA820 + difference 3 5) (sourceB820 + difference 5 3) sourceC820) = raw13482 := by
      apply Matrix.ext; unfold tripleCharges sourceA820 sourceB820 sourceC820 difference raw13482; decide +kernel
    rw [ha]
    exact (canonical13482 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA820 + difference 4 0) (sourceB820 + difference 0 4) sourceC820) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4603) := by
    have ha : (tripleCharges (sourceA820 + difference 4 0) (sourceB820 + difference 0 4) sourceC820) = raw13483 := by
      apply Matrix.ext; unfold tripleCharges sourceA820 sourceB820 sourceC820 difference raw13483; decide +kernel
    rw [ha]
    exact (canonical13483 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA820 + difference 4 1) (sourceB820 + difference 1 4) sourceC820) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5199) := by
    have ha : (tripleCharges (sourceA820 + difference 4 1) (sourceB820 + difference 1 4) sourceC820) = raw13484 := by
      apply Matrix.ext; unfold tripleCharges sourceA820 sourceB820 sourceC820 difference raw13484; decide +kernel
    rw [ha]
    exact (canonical13484 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA820 + difference 4 2) (sourceB820 + difference 2 4) sourceC820) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5145) := by
    have ha : (tripleCharges (sourceA820 + difference 4 2) (sourceB820 + difference 2 4) sourceC820) = raw13485 := by
      apply Matrix.ext; unfold tripleCharges sourceA820 sourceB820 sourceC820 difference raw13485; decide +kernel
    rw [ha]
    exact (canonical13485 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA820 + difference 4 3) (sourceB820 + difference 3 4) sourceC820) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5282) := by
    have ha : (tripleCharges (sourceA820 + difference 4 3) (sourceB820 + difference 3 4) sourceC820) = raw13486 := by
      apply Matrix.ext; unfold tripleCharges sourceA820 sourceB820 sourceC820 difference raw13486; decide +kernel
    rw [ha]
    exact (canonical13486 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA820 + difference 4 5) (sourceB820 + difference 5 4) sourceC820) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA820 + difference 4 5) (sourceB820 + difference 5 4) sourceC820) = raw13487 := by
      apply Matrix.ext; unfold tripleCharges sourceA820 sourceB820 sourceC820 difference raw13487; decide +kernel
    rw [ha]
    exact (canonical13487 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA820 + difference 5 0) (sourceB820 + difference 0 5) sourceC820) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4600) := by
    have ha : (tripleCharges (sourceA820 + difference 5 0) (sourceB820 + difference 0 5) sourceC820) = raw13488 := by
      apply Matrix.ext; unfold tripleCharges sourceA820 sourceB820 sourceC820 difference raw13488; decide +kernel
    rw [ha]
    exact (canonical13488 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA820 + difference 5 1) (sourceB820 + difference 1 5) sourceC820) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5205) := by
    have ha : (tripleCharges (sourceA820 + difference 5 1) (sourceB820 + difference 1 5) sourceC820) = raw13489 := by
      apply Matrix.ext; unfold tripleCharges sourceA820 sourceB820 sourceC820 difference raw13489; decide +kernel
    rw [ha]
    exact (canonical13489 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA820 + difference 5 2) (sourceB820 + difference 2 5) sourceC820) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5150) := by
    have ha : (tripleCharges (sourceA820 + difference 5 2) (sourceB820 + difference 2 5) sourceC820) = raw13490 := by
      apply Matrix.ext; unfold tripleCharges sourceA820 sourceB820 sourceC820 difference raw13490; decide +kernel
    rw [ha]
    exact (canonical13490 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA820 + difference 5 3) (sourceB820 + difference 3 5) sourceC820) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5270) := by
    have ha : (tripleCharges (sourceA820 + difference 5 3) (sourceB820 + difference 3 5) sourceC820) = raw13491 := by
      apply Matrix.ext; unfold tripleCharges sourceA820 sourceB820 sourceC820 difference raw13491; decide +kernel
    rw [ha]
    exact (canonical13491 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA820 + difference 5 4) (sourceB820 + difference 4 5) sourceC820) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5270) := by
    have ha : (tripleCharges (sourceA820 + difference 5 4) (sourceB820 + difference 4 5) sourceC820) = raw13492 := by
      apply Matrix.ext; unfold tripleCharges sourceA820 sourceB820 sourceC820 difference raw13492; decide +kernel
    rw [ha]
    exact (canonical13492 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA820 sourceB820 sourceC820
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm820, Integer.Sparse.eval]
  linarith only [hs]

def sourceA821 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB821 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC821 : Charge := ![2, -1, 0, -1, -1, 1]
def sourceForm821 : Integer.Sparse Master := [(Sum.inr 1233, 1), (Sum.inr 1234, 1), (Sum.inr 1237, 2), (Sum.inr 1298, 1), (Sum.inr 2878, 1), (Sum.inr 2879, 1), (Sum.inr 2882, 2), (Sum.inr 2923, 1), (Sum.inr 2925, 2), (Sum.inr 2957, 1), (Sum.inr 3074, 2), (Sum.inr 3075, 2), (Sum.inr 3078, 2), (Sum.inr 3087, 1), (Sum.inr 3088, 2), (Sum.inr 3099, 2), (Sum.inr 3111, 1), (Sum.inr 4026, 1), (Sum.inr 4028, 1), (Sum.inr 4029, 2), (Sum.inr 4036, 1)]

theorem sourceEq821 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm821 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA821 + difference 0 1) (sourceB821 + difference 1 0) sourceC821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4028) := by
    have ha : (tripleCharges (sourceA821 + difference 0 1) (sourceB821 + difference 1 0) sourceC821) = raw13493 := by
      apply Matrix.ext; unfold tripleCharges sourceA821 sourceB821 sourceC821 difference raw13493; decide +kernel
    rw [ha]
    exact (canonical13493 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA821 + difference 0 2) (sourceB821 + difference 2 0) sourceC821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4026) := by
    have ha : (tripleCharges (sourceA821 + difference 0 2) (sourceB821 + difference 2 0) sourceC821) = raw13494 := by
      apply Matrix.ext; unfold tripleCharges sourceA821 sourceB821 sourceC821 difference raw13494; decide +kernel
    rw [ha]
    exact (canonical13494 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA821 + difference 0 3) (sourceB821 + difference 3 0) sourceC821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4029) := by
    have ha : (tripleCharges (sourceA821 + difference 0 3) (sourceB821 + difference 3 0) sourceC821) = raw13495 := by
      apply Matrix.ext; unfold tripleCharges sourceA821 sourceB821 sourceC821 difference raw13495; decide +kernel
    rw [ha]
    exact (canonical13495 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA821 + difference 0 4) (sourceB821 + difference 4 0) sourceC821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4029) := by
    have ha : (tripleCharges (sourceA821 + difference 0 4) (sourceB821 + difference 4 0) sourceC821) = raw13496 := by
      apply Matrix.ext; unfold tripleCharges sourceA821 sourceB821 sourceC821 difference raw13496; decide +kernel
    rw [ha]
    exact (canonical13496 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA821 + difference 0 5) (sourceB821 + difference 5 0) sourceC821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4036) := by
    have ha : (tripleCharges (sourceA821 + difference 0 5) (sourceB821 + difference 5 0) sourceC821) = raw13497 := by
      apply Matrix.ext; unfold tripleCharges sourceA821 sourceB821 sourceC821 difference raw13497; decide +kernel
    rw [ha]
    exact (canonical13497 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA821 + difference 1 0) (sourceB821 + difference 0 1) sourceC821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1298) := by
    have ha : (tripleCharges (sourceA821 + difference 1 0) (sourceB821 + difference 0 1) sourceC821) = raw13498 := by
      apply Matrix.ext; unfold tripleCharges sourceA821 sourceB821 sourceC821 difference raw13498; decide +kernel
    rw [ha]
    exact (canonical13498 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA821 + difference 1 2) (sourceB821 + difference 2 1) sourceC821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2957) := by
    have ha : (tripleCharges (sourceA821 + difference 1 2) (sourceB821 + difference 2 1) sourceC821) = raw13499 := by
      apply Matrix.ext; unfold tripleCharges sourceA821 sourceB821 sourceC821 difference raw13499; decide +kernel
    rw [ha]
    exact (canonical13499 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA821 + difference 1 3) (sourceB821 + difference 3 1) sourceC821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3099) := by
    have ha : (tripleCharges (sourceA821 + difference 1 3) (sourceB821 + difference 3 1) sourceC821) = raw13500 := by
      apply Matrix.ext; unfold tripleCharges sourceA821 sourceB821 sourceC821 difference raw13500; decide +kernel
    rw [ha]
    exact (canonical13500 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA821 + difference 1 4) (sourceB821 + difference 4 1) sourceC821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3099) := by
    have ha : (tripleCharges (sourceA821 + difference 1 4) (sourceB821 + difference 4 1) sourceC821) = raw13501 := by
      apply Matrix.ext; unfold tripleCharges sourceA821 sourceB821 sourceC821 difference raw13501; decide +kernel
    rw [ha]
    exact (canonical13501 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA821 + difference 1 5) (sourceB821 + difference 5 1) sourceC821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3111) := by
    have ha : (tripleCharges (sourceA821 + difference 1 5) (sourceB821 + difference 5 1) sourceC821) = raw13502 := by
      apply Matrix.ext; unfold tripleCharges sourceA821 sourceB821 sourceC821 difference raw13502; decide +kernel
    rw [ha]
    exact (canonical13502 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA821 + difference 2 0) (sourceB821 + difference 0 2) sourceC821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1233) := by
    have ha : (tripleCharges (sourceA821 + difference 2 0) (sourceB821 + difference 0 2) sourceC821) = raw13503 := by
      apply Matrix.ext; unfold tripleCharges sourceA821 sourceB821 sourceC821 difference raw13503; decide +kernel
    rw [ha]
    exact (canonical13503 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA821 + difference 2 1) (sourceB821 + difference 1 2) sourceC821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2878) := by
    have ha : (tripleCharges (sourceA821 + difference 2 1) (sourceB821 + difference 1 2) sourceC821) = raw13504 := by
      apply Matrix.ext; unfold tripleCharges sourceA821 sourceB821 sourceC821 difference raw13504; decide +kernel
    rw [ha]
    exact (canonical13504 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA821 + difference 2 3) (sourceB821 + difference 3 2) sourceC821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3074) := by
    have ha : (tripleCharges (sourceA821 + difference 2 3) (sourceB821 + difference 3 2) sourceC821) = raw13505 := by
      apply Matrix.ext; unfold tripleCharges sourceA821 sourceB821 sourceC821 difference raw13505; decide +kernel
    rw [ha]
    exact (canonical13505 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA821 + difference 2 4) (sourceB821 + difference 4 2) sourceC821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3074) := by
    have ha : (tripleCharges (sourceA821 + difference 2 4) (sourceB821 + difference 4 2) sourceC821) = raw13506 := by
      apply Matrix.ext; unfold tripleCharges sourceA821 sourceB821 sourceC821 difference raw13506; decide +kernel
    rw [ha]
    exact (canonical13506 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA821 + difference 2 5) (sourceB821 + difference 5 2) sourceC821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3087) := by
    have ha : (tripleCharges (sourceA821 + difference 2 5) (sourceB821 + difference 5 2) sourceC821) = raw13507 := by
      apply Matrix.ext; unfold tripleCharges sourceA821 sourceB821 sourceC821 difference raw13507; decide +kernel
    rw [ha]
    exact (canonical13507 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA821 + difference 3 0) (sourceB821 + difference 0 3) sourceC821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1237) := by
    have ha : (tripleCharges (sourceA821 + difference 3 0) (sourceB821 + difference 0 3) sourceC821) = raw13508 := by
      apply Matrix.ext; unfold tripleCharges sourceA821 sourceB821 sourceC821 difference raw13508; decide +kernel
    rw [ha]
    exact (canonical13508 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA821 + difference 3 1) (sourceB821 + difference 1 3) sourceC821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2882) := by
    have ha : (tripleCharges (sourceA821 + difference 3 1) (sourceB821 + difference 1 3) sourceC821) = raw13509 := by
      apply Matrix.ext; unfold tripleCharges sourceA821 sourceB821 sourceC821 difference raw13509; decide +kernel
    rw [ha]
    exact (canonical13509 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA821 + difference 3 2) (sourceB821 + difference 2 3) sourceC821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2925) := by
    have ha : (tripleCharges (sourceA821 + difference 3 2) (sourceB821 + difference 2 3) sourceC821) = raw13510 := by
      apply Matrix.ext; unfold tripleCharges sourceA821 sourceB821 sourceC821 difference raw13510; decide +kernel
    rw [ha]
    exact (canonical13510 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA821 + difference 3 4) (sourceB821 + difference 4 3) sourceC821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3078) := by
    have ha : (tripleCharges (sourceA821 + difference 3 4) (sourceB821 + difference 4 3) sourceC821) = raw13511 := by
      apply Matrix.ext; unfold tripleCharges sourceA821 sourceB821 sourceC821 difference raw13511; decide +kernel
    rw [ha]
    exact (canonical13511 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA821 + difference 3 5) (sourceB821 + difference 5 3) sourceC821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3088) := by
    have ha : (tripleCharges (sourceA821 + difference 3 5) (sourceB821 + difference 5 3) sourceC821) = raw13512 := by
      apply Matrix.ext; unfold tripleCharges sourceA821 sourceB821 sourceC821 difference raw13512; decide +kernel
    rw [ha]
    exact (canonical13512 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA821 + difference 4 0) (sourceB821 + difference 0 4) sourceC821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1237) := by
    have ha : (tripleCharges (sourceA821 + difference 4 0) (sourceB821 + difference 0 4) sourceC821) = raw13513 := by
      apply Matrix.ext; unfold tripleCharges sourceA821 sourceB821 sourceC821 difference raw13513; decide +kernel
    rw [ha]
    exact (canonical13513 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA821 + difference 4 1) (sourceB821 + difference 1 4) sourceC821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2882) := by
    have ha : (tripleCharges (sourceA821 + difference 4 1) (sourceB821 + difference 1 4) sourceC821) = raw13514 := by
      apply Matrix.ext; unfold tripleCharges sourceA821 sourceB821 sourceC821 difference raw13514; decide +kernel
    rw [ha]
    exact (canonical13514 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA821 + difference 4 2) (sourceB821 + difference 2 4) sourceC821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2925) := by
    have ha : (tripleCharges (sourceA821 + difference 4 2) (sourceB821 + difference 2 4) sourceC821) = raw13515 := by
      apply Matrix.ext; unfold tripleCharges sourceA821 sourceB821 sourceC821 difference raw13515; decide +kernel
    rw [ha]
    exact (canonical13515 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA821 + difference 4 3) (sourceB821 + difference 3 4) sourceC821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3078) := by
    have ha : (tripleCharges (sourceA821 + difference 4 3) (sourceB821 + difference 3 4) sourceC821) = raw13516 := by
      apply Matrix.ext; unfold tripleCharges sourceA821 sourceB821 sourceC821 difference raw13516; decide +kernel
    rw [ha]
    exact (canonical13516 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA821 + difference 4 5) (sourceB821 + difference 5 4) sourceC821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3088) := by
    have ha : (tripleCharges (sourceA821 + difference 4 5) (sourceB821 + difference 5 4) sourceC821) = raw13517 := by
      apply Matrix.ext; unfold tripleCharges sourceA821 sourceB821 sourceC821 difference raw13517; decide +kernel
    rw [ha]
    exact (canonical13517 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA821 + difference 5 0) (sourceB821 + difference 0 5) sourceC821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1234) := by
    have ha : (tripleCharges (sourceA821 + difference 5 0) (sourceB821 + difference 0 5) sourceC821) = raw13518 := by
      apply Matrix.ext; unfold tripleCharges sourceA821 sourceB821 sourceC821 difference raw13518; decide +kernel
    rw [ha]
    exact (canonical13518 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA821 + difference 5 1) (sourceB821 + difference 1 5) sourceC821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2879) := by
    have ha : (tripleCharges (sourceA821 + difference 5 1) (sourceB821 + difference 1 5) sourceC821) = raw13519 := by
      apply Matrix.ext; unfold tripleCharges sourceA821 sourceB821 sourceC821 difference raw13519; decide +kernel
    rw [ha]
    exact (canonical13519 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA821 + difference 5 2) (sourceB821 + difference 2 5) sourceC821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2923) := by
    have ha : (tripleCharges (sourceA821 + difference 5 2) (sourceB821 + difference 2 5) sourceC821) = raw13520 := by
      apply Matrix.ext; unfold tripleCharges sourceA821 sourceB821 sourceC821 difference raw13520; decide +kernel
    rw [ha]
    exact (canonical13520 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA821 + difference 5 3) (sourceB821 + difference 3 5) sourceC821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3075) := by
    have ha : (tripleCharges (sourceA821 + difference 5 3) (sourceB821 + difference 3 5) sourceC821) = raw13521 := by
      apply Matrix.ext; unfold tripleCharges sourceA821 sourceB821 sourceC821 difference raw13521; decide +kernel
    rw [ha]
    exact (canonical13521 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA821 + difference 5 4) (sourceB821 + difference 4 5) sourceC821) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3075) := by
    have ha : (tripleCharges (sourceA821 + difference 5 4) (sourceB821 + difference 4 5) sourceC821) = raw13522 := by
      apply Matrix.ext; unfold tripleCharges sourceA821 sourceB821 sourceC821 difference raw13522; decide +kernel
    rw [ha]
    exact (canonical13522 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA821 sourceB821 sourceC821
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm821, Integer.Sparse.eval]
  linarith only [hs]

def sourceA822 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB822 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC822 : Charge := ![2, -1, 0, -1, -1, 1]
def sourceForm822 : Integer.Sparse Master := [(Sum.inr 2700, 1), (Sum.inr 2702, 1), (Sum.inr 2706, 1), (Sum.inr 2738, 2), (Sum.inr 3289, 1), (Sum.inr 3294, 2), (Sum.inr 3304, 1), (Sum.inr 3532, 1), (Sum.inr 3544, 2), (Sum.inr 3546, 1), (Sum.inr 3562, 2), (Sum.inr 3563, 1), (Sum.inr 3569, 1), (Sum.inr 3571, 2), (Sum.inr 3578, 2), (Sum.inr 3580, 2), (Sum.inr 3581, 2), (Sum.inr 3859, 1), (Sum.inr 3875, 1), (Sum.inr 3885, 1), (Sum.inr 3887, 2)]

theorem sourceEq822 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm822 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA822 + difference 0 1) (sourceB822 + difference 1 0) sourceC822) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3885) := by
    have ha : (tripleCharges (sourceA822 + difference 0 1) (sourceB822 + difference 1 0) sourceC822) = raw13523 := by
      apply Matrix.ext; unfold tripleCharges sourceA822 sourceB822 sourceC822 difference raw13523; decide +kernel
    rw [ha]
    exact (canonical13523 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA822 + difference 0 2) (sourceB822 + difference 2 0) sourceC822) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3875) := by
    have ha : (tripleCharges (sourceA822 + difference 0 2) (sourceB822 + difference 2 0) sourceC822) = raw13524 := by
      apply Matrix.ext; unfold tripleCharges sourceA822 sourceB822 sourceC822 difference raw13524; decide +kernel
    rw [ha]
    exact (canonical13524 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA822 + difference 0 3) (sourceB822 + difference 3 0) sourceC822) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3887) := by
    have ha : (tripleCharges (sourceA822 + difference 0 3) (sourceB822 + difference 3 0) sourceC822) = raw13525 := by
      apply Matrix.ext; unfold tripleCharges sourceA822 sourceB822 sourceC822 difference raw13525; decide +kernel
    rw [ha]
    exact (canonical13525 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA822 + difference 0 4) (sourceB822 + difference 4 0) sourceC822) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3887) := by
    have ha : (tripleCharges (sourceA822 + difference 0 4) (sourceB822 + difference 4 0) sourceC822) = raw13526 := by
      apply Matrix.ext; unfold tripleCharges sourceA822 sourceB822 sourceC822 difference raw13526; decide +kernel
    rw [ha]
    exact (canonical13526 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA822 + difference 0 5) (sourceB822 + difference 5 0) sourceC822) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3859) := by
    have ha : (tripleCharges (sourceA822 + difference 0 5) (sourceB822 + difference 5 0) sourceC822) = raw13527 := by
      apply Matrix.ext; unfold tripleCharges sourceA822 sourceB822 sourceC822 difference raw13527; decide +kernel
    rw [ha]
    exact (canonical13527 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA822 + difference 1 0) (sourceB822 + difference 0 1) sourceC822) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3304) := by
    have ha : (tripleCharges (sourceA822 + difference 1 0) (sourceB822 + difference 0 1) sourceC822) = raw13528 := by
      apply Matrix.ext; unfold tripleCharges sourceA822 sourceB822 sourceC822 difference raw13528; decide +kernel
    rw [ha]
    exact (canonical13528 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA822 + difference 1 2) (sourceB822 + difference 2 1) sourceC822) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3563) := by
    have ha : (tripleCharges (sourceA822 + difference 1 2) (sourceB822 + difference 2 1) sourceC822) = raw13529 := by
      apply Matrix.ext; unfold tripleCharges sourceA822 sourceB822 sourceC822 difference raw13529; decide +kernel
    rw [ha]
    exact (canonical13529 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA822 + difference 1 3) (sourceB822 + difference 3 1) sourceC822) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3581) := by
    have ha : (tripleCharges (sourceA822 + difference 1 3) (sourceB822 + difference 3 1) sourceC822) = raw13530 := by
      apply Matrix.ext; unfold tripleCharges sourceA822 sourceB822 sourceC822 difference raw13530; decide +kernel
    rw [ha]
    exact (canonical13530 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA822 + difference 1 4) (sourceB822 + difference 4 1) sourceC822) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3581) := by
    have ha : (tripleCharges (sourceA822 + difference 1 4) (sourceB822 + difference 4 1) sourceC822) = raw13531 := by
      apply Matrix.ext; unfold tripleCharges sourceA822 sourceB822 sourceC822 difference raw13531; decide +kernel
    rw [ha]
    exact (canonical13531 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA822 + difference 1 5) (sourceB822 + difference 5 1) sourceC822) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3546) := by
    have ha : (tripleCharges (sourceA822 + difference 1 5) (sourceB822 + difference 5 1) sourceC822) = raw13532 := by
      apply Matrix.ext; unfold tripleCharges sourceA822 sourceB822 sourceC822 difference raw13532; decide +kernel
    rw [ha]
    exact (canonical13532 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA822 + difference 2 0) (sourceB822 + difference 0 2) sourceC822) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3289) := by
    have ha : (tripleCharges (sourceA822 + difference 2 0) (sourceB822 + difference 0 2) sourceC822) = raw13533 := by
      apply Matrix.ext; unfold tripleCharges sourceA822 sourceB822 sourceC822 difference raw13533; decide +kernel
    rw [ha]
    exact (canonical13533 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA822 + difference 2 1) (sourceB822 + difference 1 2) sourceC822) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3569) := by
    have ha : (tripleCharges (sourceA822 + difference 2 1) (sourceB822 + difference 1 2) sourceC822) = raw13534 := by
      apply Matrix.ext; unfold tripleCharges sourceA822 sourceB822 sourceC822 difference raw13534; decide +kernel
    rw [ha]
    exact (canonical13534 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA822 + difference 2 3) (sourceB822 + difference 3 2) sourceC822) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3571) := by
    have ha : (tripleCharges (sourceA822 + difference 2 3) (sourceB822 + difference 3 2) sourceC822) = raw13535 := by
      apply Matrix.ext; unfold tripleCharges sourceA822 sourceB822 sourceC822 difference raw13535; decide +kernel
    rw [ha]
    exact (canonical13535 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA822 + difference 2 4) (sourceB822 + difference 4 2) sourceC822) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3571) := by
    have ha : (tripleCharges (sourceA822 + difference 2 4) (sourceB822 + difference 4 2) sourceC822) = raw13536 := by
      apply Matrix.ext; unfold tripleCharges sourceA822 sourceB822 sourceC822 difference raw13536; decide +kernel
    rw [ha]
    exact (canonical13536 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA822 + difference 2 5) (sourceB822 + difference 5 2) sourceC822) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3532) := by
    have ha : (tripleCharges (sourceA822 + difference 2 5) (sourceB822 + difference 5 2) sourceC822) = raw13537 := by
      apply Matrix.ext; unfold tripleCharges sourceA822 sourceB822 sourceC822 difference raw13537; decide +kernel
    rw [ha]
    exact (canonical13537 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA822 + difference 3 0) (sourceB822 + difference 0 3) sourceC822) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3294) := by
    have ha : (tripleCharges (sourceA822 + difference 3 0) (sourceB822 + difference 0 3) sourceC822) = raw13538 := by
      apply Matrix.ext; unfold tripleCharges sourceA822 sourceB822 sourceC822 difference raw13538; decide +kernel
    rw [ha]
    exact (canonical13538 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA822 + difference 3 1) (sourceB822 + difference 1 3) sourceC822) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3578) := by
    have ha : (tripleCharges (sourceA822 + difference 3 1) (sourceB822 + difference 1 3) sourceC822) = raw13539 := by
      apply Matrix.ext; unfold tripleCharges sourceA822 sourceB822 sourceC822 difference raw13539; decide +kernel
    rw [ha]
    exact (canonical13539 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA822 + difference 3 2) (sourceB822 + difference 2 3) sourceC822) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3562) := by
    have ha : (tripleCharges (sourceA822 + difference 3 2) (sourceB822 + difference 2 3) sourceC822) = raw13540 := by
      apply Matrix.ext; unfold tripleCharges sourceA822 sourceB822 sourceC822 difference raw13540; decide +kernel
    rw [ha]
    exact (canonical13540 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA822 + difference 3 4) (sourceB822 + difference 4 3) sourceC822) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3580) := by
    have ha : (tripleCharges (sourceA822 + difference 3 4) (sourceB822 + difference 4 3) sourceC822) = raw13541 := by
      apply Matrix.ext; unfold tripleCharges sourceA822 sourceB822 sourceC822 difference raw13541; decide +kernel
    rw [ha]
    exact (canonical13541 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA822 + difference 3 5) (sourceB822 + difference 5 3) sourceC822) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3544) := by
    have ha : (tripleCharges (sourceA822 + difference 3 5) (sourceB822 + difference 5 3) sourceC822) = raw13542 := by
      apply Matrix.ext; unfold tripleCharges sourceA822 sourceB822 sourceC822 difference raw13542; decide +kernel
    rw [ha]
    exact (canonical13542 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA822 + difference 4 0) (sourceB822 + difference 0 4) sourceC822) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3294) := by
    have ha : (tripleCharges (sourceA822 + difference 4 0) (sourceB822 + difference 0 4) sourceC822) = raw13543 := by
      apply Matrix.ext; unfold tripleCharges sourceA822 sourceB822 sourceC822 difference raw13543; decide +kernel
    rw [ha]
    exact (canonical13543 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA822 + difference 4 1) (sourceB822 + difference 1 4) sourceC822) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3578) := by
    have ha : (tripleCharges (sourceA822 + difference 4 1) (sourceB822 + difference 1 4) sourceC822) = raw13544 := by
      apply Matrix.ext; unfold tripleCharges sourceA822 sourceB822 sourceC822 difference raw13544; decide +kernel
    rw [ha]
    exact (canonical13544 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA822 + difference 4 2) (sourceB822 + difference 2 4) sourceC822) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3562) := by
    have ha : (tripleCharges (sourceA822 + difference 4 2) (sourceB822 + difference 2 4) sourceC822) = raw13545 := by
      apply Matrix.ext; unfold tripleCharges sourceA822 sourceB822 sourceC822 difference raw13545; decide +kernel
    rw [ha]
    exact (canonical13545 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA822 + difference 4 3) (sourceB822 + difference 3 4) sourceC822) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3580) := by
    have ha : (tripleCharges (sourceA822 + difference 4 3) (sourceB822 + difference 3 4) sourceC822) = raw13546 := by
      apply Matrix.ext; unfold tripleCharges sourceA822 sourceB822 sourceC822 difference raw13546; decide +kernel
    rw [ha]
    exact (canonical13546 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA822 + difference 4 5) (sourceB822 + difference 5 4) sourceC822) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3544) := by
    have ha : (tripleCharges (sourceA822 + difference 4 5) (sourceB822 + difference 5 4) sourceC822) = raw13547 := by
      apply Matrix.ext; unfold tripleCharges sourceA822 sourceB822 sourceC822 difference raw13547; decide +kernel
    rw [ha]
    exact (canonical13547 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA822 + difference 5 0) (sourceB822 + difference 0 5) sourceC822) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2702) := by
    have ha : (tripleCharges (sourceA822 + difference 5 0) (sourceB822 + difference 0 5) sourceC822) = raw13548 := by
      apply Matrix.ext; unfold tripleCharges sourceA822 sourceB822 sourceC822 difference raw13548; decide +kernel
    rw [ha]
    exact (canonical13548 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA822 + difference 5 1) (sourceB822 + difference 1 5) sourceC822) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2706) := by
    have ha : (tripleCharges (sourceA822 + difference 5 1) (sourceB822 + difference 1 5) sourceC822) = raw13549 := by
      apply Matrix.ext; unfold tripleCharges sourceA822 sourceB822 sourceC822 difference raw13549; decide +kernel
    rw [ha]
    exact (canonical13549 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA822 + difference 5 2) (sourceB822 + difference 2 5) sourceC822) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2700) := by
    have ha : (tripleCharges (sourceA822 + difference 5 2) (sourceB822 + difference 2 5) sourceC822) = raw13550 := by
      apply Matrix.ext; unfold tripleCharges sourceA822 sourceB822 sourceC822 difference raw13550; decide +kernel
    rw [ha]
    exact (canonical13550 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA822 + difference 5 3) (sourceB822 + difference 3 5) sourceC822) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2738) := by
    have ha : (tripleCharges (sourceA822 + difference 5 3) (sourceB822 + difference 3 5) sourceC822) = raw13551 := by
      apply Matrix.ext; unfold tripleCharges sourceA822 sourceB822 sourceC822 difference raw13551; decide +kernel
    rw [ha]
    exact (canonical13551 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA822 + difference 5 4) (sourceB822 + difference 4 5) sourceC822) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2738) := by
    have ha : (tripleCharges (sourceA822 + difference 5 4) (sourceB822 + difference 4 5) sourceC822) = raw13552 := by
      apply Matrix.ext; unfold tripleCharges sourceA822 sourceB822 sourceC822 difference raw13552; decide +kernel
    rw [ha]
    exact (canonical13552 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA822 sourceB822 sourceC822
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm822, Integer.Sparse.eval]
  linarith only [hs]

def sourceA823 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB823 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC823 : Charge := ![2, -1, 0, -1, -1, 1]
def sourceForm823 : Integer.Sparse Master := [(Sum.inr 2764, 1), (Sum.inr 3849, 1), (Sum.inr 3885, 1), (Sum.inr 3904, 1), (Sum.inr 3910, 2), (Sum.inr 4091, -1)]

theorem sourceEq823 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm823 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA823 + difference 0 0) (sourceB823 + difference 0 0) sourceC823) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2764) := by
    have ha : (tripleCharges (sourceA823 + difference 0 0) (sourceB823 + difference 0 0) sourceC823) = raw13553 := by
      apply Matrix.ext; unfold tripleCharges sourceA823 sourceB823 sourceC823 difference raw13553; decide +kernel
    rw [ha]
    exact (canonical13553 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA823 + difference 0 1) (sourceB823 + difference 1 0) sourceC823) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3885) := by
    have ha : (tripleCharges (sourceA823 + difference 0 1) (sourceB823 + difference 1 0) sourceC823) = raw13554 := by
      apply Matrix.ext; unfold tripleCharges sourceA823 sourceB823 sourceC823 difference raw13554; decide +kernel
    rw [ha]
    exact (canonical13554 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA823 + difference 0 2) (sourceB823 + difference 2 0) sourceC823) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3849) := by
    have ha : (tripleCharges (sourceA823 + difference 0 2) (sourceB823 + difference 2 0) sourceC823) = raw13555 := by
      apply Matrix.ext; unfold tripleCharges sourceA823 sourceB823 sourceC823 difference raw13555; decide +kernel
    rw [ha]
    exact (canonical13555 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA823 + difference 0 3) (sourceB823 + difference 3 0) sourceC823) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3910) := by
    have ha : (tripleCharges (sourceA823 + difference 0 3) (sourceB823 + difference 3 0) sourceC823) = raw13556 := by
      apply Matrix.ext; unfold tripleCharges sourceA823 sourceB823 sourceC823 difference raw13556; decide +kernel
    rw [ha]
    exact (canonical13556 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA823 + difference 0 4) (sourceB823 + difference 4 0) sourceC823) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3910) := by
    have ha : (tripleCharges (sourceA823 + difference 0 4) (sourceB823 + difference 4 0) sourceC823) = raw13557 := by
      apply Matrix.ext; unfold tripleCharges sourceA823 sourceB823 sourceC823 difference raw13557; decide +kernel
    rw [ha]
    exact (canonical13557 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA823 + difference 0 5) (sourceB823 + difference 5 0) sourceC823) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3904) := by
    have ha : (tripleCharges (sourceA823 + difference 0 5) (sourceB823 + difference 5 0) sourceC823) = raw13558 := by
      apply Matrix.ext; unfold tripleCharges sourceA823 sourceB823 sourceC823 difference raw13558; decide +kernel
    rw [ha]
    exact (canonical13558 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA823 + sourceB823) sourceC823) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA823 + sourceB823) sourceC823) = raw13559 := by
      apply Matrix.ext; unfold doubleCharges sourceA823 sourceB823 sourceC823 raw13559; decide +kernel
    rw [ha]
    exact (canonical13559 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA823 sourceB823 sourceC823
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm823, Integer.Sparse.eval]
  linarith only [hs]

def sourceA824 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB824 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC824 : Charge := ![2, -1, 0, -1, -1, 1]
def sourceForm824 : Integer.Sparse Master := [(Sum.inr 1260, 1), (Sum.inr 1262, 2), (Sum.inr 1270, 1), (Sum.inr 1293, 1), (Sum.inr 2764, 1), (Sum.inr 4091, -1)]

theorem sourceEq824 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm824 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA824 + difference 0 0) (sourceB824 + difference 0 0) sourceC824) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2764) := by
    have ha : (tripleCharges (sourceA824 + difference 0 0) (sourceB824 + difference 0 0) sourceC824) = raw13553 := by
      apply Matrix.ext; unfold tripleCharges sourceA824 sourceB824 sourceC824 difference raw13553; decide +kernel
    rw [ha]
    exact (canonical13553 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA824 + difference 1 0) (sourceB824 + difference 0 1) sourceC824) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1293) := by
    have ha : (tripleCharges (sourceA824 + difference 1 0) (sourceB824 + difference 0 1) sourceC824) = raw13560 := by
      apply Matrix.ext; unfold tripleCharges sourceA824 sourceB824 sourceC824 difference raw13560; decide +kernel
    rw [ha]
    exact (canonical13560 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA824 + difference 2 0) (sourceB824 + difference 0 2) sourceC824) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1260) := by
    have ha : (tripleCharges (sourceA824 + difference 2 0) (sourceB824 + difference 0 2) sourceC824) = raw13561 := by
      apply Matrix.ext; unfold tripleCharges sourceA824 sourceB824 sourceC824 difference raw13561; decide +kernel
    rw [ha]
    exact (canonical13561 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA824 + difference 3 0) (sourceB824 + difference 0 3) sourceC824) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1262) := by
    have ha : (tripleCharges (sourceA824 + difference 3 0) (sourceB824 + difference 0 3) sourceC824) = raw13562 := by
      apply Matrix.ext; unfold tripleCharges sourceA824 sourceB824 sourceC824 difference raw13562; decide +kernel
    rw [ha]
    exact (canonical13562 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA824 + difference 4 0) (sourceB824 + difference 0 4) sourceC824) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1262) := by
    have ha : (tripleCharges (sourceA824 + difference 4 0) (sourceB824 + difference 0 4) sourceC824) = raw13563 := by
      apply Matrix.ext; unfold tripleCharges sourceA824 sourceB824 sourceC824 difference raw13563; decide +kernel
    rw [ha]
    exact (canonical13563 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA824 + difference 5 0) (sourceB824 + difference 0 5) sourceC824) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1270) := by
    have ha : (tripleCharges (sourceA824 + difference 5 0) (sourceB824 + difference 0 5) sourceC824) = raw13564 := by
      apply Matrix.ext; unfold tripleCharges sourceA824 sourceB824 sourceC824 difference raw13564; decide +kernel
    rw [ha]
    exact (canonical13564 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA824 + sourceB824) sourceC824) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA824 + sourceB824) sourceC824) = raw13559 := by
      apply Matrix.ext; unfold doubleCharges sourceA824 sourceB824 sourceC824 raw13559; decide +kernel
    rw [ha]
    exact (canonical13559 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA824 sourceB824 sourceC824
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm824, Integer.Sparse.eval]
  linarith only [hs]

def sourceA825 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB825 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC825 : Charge := ![2, -1, 0, -1, -1, 1]
def sourceForm825 : Integer.Sparse Master := [(Sum.inr 1293, 1), (Sum.inr 2589, 1), (Sum.inr 2741, 1), (Sum.inr 2764, 3), (Sum.inr 4091, -1)]

theorem sourceEq825 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm825 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA825 + difference 1 0) (sourceB825 + difference 0 1) sourceC825) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1293) := by
    have ha : (tripleCharges (sourceA825 + difference 1 0) (sourceB825 + difference 0 1) sourceC825) = raw13560 := by
      apply Matrix.ext; unfold tripleCharges sourceA825 sourceB825 sourceC825 difference raw13560; decide +kernel
    rw [ha]
    exact (canonical13560 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA825 + difference 1 1) (sourceB825 + difference 1 1) sourceC825) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2764) := by
    have ha : (tripleCharges (sourceA825 + difference 1 1) (sourceB825 + difference 1 1) sourceC825) = raw13553 := by
      apply Matrix.ext; unfold tripleCharges sourceA825 sourceB825 sourceC825 difference raw13553; decide +kernel
    rw [ha]
    exact (canonical13553 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA825 + difference 1 2) (sourceB825 + difference 2 1) sourceC825) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2589) := by
    have ha : (tripleCharges (sourceA825 + difference 1 2) (sourceB825 + difference 2 1) sourceC825) = raw13565 := by
      apply Matrix.ext; unfold tripleCharges sourceA825 sourceB825 sourceC825 difference raw13565; decide +kernel
    rw [ha]
    exact (canonical13565 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA825 + difference 1 3) (sourceB825 + difference 3 1) sourceC825) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2764) := by
    have ha : (tripleCharges (sourceA825 + difference 1 3) (sourceB825 + difference 3 1) sourceC825) = raw13566 := by
      apply Matrix.ext; unfold tripleCharges sourceA825 sourceB825 sourceC825 difference raw13566; decide +kernel
    rw [ha]
    exact (canonical13566 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA825 + difference 1 4) (sourceB825 + difference 4 1) sourceC825) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2764) := by
    have ha : (tripleCharges (sourceA825 + difference 1 4) (sourceB825 + difference 4 1) sourceC825) = raw13567 := by
      apply Matrix.ext; unfold tripleCharges sourceA825 sourceB825 sourceC825 difference raw13567; decide +kernel
    rw [ha]
    exact (canonical13567 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA825 + difference 1 5) (sourceB825 + difference 5 1) sourceC825) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2741) := by
    have ha : (tripleCharges (sourceA825 + difference 1 5) (sourceB825 + difference 5 1) sourceC825) = raw13568 := by
      apply Matrix.ext; unfold tripleCharges sourceA825 sourceB825 sourceC825 difference raw13568; decide +kernel
    rw [ha]
    exact (canonical13568 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA825 + sourceB825) sourceC825) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA825 + sourceB825) sourceC825) = raw13559 := by
      apply Matrix.ext; unfold doubleCharges sourceA825 sourceB825 sourceC825 raw13559; decide +kernel
    rw [ha]
    exact (canonical13559 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA825 sourceB825 sourceC825
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm825, Integer.Sparse.eval]
  linarith only [hs]

def sourceA826 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB826 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC826 : Charge := ![2, -1, 0, -1, -1, 1]
def sourceForm826 : Integer.Sparse Master := [(Sum.inr 2631, 1), (Sum.inr 2633, 2), (Sum.inr 2641, 1), (Sum.inr 2764, 1), (Sum.inr 3885, 1), (Sum.inr 4091, -1)]

theorem sourceEq826 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm826 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA826 + difference 0 1) (sourceB826 + difference 1 0) sourceC826) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3885) := by
    have ha : (tripleCharges (sourceA826 + difference 0 1) (sourceB826 + difference 1 0) sourceC826) = raw13554 := by
      apply Matrix.ext; unfold tripleCharges sourceA826 sourceB826 sourceC826 difference raw13554; decide +kernel
    rw [ha]
    exact (canonical13554 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA826 + difference 1 1) (sourceB826 + difference 1 1) sourceC826) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2764) := by
    have ha : (tripleCharges (sourceA826 + difference 1 1) (sourceB826 + difference 1 1) sourceC826) = raw13553 := by
      apply Matrix.ext; unfold tripleCharges sourceA826 sourceB826 sourceC826 difference raw13553; decide +kernel
    rw [ha]
    exact (canonical13553 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA826 + difference 2 1) (sourceB826 + difference 1 2) sourceC826) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2631) := by
    have ha : (tripleCharges (sourceA826 + difference 2 1) (sourceB826 + difference 1 2) sourceC826) = raw13569 := by
      apply Matrix.ext; unfold tripleCharges sourceA826 sourceB826 sourceC826 difference raw13569; decide +kernel
    rw [ha]
    exact (canonical13569 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA826 + difference 3 1) (sourceB826 + difference 1 3) sourceC826) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2633) := by
    have ha : (tripleCharges (sourceA826 + difference 3 1) (sourceB826 + difference 1 3) sourceC826) = raw13570 := by
      apply Matrix.ext; unfold tripleCharges sourceA826 sourceB826 sourceC826 difference raw13570; decide +kernel
    rw [ha]
    exact (canonical13570 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA826 + difference 4 1) (sourceB826 + difference 1 4) sourceC826) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2633) := by
    have ha : (tripleCharges (sourceA826 + difference 4 1) (sourceB826 + difference 1 4) sourceC826) = raw13571 := by
      apply Matrix.ext; unfold tripleCharges sourceA826 sourceB826 sourceC826 difference raw13571; decide +kernel
    rw [ha]
    exact (canonical13571 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA826 + difference 5 1) (sourceB826 + difference 1 5) sourceC826) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2641) := by
    have ha : (tripleCharges (sourceA826 + difference 5 1) (sourceB826 + difference 1 5) sourceC826) = raw13572 := by
      apply Matrix.ext; unfold tripleCharges sourceA826 sourceB826 sourceC826 difference raw13572; decide +kernel
    rw [ha]
    exact (canonical13572 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA826 + sourceB826) sourceC826) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA826 + sourceB826) sourceC826) = raw13559 := by
      apply Matrix.ext; unfold doubleCharges sourceA826 sourceB826 sourceC826 raw13559; decide +kernel
    rw [ha]
    exact (canonical13559 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA826 sourceB826 sourceC826
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm826, Integer.Sparse.eval]
  linarith only [hs]

def sourceA827 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB827 : Charge := ![2, -1, 0, -1, -1, 1]
def sourceC827 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceForm827 : Integer.Sparse Master := [(Sum.inr 4451, 1), (Sum.inr 4452, 2), (Sum.inr 4461, 1), (Sum.inr 4489, 1), (Sum.inr 5070, 2), (Sum.inr 5076, 1), (Sum.inr 5093, 1), (Sum.inr 5162, 1), (Sum.inr 5163, 2), (Sum.inr 5172, 1), (Sum.inr 5227, 1), (Sum.inr 5228, 2), (Sum.inr 5237, 1), (Sum.inr 5290, 2), (Sum.inr 5291, 2), (Sum.inr 5294, 2), (Sum.inr 5304, 2), (Sum.inr 5450, 1), (Sum.inr 5481, 1), (Sum.inr 5485, 1), (Sum.inr 5492, 2)]

theorem sourceEq827 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm827 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA827 + difference 0 1) (sourceB827 + difference 1 0) sourceC827) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA827 + difference 0 1) (sourceB827 + difference 1 0) sourceC827) = raw3045 := by
      apply Matrix.ext; unfold tripleCharges sourceA827 sourceB827 sourceC827 difference raw3045; decide +kernel
    rw [ha]
    exact (canonical3045 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA827 + difference 0 2) (sourceB827 + difference 2 0) sourceC827) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5481) := by
    have ha : (tripleCharges (sourceA827 + difference 0 2) (sourceB827 + difference 2 0) sourceC827) = raw3046 := by
      apply Matrix.ext; unfold tripleCharges sourceA827 sourceB827 sourceC827 difference raw3046; decide +kernel
    rw [ha]
    exact (canonical3046 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA827 + difference 0 3) (sourceB827 + difference 3 0) sourceC827) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5492) := by
    have ha : (tripleCharges (sourceA827 + difference 0 3) (sourceB827 + difference 3 0) sourceC827) = raw13573 := by
      apply Matrix.ext; unfold tripleCharges sourceA827 sourceB827 sourceC827 difference raw13573; decide +kernel
    rw [ha]
    exact (canonical13573 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA827 + difference 0 4) (sourceB827 + difference 4 0) sourceC827) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5492) := by
    have ha : (tripleCharges (sourceA827 + difference 0 4) (sourceB827 + difference 4 0) sourceC827) = raw3047 := by
      apply Matrix.ext; unfold tripleCharges sourceA827 sourceB827 sourceC827 difference raw3047; decide +kernel
    rw [ha]
    exact (canonical3047 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA827 + difference 0 5) (sourceB827 + difference 5 0) sourceC827) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA827 + difference 0 5) (sourceB827 + difference 5 0) sourceC827) = raw3048 := by
      apply Matrix.ext; unfold tripleCharges sourceA827 sourceB827 sourceC827 difference raw3048; decide +kernel
    rw [ha]
    exact (canonical3048 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA827 + difference 1 0) (sourceB827 + difference 0 1) sourceC827) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4489) := by
    have ha : (tripleCharges (sourceA827 + difference 1 0) (sourceB827 + difference 0 1) sourceC827) = raw13574 := by
      apply Matrix.ext; unfold tripleCharges sourceA827 sourceB827 sourceC827 difference raw13574; decide +kernel
    rw [ha]
    exact (canonical13574 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA827 + difference 1 2) (sourceB827 + difference 2 1) sourceC827) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5093) := by
    have ha : (tripleCharges (sourceA827 + difference 1 2) (sourceB827 + difference 2 1) sourceC827) = raw13575 := by
      apply Matrix.ext; unfold tripleCharges sourceA827 sourceB827 sourceC827 difference raw13575; decide +kernel
    rw [ha]
    exact (canonical13575 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA827 + difference 1 3) (sourceB827 + difference 3 1) sourceC827) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA827 + difference 1 3) (sourceB827 + difference 3 1) sourceC827) = raw3034 := by
      apply Matrix.ext; unfold tripleCharges sourceA827 sourceB827 sourceC827 difference raw3034; decide +kernel
    rw [ha]
    exact (canonical3034 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA827 + difference 1 4) (sourceB827 + difference 4 1) sourceC827) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA827 + difference 1 4) (sourceB827 + difference 4 1) sourceC827) = raw13576 := by
      apply Matrix.ext; unfold tripleCharges sourceA827 sourceB827 sourceC827 difference raw13576; decide +kernel
    rw [ha]
    exact (canonical13576 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA827 + difference 1 5) (sourceB827 + difference 5 1) sourceC827) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5237) := by
    have ha : (tripleCharges (sourceA827 + difference 1 5) (sourceB827 + difference 5 1) sourceC827) = raw13577 := by
      apply Matrix.ext; unfold tripleCharges sourceA827 sourceB827 sourceC827 difference raw13577; decide +kernel
    rw [ha]
    exact (canonical13577 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA827 + difference 2 0) (sourceB827 + difference 0 2) sourceC827) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4451) := by
    have ha : (tripleCharges (sourceA827 + difference 2 0) (sourceB827 + difference 0 2) sourceC827) = raw13578 := by
      apply Matrix.ext; unfold tripleCharges sourceA827 sourceB827 sourceC827 difference raw13578; decide +kernel
    rw [ha]
    exact (canonical13578 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA827 + difference 2 1) (sourceB827 + difference 1 2) sourceC827) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5162) := by
    have ha : (tripleCharges (sourceA827 + difference 2 1) (sourceB827 + difference 1 2) sourceC827) = raw13579 := by
      apply Matrix.ext; unfold tripleCharges sourceA827 sourceB827 sourceC827 difference raw13579; decide +kernel
    rw [ha]
    exact (canonical13579 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA827 + difference 2 3) (sourceB827 + difference 3 2) sourceC827) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA827 + difference 2 3) (sourceB827 + difference 3 2) sourceC827) = raw3039 := by
      apply Matrix.ext; unfold tripleCharges sourceA827 sourceB827 sourceC827 difference raw3039; decide +kernel
    rw [ha]
    exact (canonical3039 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA827 + difference 2 4) (sourceB827 + difference 4 2) sourceC827) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA827 + difference 2 4) (sourceB827 + difference 4 2) sourceC827) = raw13580 := by
      apply Matrix.ext; unfold tripleCharges sourceA827 sourceB827 sourceC827 difference raw13580; decide +kernel
    rw [ha]
    exact (canonical13580 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA827 + difference 2 5) (sourceB827 + difference 5 2) sourceC827) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5227) := by
    have ha : (tripleCharges (sourceA827 + difference 2 5) (sourceB827 + difference 5 2) sourceC827) = raw13581 := by
      apply Matrix.ext; unfold tripleCharges sourceA827 sourceB827 sourceC827 difference raw13581; decide +kernel
    rw [ha]
    exact (canonical13581 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA827 + difference 3 0) (sourceB827 + difference 0 3) sourceC827) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4452) := by
    have ha : (tripleCharges (sourceA827 + difference 3 0) (sourceB827 + difference 0 3) sourceC827) = raw13582 := by
      apply Matrix.ext; unfold tripleCharges sourceA827 sourceB827 sourceC827 difference raw13582; decide +kernel
    rw [ha]
    exact (canonical13582 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA827 + difference 3 1) (sourceB827 + difference 1 3) sourceC827) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5163) := by
    have ha : (tripleCharges (sourceA827 + difference 3 1) (sourceB827 + difference 1 3) sourceC827) = raw13583 := by
      apply Matrix.ext; unfold tripleCharges sourceA827 sourceB827 sourceC827 difference raw13583; decide +kernel
    rw [ha]
    exact (canonical13583 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA827 + difference 3 2) (sourceB827 + difference 2 3) sourceC827) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5070) := by
    have ha : (tripleCharges (sourceA827 + difference 3 2) (sourceB827 + difference 2 3) sourceC827) = raw13584 := by
      apply Matrix.ext; unfold tripleCharges sourceA827 sourceB827 sourceC827 difference raw13584; decide +kernel
    rw [ha]
    exact (canonical13584 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA827 + difference 3 4) (sourceB827 + difference 4 3) sourceC827) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5291) := by
    have ha : (tripleCharges (sourceA827 + difference 3 4) (sourceB827 + difference 4 3) sourceC827) = raw13585 := by
      apply Matrix.ext; unfold tripleCharges sourceA827 sourceB827 sourceC827 difference raw13585; decide +kernel
    rw [ha]
    exact (canonical13585 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA827 + difference 3 5) (sourceB827 + difference 5 3) sourceC827) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5228) := by
    have ha : (tripleCharges (sourceA827 + difference 3 5) (sourceB827 + difference 5 3) sourceC827) = raw13586 := by
      apply Matrix.ext; unfold tripleCharges sourceA827 sourceB827 sourceC827 difference raw13586; decide +kernel
    rw [ha]
    exact (canonical13586 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA827 + difference 4 0) (sourceB827 + difference 0 4) sourceC827) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4452) := by
    have ha : (tripleCharges (sourceA827 + difference 4 0) (sourceB827 + difference 0 4) sourceC827) = raw13587 := by
      apply Matrix.ext; unfold tripleCharges sourceA827 sourceB827 sourceC827 difference raw13587; decide +kernel
    rw [ha]
    exact (canonical13587 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA827 + difference 4 1) (sourceB827 + difference 1 4) sourceC827) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5163) := by
    have ha : (tripleCharges (sourceA827 + difference 4 1) (sourceB827 + difference 1 4) sourceC827) = raw13588 := by
      apply Matrix.ext; unfold tripleCharges sourceA827 sourceB827 sourceC827 difference raw13588; decide +kernel
    rw [ha]
    exact (canonical13588 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA827 + difference 4 2) (sourceB827 + difference 2 4) sourceC827) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5070) := by
    have ha : (tripleCharges (sourceA827 + difference 4 2) (sourceB827 + difference 2 4) sourceC827) = raw13589 := by
      apply Matrix.ext; unfold tripleCharges sourceA827 sourceB827 sourceC827 difference raw13589; decide +kernel
    rw [ha]
    exact (canonical13589 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA827 + difference 4 3) (sourceB827 + difference 3 4) sourceC827) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5291) := by
    have ha : (tripleCharges (sourceA827 + difference 4 3) (sourceB827 + difference 3 4) sourceC827) = raw3049 := by
      apply Matrix.ext; unfold tripleCharges sourceA827 sourceB827 sourceC827 difference raw3049; decide +kernel
    rw [ha]
    exact (canonical3049 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA827 + difference 4 5) (sourceB827 + difference 5 4) sourceC827) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5228) := by
    have ha : (tripleCharges (sourceA827 + difference 4 5) (sourceB827 + difference 5 4) sourceC827) = raw13590 := by
      apply Matrix.ext; unfold tripleCharges sourceA827 sourceB827 sourceC827 difference raw13590; decide +kernel
    rw [ha]
    exact (canonical13590 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA827 + difference 5 0) (sourceB827 + difference 0 5) sourceC827) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4461) := by
    have ha : (tripleCharges (sourceA827 + difference 5 0) (sourceB827 + difference 0 5) sourceC827) = raw13591 := by
      apply Matrix.ext; unfold tripleCharges sourceA827 sourceB827 sourceC827 difference raw13591; decide +kernel
    rw [ha]
    exact (canonical13591 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA827 + difference 5 1) (sourceB827 + difference 1 5) sourceC827) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5172) := by
    have ha : (tripleCharges (sourceA827 + difference 5 1) (sourceB827 + difference 1 5) sourceC827) = raw13592 := by
      apply Matrix.ext; unfold tripleCharges sourceA827 sourceB827 sourceC827 difference raw13592; decide +kernel
    rw [ha]
    exact (canonical13592 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA827 + difference 5 2) (sourceB827 + difference 2 5) sourceC827) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5076) := by
    have ha : (tripleCharges (sourceA827 + difference 5 2) (sourceB827 + difference 2 5) sourceC827) = raw13593 := by
      apply Matrix.ext; unfold tripleCharges sourceA827 sourceB827 sourceC827 difference raw13593; decide +kernel
    rw [ha]
    exact (canonical13593 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA827 + difference 5 3) (sourceB827 + difference 3 5) sourceC827) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA827 + difference 5 3) (sourceB827 + difference 3 5) sourceC827) = raw3054 := by
      apply Matrix.ext; unfold tripleCharges sourceA827 sourceB827 sourceC827 difference raw3054; decide +kernel
    rw [ha]
    exact (canonical3054 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA827 + difference 5 4) (sourceB827 + difference 4 5) sourceC827) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA827 + difference 5 4) (sourceB827 + difference 4 5) sourceC827) = raw13594 := by
      apply Matrix.ext; unfold tripleCharges sourceA827 sourceB827 sourceC827 difference raw13594; decide +kernel
    rw [ha]
    exact (canonical13594 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA827 sourceB827 sourceC827
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm827, Integer.Sparse.eval]
  linarith only [hs]

def sourceA828 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB828 : Charge := ![2, -1, 0, -1, -1, 1]
def sourceC828 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceForm828 : Integer.Sparse Master := [(Sum.inr 1034, 1), (Sum.inr 1035, 2), (Sum.inr 1044, 1), (Sum.inr 1073, 1), (Sum.inr 2477, 2), (Sum.inr 2483, 1), (Sum.inr 2503, 1), (Sum.inr 2589, 1), (Sum.inr 2590, 2), (Sum.inr 2599, 1), (Sum.inr 2671, 1), (Sum.inr 2672, 2), (Sum.inr 2684, 1), (Sum.inr 2764, 2), (Sum.inr 2765, 2), (Sum.inr 2768, 2), (Sum.inr 2782, 2), (Sum.inr 3910, 1), (Sum.inr 3979, 1), (Sum.inr 3998, 1), (Sum.inr 4017, 2)]

theorem sourceEq828 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm828 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA828 + difference 0 1) (sourceB828 + difference 1 0) sourceC828) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3998) := by
    have ha : (tripleCharges (sourceA828 + difference 0 1) (sourceB828 + difference 1 0) sourceC828) = raw3075 := by
      apply Matrix.ext; unfold tripleCharges sourceA828 sourceB828 sourceC828 difference raw3075; decide +kernel
    rw [ha]
    exact (canonical3075 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA828 + difference 0 2) (sourceB828 + difference 2 0) sourceC828) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3979) := by
    have ha : (tripleCharges (sourceA828 + difference 0 2) (sourceB828 + difference 2 0) sourceC828) = raw3076 := by
      apply Matrix.ext; unfold tripleCharges sourceA828 sourceB828 sourceC828 difference raw3076; decide +kernel
    rw [ha]
    exact (canonical3076 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA828 + difference 0 3) (sourceB828 + difference 3 0) sourceC828) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4017) := by
    have ha : (tripleCharges (sourceA828 + difference 0 3) (sourceB828 + difference 3 0) sourceC828) = raw13595 := by
      apply Matrix.ext; unfold tripleCharges sourceA828 sourceB828 sourceC828 difference raw13595; decide +kernel
    rw [ha]
    exact (canonical13595 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA828 + difference 0 4) (sourceB828 + difference 4 0) sourceC828) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4017) := by
    have ha : (tripleCharges (sourceA828 + difference 0 4) (sourceB828 + difference 4 0) sourceC828) = raw3077 := by
      apply Matrix.ext; unfold tripleCharges sourceA828 sourceB828 sourceC828 difference raw3077; decide +kernel
    rw [ha]
    exact (canonical3077 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA828 + difference 0 5) (sourceB828 + difference 5 0) sourceC828) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3910) := by
    have ha : (tripleCharges (sourceA828 + difference 0 5) (sourceB828 + difference 5 0) sourceC828) = raw3078 := by
      apply Matrix.ext; unfold tripleCharges sourceA828 sourceB828 sourceC828 difference raw3078; decide +kernel
    rw [ha]
    exact (canonical3078 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA828 + difference 1 0) (sourceB828 + difference 0 1) sourceC828) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1073) := by
    have ha : (tripleCharges (sourceA828 + difference 1 0) (sourceB828 + difference 0 1) sourceC828) = raw13596 := by
      apply Matrix.ext; unfold tripleCharges sourceA828 sourceB828 sourceC828 difference raw13596; decide +kernel
    rw [ha]
    exact (canonical13596 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA828 + difference 1 2) (sourceB828 + difference 2 1) sourceC828) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2503) := by
    have ha : (tripleCharges (sourceA828 + difference 1 2) (sourceB828 + difference 2 1) sourceC828) = raw13597 := by
      apply Matrix.ext; unfold tripleCharges sourceA828 sourceB828 sourceC828 difference raw13597; decide +kernel
    rw [ha]
    exact (canonical13597 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA828 + difference 1 3) (sourceB828 + difference 3 1) sourceC828) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2782) := by
    have ha : (tripleCharges (sourceA828 + difference 1 3) (sourceB828 + difference 3 1) sourceC828) = raw3064 := by
      apply Matrix.ext; unfold tripleCharges sourceA828 sourceB828 sourceC828 difference raw3064; decide +kernel
    rw [ha]
    exact (canonical3064 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA828 + difference 1 4) (sourceB828 + difference 4 1) sourceC828) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2782) := by
    have ha : (tripleCharges (sourceA828 + difference 1 4) (sourceB828 + difference 4 1) sourceC828) = raw13598 := by
      apply Matrix.ext; unfold tripleCharges sourceA828 sourceB828 sourceC828 difference raw13598; decide +kernel
    rw [ha]
    exact (canonical13598 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA828 + difference 1 5) (sourceB828 + difference 5 1) sourceC828) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2684) := by
    have ha : (tripleCharges (sourceA828 + difference 1 5) (sourceB828 + difference 5 1) sourceC828) = raw13599 := by
      apply Matrix.ext; unfold tripleCharges sourceA828 sourceB828 sourceC828 difference raw13599; decide +kernel
    rw [ha]
    exact (canonical13599 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA828 + difference 2 0) (sourceB828 + difference 0 2) sourceC828) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1034) := by
    have ha : (tripleCharges (sourceA828 + difference 2 0) (sourceB828 + difference 0 2) sourceC828) = raw13600 := by
      apply Matrix.ext; unfold tripleCharges sourceA828 sourceB828 sourceC828 difference raw13600; decide +kernel
    rw [ha]
    exact (canonical13600 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA828 + difference 2 1) (sourceB828 + difference 1 2) sourceC828) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2589) := by
    have ha : (tripleCharges (sourceA828 + difference 2 1) (sourceB828 + difference 1 2) sourceC828) = raw13601 := by
      apply Matrix.ext; unfold tripleCharges sourceA828 sourceB828 sourceC828 difference raw13601; decide +kernel
    rw [ha]
    exact (canonical13601 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA828 + difference 2 3) (sourceB828 + difference 3 2) sourceC828) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2764) := by
    have ha : (tripleCharges (sourceA828 + difference 2 3) (sourceB828 + difference 3 2) sourceC828) = raw3069 := by
      apply Matrix.ext; unfold tripleCharges sourceA828 sourceB828 sourceC828 difference raw3069; decide +kernel
    rw [ha]
    exact (canonical3069 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA828 + difference 2 4) (sourceB828 + difference 4 2) sourceC828) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2764) := by
    have ha : (tripleCharges (sourceA828 + difference 2 4) (sourceB828 + difference 4 2) sourceC828) = raw13602 := by
      apply Matrix.ext; unfold tripleCharges sourceA828 sourceB828 sourceC828 difference raw13602; decide +kernel
    rw [ha]
    exact (canonical13602 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA828 + difference 2 5) (sourceB828 + difference 5 2) sourceC828) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2671) := by
    have ha : (tripleCharges (sourceA828 + difference 2 5) (sourceB828 + difference 5 2) sourceC828) = raw13603 := by
      apply Matrix.ext; unfold tripleCharges sourceA828 sourceB828 sourceC828 difference raw13603; decide +kernel
    rw [ha]
    exact (canonical13603 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA828 + difference 3 0) (sourceB828 + difference 0 3) sourceC828) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1035) := by
    have ha : (tripleCharges (sourceA828 + difference 3 0) (sourceB828 + difference 0 3) sourceC828) = raw13604 := by
      apply Matrix.ext; unfold tripleCharges sourceA828 sourceB828 sourceC828 difference raw13604; decide +kernel
    rw [ha]
    exact (canonical13604 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA828 + difference 3 1) (sourceB828 + difference 1 3) sourceC828) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2590) := by
    have ha : (tripleCharges (sourceA828 + difference 3 1) (sourceB828 + difference 1 3) sourceC828) = raw13605 := by
      apply Matrix.ext; unfold tripleCharges sourceA828 sourceB828 sourceC828 difference raw13605; decide +kernel
    rw [ha]
    exact (canonical13605 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA828 + difference 3 2) (sourceB828 + difference 2 3) sourceC828) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2477) := by
    have ha : (tripleCharges (sourceA828 + difference 3 2) (sourceB828 + difference 2 3) sourceC828) = raw13606 := by
      apply Matrix.ext; unfold tripleCharges sourceA828 sourceB828 sourceC828 difference raw13606; decide +kernel
    rw [ha]
    exact (canonical13606 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA828 + difference 3 4) (sourceB828 + difference 4 3) sourceC828) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2765) := by
    have ha : (tripleCharges (sourceA828 + difference 3 4) (sourceB828 + difference 4 3) sourceC828) = raw13607 := by
      apply Matrix.ext; unfold tripleCharges sourceA828 sourceB828 sourceC828 difference raw13607; decide +kernel
    rw [ha]
    exact (canonical13607 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA828 + difference 3 5) (sourceB828 + difference 5 3) sourceC828) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2672) := by
    have ha : (tripleCharges (sourceA828 + difference 3 5) (sourceB828 + difference 5 3) sourceC828) = raw13608 := by
      apply Matrix.ext; unfold tripleCharges sourceA828 sourceB828 sourceC828 difference raw13608; decide +kernel
    rw [ha]
    exact (canonical13608 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA828 + difference 4 0) (sourceB828 + difference 0 4) sourceC828) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1035) := by
    have ha : (tripleCharges (sourceA828 + difference 4 0) (sourceB828 + difference 0 4) sourceC828) = raw13609 := by
      apply Matrix.ext; unfold tripleCharges sourceA828 sourceB828 sourceC828 difference raw13609; decide +kernel
    rw [ha]
    exact (canonical13609 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA828 + difference 4 1) (sourceB828 + difference 1 4) sourceC828) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2590) := by
    have ha : (tripleCharges (sourceA828 + difference 4 1) (sourceB828 + difference 1 4) sourceC828) = raw13610 := by
      apply Matrix.ext; unfold tripleCharges sourceA828 sourceB828 sourceC828 difference raw13610; decide +kernel
    rw [ha]
    exact (canonical13610 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA828 + difference 4 2) (sourceB828 + difference 2 4) sourceC828) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2477) := by
    have ha : (tripleCharges (sourceA828 + difference 4 2) (sourceB828 + difference 2 4) sourceC828) = raw13611 := by
      apply Matrix.ext; unfold tripleCharges sourceA828 sourceB828 sourceC828 difference raw13611; decide +kernel
    rw [ha]
    exact (canonical13611 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA828 + difference 4 3) (sourceB828 + difference 3 4) sourceC828) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2765) := by
    have ha : (tripleCharges (sourceA828 + difference 4 3) (sourceB828 + difference 3 4) sourceC828) = raw3079 := by
      apply Matrix.ext; unfold tripleCharges sourceA828 sourceB828 sourceC828 difference raw3079; decide +kernel
    rw [ha]
    exact (canonical3079 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA828 + difference 4 5) (sourceB828 + difference 5 4) sourceC828) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2672) := by
    have ha : (tripleCharges (sourceA828 + difference 4 5) (sourceB828 + difference 5 4) sourceC828) = raw13612 := by
      apply Matrix.ext; unfold tripleCharges sourceA828 sourceB828 sourceC828 difference raw13612; decide +kernel
    rw [ha]
    exact (canonical13612 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA828 + difference 5 0) (sourceB828 + difference 0 5) sourceC828) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1044) := by
    have ha : (tripleCharges (sourceA828 + difference 5 0) (sourceB828 + difference 0 5) sourceC828) = raw13613 := by
      apply Matrix.ext; unfold tripleCharges sourceA828 sourceB828 sourceC828 difference raw13613; decide +kernel
    rw [ha]
    exact (canonical13613 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA828 + difference 5 1) (sourceB828 + difference 1 5) sourceC828) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2599) := by
    have ha : (tripleCharges (sourceA828 + difference 5 1) (sourceB828 + difference 1 5) sourceC828) = raw13614 := by
      apply Matrix.ext; unfold tripleCharges sourceA828 sourceB828 sourceC828 difference raw13614; decide +kernel
    rw [ha]
    exact (canonical13614 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA828 + difference 5 2) (sourceB828 + difference 2 5) sourceC828) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2483) := by
    have ha : (tripleCharges (sourceA828 + difference 5 2) (sourceB828 + difference 2 5) sourceC828) = raw13615 := by
      apply Matrix.ext; unfold tripleCharges sourceA828 sourceB828 sourceC828 difference raw13615; decide +kernel
    rw [ha]
    exact (canonical13615 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA828 + difference 5 3) (sourceB828 + difference 3 5) sourceC828) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2768) := by
    have ha : (tripleCharges (sourceA828 + difference 5 3) (sourceB828 + difference 3 5) sourceC828) = raw3084 := by
      apply Matrix.ext; unfold tripleCharges sourceA828 sourceB828 sourceC828 difference raw3084; decide +kernel
    rw [ha]
    exact (canonical3084 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA828 + difference 5 4) (sourceB828 + difference 4 5) sourceC828) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2768) := by
    have ha : (tripleCharges (sourceA828 + difference 5 4) (sourceB828 + difference 4 5) sourceC828) = raw13616 := by
      apply Matrix.ext; unfold tripleCharges sourceA828 sourceB828 sourceC828 difference raw13616; decide +kernel
    rw [ha]
    exact (canonical13616 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA828 sourceB828 sourceC828
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm828, Integer.Sparse.eval]
  linarith only [hs]

def sourceA829 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceB829 : Charge := ![2, -1, 0, -1, -1, 1]
def sourceC829 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceForm829 : Integer.Sparse Master := [(Sum.inr 4864, 1), (Sum.inr 4866, 2), (Sum.inr 4869, 1), (Sum.inr 4893, 1), (Sum.inr 5255, 2), (Sum.inr 5256, 1), (Sum.inr 5257, 1), (Sum.inr 5263, 1), (Sum.inr 5270, 1), (Sum.inr 5271, 2), (Sum.inr 5278, 1), (Sum.inr 5279, 1), (Sum.inr 5281, 2), (Sum.inr 5288, 2), (Sum.inr 5289, 2), (Sum.inr 5290, 1), (Sum.inr 5292, 2), (Sum.inr 5299, 2), (Sum.inr 5304, 2), (Sum.inr 5306, 1), (Sum.inr 5307, 1)]

theorem sourceEq829 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm829 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA829 + difference 0 1) (sourceB829 + difference 1 0) sourceC829) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5306) := by
    have ha : (tripleCharges (sourceA829 + difference 0 1) (sourceB829 + difference 1 0) sourceC829) = raw13617 := by
      apply Matrix.ext; unfold tripleCharges sourceA829 sourceB829 sourceC829 difference raw13617; decide +kernel
    rw [ha]
    exact (canonical13617 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA829 + difference 0 2) (sourceB829 + difference 2 0) sourceC829) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5256) := by
    have ha : (tripleCharges (sourceA829 + difference 0 2) (sourceB829 + difference 2 0) sourceC829) = raw13618 := by
      apply Matrix.ext; unfold tripleCharges sourceA829 sourceB829 sourceC829 difference raw13618; decide +kernel
    rw [ha]
    exact (canonical13618 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA829 + difference 0 3) (sourceB829 + difference 3 0) sourceC829) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA829 + difference 0 3) (sourceB829 + difference 3 0) sourceC829) = raw13619 := by
      apply Matrix.ext; unfold tripleCharges sourceA829 sourceB829 sourceC829 difference raw13619; decide +kernel
    rw [ha]
    exact (canonical13619 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA829 + difference 0 4) (sourceB829 + difference 4 0) sourceC829) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA829 + difference 0 4) (sourceB829 + difference 4 0) sourceC829) = raw13620 := by
      apply Matrix.ext; unfold tripleCharges sourceA829 sourceB829 sourceC829 difference raw13620; decide +kernel
    rw [ha]
    exact (canonical13620 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA829 + difference 0 5) (sourceB829 + difference 5 0) sourceC829) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5270) := by
    have ha : (tripleCharges (sourceA829 + difference 0 5) (sourceB829 + difference 5 0) sourceC829) = raw13621 := by
      apply Matrix.ext; unfold tripleCharges sourceA829 sourceB829 sourceC829 difference raw13621; decide +kernel
    rw [ha]
    exact (canonical13621 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA829 + difference 1 0) (sourceB829 + difference 0 1) sourceC829) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4869) := by
    have ha : (tripleCharges (sourceA829 + difference 1 0) (sourceB829 + difference 0 1) sourceC829) = raw13622 := by
      apply Matrix.ext; unfold tripleCharges sourceA829 sourceB829 sourceC829 difference raw13622; decide +kernel
    rw [ha]
    exact (canonical13622 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA829 + difference 1 2) (sourceB829 + difference 2 1) sourceC829) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5263) := by
    have ha : (tripleCharges (sourceA829 + difference 1 2) (sourceB829 + difference 2 1) sourceC829) = raw13623 := by
      apply Matrix.ext; unfold tripleCharges sourceA829 sourceB829 sourceC829 difference raw13623; decide +kernel
    rw [ha]
    exact (canonical13623 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA829 + difference 1 3) (sourceB829 + difference 3 1) sourceC829) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA829 + difference 1 3) (sourceB829 + difference 3 1) sourceC829) = raw13624 := by
      apply Matrix.ext; unfold tripleCharges sourceA829 sourceB829 sourceC829 difference raw13624; decide +kernel
    rw [ha]
    exact (canonical13624 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA829 + difference 1 4) (sourceB829 + difference 4 1) sourceC829) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA829 + difference 1 4) (sourceB829 + difference 4 1) sourceC829) = raw13625 := by
      apply Matrix.ext; unfold tripleCharges sourceA829 sourceB829 sourceC829 difference raw13625; decide +kernel
    rw [ha]
    exact (canonical13625 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA829 + difference 1 5) (sourceB829 + difference 5 1) sourceC829) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5279) := by
    have ha : (tripleCharges (sourceA829 + difference 1 5) (sourceB829 + difference 5 1) sourceC829) = raw13626 := by
      apply Matrix.ext; unfold tripleCharges sourceA829 sourceB829 sourceC829 difference raw13626; decide +kernel
    rw [ha]
    exact (canonical13626 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA829 + difference 2 0) (sourceB829 + difference 0 2) sourceC829) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4864) := by
    have ha : (tripleCharges (sourceA829 + difference 2 0) (sourceB829 + difference 0 2) sourceC829) = raw13627 := by
      apply Matrix.ext; unfold tripleCharges sourceA829 sourceB829 sourceC829 difference raw13627; decide +kernel
    rw [ha]
    exact (canonical13627 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA829 + difference 2 1) (sourceB829 + difference 1 2) sourceC829) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA829 + difference 2 1) (sourceB829 + difference 1 2) sourceC829) = raw13628 := by
      apply Matrix.ext; unfold tripleCharges sourceA829 sourceB829 sourceC829 difference raw13628; decide +kernel
    rw [ha]
    exact (canonical13628 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA829 + difference 2 3) (sourceB829 + difference 3 2) sourceC829) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5281) := by
    have ha : (tripleCharges (sourceA829 + difference 2 3) (sourceB829 + difference 3 2) sourceC829) = raw13448 := by
      apply Matrix.ext; unfold tripleCharges sourceA829 sourceB829 sourceC829 difference raw13448; decide +kernel
    rw [ha]
    exact (canonical13448 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA829 + difference 2 4) (sourceB829 + difference 4 2) sourceC829) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5281) := by
    have ha : (tripleCharges (sourceA829 + difference 2 4) (sourceB829 + difference 4 2) sourceC829) = raw13445 := by
      apply Matrix.ext; unfold tripleCharges sourceA829 sourceB829 sourceC829 difference raw13445; decide +kernel
    rw [ha]
    exact (canonical13445 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA829 + difference 2 5) (sourceB829 + difference 5 2) sourceC829) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5278) := by
    have ha : (tripleCharges (sourceA829 + difference 2 5) (sourceB829 + difference 5 2) sourceC829) = raw13629 := by
      apply Matrix.ext; unfold tripleCharges sourceA829 sourceB829 sourceC829 difference raw13629; decide +kernel
    rw [ha]
    exact (canonical13629 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA829 + difference 3 0) (sourceB829 + difference 0 3) sourceC829) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA829 + difference 3 0) (sourceB829 + difference 0 3) sourceC829) = raw13630 := by
      apply Matrix.ext; unfold tripleCharges sourceA829 sourceB829 sourceC829 difference raw13630; decide +kernel
    rw [ha]
    exact (canonical13630 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA829 + difference 3 1) (sourceB829 + difference 1 3) sourceC829) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA829 + difference 3 1) (sourceB829 + difference 1 3) sourceC829) = raw13631 := by
      apply Matrix.ext; unfold tripleCharges sourceA829 sourceB829 sourceC829 difference raw13631; decide +kernel
    rw [ha]
    exact (canonical13631 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA829 + difference 3 2) (sourceB829 + difference 2 3) sourceC829) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5255) := by
    have ha : (tripleCharges (sourceA829 + difference 3 2) (sourceB829 + difference 2 3) sourceC829) = raw13632 := by
      apply Matrix.ext; unfold tripleCharges sourceA829 sourceB829 sourceC829 difference raw13632; decide +kernel
    rw [ha]
    exact (canonical13632 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA829 + difference 3 4) (sourceB829 + difference 4 3) sourceC829) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA829 + difference 3 4) (sourceB829 + difference 4 3) sourceC829) = raw13633 := by
      apply Matrix.ext; unfold tripleCharges sourceA829 sourceB829 sourceC829 difference raw13633; decide +kernel
    rw [ha]
    exact (canonical13633 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA829 + difference 3 5) (sourceB829 + difference 5 3) sourceC829) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5288) := by
    have ha : (tripleCharges (sourceA829 + difference 3 5) (sourceB829 + difference 5 3) sourceC829) = raw13634 := by
      apply Matrix.ext; unfold tripleCharges sourceA829 sourceB829 sourceC829 difference raw13634; decide +kernel
    rw [ha]
    exact (canonical13634 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA829 + difference 4 0) (sourceB829 + difference 0 4) sourceC829) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA829 + difference 4 0) (sourceB829 + difference 0 4) sourceC829) = raw13635 := by
      apply Matrix.ext; unfold tripleCharges sourceA829 sourceB829 sourceC829 difference raw13635; decide +kernel
    rw [ha]
    exact (canonical13635 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA829 + difference 4 1) (sourceB829 + difference 1 4) sourceC829) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA829 + difference 4 1) (sourceB829 + difference 1 4) sourceC829) = raw13636 := by
      apply Matrix.ext; unfold tripleCharges sourceA829 sourceB829 sourceC829 difference raw13636; decide +kernel
    rw [ha]
    exact (canonical13636 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA829 + difference 4 2) (sourceB829 + difference 2 4) sourceC829) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5255) := by
    have ha : (tripleCharges (sourceA829 + difference 4 2) (sourceB829 + difference 2 4) sourceC829) = raw13637 := by
      apply Matrix.ext; unfold tripleCharges sourceA829 sourceB829 sourceC829 difference raw13637; decide +kernel
    rw [ha]
    exact (canonical13637 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA829 + difference 4 3) (sourceB829 + difference 3 4) sourceC829) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA829 + difference 4 3) (sourceB829 + difference 3 4) sourceC829) = raw13638 := by
      apply Matrix.ext; unfold tripleCharges sourceA829 sourceB829 sourceC829 difference raw13638; decide +kernel
    rw [ha]
    exact (canonical13638 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA829 + difference 4 5) (sourceB829 + difference 5 4) sourceC829) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5288) := by
    have ha : (tripleCharges (sourceA829 + difference 4 5) (sourceB829 + difference 5 4) sourceC829) = raw13639 := by
      apply Matrix.ext; unfold tripleCharges sourceA829 sourceB829 sourceC829 difference raw13639; decide +kernel
    rw [ha]
    exact (canonical13639 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA829 + difference 5 0) (sourceB829 + difference 0 5) sourceC829) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4893) := by
    have ha : (tripleCharges (sourceA829 + difference 5 0) (sourceB829 + difference 0 5) sourceC829) = raw13640 := by
      apply Matrix.ext; unfold tripleCharges sourceA829 sourceB829 sourceC829 difference raw13640; decide +kernel
    rw [ha]
    exact (canonical13640 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA829 + difference 5 1) (sourceB829 + difference 1 5) sourceC829) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5307) := by
    have ha : (tripleCharges (sourceA829 + difference 5 1) (sourceB829 + difference 1 5) sourceC829) = raw13641 := by
      apply Matrix.ext; unfold tripleCharges sourceA829 sourceB829 sourceC829 difference raw13641; decide +kernel
    rw [ha]
    exact (canonical13641 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA829 + difference 5 2) (sourceB829 + difference 2 5) sourceC829) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA829 + difference 5 2) (sourceB829 + difference 2 5) sourceC829) = raw13642 := by
      apply Matrix.ext; unfold tripleCharges sourceA829 sourceB829 sourceC829 difference raw13642; decide +kernel
    rw [ha]
    exact (canonical13642 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA829 + difference 5 3) (sourceB829 + difference 3 5) sourceC829) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA829 + difference 5 3) (sourceB829 + difference 3 5) sourceC829) = raw13447 := by
      apply Matrix.ext; unfold tripleCharges sourceA829 sourceB829 sourceC829 difference raw13447; decide +kernel
    rw [ha]
    exact (canonical13447 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA829 + difference 5 4) (sourceB829 + difference 4 5) sourceC829) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA829 + difference 5 4) (sourceB829 + difference 4 5) sourceC829) = raw13443 := by
      apply Matrix.ext; unfold tripleCharges sourceA829 sourceB829 sourceC829 difference raw13443; decide +kernel
    rw [ha]
    exact (canonical13443 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA829 sourceB829 sourceC829
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm829, Integer.Sparse.eval]
  linarith only [hs]

def sourceA830 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceB830 : Charge := ![2, -1, 0, -1, -1, 1]
def sourceC830 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceForm830 : Integer.Sparse Master := [(Sum.inr 2241, 1), (Sum.inr 2260, 2), (Sum.inr 2263, 1), (Sum.inr 2275, 1), (Sum.inr 2718, 2), (Sum.inr 2721, 1), (Sum.inr 2728, 1), (Sum.inr 2747, 1), (Sum.inr 2748, 1), (Sum.inr 2750, 2), (Sum.inr 2754, 1), (Sum.inr 2760, 2), (Sum.inr 2763, 2), (Sum.inr 2764, 1), (Sum.inr 2766, 2), (Sum.inr 2773, 2), (Sum.inr 2782, 2), (Sum.inr 2785, 1), (Sum.inr 3085, 1), (Sum.inr 3109, 2), (Sum.inr 3120, 1)]

theorem sourceEq830 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm830 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA830 + difference 0 1) (sourceB830 + difference 1 0) sourceC830) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3120) := by
    have ha : (tripleCharges (sourceA830 + difference 0 1) (sourceB830 + difference 1 0) sourceC830) = raw13643 := by
      apply Matrix.ext; unfold tripleCharges sourceA830 sourceB830 sourceC830 difference raw13643; decide +kernel
    rw [ha]
    exact (canonical13643 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA830 + difference 0 2) (sourceB830 + difference 2 0) sourceC830) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3085) := by
    have ha : (tripleCharges (sourceA830 + difference 0 2) (sourceB830 + difference 2 0) sourceC830) = raw13644 := by
      apply Matrix.ext; unfold tripleCharges sourceA830 sourceB830 sourceC830 difference raw13644; decide +kernel
    rw [ha]
    exact (canonical13644 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA830 + difference 0 3) (sourceB830 + difference 3 0) sourceC830) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3109) := by
    have ha : (tripleCharges (sourceA830 + difference 0 3) (sourceB830 + difference 3 0) sourceC830) = raw13645 := by
      apply Matrix.ext; unfold tripleCharges sourceA830 sourceB830 sourceC830 difference raw13645; decide +kernel
    rw [ha]
    exact (canonical13645 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA830 + difference 0 4) (sourceB830 + difference 4 0) sourceC830) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3109) := by
    have ha : (tripleCharges (sourceA830 + difference 0 4) (sourceB830 + difference 4 0) sourceC830) = raw13646 := by
      apply Matrix.ext; unfold tripleCharges sourceA830 sourceB830 sourceC830 difference raw13646; decide +kernel
    rw [ha]
    exact (canonical13646 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA830 + difference 0 5) (sourceB830 + difference 5 0) sourceC830) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2754) := by
    have ha : (tripleCharges (sourceA830 + difference 0 5) (sourceB830 + difference 5 0) sourceC830) = raw13647 := by
      apply Matrix.ext; unfold tripleCharges sourceA830 sourceB830 sourceC830 difference raw13647; decide +kernel
    rw [ha]
    exact (canonical13647 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA830 + difference 1 0) (sourceB830 + difference 0 1) sourceC830) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2275) := by
    have ha : (tripleCharges (sourceA830 + difference 1 0) (sourceB830 + difference 0 1) sourceC830) = raw13648 := by
      apply Matrix.ext; unfold tripleCharges sourceA830 sourceB830 sourceC830 difference raw13648; decide +kernel
    rw [ha]
    exact (canonical13648 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA830 + difference 1 2) (sourceB830 + difference 2 1) sourceC830) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2728) := by
    have ha : (tripleCharges (sourceA830 + difference 1 2) (sourceB830 + difference 2 1) sourceC830) = raw13649 := by
      apply Matrix.ext; unfold tripleCharges sourceA830 sourceB830 sourceC830 difference raw13649; decide +kernel
    rw [ha]
    exact (canonical13649 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA830 + difference 1 3) (sourceB830 + difference 3 1) sourceC830) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2773) := by
    have ha : (tripleCharges (sourceA830 + difference 1 3) (sourceB830 + difference 3 1) sourceC830) = raw13650 := by
      apply Matrix.ext; unfold tripleCharges sourceA830 sourceB830 sourceC830 difference raw13650; decide +kernel
    rw [ha]
    exact (canonical13650 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA830 + difference 1 4) (sourceB830 + difference 4 1) sourceC830) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2773) := by
    have ha : (tripleCharges (sourceA830 + difference 1 4) (sourceB830 + difference 4 1) sourceC830) = raw13651 := by
      apply Matrix.ext; unfold tripleCharges sourceA830 sourceB830 sourceC830 difference raw13651; decide +kernel
    rw [ha]
    exact (canonical13651 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA830 + difference 1 5) (sourceB830 + difference 5 1) sourceC830) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2748) := by
    have ha : (tripleCharges (sourceA830 + difference 1 5) (sourceB830 + difference 5 1) sourceC830) = raw13652 := by
      apply Matrix.ext; unfold tripleCharges sourceA830 sourceB830 sourceC830 difference raw13652; decide +kernel
    rw [ha]
    exact (canonical13652 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA830 + difference 2 0) (sourceB830 + difference 0 2) sourceC830) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2241) := by
    have ha : (tripleCharges (sourceA830 + difference 2 0) (sourceB830 + difference 0 2) sourceC830) = raw13653 := by
      apply Matrix.ext; unfold tripleCharges sourceA830 sourceB830 sourceC830 difference raw13653; decide +kernel
    rw [ha]
    exact (canonical13653 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA830 + difference 2 1) (sourceB830 + difference 1 2) sourceC830) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2764) := by
    have ha : (tripleCharges (sourceA830 + difference 2 1) (sourceB830 + difference 1 2) sourceC830) = raw13654 := by
      apply Matrix.ext; unfold tripleCharges sourceA830 sourceB830 sourceC830 difference raw13654; decide +kernel
    rw [ha]
    exact (canonical13654 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA830 + difference 2 3) (sourceB830 + difference 3 2) sourceC830) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2750) := by
    have ha : (tripleCharges (sourceA830 + difference 2 3) (sourceB830 + difference 3 2) sourceC830) = raw13655 := by
      apply Matrix.ext; unfold tripleCharges sourceA830 sourceB830 sourceC830 difference raw13655; decide +kernel
    rw [ha]
    exact (canonical13655 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA830 + difference 2 4) (sourceB830 + difference 4 2) sourceC830) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2750) := by
    have ha : (tripleCharges (sourceA830 + difference 2 4) (sourceB830 + difference 4 2) sourceC830) = raw13656 := by
      apply Matrix.ext; unfold tripleCharges sourceA830 sourceB830 sourceC830 difference raw13656; decide +kernel
    rw [ha]
    exact (canonical13656 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA830 + difference 2 5) (sourceB830 + difference 5 2) sourceC830) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2747) := by
    have ha : (tripleCharges (sourceA830 + difference 2 5) (sourceB830 + difference 5 2) sourceC830) = raw13657 := by
      apply Matrix.ext; unfold tripleCharges sourceA830 sourceB830 sourceC830 difference raw13657; decide +kernel
    rw [ha]
    exact (canonical13657 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA830 + difference 3 0) (sourceB830 + difference 0 3) sourceC830) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2260) := by
    have ha : (tripleCharges (sourceA830 + difference 3 0) (sourceB830 + difference 0 3) sourceC830) = raw13658 := by
      apply Matrix.ext; unfold tripleCharges sourceA830 sourceB830 sourceC830 difference raw13658; decide +kernel
    rw [ha]
    exact (canonical13658 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA830 + difference 3 1) (sourceB830 + difference 1 3) sourceC830) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2782) := by
    have ha : (tripleCharges (sourceA830 + difference 3 1) (sourceB830 + difference 1 3) sourceC830) = raw13659 := by
      apply Matrix.ext; unfold tripleCharges sourceA830 sourceB830 sourceC830 difference raw13659; decide +kernel
    rw [ha]
    exact (canonical13659 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA830 + difference 3 2) (sourceB830 + difference 2 3) sourceC830) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2718) := by
    have ha : (tripleCharges (sourceA830 + difference 3 2) (sourceB830 + difference 2 3) sourceC830) = raw13660 := by
      apply Matrix.ext; unfold tripleCharges sourceA830 sourceB830 sourceC830 difference raw13660; decide +kernel
    rw [ha]
    exact (canonical13660 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA830 + difference 3 4) (sourceB830 + difference 4 3) sourceC830) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2763) := by
    have ha : (tripleCharges (sourceA830 + difference 3 4) (sourceB830 + difference 4 3) sourceC830) = raw13661 := by
      apply Matrix.ext; unfold tripleCharges sourceA830 sourceB830 sourceC830 difference raw13661; decide +kernel
    rw [ha]
    exact (canonical13661 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA830 + difference 3 5) (sourceB830 + difference 5 3) sourceC830) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2760) := by
    have ha : (tripleCharges (sourceA830 + difference 3 5) (sourceB830 + difference 5 3) sourceC830) = raw13662 := by
      apply Matrix.ext; unfold tripleCharges sourceA830 sourceB830 sourceC830 difference raw13662; decide +kernel
    rw [ha]
    exact (canonical13662 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA830 + difference 4 0) (sourceB830 + difference 0 4) sourceC830) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2260) := by
    have ha : (tripleCharges (sourceA830 + difference 4 0) (sourceB830 + difference 0 4) sourceC830) = raw13663 := by
      apply Matrix.ext; unfold tripleCharges sourceA830 sourceB830 sourceC830 difference raw13663; decide +kernel
    rw [ha]
    exact (canonical13663 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA830 + difference 4 1) (sourceB830 + difference 1 4) sourceC830) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2782) := by
    have ha : (tripleCharges (sourceA830 + difference 4 1) (sourceB830 + difference 1 4) sourceC830) = raw13664 := by
      apply Matrix.ext; unfold tripleCharges sourceA830 sourceB830 sourceC830 difference raw13664; decide +kernel
    rw [ha]
    exact (canonical13664 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA830 + difference 4 2) (sourceB830 + difference 2 4) sourceC830) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2718) := by
    have ha : (tripleCharges (sourceA830 + difference 4 2) (sourceB830 + difference 2 4) sourceC830) = raw13665 := by
      apply Matrix.ext; unfold tripleCharges sourceA830 sourceB830 sourceC830 difference raw13665; decide +kernel
    rw [ha]
    exact (canonical13665 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA830 + difference 4 3) (sourceB830 + difference 3 4) sourceC830) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2763) := by
    have ha : (tripleCharges (sourceA830 + difference 4 3) (sourceB830 + difference 3 4) sourceC830) = raw13666 := by
      apply Matrix.ext; unfold tripleCharges sourceA830 sourceB830 sourceC830 difference raw13666; decide +kernel
    rw [ha]
    exact (canonical13666 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA830 + difference 4 5) (sourceB830 + difference 5 4) sourceC830) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2760) := by
    have ha : (tripleCharges (sourceA830 + difference 4 5) (sourceB830 + difference 5 4) sourceC830) = raw13667 := by
      apply Matrix.ext; unfold tripleCharges sourceA830 sourceB830 sourceC830 difference raw13667; decide +kernel
    rw [ha]
    exact (canonical13667 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA830 + difference 5 0) (sourceB830 + difference 0 5) sourceC830) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2263) := by
    have ha : (tripleCharges (sourceA830 + difference 5 0) (sourceB830 + difference 0 5) sourceC830) = raw13668 := by
      apply Matrix.ext; unfold tripleCharges sourceA830 sourceB830 sourceC830 difference raw13668; decide +kernel
    rw [ha]
    exact (canonical13668 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA830 + difference 5 1) (sourceB830 + difference 1 5) sourceC830) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2785) := by
    have ha : (tripleCharges (sourceA830 + difference 5 1) (sourceB830 + difference 1 5) sourceC830) = raw13669 := by
      apply Matrix.ext; unfold tripleCharges sourceA830 sourceB830 sourceC830 difference raw13669; decide +kernel
    rw [ha]
    exact (canonical13669 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA830 + difference 5 2) (sourceB830 + difference 2 5) sourceC830) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2721) := by
    have ha : (tripleCharges (sourceA830 + difference 5 2) (sourceB830 + difference 2 5) sourceC830) = raw13670 := by
      apply Matrix.ext; unfold tripleCharges sourceA830 sourceB830 sourceC830 difference raw13670; decide +kernel
    rw [ha]
    exact (canonical13670 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA830 + difference 5 3) (sourceB830 + difference 3 5) sourceC830) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2766) := by
    have ha : (tripleCharges (sourceA830 + difference 5 3) (sourceB830 + difference 3 5) sourceC830) = raw13671 := by
      apply Matrix.ext; unfold tripleCharges sourceA830 sourceB830 sourceC830 difference raw13671; decide +kernel
    rw [ha]
    exact (canonical13671 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA830 + difference 5 4) (sourceB830 + difference 4 5) sourceC830) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2766) := by
    have ha : (tripleCharges (sourceA830 + difference 5 4) (sourceB830 + difference 4 5) sourceC830) = raw13672 := by
      apply Matrix.ext; unfold tripleCharges sourceA830 sourceB830 sourceC830 difference raw13672; decide +kernel
    rw [ha]
    exact (canonical13672 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA830 sourceB830 sourceC830
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm830, Integer.Sparse.eval]
  linarith only [hs]

def sourceA831 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB831 : Charge := ![1, 1, -1, 0, 0, -1]
def sourceC831 : Charge := ![2, -1, 1, -1, -1, 0]
def sourceForm831 : Integer.Sparse Master := [(Sum.inr 4589, 1), (Sum.inr 4590, 2), (Sum.inr 4599, 1), (Sum.inr 4601, 1), (Sum.inr 5073, 2), (Sum.inr 5076, 1), (Sum.inr 5100, 1), (Sum.inr 5185, 2), (Sum.inr 5187, 1), (Sum.inr 5197, 1), (Sum.inr 5250, 2), (Sum.inr 5251, 2), (Sum.inr 5257, 2), (Sum.inr 5259, 2), (Sum.inr 5273, 1), (Sum.inr 5281, 2), (Sum.inr 5290, 1), (Sum.inr 5408, 1), (Sum.inr 5431, 1), (Sum.inr 5433, 2), (Sum.inr 5440, 1)]

theorem sourceEq831 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm831 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA831 + difference 0 1) (sourceB831 + difference 1 0) sourceC831) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA831 + difference 0 1) (sourceB831 + difference 1 0) sourceC831) = raw13673 := by
      apply Matrix.ext; unfold tripleCharges sourceA831 sourceB831 sourceC831 difference raw13673; decide +kernel
    rw [ha]
    exact (canonical13673 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA831 + difference 0 2) (sourceB831 + difference 2 0) sourceC831) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5408) := by
    have ha : (tripleCharges (sourceA831 + difference 0 2) (sourceB831 + difference 2 0) sourceC831) = raw13674 := by
      apply Matrix.ext; unfold tripleCharges sourceA831 sourceB831 sourceC831 difference raw13674; decide +kernel
    rw [ha]
    exact (canonical13674 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA831 + difference 0 3) (sourceB831 + difference 3 0) sourceC831) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA831 + difference 0 3) (sourceB831 + difference 3 0) sourceC831) = raw13675 := by
      apply Matrix.ext; unfold tripleCharges sourceA831 sourceB831 sourceC831 difference raw13675; decide +kernel
    rw [ha]
    exact (canonical13675 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA831 + difference 0 4) (sourceB831 + difference 4 0) sourceC831) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA831 + difference 0 4) (sourceB831 + difference 4 0) sourceC831) = raw13676 := by
      apply Matrix.ext; unfold tripleCharges sourceA831 sourceB831 sourceC831 difference raw13676; decide +kernel
    rw [ha]
    exact (canonical13676 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA831 + difference 0 5) (sourceB831 + difference 5 0) sourceC831) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5440) := by
    have ha : (tripleCharges (sourceA831 + difference 0 5) (sourceB831 + difference 5 0) sourceC831) = raw13677 := by
      apply Matrix.ext; unfold tripleCharges sourceA831 sourceB831 sourceC831 difference raw13677; decide +kernel
    rw [ha]
    exact (canonical13677 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA831 + difference 1 0) (sourceB831 + difference 0 1) sourceC831) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4601) := by
    have ha : (tripleCharges (sourceA831 + difference 1 0) (sourceB831 + difference 0 1) sourceC831) = raw13678 := by
      apply Matrix.ext; unfold tripleCharges sourceA831 sourceB831 sourceC831 difference raw13678; decide +kernel
    rw [ha]
    exact (canonical13678 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA831 + difference 1 2) (sourceB831 + difference 2 1) sourceC831) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5100) := by
    have ha : (tripleCharges (sourceA831 + difference 1 2) (sourceB831 + difference 2 1) sourceC831) = raw13679 := by
      apply Matrix.ext; unfold tripleCharges sourceA831 sourceB831 sourceC831 difference raw13679; decide +kernel
    rw [ha]
    exact (canonical13679 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA831 + difference 1 3) (sourceB831 + difference 3 1) sourceC831) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA831 + difference 1 3) (sourceB831 + difference 3 1) sourceC831) = raw13680 := by
      apply Matrix.ext; unfold tripleCharges sourceA831 sourceB831 sourceC831 difference raw13680; decide +kernel
    rw [ha]
    exact (canonical13680 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA831 + difference 1 4) (sourceB831 + difference 4 1) sourceC831) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA831 + difference 1 4) (sourceB831 + difference 4 1) sourceC831) = raw13681 := by
      apply Matrix.ext; unfold tripleCharges sourceA831 sourceB831 sourceC831 difference raw13681; decide +kernel
    rw [ha]
    exact (canonical13681 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA831 + difference 1 5) (sourceB831 + difference 5 1) sourceC831) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5273) := by
    have ha : (tripleCharges (sourceA831 + difference 1 5) (sourceB831 + difference 5 1) sourceC831) = raw13682 := by
      apply Matrix.ext; unfold tripleCharges sourceA831 sourceB831 sourceC831 difference raw13682; decide +kernel
    rw [ha]
    exact (canonical13682 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA831 + difference 2 0) (sourceB831 + difference 0 2) sourceC831) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4599) := by
    have ha : (tripleCharges (sourceA831 + difference 2 0) (sourceB831 + difference 0 2) sourceC831) = raw13683 := by
      apply Matrix.ext; unfold tripleCharges sourceA831 sourceB831 sourceC831 difference raw13683; decide +kernel
    rw [ha]
    exact (canonical13683 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA831 + difference 2 1) (sourceB831 + difference 1 2) sourceC831) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5197) := by
    have ha : (tripleCharges (sourceA831 + difference 2 1) (sourceB831 + difference 1 2) sourceC831) = raw13684 := by
      apply Matrix.ext; unfold tripleCharges sourceA831 sourceB831 sourceC831 difference raw13684; decide +kernel
    rw [ha]
    exact (canonical13684 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA831 + difference 2 3) (sourceB831 + difference 3 2) sourceC831) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5281) := by
    have ha : (tripleCharges (sourceA831 + difference 2 3) (sourceB831 + difference 3 2) sourceC831) = raw13685 := by
      apply Matrix.ext; unfold tripleCharges sourceA831 sourceB831 sourceC831 difference raw13685; decide +kernel
    rw [ha]
    exact (canonical13685 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA831 + difference 2 4) (sourceB831 + difference 4 2) sourceC831) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5281) := by
    have ha : (tripleCharges (sourceA831 + difference 2 4) (sourceB831 + difference 4 2) sourceC831) = raw13686 := by
      apply Matrix.ext; unfold tripleCharges sourceA831 sourceB831 sourceC831 difference raw13686; decide +kernel
    rw [ha]
    exact (canonical13686 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA831 + difference 2 5) (sourceB831 + difference 5 2) sourceC831) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA831 + difference 2 5) (sourceB831 + difference 5 2) sourceC831) = raw13687 := by
      apply Matrix.ext; unfold tripleCharges sourceA831 sourceB831 sourceC831 difference raw13687; decide +kernel
    rw [ha]
    exact (canonical13687 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA831 + difference 3 0) (sourceB831 + difference 0 3) sourceC831) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4590) := by
    have ha : (tripleCharges (sourceA831 + difference 3 0) (sourceB831 + difference 0 3) sourceC831) = raw13688 := by
      apply Matrix.ext; unfold tripleCharges sourceA831 sourceB831 sourceC831 difference raw13688; decide +kernel
    rw [ha]
    exact (canonical13688 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA831 + difference 3 1) (sourceB831 + difference 1 3) sourceC831) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5185) := by
    have ha : (tripleCharges (sourceA831 + difference 3 1) (sourceB831 + difference 1 3) sourceC831) = raw13689 := by
      apply Matrix.ext; unfold tripleCharges sourceA831 sourceB831 sourceC831 difference raw13689; decide +kernel
    rw [ha]
    exact (canonical13689 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA831 + difference 3 2) (sourceB831 + difference 2 3) sourceC831) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5073) := by
    have ha : (tripleCharges (sourceA831 + difference 3 2) (sourceB831 + difference 2 3) sourceC831) = raw13690 := by
      apply Matrix.ext; unfold tripleCharges sourceA831 sourceB831 sourceC831 difference raw13690; decide +kernel
    rw [ha]
    exact (canonical13690 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA831 + difference 3 4) (sourceB831 + difference 4 3) sourceC831) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5250) := by
    have ha : (tripleCharges (sourceA831 + difference 3 4) (sourceB831 + difference 4 3) sourceC831) = raw13691 := by
      apply Matrix.ext; unfold tripleCharges sourceA831 sourceB831 sourceC831 difference raw13691; decide +kernel
    rw [ha]
    exact (canonical13691 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA831 + difference 3 5) (sourceB831 + difference 5 3) sourceC831) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA831 + difference 3 5) (sourceB831 + difference 5 3) sourceC831) = raw13692 := by
      apply Matrix.ext; unfold tripleCharges sourceA831 sourceB831 sourceC831 difference raw13692; decide +kernel
    rw [ha]
    exact (canonical13692 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA831 + difference 4 0) (sourceB831 + difference 0 4) sourceC831) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4590) := by
    have ha : (tripleCharges (sourceA831 + difference 4 0) (sourceB831 + difference 0 4) sourceC831) = raw13693 := by
      apply Matrix.ext; unfold tripleCharges sourceA831 sourceB831 sourceC831 difference raw13693; decide +kernel
    rw [ha]
    exact (canonical13693 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA831 + difference 4 1) (sourceB831 + difference 1 4) sourceC831) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5185) := by
    have ha : (tripleCharges (sourceA831 + difference 4 1) (sourceB831 + difference 1 4) sourceC831) = raw13694 := by
      apply Matrix.ext; unfold tripleCharges sourceA831 sourceB831 sourceC831 difference raw13694; decide +kernel
    rw [ha]
    exact (canonical13694 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA831 + difference 4 2) (sourceB831 + difference 2 4) sourceC831) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5073) := by
    have ha : (tripleCharges (sourceA831 + difference 4 2) (sourceB831 + difference 2 4) sourceC831) = raw13695 := by
      apply Matrix.ext; unfold tripleCharges sourceA831 sourceB831 sourceC831 difference raw13695; decide +kernel
    rw [ha]
    exact (canonical13695 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA831 + difference 4 3) (sourceB831 + difference 3 4) sourceC831) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5250) := by
    have ha : (tripleCharges (sourceA831 + difference 4 3) (sourceB831 + difference 3 4) sourceC831) = raw13696 := by
      apply Matrix.ext; unfold tripleCharges sourceA831 sourceB831 sourceC831 difference raw13696; decide +kernel
    rw [ha]
    exact (canonical13696 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA831 + difference 4 5) (sourceB831 + difference 5 4) sourceC831) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA831 + difference 4 5) (sourceB831 + difference 5 4) sourceC831) = raw13697 := by
      apply Matrix.ext; unfold tripleCharges sourceA831 sourceB831 sourceC831 difference raw13697; decide +kernel
    rw [ha]
    exact (canonical13697 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA831 + difference 5 0) (sourceB831 + difference 0 5) sourceC831) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4589) := by
    have ha : (tripleCharges (sourceA831 + difference 5 0) (sourceB831 + difference 0 5) sourceC831) = raw13698 := by
      apply Matrix.ext; unfold tripleCharges sourceA831 sourceB831 sourceC831 difference raw13698; decide +kernel
    rw [ha]
    exact (canonical13698 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA831 + difference 5 1) (sourceB831 + difference 1 5) sourceC831) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5187) := by
    have ha : (tripleCharges (sourceA831 + difference 5 1) (sourceB831 + difference 1 5) sourceC831) = raw13699 := by
      apply Matrix.ext; unfold tripleCharges sourceA831 sourceB831 sourceC831 difference raw13699; decide +kernel
    rw [ha]
    exact (canonical13699 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA831 + difference 5 2) (sourceB831 + difference 2 5) sourceC831) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5076) := by
    have ha : (tripleCharges (sourceA831 + difference 5 2) (sourceB831 + difference 2 5) sourceC831) = raw13700 := by
      apply Matrix.ext; unfold tripleCharges sourceA831 sourceB831 sourceC831 difference raw13700; decide +kernel
    rw [ha]
    exact (canonical13700 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA831 + difference 5 3) (sourceB831 + difference 3 5) sourceC831) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5251) := by
    have ha : (tripleCharges (sourceA831 + difference 5 3) (sourceB831 + difference 3 5) sourceC831) = raw13701 := by
      apply Matrix.ext; unfold tripleCharges sourceA831 sourceB831 sourceC831 difference raw13701; decide +kernel
    rw [ha]
    exact (canonical13701 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA831 + difference 5 4) (sourceB831 + difference 4 5) sourceC831) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5251) := by
    have ha : (tripleCharges (sourceA831 + difference 5 4) (sourceB831 + difference 4 5) sourceC831) = raw13702 := by
      apply Matrix.ext; unfold tripleCharges sourceA831 sourceB831 sourceC831 difference raw13702; decide +kernel
    rw [ha]
    exact (canonical13702 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA831 sourceB831 sourceC831
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm831, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
