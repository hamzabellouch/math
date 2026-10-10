import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical94
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical96
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical97
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical98
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical103
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical104
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical106
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical109
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical113
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical116
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical118
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical132
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical133
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical135
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical138
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical142
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical143
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical148
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical159
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical160
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical163
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical166
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical175
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical176
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical180
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical188
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical189
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical191
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical192
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical193
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical195
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical198
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical208
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical214
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical215
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical216
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical218
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical224
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical225
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical230
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical231
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical235
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical250
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical251
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical252
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical253

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA2336 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2336 : Charge := ![1, 1, -1, 0, 1, -2]
def sourceC2336 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceForm2336 : Integer.Sparse Master := [(Sum.inr 2430, 1), (Sum.inr 2431, 1), (Sum.inr 2433, 1), (Sum.inr 2515, 1), (Sum.inr 2557, 1), (Sum.inr 3782, 1), (Sum.inr 4092, -1)]

theorem sourceEq2336 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2336 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2336 + difference 0 2) (sourceB2336 + difference 2 0) sourceC2336) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3782) := by
    have ha : (tripleCharges (sourceA2336 + difference 0 2) (sourceB2336 + difference 2 0) sourceC2336) = raw14566 := by
      apply Matrix.ext; unfold tripleCharges sourceA2336 sourceB2336 sourceC2336 difference raw14566; decide +kernel
    rw [ha]
    exact (canonical14566 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2336 + difference 1 2) (sourceB2336 + difference 2 1) sourceC2336) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2515) := by
    have ha : (tripleCharges (sourceA2336 + difference 1 2) (sourceB2336 + difference 2 1) sourceC2336) = raw32022 := by
      apply Matrix.ext; unfold tripleCharges sourceA2336 sourceB2336 sourceC2336 difference raw32022; decide +kernel
    rw [ha]
    exact (canonical32022 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2336 + difference 2 2) (sourceB2336 + difference 2 2) sourceC2336) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2557) := by
    have ha : (tripleCharges (sourceA2336 + difference 2 2) (sourceB2336 + difference 2 2) sourceC2336) = raw14569 := by
      apply Matrix.ext; unfold tripleCharges sourceA2336 sourceB2336 sourceC2336 difference raw14569; decide +kernel
    rw [ha]
    exact (canonical14569 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2336 + difference 3 2) (sourceB2336 + difference 2 3) sourceC2336) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2433) := by
    have ha : (tripleCharges (sourceA2336 + difference 3 2) (sourceB2336 + difference 2 3) sourceC2336) = raw32023 := by
      apply Matrix.ext; unfold tripleCharges sourceA2336 sourceB2336 sourceC2336 difference raw32023; decide +kernel
    rw [ha]
    exact (canonical32023 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2336 + difference 4 2) (sourceB2336 + difference 2 4) sourceC2336) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2431) := by
    have ha : (tripleCharges (sourceA2336 + difference 4 2) (sourceB2336 + difference 2 4) sourceC2336) = raw32024 := by
      apply Matrix.ext; unfold tripleCharges sourceA2336 sourceB2336 sourceC2336 difference raw32024; decide +kernel
    rw [ha]
    exact (canonical32024 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2336 + difference 5 2) (sourceB2336 + difference 2 5) sourceC2336) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2430) := by
    have ha : (tripleCharges (sourceA2336 + difference 5 2) (sourceB2336 + difference 2 5) sourceC2336) = raw32025 := by
      apply Matrix.ext; unfold tripleCharges sourceA2336 sourceB2336 sourceC2336 difference raw32025; decide +kernel
    rw [ha]
    exact (canonical32025 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2336 + sourceB2336) sourceC2336) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2336 + sourceB2336) sourceC2336) = raw14556 := by
      apply Matrix.ext; unfold doubleCharges sourceA2336 sourceB2336 sourceC2336 raw14556; decide +kernel
    rw [ha]
    exact (canonical14556 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2336 sourceB2336 sourceC2336
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2336, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2337 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2337 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceC2337 : Charge := ![1, 1, -1, 0, 1, -2]
def sourceForm2337 : Integer.Sparse Master := [(Sum.inr 1335, 1), (Sum.inr 2826, 1), (Sum.inr 2924, 1), (Sum.inr 2933, 1), (Sum.inr 2951, 1), (Sum.inr 2954, 1), (Sum.inr 4091, -1)]

theorem sourceEq2337 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2337 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2337 + difference 2 0) (sourceB2337 + difference 0 2) sourceC2337) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1335) := by
    have ha : (tripleCharges (sourceA2337 + difference 2 0) (sourceB2337 + difference 0 2) sourceC2337) = raw32026 := by
      apply Matrix.ext; unfold tripleCharges sourceA2337 sourceB2337 sourceC2337 difference raw32026; decide +kernel
    rw [ha]
    exact (canonical32026 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2337 + difference 2 1) (sourceB2337 + difference 1 2) sourceC2337) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2826) := by
    have ha : (tripleCharges (sourceA2337 + difference 2 1) (sourceB2337 + difference 1 2) sourceC2337) = raw32027 := by
      apply Matrix.ext; unfold tripleCharges sourceA2337 sourceB2337 sourceC2337 difference raw32027; decide +kernel
    rw [ha]
    exact (canonical32027 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2337 + difference 2 2) (sourceB2337 + difference 2 2) sourceC2337) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2933) := by
    have ha : (tripleCharges (sourceA2337 + difference 2 2) (sourceB2337 + difference 2 2) sourceC2337) = raw32028 := by
      apply Matrix.ext; unfold tripleCharges sourceA2337 sourceB2337 sourceC2337 difference raw32028; decide +kernel
    rw [ha]
    exact (canonical32028 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2337 + difference 2 3) (sourceB2337 + difference 3 2) sourceC2337) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2954) := by
    have ha : (tripleCharges (sourceA2337 + difference 2 3) (sourceB2337 + difference 3 2) sourceC2337) = raw27476 := by
      apply Matrix.ext; unfold tripleCharges sourceA2337 sourceB2337 sourceC2337 difference raw27476; decide +kernel
    rw [ha]
    exact (canonical27476 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2337 + difference 2 4) (sourceB2337 + difference 4 2) sourceC2337) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2924) := by
    have ha : (tripleCharges (sourceA2337 + difference 2 4) (sourceB2337 + difference 4 2) sourceC2337) = raw32029 := by
      apply Matrix.ext; unfold tripleCharges sourceA2337 sourceB2337 sourceC2337 difference raw32029; decide +kernel
    rw [ha]
    exact (canonical32029 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2337 + difference 2 5) (sourceB2337 + difference 5 2) sourceC2337) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2951) := by
    have ha : (tripleCharges (sourceA2337 + difference 2 5) (sourceB2337 + difference 5 2) sourceC2337) = raw32030 := by
      apply Matrix.ext; unfold tripleCharges sourceA2337 sourceB2337 sourceC2337 difference raw32030; decide +kernel
    rw [ha]
    exact (canonical32030 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2337 + sourceB2337) sourceC2337) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA2337 + sourceB2337) sourceC2337) = raw17313 := by
      apply Matrix.ext; unfold doubleCharges sourceA2337 sourceB2337 sourceC2337 raw17313; decide +kernel
    rw [ha]
    exact (canonical17313 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2337 sourceB2337 sourceC2337
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2337, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2338 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2338 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC2338 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceForm2338 : Integer.Sparse Master := [(Sum.inr 4550, 1), (Sum.inr 4551, 1), (Sum.inr 4553, 2), (Sum.inr 4623, 1), (Sum.inr 4967, 1), (Sum.inr 4970, 1), (Sum.inr 4973, 2), (Sum.inr 5113, 1), (Sum.inr 5114, 2), (Sum.inr 5166, 1), (Sum.inr 5168, 3), (Sum.inr 5170, 2), (Sum.inr 5171, 2), (Sum.inr 5176, 2), (Sum.inr 5306, 1), (Sum.inr 5308, 2), (Sum.inr 5387, 1), (Sum.inr 5415, 1), (Sum.inr 5439, 1), (Sum.inr 5441, 2)]

theorem sourceEq2338 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2338 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2338 + difference 0 1) (sourceB2338 + difference 1 0) sourceC2338) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5387) := by
    have ha : (tripleCharges (sourceA2338 + difference 0 1) (sourceB2338 + difference 1 0) sourceC2338) = raw18303 := by
      apply Matrix.ext; unfold tripleCharges sourceA2338 sourceB2338 sourceC2338 difference raw18303; decide +kernel
    rw [ha]
    exact (canonical18303 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2338 + difference 0 2) (sourceB2338 + difference 2 0) sourceC2338) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5415) := by
    have ha : (tripleCharges (sourceA2338 + difference 0 2) (sourceB2338 + difference 2 0) sourceC2338) = raw18304 := by
      apply Matrix.ext; unfold tripleCharges sourceA2338 sourceB2338 sourceC2338 difference raw18304; decide +kernel
    rw [ha]
    exact (canonical18304 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2338 + difference 0 3) (sourceB2338 + difference 3 0) sourceC2338) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5441) := by
    have ha : (tripleCharges (sourceA2338 + difference 0 3) (sourceB2338 + difference 3 0) sourceC2338) = raw10216 := by
      apply Matrix.ext; unfold tripleCharges sourceA2338 sourceB2338 sourceC2338 difference raw10216; decide +kernel
    rw [ha]
    exact (canonical10216 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2338 + difference 0 4) (sourceB2338 + difference 4 0) sourceC2338) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5441) := by
    have ha : (tripleCharges (sourceA2338 + difference 0 4) (sourceB2338 + difference 4 0) sourceC2338) = raw18305 := by
      apply Matrix.ext; unfold tripleCharges sourceA2338 sourceB2338 sourceC2338 difference raw18305; decide +kernel
    rw [ha]
    exact (canonical18305 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2338 + difference 0 5) (sourceB2338 + difference 5 0) sourceC2338) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA2338 + difference 0 5) (sourceB2338 + difference 5 0) sourceC2338) = raw12080 := by
      apply Matrix.ext; unfold tripleCharges sourceA2338 sourceB2338 sourceC2338 difference raw12080; decide +kernel
    rw [ha]
    exact (canonical12080 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2338 + difference 1 0) (sourceB2338 + difference 0 1) sourceC2338) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4623) := by
    have ha : (tripleCharges (sourceA2338 + difference 1 0) (sourceB2338 + difference 0 1) sourceC2338) = raw10228 := by
      apply Matrix.ext; unfold tripleCharges sourceA2338 sourceB2338 sourceC2338 difference raw10228; decide +kernel
    rw [ha]
    exact (canonical10228 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2338 + difference 1 2) (sourceB2338 + difference 2 1) sourceC2338) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5168) := by
    have ha : (tripleCharges (sourceA2338 + difference 1 2) (sourceB2338 + difference 2 1) sourceC2338) = raw10230 := by
      apply Matrix.ext; unfold tripleCharges sourceA2338 sourceB2338 sourceC2338 difference raw10230; decide +kernel
    rw [ha]
    exact (canonical10230 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2338 + difference 1 3) (sourceB2338 + difference 3 1) sourceC2338) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5308) := by
    have ha : (tripleCharges (sourceA2338 + difference 1 3) (sourceB2338 + difference 3 1) sourceC2338) = raw5082 := by
      apply Matrix.ext; unfold tripleCharges sourceA2338 sourceB2338 sourceC2338 difference raw5082; decide +kernel
    rw [ha]
    exact (canonical5082 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2338 + difference 1 4) (sourceB2338 + difference 4 1) sourceC2338) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5308) := by
    have ha : (tripleCharges (sourceA2338 + difference 1 4) (sourceB2338 + difference 4 1) sourceC2338) = raw5077 := by
      apply Matrix.ext; unfold tripleCharges sourceA2338 sourceB2338 sourceC2338 difference raw5077; decide +kernel
    rw [ha]
    exact (canonical5077 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2338 + difference 1 5) (sourceB2338 + difference 5 1) sourceC2338) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5306) := by
    have ha : (tripleCharges (sourceA2338 + difference 1 5) (sourceB2338 + difference 5 1) sourceC2338) = raw10231 := by
      apply Matrix.ext; unfold tripleCharges sourceA2338 sourceB2338 sourceC2338 difference raw10231; decide +kernel
    rw [ha]
    exact (canonical10231 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2338 + difference 2 0) (sourceB2338 + difference 0 2) sourceC2338) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4550) := by
    have ha : (tripleCharges (sourceA2338 + difference 2 0) (sourceB2338 + difference 0 2) sourceC2338) = raw24105 := by
      apply Matrix.ext; unfold tripleCharges sourceA2338 sourceB2338 sourceC2338 difference raw24105; decide +kernel
    rw [ha]
    exact (canonical24105 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2338 + difference 2 1) (sourceB2338 + difference 1 2) sourceC2338) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4967) := by
    have ha : (tripleCharges (sourceA2338 + difference 2 1) (sourceB2338 + difference 1 2) sourceC2338) = raw32031 := by
      apply Matrix.ext; unfold tripleCharges sourceA2338 sourceB2338 sourceC2338 difference raw32031; decide +kernel
    rw [ha]
    exact (canonical32031 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2338 + difference 2 3) (sourceB2338 + difference 3 2) sourceC2338) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5168) := by
    have ha : (tripleCharges (sourceA2338 + difference 2 3) (sourceB2338 + difference 3 2) sourceC2338) = raw10225 := by
      apply Matrix.ext; unfold tripleCharges sourceA2338 sourceB2338 sourceC2338 difference raw10225; decide +kernel
    rw [ha]
    exact (canonical10225 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2338 + difference 2 4) (sourceB2338 + difference 4 2) sourceC2338) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5168) := by
    have ha : (tripleCharges (sourceA2338 + difference 2 4) (sourceB2338 + difference 4 2) sourceC2338) = raw32032 := by
      apply Matrix.ext; unfold tripleCharges sourceA2338 sourceB2338 sourceC2338 difference raw32032; decide +kernel
    rw [ha]
    exact (canonical32032 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2338 + difference 2 5) (sourceB2338 + difference 5 2) sourceC2338) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5166) := by
    have ha : (tripleCharges (sourceA2338 + difference 2 5) (sourceB2338 + difference 5 2) sourceC2338) = raw12089 := by
      apply Matrix.ext; unfold tripleCharges sourceA2338 sourceB2338 sourceC2338 difference raw12089; decide +kernel
    rw [ha]
    exact (canonical12089 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2338 + difference 3 0) (sourceB2338 + difference 0 3) sourceC2338) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4553) := by
    have ha : (tripleCharges (sourceA2338 + difference 3 0) (sourceB2338 + difference 0 3) sourceC2338) = raw24108 := by
      apply Matrix.ext; unfold tripleCharges sourceA2338 sourceB2338 sourceC2338 difference raw24108; decide +kernel
    rw [ha]
    exact (canonical24108 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2338 + difference 3 1) (sourceB2338 + difference 1 3) sourceC2338) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4973) := by
    have ha : (tripleCharges (sourceA2338 + difference 3 1) (sourceB2338 + difference 1 3) sourceC2338) = raw32033 := by
      apply Matrix.ext; unfold tripleCharges sourceA2338 sourceB2338 sourceC2338 difference raw32033; decide +kernel
    rw [ha]
    exact (canonical32033 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2338 + difference 3 2) (sourceB2338 + difference 2 3) sourceC2338) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5114) := by
    have ha : (tripleCharges (sourceA2338 + difference 3 2) (sourceB2338 + difference 2 3) sourceC2338) = raw32034 := by
      apply Matrix.ext; unfold tripleCharges sourceA2338 sourceB2338 sourceC2338 difference raw32034; decide +kernel
    rw [ha]
    exact (canonical32034 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2338 + difference 3 4) (sourceB2338 + difference 4 3) sourceC2338) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5176) := by
    have ha : (tripleCharges (sourceA2338 + difference 3 4) (sourceB2338 + difference 4 3) sourceC2338) = raw32035 := by
      apply Matrix.ext; unfold tripleCharges sourceA2338 sourceB2338 sourceC2338 difference raw32035; decide +kernel
    rw [ha]
    exact (canonical32035 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2338 + difference 3 5) (sourceB2338 + difference 5 3) sourceC2338) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5170) := by
    have ha : (tripleCharges (sourceA2338 + difference 3 5) (sourceB2338 + difference 5 3) sourceC2338) = raw12093 := by
      apply Matrix.ext; unfold tripleCharges sourceA2338 sourceB2338 sourceC2338 difference raw12093; decide +kernel
    rw [ha]
    exact (canonical12093 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2338 + difference 4 0) (sourceB2338 + difference 0 4) sourceC2338) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4553) := by
    have ha : (tripleCharges (sourceA2338 + difference 4 0) (sourceB2338 + difference 0 4) sourceC2338) = raw22480 := by
      apply Matrix.ext; unfold tripleCharges sourceA2338 sourceB2338 sourceC2338 difference raw22480; decide +kernel
    rw [ha]
    exact (canonical22480 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2338 + difference 4 1) (sourceB2338 + difference 1 4) sourceC2338) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4973) := by
    have ha : (tripleCharges (sourceA2338 + difference 4 1) (sourceB2338 + difference 1 4) sourceC2338) = raw29509 := by
      apply Matrix.ext; unfold tripleCharges sourceA2338 sourceB2338 sourceC2338 difference raw29509; decide +kernel
    rw [ha]
    exact (canonical29509 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2338 + difference 4 2) (sourceB2338 + difference 2 4) sourceC2338) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5114) := by
    have ha : (tripleCharges (sourceA2338 + difference 4 2) (sourceB2338 + difference 2 4) sourceC2338) = raw29510 := by
      apply Matrix.ext; unfold tripleCharges sourceA2338 sourceB2338 sourceC2338 difference raw29510; decide +kernel
    rw [ha]
    exact (canonical29510 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2338 + difference 4 3) (sourceB2338 + difference 3 4) sourceC2338) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5176) := by
    have ha : (tripleCharges (sourceA2338 + difference 4 3) (sourceB2338 + difference 3 4) sourceC2338) = raw10233 := by
      apply Matrix.ext; unfold tripleCharges sourceA2338 sourceB2338 sourceC2338 difference raw10233; decide +kernel
    rw [ha]
    exact (canonical10233 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2338 + difference 4 5) (sourceB2338 + difference 5 4) sourceC2338) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5170) := by
    have ha : (tripleCharges (sourceA2338 + difference 4 5) (sourceB2338 + difference 5 4) sourceC2338) = raw12098 := by
      apply Matrix.ext; unfold tripleCharges sourceA2338 sourceB2338 sourceC2338 difference raw12098; decide +kernel
    rw [ha]
    exact (canonical12098 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2338 + difference 5 0) (sourceB2338 + difference 0 5) sourceC2338) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4551) := by
    have ha : (tripleCharges (sourceA2338 + difference 5 0) (sourceB2338 + difference 0 5) sourceC2338) = raw20358 := by
      apply Matrix.ext; unfold tripleCharges sourceA2338 sourceB2338 sourceC2338 difference raw20358; decide +kernel
    rw [ha]
    exact (canonical20358 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2338 + difference 5 1) (sourceB2338 + difference 1 5) sourceC2338) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4970) := by
    have ha : (tripleCharges (sourceA2338 + difference 5 1) (sourceB2338 + difference 1 5) sourceC2338) = raw27560 := by
      apply Matrix.ext; unfold tripleCharges sourceA2338 sourceB2338 sourceC2338 difference raw27560; decide +kernel
    rw [ha]
    exact (canonical27560 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2338 + difference 5 2) (sourceB2338 + difference 2 5) sourceC2338) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5113) := by
    have ha : (tripleCharges (sourceA2338 + difference 5 2) (sourceB2338 + difference 2 5) sourceC2338) = raw27561 := by
      apply Matrix.ext; unfold tripleCharges sourceA2338 sourceB2338 sourceC2338 difference raw27561; decide +kernel
    rw [ha]
    exact (canonical27561 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2338 + difference 5 3) (sourceB2338 + difference 3 5) sourceC2338) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5171) := by
    have ha : (tripleCharges (sourceA2338 + difference 5 3) (sourceB2338 + difference 3 5) sourceC2338) = raw5079 := by
      apply Matrix.ext; unfold tripleCharges sourceA2338 sourceB2338 sourceC2338 difference raw5079; decide +kernel
    rw [ha]
    exact (canonical5079 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2338 + difference 5 4) (sourceB2338 + difference 4 5) sourceC2338) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5171) := by
    have ha : (tripleCharges (sourceA2338 + difference 5 4) (sourceB2338 + difference 4 5) sourceC2338) = raw5074 := by
      apply Matrix.ext; unfold tripleCharges sourceA2338 sourceB2338 sourceC2338 difference raw5074; decide +kernel
    rw [ha]
    exact (canonical5074 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2338 sourceB2338 sourceC2338
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2338, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2339 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2339 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC2339 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceForm2339 : Integer.Sparse Master := [(Sum.inr 1135, 1), (Sum.inr 1136, 1), (Sum.inr 1138, 2), (Sum.inr 1305, 1), (Sum.inr 2814, 1), (Sum.inr 2815, 1), (Sum.inr 2817, 2), (Sum.inr 2894, 1), (Sum.inr 2896, 2), (Sum.inr 2953, 1), (Sum.inr 2954, 2), (Sum.inr 2963, 3), (Sum.inr 2965, 2), (Sum.inr 2968, 2), (Sum.inr 3120, 1), (Sum.inr 3124, 2), (Sum.inr 3739, 1), (Sum.inr 4012, 1), (Sum.inr 4031, 1), (Sum.inr 4037, 2)]

theorem sourceEq2339 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2339 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2339 + difference 0 1) (sourceB2339 + difference 1 0) sourceC2339) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3739) := by
    have ha : (tripleCharges (sourceA2339 + difference 0 1) (sourceB2339 + difference 1 0) sourceC2339) = raw32036 := by
      apply Matrix.ext; unfold tripleCharges sourceA2339 sourceB2339 sourceC2339 difference raw32036; decide +kernel
    rw [ha]
    exact (canonical32036 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2339 + difference 0 2) (sourceB2339 + difference 2 0) sourceC2339) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4031) := by
    have ha : (tripleCharges (sourceA2339 + difference 0 2) (sourceB2339 + difference 2 0) sourceC2339) = raw32037 := by
      apply Matrix.ext; unfold tripleCharges sourceA2339 sourceB2339 sourceC2339 difference raw32037; decide +kernel
    rw [ha]
    exact (canonical32037 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2339 + difference 0 3) (sourceB2339 + difference 3 0) sourceC2339) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4037) := by
    have ha : (tripleCharges (sourceA2339 + difference 0 3) (sourceB2339 + difference 3 0) sourceC2339) = raw27572 := by
      apply Matrix.ext; unfold tripleCharges sourceA2339 sourceB2339 sourceC2339 difference raw27572; decide +kernel
    rw [ha]
    exact (canonical27572 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2339 + difference 0 4) (sourceB2339 + difference 4 0) sourceC2339) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4037) := by
    have ha : (tripleCharges (sourceA2339 + difference 0 4) (sourceB2339 + difference 4 0) sourceC2339) = raw32038 := by
      apply Matrix.ext; unfold tripleCharges sourceA2339 sourceB2339 sourceC2339 difference raw32038; decide +kernel
    rw [ha]
    exact (canonical32038 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2339 + difference 0 5) (sourceB2339 + difference 5 0) sourceC2339) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4012) := by
    have ha : (tripleCharges (sourceA2339 + difference 0 5) (sourceB2339 + difference 5 0) sourceC2339) = raw12101 := by
      apply Matrix.ext; unfold tripleCharges sourceA2339 sourceB2339 sourceC2339 difference raw12101; decide +kernel
    rw [ha]
    exact (canonical12101 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2339 + difference 1 0) (sourceB2339 + difference 0 1) sourceC2339) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1305) := by
    have ha : (tripleCharges (sourceA2339 + difference 1 0) (sourceB2339 + difference 0 1) sourceC2339) = raw12126 := by
      apply Matrix.ext; unfold tripleCharges sourceA2339 sourceB2339 sourceC2339 difference raw12126; decide +kernel
    rw [ha]
    exact (canonical12126 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2339 + difference 1 2) (sourceB2339 + difference 2 1) sourceC2339) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2963) := by
    have ha : (tripleCharges (sourceA2339 + difference 1 2) (sourceB2339 + difference 2 1) sourceC2339) = raw12128 := by
      apply Matrix.ext; unfold tripleCharges sourceA2339 sourceB2339 sourceC2339 difference raw12128; decide +kernel
    rw [ha]
    exact (canonical12128 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2339 + difference 1 3) (sourceB2339 + difference 3 1) sourceC2339) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3124) := by
    have ha : (tripleCharges (sourceA2339 + difference 1 3) (sourceB2339 + difference 3 1) sourceC2339) = raw12129 := by
      apply Matrix.ext; unfold tripleCharges sourceA2339 sourceB2339 sourceC2339 difference raw12129; decide +kernel
    rw [ha]
    exact (canonical12129 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2339 + difference 1 4) (sourceB2339 + difference 4 1) sourceC2339) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3124) := by
    have ha : (tripleCharges (sourceA2339 + difference 1 4) (sourceB2339 + difference 4 1) sourceC2339) = raw12130 := by
      apply Matrix.ext; unfold tripleCharges sourceA2339 sourceB2339 sourceC2339 difference raw12130; decide +kernel
    rw [ha]
    exact (canonical12130 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2339 + difference 1 5) (sourceB2339 + difference 5 1) sourceC2339) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3120) := by
    have ha : (tripleCharges (sourceA2339 + difference 1 5) (sourceB2339 + difference 5 1) sourceC2339) = raw24111 := by
      apply Matrix.ext; unfold tripleCharges sourceA2339 sourceB2339 sourceC2339 difference raw24111; decide +kernel
    rw [ha]
    exact (canonical24111 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2339 + difference 2 0) (sourceB2339 + difference 0 2) sourceC2339) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1135) := by
    have ha : (tripleCharges (sourceA2339 + difference 2 0) (sourceB2339 + difference 0 2) sourceC2339) = raw24116 := by
      apply Matrix.ext; unfold tripleCharges sourceA2339 sourceB2339 sourceC2339 difference raw24116; decide +kernel
    rw [ha]
    exact (canonical24116 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2339 + difference 2 1) (sourceB2339 + difference 1 2) sourceC2339) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2814) := by
    have ha : (tripleCharges (sourceA2339 + difference 2 1) (sourceB2339 + difference 1 2) sourceC2339) = raw32039 := by
      apply Matrix.ext; unfold tripleCharges sourceA2339 sourceB2339 sourceC2339 difference raw32039; decide +kernel
    rw [ha]
    exact (canonical32039 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2339 + difference 2 3) (sourceB2339 + difference 3 2) sourceC2339) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2963) := by
    have ha : (tripleCharges (sourceA2339 + difference 2 3) (sourceB2339 + difference 3 2) sourceC2339) = raw27576 := by
      apply Matrix.ext; unfold tripleCharges sourceA2339 sourceB2339 sourceC2339 difference raw27576; decide +kernel
    rw [ha]
    exact (canonical27576 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2339 + difference 2 4) (sourceB2339 + difference 4 2) sourceC2339) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2963) := by
    have ha : (tripleCharges (sourceA2339 + difference 2 4) (sourceB2339 + difference 4 2) sourceC2339) = raw32040 := by
      apply Matrix.ext; unfold tripleCharges sourceA2339 sourceB2339 sourceC2339 difference raw32040; decide +kernel
    rw [ha]
    exact (canonical32040 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2339 + difference 2 5) (sourceB2339 + difference 5 2) sourceC2339) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2953) := by
    have ha : (tripleCharges (sourceA2339 + difference 2 5) (sourceB2339 + difference 5 2) sourceC2339) = raw12112 := by
      apply Matrix.ext; unfold tripleCharges sourceA2339 sourceB2339 sourceC2339 difference raw12112; decide +kernel
    rw [ha]
    exact (canonical12112 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2339 + difference 3 0) (sourceB2339 + difference 0 3) sourceC2339) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1138) := by
    have ha : (tripleCharges (sourceA2339 + difference 3 0) (sourceB2339 + difference 0 3) sourceC2339) = raw24119 := by
      apply Matrix.ext; unfold tripleCharges sourceA2339 sourceB2339 sourceC2339 difference raw24119; decide +kernel
    rw [ha]
    exact (canonical24119 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2339 + difference 3 1) (sourceB2339 + difference 1 3) sourceC2339) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2817) := by
    have ha : (tripleCharges (sourceA2339 + difference 3 1) (sourceB2339 + difference 1 3) sourceC2339) = raw32041 := by
      apply Matrix.ext; unfold tripleCharges sourceA2339 sourceB2339 sourceC2339 difference raw32041; decide +kernel
    rw [ha]
    exact (canonical32041 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2339 + difference 3 2) (sourceB2339 + difference 2 3) sourceC2339) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2896) := by
    have ha : (tripleCharges (sourceA2339 + difference 3 2) (sourceB2339 + difference 2 3) sourceC2339) = raw32042 := by
      apply Matrix.ext; unfold tripleCharges sourceA2339 sourceB2339 sourceC2339 difference raw32042; decide +kernel
    rw [ha]
    exact (canonical32042 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2339 + difference 3 4) (sourceB2339 + difference 4 3) sourceC2339) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2968) := by
    have ha : (tripleCharges (sourceA2339 + difference 3 4) (sourceB2339 + difference 4 3) sourceC2339) = raw32043 := by
      apply Matrix.ext; unfold tripleCharges sourceA2339 sourceB2339 sourceC2339 difference raw32043; decide +kernel
    rw [ha]
    exact (canonical32043 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2339 + difference 3 5) (sourceB2339 + difference 5 3) sourceC2339) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2954) := by
    have ha : (tripleCharges (sourceA2339 + difference 3 5) (sourceB2339 + difference 5 3) sourceC2339) = raw12117 := by
      apply Matrix.ext; unfold tripleCharges sourceA2339 sourceB2339 sourceC2339 difference raw12117; decide +kernel
    rw [ha]
    exact (canonical12117 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2339 + difference 4 0) (sourceB2339 + difference 0 4) sourceC2339) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1138) := by
    have ha : (tripleCharges (sourceA2339 + difference 4 0) (sourceB2339 + difference 0 4) sourceC2339) = raw22499 := by
      apply Matrix.ext; unfold tripleCharges sourceA2339 sourceB2339 sourceC2339 difference raw22499; decide +kernel
    rw [ha]
    exact (canonical22499 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2339 + difference 4 1) (sourceB2339 + difference 1 4) sourceC2339) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2817) := by
    have ha : (tripleCharges (sourceA2339 + difference 4 1) (sourceB2339 + difference 1 4) sourceC2339) = raw29522 := by
      apply Matrix.ext; unfold tripleCharges sourceA2339 sourceB2339 sourceC2339 difference raw29522; decide +kernel
    rw [ha]
    exact (canonical29522 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2339 + difference 4 2) (sourceB2339 + difference 2 4) sourceC2339) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2896) := by
    have ha : (tripleCharges (sourceA2339 + difference 4 2) (sourceB2339 + difference 2 4) sourceC2339) = raw29523 := by
      apply Matrix.ext; unfold tripleCharges sourceA2339 sourceB2339 sourceC2339 difference raw29523; decide +kernel
    rw [ha]
    exact (canonical29523 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2339 + difference 4 3) (sourceB2339 + difference 3 4) sourceC2339) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2968) := by
    have ha : (tripleCharges (sourceA2339 + difference 4 3) (sourceB2339 + difference 3 4) sourceC2339) = raw22487 := by
      apply Matrix.ext; unfold tripleCharges sourceA2339 sourceB2339 sourceC2339 difference raw22487; decide +kernel
    rw [ha]
    exact (canonical22487 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2339 + difference 4 5) (sourceB2339 + difference 5 4) sourceC2339) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2954) := by
    have ha : (tripleCharges (sourceA2339 + difference 4 5) (sourceB2339 + difference 5 4) sourceC2339) = raw12122 := by
      apply Matrix.ext; unfold tripleCharges sourceA2339 sourceB2339 sourceC2339 difference raw12122; decide +kernel
    rw [ha]
    exact (canonical12122 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2339 + difference 5 0) (sourceB2339 + difference 0 5) sourceC2339) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1136) := by
    have ha : (tripleCharges (sourceA2339 + difference 5 0) (sourceB2339 + difference 0 5) sourceC2339) = raw20376 := by
      apply Matrix.ext; unfold tripleCharges sourceA2339 sourceB2339 sourceC2339 difference raw20376; decide +kernel
    rw [ha]
    exact (canonical20376 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2339 + difference 5 1) (sourceB2339 + difference 1 5) sourceC2339) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2815) := by
    have ha : (tripleCharges (sourceA2339 + difference 5 1) (sourceB2339 + difference 1 5) sourceC2339) = raw27577 := by
      apply Matrix.ext; unfold tripleCharges sourceA2339 sourceB2339 sourceC2339 difference raw27577; decide +kernel
    rw [ha]
    exact (canonical27577 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2339 + difference 5 2) (sourceB2339 + difference 2 5) sourceC2339) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2894) := by
    have ha : (tripleCharges (sourceA2339 + difference 5 2) (sourceB2339 + difference 2 5) sourceC2339) = raw27578 := by
      apply Matrix.ext; unfold tripleCharges sourceA2339 sourceB2339 sourceC2339 difference raw27578; decide +kernel
    rw [ha]
    exact (canonical27578 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2339 + difference 5 3) (sourceB2339 + difference 3 5) sourceC2339) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2965) := by
    have ha : (tripleCharges (sourceA2339 + difference 5 3) (sourceB2339 + difference 3 5) sourceC2339) = raw20364 := by
      apply Matrix.ext; unfold tripleCharges sourceA2339 sourceB2339 sourceC2339 difference raw20364; decide +kernel
    rw [ha]
    exact (canonical20364 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2339 + difference 5 4) (sourceB2339 + difference 4 5) sourceC2339) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2965) := by
    have ha : (tripleCharges (sourceA2339 + difference 5 4) (sourceB2339 + difference 4 5) sourceC2339) = raw27579 := by
      apply Matrix.ext; unfold tripleCharges sourceA2339 sourceB2339 sourceC2339 difference raw27579; decide +kernel
    rw [ha]
    exact (canonical27579 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2339 sourceB2339 sourceC2339
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2339, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2340 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2340 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC2340 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceForm2340 : Integer.Sparse Master := [(Sum.inr 4341, 1), (Sum.inr 4343, 1), (Sum.inr 4349, 2), (Sum.inr 4457, 1), (Sum.inr 4760, 1), (Sum.inr 4769, 1), (Sum.inr 4804, 2), (Sum.inr 4939, 1), (Sum.inr 4946, 2), (Sum.inr 5036, 2), (Sum.inr 5072, 1), (Sum.inr 5134, 2), (Sum.inr 5141, 2), (Sum.inr 5167, 1), (Sum.inr 5169, 2), (Sum.inr 5258, 2), (Sum.inr 5292, 1), (Sum.inr 5416, 1), (Sum.inr 5418, 1), (Sum.inr 5434, 2), (Sum.inr 5486, 1)]

theorem sourceEq2340 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2340 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2340 + difference 0 1) (sourceB2340 + difference 1 0) sourceC2340) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5418) := by
    have ha : (tripleCharges (sourceA2340 + difference 0 1) (sourceB2340 + difference 1 0) sourceC2340) = raw19026 := by
      apply Matrix.ext; unfold tripleCharges sourceA2340 sourceB2340 sourceC2340 difference raw19026; decide +kernel
    rw [ha]
    exact (canonical19026 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2340 + difference 0 2) (sourceB2340 + difference 2 0) sourceC2340) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5416) := by
    have ha : (tripleCharges (sourceA2340 + difference 0 2) (sourceB2340 + difference 2 0) sourceC2340) = raw19027 := by
      apply Matrix.ext; unfold tripleCharges sourceA2340 sourceB2340 sourceC2340 difference raw19027; decide +kernel
    rw [ha]
    exact (canonical19027 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2340 + difference 0 3) (sourceB2340 + difference 3 0) sourceC2340) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA2340 + difference 0 3) (sourceB2340 + difference 3 0) sourceC2340) = raw10085 := by
      apply Matrix.ext; unfold tripleCharges sourceA2340 sourceB2340 sourceC2340 difference raw10085; decide +kernel
    rw [ha]
    exact (canonical10085 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2340 + difference 0 4) (sourceB2340 + difference 4 0) sourceC2340) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA2340 + difference 0 4) (sourceB2340 + difference 4 0) sourceC2340) = raw19028 := by
      apply Matrix.ext; unfold tripleCharges sourceA2340 sourceB2340 sourceC2340 difference raw19028; decide +kernel
    rw [ha]
    exact (canonical19028 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2340 + difference 0 5) (sourceB2340 + difference 5 0) sourceC2340) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5486) := by
    have ha : (tripleCharges (sourceA2340 + difference 0 5) (sourceB2340 + difference 5 0) sourceC2340) = raw32044 := by
      apply Matrix.ext; unfold tripleCharges sourceA2340 sourceB2340 sourceC2340 difference raw32044; decide +kernel
    rw [ha]
    exact (canonical32044 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2340 + difference 1 0) (sourceB2340 + difference 0 1) sourceC2340) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4457) := by
    have ha : (tripleCharges (sourceA2340 + difference 1 0) (sourceB2340 + difference 0 1) sourceC2340) = raw10100 := by
      apply Matrix.ext; unfold tripleCharges sourceA2340 sourceB2340 sourceC2340 difference raw10100; decide +kernel
    rw [ha]
    exact (canonical10100 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2340 + difference 1 2) (sourceB2340 + difference 2 1) sourceC2340) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5072) := by
    have ha : (tripleCharges (sourceA2340 + difference 1 2) (sourceB2340 + difference 2 1) sourceC2340) = raw10102 := by
      apply Matrix.ext; unfold tripleCharges sourceA2340 sourceB2340 sourceC2340 difference raw10102; decide +kernel
    rw [ha]
    exact (canonical10102 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2340 + difference 1 3) (sourceB2340 + difference 3 1) sourceC2340) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA2340 + difference 1 3) (sourceB2340 + difference 3 1) sourceC2340) = raw25427 := by
      apply Matrix.ext; unfold tripleCharges sourceA2340 sourceB2340 sourceC2340 difference raw25427; decide +kernel
    rw [ha]
    exact (canonical25427 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2340 + difference 1 4) (sourceB2340 + difference 4 1) sourceC2340) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA2340 + difference 1 4) (sourceB2340 + difference 4 1) sourceC2340) = raw10103 := by
      apply Matrix.ext; unfold tripleCharges sourceA2340 sourceB2340 sourceC2340 difference raw10103; decide +kernel
    rw [ha]
    exact (canonical10103 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2340 + difference 1 5) (sourceB2340 + difference 5 1) sourceC2340) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA2340 + difference 1 5) (sourceB2340 + difference 5 1) sourceC2340) = raw10104 := by
      apply Matrix.ext; unfold tripleCharges sourceA2340 sourceB2340 sourceC2340 difference raw10104; decide +kernel
    rw [ha]
    exact (canonical10104 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2340 + difference 2 0) (sourceB2340 + difference 0 2) sourceC2340) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4341) := by
    have ha : (tripleCharges (sourceA2340 + difference 2 0) (sourceB2340 + difference 0 2) sourceC2340) = raw25433 := by
      apply Matrix.ext; unfold tripleCharges sourceA2340 sourceB2340 sourceC2340 difference raw25433; decide +kernel
    rw [ha]
    exact (canonical25433 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2340 + difference 2 1) (sourceB2340 + difference 1 2) sourceC2340) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4939) := by
    have ha : (tripleCharges (sourceA2340 + difference 2 1) (sourceB2340 + difference 1 2) sourceC2340) = raw32045 := by
      apply Matrix.ext; unfold tripleCharges sourceA2340 sourceB2340 sourceC2340 difference raw32045; decide +kernel
    rw [ha]
    exact (canonical32045 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2340 + difference 2 3) (sourceB2340 + difference 3 2) sourceC2340) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5134) := by
    have ha : (tripleCharges (sourceA2340 + difference 2 3) (sourceB2340 + difference 3 2) sourceC2340) = raw10096 := by
      apply Matrix.ext; unfold tripleCharges sourceA2340 sourceB2340 sourceC2340 difference raw10096; decide +kernel
    rw [ha]
    exact (canonical10096 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2340 + difference 2 4) (sourceB2340 + difference 4 2) sourceC2340) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5134) := by
    have ha : (tripleCharges (sourceA2340 + difference 2 4) (sourceB2340 + difference 4 2) sourceC2340) = raw32046 := by
      apply Matrix.ext; unfold tripleCharges sourceA2340 sourceB2340 sourceC2340 difference raw32046; decide +kernel
    rw [ha]
    exact (canonical32046 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2340 + difference 2 5) (sourceB2340 + difference 5 2) sourceC2340) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5167) := by
    have ha : (tripleCharges (sourceA2340 + difference 2 5) (sourceB2340 + difference 5 2) sourceC2340) = raw19011 := by
      apply Matrix.ext; unfold tripleCharges sourceA2340 sourceB2340 sourceC2340 difference raw19011; decide +kernel
    rw [ha]
    exact (canonical19011 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2340 + difference 3 0) (sourceB2340 + difference 0 3) sourceC2340) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4349) := by
    have ha : (tripleCharges (sourceA2340 + difference 3 0) (sourceB2340 + difference 0 3) sourceC2340) = raw25437 := by
      apply Matrix.ext; unfold tripleCharges sourceA2340 sourceB2340 sourceC2340 difference raw25437; decide +kernel
    rw [ha]
    exact (canonical25437 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2340 + difference 3 1) (sourceB2340 + difference 1 3) sourceC2340) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4946) := by
    have ha : (tripleCharges (sourceA2340 + difference 3 1) (sourceB2340 + difference 1 3) sourceC2340) = raw32047 := by
      apply Matrix.ext; unfold tripleCharges sourceA2340 sourceB2340 sourceC2340 difference raw32047; decide +kernel
    rw [ha]
    exact (canonical32047 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2340 + difference 3 2) (sourceB2340 + difference 2 3) sourceC2340) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5036) := by
    have ha : (tripleCharges (sourceA2340 + difference 3 2) (sourceB2340 + difference 2 3) sourceC2340) = raw32048 := by
      apply Matrix.ext; unfold tripleCharges sourceA2340 sourceB2340 sourceC2340 difference raw32048; decide +kernel
    rw [ha]
    exact (canonical32048 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2340 + difference 3 4) (sourceB2340 + difference 4 3) sourceC2340) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA2340 + difference 3 4) (sourceB2340 + difference 4 3) sourceC2340) = raw32049 := by
      apply Matrix.ext; unfold tripleCharges sourceA2340 sourceB2340 sourceC2340 difference raw32049; decide +kernel
    rw [ha]
    exact (canonical32049 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2340 + difference 3 5) (sourceB2340 + difference 5 3) sourceC2340) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA2340 + difference 3 5) (sourceB2340 + difference 5 3) sourceC2340) = raw19016 := by
      apply Matrix.ext; unfold tripleCharges sourceA2340 sourceB2340 sourceC2340 difference raw19016; decide +kernel
    rw [ha]
    exact (canonical19016 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2340 + difference 4 0) (sourceB2340 + difference 0 4) sourceC2340) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4349) := by
    have ha : (tripleCharges (sourceA2340 + difference 4 0) (sourceB2340 + difference 0 4) sourceC2340) = raw25442 := by
      apply Matrix.ext; unfold tripleCharges sourceA2340 sourceB2340 sourceC2340 difference raw25442; decide +kernel
    rw [ha]
    exact (canonical25442 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2340 + difference 4 1) (sourceB2340 + difference 1 4) sourceC2340) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4946) := by
    have ha : (tripleCharges (sourceA2340 + difference 4 1) (sourceB2340 + difference 1 4) sourceC2340) = raw32050 := by
      apply Matrix.ext; unfold tripleCharges sourceA2340 sourceB2340 sourceC2340 difference raw32050; decide +kernel
    rw [ha]
    exact (canonical32050 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2340 + difference 4 2) (sourceB2340 + difference 2 4) sourceC2340) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5036) := by
    have ha : (tripleCharges (sourceA2340 + difference 4 2) (sourceB2340 + difference 2 4) sourceC2340) = raw32051 := by
      apply Matrix.ext; unfold tripleCharges sourceA2340 sourceB2340 sourceC2340 difference raw32051; decide +kernel
    rw [ha]
    exact (canonical32051 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2340 + difference 4 3) (sourceB2340 + difference 3 4) sourceC2340) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA2340 + difference 4 3) (sourceB2340 + difference 3 4) sourceC2340) = raw10106 := by
      apply Matrix.ext; unfold tripleCharges sourceA2340 sourceB2340 sourceC2340 difference raw10106; decide +kernel
    rw [ha]
    exact (canonical10106 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2340 + difference 4 5) (sourceB2340 + difference 5 4) sourceC2340) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA2340 + difference 4 5) (sourceB2340 + difference 5 4) sourceC2340) = raw19021 := by
      apply Matrix.ext; unfold tripleCharges sourceA2340 sourceB2340 sourceC2340 difference raw19021; decide +kernel
    rw [ha]
    exact (canonical19021 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2340 + difference 5 0) (sourceB2340 + difference 0 5) sourceC2340) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4343) := by
    have ha : (tripleCharges (sourceA2340 + difference 5 0) (sourceB2340 + difference 0 5) sourceC2340) = raw25446 := by
      apply Matrix.ext; unfold tripleCharges sourceA2340 sourceB2340 sourceC2340 difference raw25446; decide +kernel
    rw [ha]
    exact (canonical25446 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2340 + difference 5 1) (sourceB2340 + difference 1 5) sourceC2340) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4769) := by
    have ha : (tripleCharges (sourceA2340 + difference 5 1) (sourceB2340 + difference 1 5) sourceC2340) = raw28893 := by
      apply Matrix.ext; unfold tripleCharges sourceA2340 sourceB2340 sourceC2340 difference raw28893; decide +kernel
    rw [ha]
    exact (canonical28893 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2340 + difference 5 2) (sourceB2340 + difference 2 5) sourceC2340) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4760) := by
    have ha : (tripleCharges (sourceA2340 + difference 5 2) (sourceB2340 + difference 2 5) sourceC2340) = raw28894 := by
      apply Matrix.ext; unfold tripleCharges sourceA2340 sourceB2340 sourceC2340 difference raw28894; decide +kernel
    rw [ha]
    exact (canonical28894 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2340 + difference 5 3) (sourceB2340 + difference 3 5) sourceC2340) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA2340 + difference 5 3) (sourceB2340 + difference 3 5) sourceC2340) = raw10111 := by
      apply Matrix.ext; unfold tripleCharges sourceA2340 sourceB2340 sourceC2340 difference raw10111; decide +kernel
    rw [ha]
    exact (canonical10111 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2340 + difference 5 4) (sourceB2340 + difference 4 5) sourceC2340) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA2340 + difference 5 4) (sourceB2340 + difference 4 5) sourceC2340) = raw28895 := by
      apply Matrix.ext; unfold tripleCharges sourceA2340 sourceB2340 sourceC2340 difference raw28895; decide +kernel
    rw [ha]
    exact (canonical28895 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2340 sourceB2340 sourceC2340
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2340, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2341 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2341 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC2341 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceForm2341 : Integer.Sparse Master := [(Sum.inr 919, 1), (Sum.inr 921, 1), (Sum.inr 927, 2), (Sum.inr 1040, 1), (Sum.inr 1960, 1), (Sum.inr 1969, 1), (Sum.inr 2022, 2), (Sum.inr 2330, 1), (Sum.inr 2337, 2), (Sum.inr 2428, 2), (Sum.inr 2479, 1), (Sum.inr 2553, 2), (Sum.inr 2561, 2), (Sum.inr 2593, 1), (Sum.inr 2595, 2), (Sum.inr 2722, 2), (Sum.inr 2766, 1), (Sum.inr 3821, 1), (Sum.inr 3824, 1), (Sum.inr 3852, 2), (Sum.inr 3999, 1)]

theorem sourceEq2341 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2341 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2341 + difference 0 1) (sourceB2341 + difference 1 0) sourceC2341) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3824) := by
    have ha : (tripleCharges (sourceA2341 + difference 0 1) (sourceB2341 + difference 1 0) sourceC2341) = raw32052 := by
      apply Matrix.ext; unfold tripleCharges sourceA2341 sourceB2341 sourceC2341 difference raw32052; decide +kernel
    rw [ha]
    exact (canonical32052 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2341 + difference 0 2) (sourceB2341 + difference 2 0) sourceC2341) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3821) := by
    have ha : (tripleCharges (sourceA2341 + difference 0 2) (sourceB2341 + difference 2 0) sourceC2341) = raw32053 := by
      apply Matrix.ext; unfold tripleCharges sourceA2341 sourceB2341 sourceC2341 difference raw32053; decide +kernel
    rw [ha]
    exact (canonical32053 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2341 + difference 0 3) (sourceB2341 + difference 3 0) sourceC2341) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3852) := by
    have ha : (tripleCharges (sourceA2341 + difference 0 3) (sourceB2341 + difference 3 0) sourceC2341) = raw10115 := by
      apply Matrix.ext; unfold tripleCharges sourceA2341 sourceB2341 sourceC2341 difference raw10115; decide +kernel
    rw [ha]
    exact (canonical10115 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2341 + difference 0 4) (sourceB2341 + difference 4 0) sourceC2341) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3852) := by
    have ha : (tripleCharges (sourceA2341 + difference 0 4) (sourceB2341 + difference 4 0) sourceC2341) = raw32054 := by
      apply Matrix.ext; unfold tripleCharges sourceA2341 sourceB2341 sourceC2341 difference raw32054; decide +kernel
    rw [ha]
    exact (canonical32054 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2341 + difference 0 5) (sourceB2341 + difference 5 0) sourceC2341) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3999) := by
    have ha : (tripleCharges (sourceA2341 + difference 0 5) (sourceB2341 + difference 5 0) sourceC2341) = raw32055 := by
      apply Matrix.ext; unfold tripleCharges sourceA2341 sourceB2341 sourceC2341 difference raw32055; decide +kernel
    rw [ha]
    exact (canonical32055 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2341 + difference 1 0) (sourceB2341 + difference 0 1) sourceC2341) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1040) := by
    have ha : (tripleCharges (sourceA2341 + difference 1 0) (sourceB2341 + difference 0 1) sourceC2341) = raw10130 := by
      apply Matrix.ext; unfold tripleCharges sourceA2341 sourceB2341 sourceC2341 difference raw10130; decide +kernel
    rw [ha]
    exact (canonical10130 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2341 + difference 1 2) (sourceB2341 + difference 2 1) sourceC2341) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2479) := by
    have ha : (tripleCharges (sourceA2341 + difference 1 2) (sourceB2341 + difference 2 1) sourceC2341) = raw10132 := by
      apply Matrix.ext; unfold tripleCharges sourceA2341 sourceB2341 sourceC2341 difference raw10132; decide +kernel
    rw [ha]
    exact (canonical10132 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2341 + difference 1 3) (sourceB2341 + difference 3 1) sourceC2341) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA2341 + difference 1 3) (sourceB2341 + difference 3 1) sourceC2341) = raw25449 := by
      apply Matrix.ext; unfold tripleCharges sourceA2341 sourceB2341 sourceC2341 difference raw25449; decide +kernel
    rw [ha]
    exact (canonical25449 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2341 + difference 1 4) (sourceB2341 + difference 4 1) sourceC2341) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA2341 + difference 1 4) (sourceB2341 + difference 4 1) sourceC2341) = raw10133 := by
      apply Matrix.ext; unfold tripleCharges sourceA2341 sourceB2341 sourceC2341 difference raw10133; decide +kernel
    rw [ha]
    exact (canonical10133 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2341 + difference 1 5) (sourceB2341 + difference 5 1) sourceC2341) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2766) := by
    have ha : (tripleCharges (sourceA2341 + difference 1 5) (sourceB2341 + difference 5 1) sourceC2341) = raw10134 := by
      apply Matrix.ext; unfold tripleCharges sourceA2341 sourceB2341 sourceC2341 difference raw10134; decide +kernel
    rw [ha]
    exact (canonical10134 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2341 + difference 2 0) (sourceB2341 + difference 0 2) sourceC2341) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 919) := by
    have ha : (tripleCharges (sourceA2341 + difference 2 0) (sourceB2341 + difference 0 2) sourceC2341) = raw25455 := by
      apply Matrix.ext; unfold tripleCharges sourceA2341 sourceB2341 sourceC2341 difference raw25455; decide +kernel
    rw [ha]
    exact (canonical25455 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2341 + difference 2 1) (sourceB2341 + difference 1 2) sourceC2341) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2330) := by
    have ha : (tripleCharges (sourceA2341 + difference 2 1) (sourceB2341 + difference 1 2) sourceC2341) = raw32056 := by
      apply Matrix.ext; unfold tripleCharges sourceA2341 sourceB2341 sourceC2341 difference raw32056; decide +kernel
    rw [ha]
    exact (canonical32056 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2341 + difference 2 3) (sourceB2341 + difference 3 2) sourceC2341) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2553) := by
    have ha : (tripleCharges (sourceA2341 + difference 2 3) (sourceB2341 + difference 3 2) sourceC2341) = raw10126 := by
      apply Matrix.ext; unfold tripleCharges sourceA2341 sourceB2341 sourceC2341 difference raw10126; decide +kernel
    rw [ha]
    exact (canonical10126 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2341 + difference 2 4) (sourceB2341 + difference 4 2) sourceC2341) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2553) := by
    have ha : (tripleCharges (sourceA2341 + difference 2 4) (sourceB2341 + difference 4 2) sourceC2341) = raw32057 := by
      apply Matrix.ext; unfold tripleCharges sourceA2341 sourceB2341 sourceC2341 difference raw32057; decide +kernel
    rw [ha]
    exact (canonical32057 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2341 + difference 2 5) (sourceB2341 + difference 5 2) sourceC2341) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2593) := by
    have ha : (tripleCharges (sourceA2341 + difference 2 5) (sourceB2341 + difference 5 2) sourceC2341) = raw32058 := by
      apply Matrix.ext; unfold tripleCharges sourceA2341 sourceB2341 sourceC2341 difference raw32058; decide +kernel
    rw [ha]
    exact (canonical32058 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2341 + difference 3 0) (sourceB2341 + difference 0 3) sourceC2341) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 927) := by
    have ha : (tripleCharges (sourceA2341 + difference 3 0) (sourceB2341 + difference 0 3) sourceC2341) = raw25459 := by
      apply Matrix.ext; unfold tripleCharges sourceA2341 sourceB2341 sourceC2341 difference raw25459; decide +kernel
    rw [ha]
    exact (canonical25459 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2341 + difference 3 1) (sourceB2341 + difference 1 3) sourceC2341) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2337) := by
    have ha : (tripleCharges (sourceA2341 + difference 3 1) (sourceB2341 + difference 1 3) sourceC2341) = raw32059 := by
      apply Matrix.ext; unfold tripleCharges sourceA2341 sourceB2341 sourceC2341 difference raw32059; decide +kernel
    rw [ha]
    exact (canonical32059 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2341 + difference 3 2) (sourceB2341 + difference 2 3) sourceC2341) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2428) := by
    have ha : (tripleCharges (sourceA2341 + difference 3 2) (sourceB2341 + difference 2 3) sourceC2341) = raw32060 := by
      apply Matrix.ext; unfold tripleCharges sourceA2341 sourceB2341 sourceC2341 difference raw32060; decide +kernel
    rw [ha]
    exact (canonical32060 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2341 + difference 3 4) (sourceB2341 + difference 4 3) sourceC2341) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2561) := by
    have ha : (tripleCharges (sourceA2341 + difference 3 4) (sourceB2341 + difference 4 3) sourceC2341) = raw32061 := by
      apply Matrix.ext; unfold tripleCharges sourceA2341 sourceB2341 sourceC2341 difference raw32061; decide +kernel
    rw [ha]
    exact (canonical32061 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2341 + difference 3 5) (sourceB2341 + difference 5 3) sourceC2341) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2595) := by
    have ha : (tripleCharges (sourceA2341 + difference 3 5) (sourceB2341 + difference 5 3) sourceC2341) = raw32062 := by
      apply Matrix.ext; unfold tripleCharges sourceA2341 sourceB2341 sourceC2341 difference raw32062; decide +kernel
    rw [ha]
    exact (canonical32062 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2341 + difference 4 0) (sourceB2341 + difference 0 4) sourceC2341) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 927) := by
    have ha : (tripleCharges (sourceA2341 + difference 4 0) (sourceB2341 + difference 0 4) sourceC2341) = raw25464 := by
      apply Matrix.ext; unfold tripleCharges sourceA2341 sourceB2341 sourceC2341 difference raw25464; decide +kernel
    rw [ha]
    exact (canonical25464 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2341 + difference 4 1) (sourceB2341 + difference 1 4) sourceC2341) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2337) := by
    have ha : (tripleCharges (sourceA2341 + difference 4 1) (sourceB2341 + difference 1 4) sourceC2341) = raw32063 := by
      apply Matrix.ext; unfold tripleCharges sourceA2341 sourceB2341 sourceC2341 difference raw32063; decide +kernel
    rw [ha]
    exact (canonical32063 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2341 + difference 4 2) (sourceB2341 + difference 2 4) sourceC2341) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2428) := by
    have ha : (tripleCharges (sourceA2341 + difference 4 2) (sourceB2341 + difference 2 4) sourceC2341) = raw32064 := by
      apply Matrix.ext; unfold tripleCharges sourceA2341 sourceB2341 sourceC2341 difference raw32064; decide +kernel
    rw [ha]
    exact (canonical32064 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2341 + difference 4 3) (sourceB2341 + difference 3 4) sourceC2341) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2561) := by
    have ha : (tripleCharges (sourceA2341 + difference 4 3) (sourceB2341 + difference 3 4) sourceC2341) = raw10136 := by
      apply Matrix.ext; unfold tripleCharges sourceA2341 sourceB2341 sourceC2341 difference raw10136; decide +kernel
    rw [ha]
    exact (canonical10136 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2341 + difference 4 5) (sourceB2341 + difference 5 4) sourceC2341) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2595) := by
    have ha : (tripleCharges (sourceA2341 + difference 4 5) (sourceB2341 + difference 5 4) sourceC2341) = raw32065 := by
      apply Matrix.ext; unfold tripleCharges sourceA2341 sourceB2341 sourceC2341 difference raw32065; decide +kernel
    rw [ha]
    exact (canonical32065 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2341 + difference 5 0) (sourceB2341 + difference 0 5) sourceC2341) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 921) := by
    have ha : (tripleCharges (sourceA2341 + difference 5 0) (sourceB2341 + difference 0 5) sourceC2341) = raw25468 := by
      apply Matrix.ext; unfold tripleCharges sourceA2341 sourceB2341 sourceC2341 difference raw25468; decide +kernel
    rw [ha]
    exact (canonical25468 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2341 + difference 5 1) (sourceB2341 + difference 1 5) sourceC2341) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1969) := by
    have ha : (tripleCharges (sourceA2341 + difference 5 1) (sourceB2341 + difference 1 5) sourceC2341) = raw28913 := by
      apply Matrix.ext; unfold tripleCharges sourceA2341 sourceB2341 sourceC2341 difference raw28913; decide +kernel
    rw [ha]
    exact (canonical28913 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2341 + difference 5 2) (sourceB2341 + difference 2 5) sourceC2341) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1960) := by
    have ha : (tripleCharges (sourceA2341 + difference 5 2) (sourceB2341 + difference 2 5) sourceC2341) = raw28914 := by
      apply Matrix.ext; unfold tripleCharges sourceA2341 sourceB2341 sourceC2341 difference raw28914; decide +kernel
    rw [ha]
    exact (canonical28914 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2341 + difference 5 3) (sourceB2341 + difference 3 5) sourceC2341) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2022) := by
    have ha : (tripleCharges (sourceA2341 + difference 5 3) (sourceB2341 + difference 3 5) sourceC2341) = raw10141 := by
      apply Matrix.ext; unfold tripleCharges sourceA2341 sourceB2341 sourceC2341 difference raw10141; decide +kernel
    rw [ha]
    exact (canonical10141 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2341 + difference 5 4) (sourceB2341 + difference 4 5) sourceC2341) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2022) := by
    have ha : (tripleCharges (sourceA2341 + difference 5 4) (sourceB2341 + difference 4 5) sourceC2341) = raw28915 := by
      apply Matrix.ext; unfold tripleCharges sourceA2341 sourceB2341 sourceC2341 difference raw28915; decide +kernel
    rw [ha]
    exact (canonical28915 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2341 sourceB2341 sourceC2341
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2341, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2342 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2342 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC2342 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceForm2342 : Integer.Sparse Master := [(Sum.inr 4544, 1), (Sum.inr 4546, 1), (Sum.inr 4549, 1), (Sum.inr 4554, 1), (Sum.inr 4624, 1), (Sum.inr 4968, 1), (Sum.inr 4972, 1), (Sum.inr 4974, 1), (Sum.inr 4977, 1), (Sum.inr 5037, 1), (Sum.inr 5078, 1), (Sum.inr 5115, 1), (Sum.inr 5117, 1), (Sum.inr 5148, 1), (Sum.inr 5152, 1), (Sum.inr 5167, 1), (Sum.inr 5169, 3), (Sum.inr 5172, 1), (Sum.inr 5174, 1), (Sum.inr 5177, 1), (Sum.inr 5293, 1), (Sum.inr 5307, 1), (Sum.inr 5309, 1), (Sum.inr 5388, 1), (Sum.inr 5416, 1), (Sum.inr 5434, 1), (Sum.inr 5440, 1), (Sum.inr 5442, 1)]

theorem sourceEq2342 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2342 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2342 + difference 0 1) (sourceB2342 + difference 1 0) sourceC2342) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5388) := by
    have ha : (tripleCharges (sourceA2342 + difference 0 1) (sourceB2342 + difference 1 0) sourceC2342) = raw32066 := by
      apply Matrix.ext; unfold tripleCharges sourceA2342 sourceB2342 sourceC2342 difference raw32066; decide +kernel
    rw [ha]
    exact (canonical32066 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2342 + difference 0 2) (sourceB2342 + difference 2 0) sourceC2342) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5416) := by
    have ha : (tripleCharges (sourceA2342 + difference 0 2) (sourceB2342 + difference 2 0) sourceC2342) = raw32067 := by
      apply Matrix.ext; unfold tripleCharges sourceA2342 sourceB2342 sourceC2342 difference raw32067; decide +kernel
    rw [ha]
    exact (canonical32067 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2342 + difference 0 3) (sourceB2342 + difference 3 0) sourceC2342) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5442) := by
    have ha : (tripleCharges (sourceA2342 + difference 0 3) (sourceB2342 + difference 3 0) sourceC2342) = raw10194 := by
      apply Matrix.ext; unfold tripleCharges sourceA2342 sourceB2342 sourceC2342 difference raw10194; decide +kernel
    rw [ha]
    exact (canonical10194 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2342 + difference 0 4) (sourceB2342 + difference 4 0) sourceC2342) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA2342 + difference 0 4) (sourceB2342 + difference 4 0) sourceC2342) = raw32068 := by
      apply Matrix.ext; unfold tripleCharges sourceA2342 sourceB2342 sourceC2342 difference raw32068; decide +kernel
    rw [ha]
    exact (canonical32068 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2342 + difference 0 5) (sourceB2342 + difference 5 0) sourceC2342) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5440) := by
    have ha : (tripleCharges (sourceA2342 + difference 0 5) (sourceB2342 + difference 5 0) sourceC2342) = raw32069 := by
      apply Matrix.ext; unfold tripleCharges sourceA2342 sourceB2342 sourceC2342 difference raw32069; decide +kernel
    rw [ha]
    exact (canonical32069 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2342 + difference 1 0) (sourceB2342 + difference 0 1) sourceC2342) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4624) := by
    have ha : (tripleCharges (sourceA2342 + difference 1 0) (sourceB2342 + difference 0 1) sourceC2342) = raw10206 := by
      apply Matrix.ext; unfold tripleCharges sourceA2342 sourceB2342 sourceC2342 difference raw10206; decide +kernel
    rw [ha]
    exact (canonical10206 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2342 + difference 1 2) (sourceB2342 + difference 2 1) sourceC2342) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA2342 + difference 1 2) (sourceB2342 + difference 2 1) sourceC2342) = raw10208 := by
      apply Matrix.ext; unfold tripleCharges sourceA2342 sourceB2342 sourceC2342 difference raw10208; decide +kernel
    rw [ha]
    exact (canonical10208 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2342 + difference 1 3) (sourceB2342 + difference 3 1) sourceC2342) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5309) := by
    have ha : (tripleCharges (sourceA2342 + difference 1 3) (sourceB2342 + difference 3 1) sourceC2342) = raw4306 := by
      apply Matrix.ext; unfold tripleCharges sourceA2342 sourceB2342 sourceC2342 difference raw4306; decide +kernel
    rw [ha]
    exact (canonical4306 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2342 + difference 1 4) (sourceB2342 + difference 4 1) sourceC2342) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA2342 + difference 1 4) (sourceB2342 + difference 4 1) sourceC2342) = raw4301 := by
      apply Matrix.ext; unfold tripleCharges sourceA2342 sourceB2342 sourceC2342 difference raw4301; decide +kernel
    rw [ha]
    exact (canonical4301 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2342 + difference 1 5) (sourceB2342 + difference 5 1) sourceC2342) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5307) := by
    have ha : (tripleCharges (sourceA2342 + difference 1 5) (sourceB2342 + difference 5 1) sourceC2342) = raw10209 := by
      apply Matrix.ext; unfold tripleCharges sourceA2342 sourceB2342 sourceC2342 difference raw10209; decide +kernel
    rw [ha]
    exact (canonical10209 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2342 + difference 2 0) (sourceB2342 + difference 0 2) sourceC2342) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4544) := by
    have ha : (tripleCharges (sourceA2342 + difference 2 0) (sourceB2342 + difference 0 2) sourceC2342) = raw24224 := by
      apply Matrix.ext; unfold tripleCharges sourceA2342 sourceB2342 sourceC2342 difference raw24224; decide +kernel
    rw [ha]
    exact (canonical24224 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2342 + difference 2 1) (sourceB2342 + difference 1 2) sourceC2342) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4968) := by
    have ha : (tripleCharges (sourceA2342 + difference 2 1) (sourceB2342 + difference 1 2) sourceC2342) = raw32070 := by
      apply Matrix.ext; unfold tripleCharges sourceA2342 sourceB2342 sourceC2342 difference raw32070; decide +kernel
    rw [ha]
    exact (canonical32070 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2342 + difference 2 3) (sourceB2342 + difference 3 2) sourceC2342) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA2342 + difference 2 3) (sourceB2342 + difference 3 2) sourceC2342) = raw10203 := by
      apply Matrix.ext; unfold tripleCharges sourceA2342 sourceB2342 sourceC2342 difference raw10203; decide +kernel
    rw [ha]
    exact (canonical10203 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2342 + difference 2 4) (sourceB2342 + difference 4 2) sourceC2342) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5148) := by
    have ha : (tripleCharges (sourceA2342 + difference 2 4) (sourceB2342 + difference 4 2) sourceC2342) = raw32071 := by
      apply Matrix.ext; unfold tripleCharges sourceA2342 sourceB2342 sourceC2342 difference raw32071; decide +kernel
    rw [ha]
    exact (canonical32071 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2342 + difference 2 5) (sourceB2342 + difference 5 2) sourceC2342) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5167) := by
    have ha : (tripleCharges (sourceA2342 + difference 2 5) (sourceB2342 + difference 5 2) sourceC2342) = raw26640 := by
      apply Matrix.ext; unfold tripleCharges sourceA2342 sourceB2342 sourceC2342 difference raw26640; decide +kernel
    rw [ha]
    exact (canonical26640 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2342 + difference 3 0) (sourceB2342 + difference 0 3) sourceC2342) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4549) := by
    have ha : (tripleCharges (sourceA2342 + difference 3 0) (sourceB2342 + difference 0 3) sourceC2342) = raw24228 := by
      apply Matrix.ext; unfold tripleCharges sourceA2342 sourceB2342 sourceC2342 difference raw24228; decide +kernel
    rw [ha]
    exact (canonical24228 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2342 + difference 3 1) (sourceB2342 + difference 1 3) sourceC2342) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4977) := by
    have ha : (tripleCharges (sourceA2342 + difference 3 1) (sourceB2342 + difference 1 3) sourceC2342) = raw32072 := by
      apply Matrix.ext; unfold tripleCharges sourceA2342 sourceB2342 sourceC2342 difference raw32072; decide +kernel
    rw [ha]
    exact (canonical32072 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2342 + difference 3 2) (sourceB2342 + difference 2 3) sourceC2342) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5117) := by
    have ha : (tripleCharges (sourceA2342 + difference 3 2) (sourceB2342 + difference 2 3) sourceC2342) = raw32073 := by
      apply Matrix.ext; unfold tripleCharges sourceA2342 sourceB2342 sourceC2342 difference raw32073; decide +kernel
    rw [ha]
    exact (canonical32073 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2342 + difference 3 4) (sourceB2342 + difference 4 3) sourceC2342) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5152) := by
    have ha : (tripleCharges (sourceA2342 + difference 3 4) (sourceB2342 + difference 4 3) sourceC2342) = raw32074 := by
      apply Matrix.ext; unfold tripleCharges sourceA2342 sourceB2342 sourceC2342 difference raw32074; decide +kernel
    rw [ha]
    exact (canonical32074 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2342 + difference 3 5) (sourceB2342 + difference 5 3) sourceC2342) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5172) := by
    have ha : (tripleCharges (sourceA2342 + difference 3 5) (sourceB2342 + difference 5 3) sourceC2342) = raw32075 := by
      apply Matrix.ext; unfold tripleCharges sourceA2342 sourceB2342 sourceC2342 difference raw32075; decide +kernel
    rw [ha]
    exact (canonical32075 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2342 + difference 4 0) (sourceB2342 + difference 0 4) sourceC2342) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4554) := by
    have ha : (tripleCharges (sourceA2342 + difference 4 0) (sourceB2342 + difference 0 4) sourceC2342) = raw22578 := by
      apply Matrix.ext; unfold tripleCharges sourceA2342 sourceB2342 sourceC2342 difference raw22578; decide +kernel
    rw [ha]
    exact (canonical22578 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2342 + difference 4 1) (sourceB2342 + difference 1 4) sourceC2342) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4974) := by
    have ha : (tripleCharges (sourceA2342 + difference 4 1) (sourceB2342 + difference 1 4) sourceC2342) = raw29629 := by
      apply Matrix.ext; unfold tripleCharges sourceA2342 sourceB2342 sourceC2342 difference raw29629; decide +kernel
    rw [ha]
    exact (canonical29629 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2342 + difference 4 2) (sourceB2342 + difference 2 4) sourceC2342) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5115) := by
    have ha : (tripleCharges (sourceA2342 + difference 4 2) (sourceB2342 + difference 2 4) sourceC2342) = raw29630 := by
      apply Matrix.ext; unfold tripleCharges sourceA2342 sourceB2342 sourceC2342 difference raw29630; decide +kernel
    rw [ha]
    exact (canonical29630 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2342 + difference 4 3) (sourceB2342 + difference 3 4) sourceC2342) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5177) := by
    have ha : (tripleCharges (sourceA2342 + difference 4 3) (sourceB2342 + difference 3 4) sourceC2342) = raw10211 := by
      apply Matrix.ext; unfold tripleCharges sourceA2342 sourceB2342 sourceC2342 difference raw10211; decide +kernel
    rw [ha]
    exact (canonical10211 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2342 + difference 4 5) (sourceB2342 + difference 5 4) sourceC2342) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA2342 + difference 4 5) (sourceB2342 + difference 5 4) sourceC2342) = raw29631 := by
      apply Matrix.ext; unfold tripleCharges sourceA2342 sourceB2342 sourceC2342 difference raw29631; decide +kernel
    rw [ha]
    exact (canonical29631 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2342 + difference 5 0) (sourceB2342 + difference 0 5) sourceC2342) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4546) := by
    have ha : (tripleCharges (sourceA2342 + difference 5 0) (sourceB2342 + difference 0 5) sourceC2342) = raw20391 := by
      apply Matrix.ext; unfold tripleCharges sourceA2342 sourceB2342 sourceC2342 difference raw20391; decide +kernel
    rw [ha]
    exact (canonical20391 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2342 + difference 5 1) (sourceB2342 + difference 1 5) sourceC2342) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4972) := by
    have ha : (tripleCharges (sourceA2342 + difference 5 1) (sourceB2342 + difference 1 5) sourceC2342) = raw27615 := by
      apply Matrix.ext; unfold tripleCharges sourceA2342 sourceB2342 sourceC2342 difference raw27615; decide +kernel
    rw [ha]
    exact (canonical27615 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2342 + difference 5 2) (sourceB2342 + difference 2 5) sourceC2342) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5037) := by
    have ha : (tripleCharges (sourceA2342 + difference 5 2) (sourceB2342 + difference 2 5) sourceC2342) = raw27616 := by
      apply Matrix.ext; unfold tripleCharges sourceA2342 sourceB2342 sourceC2342 difference raw27616; decide +kernel
    rw [ha]
    exact (canonical27616 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2342 + difference 5 3) (sourceB2342 + difference 3 5) sourceC2342) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5174) := by
    have ha : (tripleCharges (sourceA2342 + difference 5 3) (sourceB2342 + difference 3 5) sourceC2342) = raw4303 := by
      apply Matrix.ext; unfold tripleCharges sourceA2342 sourceB2342 sourceC2342 difference raw4303; decide +kernel
    rw [ha]
    exact (canonical4303 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2342 + difference 5 4) (sourceB2342 + difference 4 5) sourceC2342) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5078) := by
    have ha : (tripleCharges (sourceA2342 + difference 5 4) (sourceB2342 + difference 4 5) sourceC2342) = raw4298 := by
      apply Matrix.ext; unfold tripleCharges sourceA2342 sourceB2342 sourceC2342 difference raw4298; decide +kernel
    rw [ha]
    exact (canonical4298 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2342 sourceB2342 sourceC2342
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2342, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2343 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2343 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC2343 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceForm2343 : Integer.Sparse Master := [(Sum.inr 1129, 1), (Sum.inr 1131, 1), (Sum.inr 1134, 1), (Sum.inr 1139, 1), (Sum.inr 1301, 1), (Sum.inr 2429, 1), (Sum.inr 2434, 1), (Sum.inr 2485, 1), (Sum.inr 2601, 1), (Sum.inr 2809, 1), (Sum.inr 2813, 1), (Sum.inr 2818, 1), (Sum.inr 2893, 1), (Sum.inr 2897, 1), (Sum.inr 2927, 1), (Sum.inr 2931, 1), (Sum.inr 2958, 1), (Sum.inr 2959, 1), (Sum.inr 2960, 3), (Sum.inr 2969, 1), (Sum.inr 3102, 1), (Sum.inr 3122, 1), (Sum.inr 3123, 1), (Sum.inr 3737, 1), (Sum.inr 3967, 1), (Sum.inr 3982, 1), (Sum.inr 4001, 1), (Sum.inr 4036, 1)]

theorem sourceEq2343 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2343 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2343 + difference 0 1) (sourceB2343 + difference 1 0) sourceC2343) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3737) := by
    have ha : (tripleCharges (sourceA2343 + difference 0 1) (sourceB2343 + difference 1 0) sourceC2343) = raw32076 := by
      apply Matrix.ext; unfold tripleCharges sourceA2343 sourceB2343 sourceC2343 difference raw32076; decide +kernel
    rw [ha]
    exact (canonical32076 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2343 + difference 0 2) (sourceB2343 + difference 2 0) sourceC2343) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3967) := by
    have ha : (tripleCharges (sourceA2343 + difference 0 2) (sourceB2343 + difference 2 0) sourceC2343) = raw32077 := by
      apply Matrix.ext; unfold tripleCharges sourceA2343 sourceB2343 sourceC2343 difference raw32077; decide +kernel
    rw [ha]
    exact (canonical32077 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2343 + difference 0 3) (sourceB2343 + difference 3 0) sourceC2343) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4001) := by
    have ha : (tripleCharges (sourceA2343 + difference 0 3) (sourceB2343 + difference 3 0) sourceC2343) = raw27626 := by
      apply Matrix.ext; unfold tripleCharges sourceA2343 sourceB2343 sourceC2343 difference raw27626; decide +kernel
    rw [ha]
    exact (canonical27626 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2343 + difference 0 4) (sourceB2343 + difference 4 0) sourceC2343) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3982) := by
    have ha : (tripleCharges (sourceA2343 + difference 0 4) (sourceB2343 + difference 4 0) sourceC2343) = raw32078 := by
      apply Matrix.ext; unfold tripleCharges sourceA2343 sourceB2343 sourceC2343 difference raw32078; decide +kernel
    rw [ha]
    exact (canonical32078 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2343 + difference 0 5) (sourceB2343 + difference 5 0) sourceC2343) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4036) := by
    have ha : (tripleCharges (sourceA2343 + difference 0 5) (sourceB2343 + difference 5 0) sourceC2343) = raw32079 := by
      apply Matrix.ext; unfold tripleCharges sourceA2343 sourceB2343 sourceC2343 difference raw32079; decide +kernel
    rw [ha]
    exact (canonical32079 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2343 + difference 1 0) (sourceB2343 + difference 0 1) sourceC2343) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1301) := by
    have ha : (tripleCharges (sourceA2343 + difference 1 0) (sourceB2343 + difference 0 1) sourceC2343) = raw20408 := by
      apply Matrix.ext; unfold tripleCharges sourceA2343 sourceB2343 sourceC2343 difference raw20408; decide +kernel
    rw [ha]
    exact (canonical20408 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2343 + difference 1 2) (sourceB2343 + difference 2 1) sourceC2343) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2960) := by
    have ha : (tripleCharges (sourceA2343 + difference 1 2) (sourceB2343 + difference 2 1) sourceC2343) = raw24233 := by
      apply Matrix.ext; unfold tripleCharges sourceA2343 sourceB2343 sourceC2343 difference raw24233; decide +kernel
    rw [ha]
    exact (canonical24233 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2343 + difference 1 3) (sourceB2343 + difference 3 1) sourceC2343) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3123) := by
    have ha : (tripleCharges (sourceA2343 + difference 1 3) (sourceB2343 + difference 3 1) sourceC2343) = raw4336 := by
      apply Matrix.ext; unfold tripleCharges sourceA2343 sourceB2343 sourceC2343 difference raw4336; decide +kernel
    rw [ha]
    exact (canonical4336 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2343 + difference 1 4) (sourceB2343 + difference 4 1) sourceC2343) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3102) := by
    have ha : (tripleCharges (sourceA2343 + difference 1 4) (sourceB2343 + difference 4 1) sourceC2343) = raw4331 := by
      apply Matrix.ext; unfold tripleCharges sourceA2343 sourceB2343 sourceC2343 difference raw4331; decide +kernel
    rw [ha]
    exact (canonical4331 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2343 + difference 1 5) (sourceB2343 + difference 5 1) sourceC2343) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3122) := by
    have ha : (tripleCharges (sourceA2343 + difference 1 5) (sourceB2343 + difference 5 1) sourceC2343) = raw24234 := by
      apply Matrix.ext; unfold tripleCharges sourceA2343 sourceB2343 sourceC2343 difference raw24234; decide +kernel
    rw [ha]
    exact (canonical24234 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2343 + difference 2 0) (sourceB2343 + difference 0 2) sourceC2343) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1129) := by
    have ha : (tripleCharges (sourceA2343 + difference 2 0) (sourceB2343 + difference 0 2) sourceC2343) = raw24240 := by
      apply Matrix.ext; unfold tripleCharges sourceA2343 sourceB2343 sourceC2343 difference raw24240; decide +kernel
    rw [ha]
    exact (canonical24240 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2343 + difference 2 1) (sourceB2343 + difference 1 2) sourceC2343) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2809) := by
    have ha : (tripleCharges (sourceA2343 + difference 2 1) (sourceB2343 + difference 1 2) sourceC2343) = raw32080 := by
      apply Matrix.ext; unfold tripleCharges sourceA2343 sourceB2343 sourceC2343 difference raw32080; decide +kernel
    rw [ha]
    exact (canonical32080 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2343 + difference 2 3) (sourceB2343 + difference 3 2) sourceC2343) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2960) := by
    have ha : (tripleCharges (sourceA2343 + difference 2 3) (sourceB2343 + difference 3 2) sourceC2343) = raw27629 := by
      apply Matrix.ext; unfold tripleCharges sourceA2343 sourceB2343 sourceC2343 difference raw27629; decide +kernel
    rw [ha]
    exact (canonical27629 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2343 + difference 2 4) (sourceB2343 + difference 4 2) sourceC2343) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2927) := by
    have ha : (tripleCharges (sourceA2343 + difference 2 4) (sourceB2343 + difference 4 2) sourceC2343) = raw32081 := by
      apply Matrix.ext; unfold tripleCharges sourceA2343 sourceB2343 sourceC2343 difference raw32081; decide +kernel
    rw [ha]
    exact (canonical32081 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2343 + difference 2 5) (sourceB2343 + difference 5 2) sourceC2343) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2958) := by
    have ha : (tripleCharges (sourceA2343 + difference 2 5) (sourceB2343 + difference 5 2) sourceC2343) = raw26659 := by
      apply Matrix.ext; unfold tripleCharges sourceA2343 sourceB2343 sourceC2343 difference raw26659; decide +kernel
    rw [ha]
    exact (canonical26659 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2343 + difference 3 0) (sourceB2343 + difference 0 3) sourceC2343) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1134) := by
    have ha : (tripleCharges (sourceA2343 + difference 3 0) (sourceB2343 + difference 0 3) sourceC2343) = raw24244 := by
      apply Matrix.ext; unfold tripleCharges sourceA2343 sourceB2343 sourceC2343 difference raw24244; decide +kernel
    rw [ha]
    exact (canonical24244 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2343 + difference 3 1) (sourceB2343 + difference 1 3) sourceC2343) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2813) := by
    have ha : (tripleCharges (sourceA2343 + difference 3 1) (sourceB2343 + difference 1 3) sourceC2343) = raw32082 := by
      apply Matrix.ext; unfold tripleCharges sourceA2343 sourceB2343 sourceC2343 difference raw32082; decide +kernel
    rw [ha]
    exact (canonical32082 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2343 + difference 3 2) (sourceB2343 + difference 2 3) sourceC2343) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2893) := by
    have ha : (tripleCharges (sourceA2343 + difference 3 2) (sourceB2343 + difference 2 3) sourceC2343) = raw32083 := by
      apply Matrix.ext; unfold tripleCharges sourceA2343 sourceB2343 sourceC2343 difference raw32083; decide +kernel
    rw [ha]
    exact (canonical32083 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2343 + difference 3 4) (sourceB2343 + difference 4 3) sourceC2343) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2931) := by
    have ha : (tripleCharges (sourceA2343 + difference 3 4) (sourceB2343 + difference 4 3) sourceC2343) = raw32084 := by
      apply Matrix.ext; unfold tripleCharges sourceA2343 sourceB2343 sourceC2343 difference raw32084; decide +kernel
    rw [ha]
    exact (canonical32084 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2343 + difference 3 5) (sourceB2343 + difference 5 3) sourceC2343) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2959) := by
    have ha : (tripleCharges (sourceA2343 + difference 3 5) (sourceB2343 + difference 5 3) sourceC2343) = raw32085 := by
      apply Matrix.ext; unfold tripleCharges sourceA2343 sourceB2343 sourceC2343 difference raw32085; decide +kernel
    rw [ha]
    exact (canonical32085 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2343 + difference 4 0) (sourceB2343 + difference 0 4) sourceC2343) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1139) := by
    have ha : (tripleCharges (sourceA2343 + difference 4 0) (sourceB2343 + difference 0 4) sourceC2343) = raw22599 := by
      apply Matrix.ext; unfold tripleCharges sourceA2343 sourceB2343 sourceC2343 difference raw22599; decide +kernel
    rw [ha]
    exact (canonical22599 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2343 + difference 4 1) (sourceB2343 + difference 1 4) sourceC2343) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2818) := by
    have ha : (tripleCharges (sourceA2343 + difference 4 1) (sourceB2343 + difference 1 4) sourceC2343) = raw29643 := by
      apply Matrix.ext; unfold tripleCharges sourceA2343 sourceB2343 sourceC2343 difference raw29643; decide +kernel
    rw [ha]
    exact (canonical29643 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2343 + difference 4 2) (sourceB2343 + difference 2 4) sourceC2343) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2897) := by
    have ha : (tripleCharges (sourceA2343 + difference 4 2) (sourceB2343 + difference 2 4) sourceC2343) = raw29644 := by
      apply Matrix.ext; unfold tripleCharges sourceA2343 sourceB2343 sourceC2343 difference raw29644; decide +kernel
    rw [ha]
    exact (canonical29644 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2343 + difference 4 3) (sourceB2343 + difference 3 4) sourceC2343) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2969) := by
    have ha : (tripleCharges (sourceA2343 + difference 4 3) (sourceB2343 + difference 3 4) sourceC2343) = raw22586 := by
      apply Matrix.ext; unfold tripleCharges sourceA2343 sourceB2343 sourceC2343 difference raw22586; decide +kernel
    rw [ha]
    exact (canonical22586 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2343 + difference 4 5) (sourceB2343 + difference 5 4) sourceC2343) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2960) := by
    have ha : (tripleCharges (sourceA2343 + difference 4 5) (sourceB2343 + difference 5 4) sourceC2343) = raw29645 := by
      apply Matrix.ext; unfold tripleCharges sourceA2343 sourceB2343 sourceC2343 difference raw29645; decide +kernel
    rw [ha]
    exact (canonical29645 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2343 + difference 5 0) (sourceB2343 + difference 0 5) sourceC2343) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1131) := by
    have ha : (tripleCharges (sourceA2343 + difference 5 0) (sourceB2343 + difference 0 5) sourceC2343) = raw20406 := by
      apply Matrix.ext; unfold tripleCharges sourceA2343 sourceB2343 sourceC2343 difference raw20406; decide +kernel
    rw [ha]
    exact (canonical20406 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2343 + difference 5 1) (sourceB2343 + difference 1 5) sourceC2343) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2434) := by
    have ha : (tripleCharges (sourceA2343 + difference 5 1) (sourceB2343 + difference 1 5) sourceC2343) = raw27630 := by
      apply Matrix.ext; unfold tripleCharges sourceA2343 sourceB2343 sourceC2343 difference raw27630; decide +kernel
    rw [ha]
    exact (canonical27630 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2343 + difference 5 2) (sourceB2343 + difference 2 5) sourceC2343) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2429) := by
    have ha : (tripleCharges (sourceA2343 + difference 5 2) (sourceB2343 + difference 2 5) sourceC2343) = raw27631 := by
      apply Matrix.ext; unfold tripleCharges sourceA2343 sourceB2343 sourceC2343 difference raw27631; decide +kernel
    rw [ha]
    exact (canonical27631 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2343 + difference 5 3) (sourceB2343 + difference 3 5) sourceC2343) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2601) := by
    have ha : (tripleCharges (sourceA2343 + difference 5 3) (sourceB2343 + difference 3 5) sourceC2343) = raw4333 := by
      apply Matrix.ext; unfold tripleCharges sourceA2343 sourceB2343 sourceC2343 difference raw4333; decide +kernel
    rw [ha]
    exact (canonical4333 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2343 + difference 5 4) (sourceB2343 + difference 4 5) sourceC2343) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2485) := by
    have ha : (tripleCharges (sourceA2343 + difference 5 4) (sourceB2343 + difference 4 5) sourceC2343) = raw4328 := by
      apply Matrix.ext; unfold tripleCharges sourceA2343 sourceB2343 sourceC2343 difference raw4328; decide +kernel
    rw [ha]
    exact (canonical4328 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2343 sourceB2343 sourceC2343
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2343, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2344 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2344 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC2344 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceForm2344 : Integer.Sparse Master := [(Sum.inr 4344, 1), (Sum.inr 4346, 1), (Sum.inr 4349, 1), (Sum.inr 4355, 1), (Sum.inr 4458, 1), (Sum.inr 4941, 1), (Sum.inr 4943, 1), (Sum.inr 4946, 1), (Sum.inr 4950, 1), (Sum.inr 5033, 1), (Sum.inr 5036, 1), (Sum.inr 5039, 1), (Sum.inr 5073, 1), (Sum.inr 5075, 1), (Sum.inr 5137, 1), (Sum.inr 5141, 1), (Sum.inr 5167, 1), (Sum.inr 5168, 1), (Sum.inr 5169, 2), (Sum.inr 5171, 1), (Sum.inr 5177, 1), (Sum.inr 5259, 1), (Sum.inr 5292, 1), (Sum.inr 5293, 1), (Sum.inr 5465, 1), (Sum.inr 5476, 1), (Sum.inr 5483, 1), (Sum.inr 5486, 1), (Sum.inr 5487, 1)]

theorem sourceEq2344 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2344 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2344 + difference 0 1) (sourceB2344 + difference 1 0) sourceC2344) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5465) := by
    have ha : (tripleCharges (sourceA2344 + difference 0 1) (sourceB2344 + difference 1 0) sourceC2344) = raw17093 := by
      apply Matrix.ext; unfold tripleCharges sourceA2344 sourceB2344 sourceC2344 difference raw17093; decide +kernel
    rw [ha]
    exact (canonical17093 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2344 + difference 0 2) (sourceB2344 + difference 2 0) sourceC2344) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5476) := by
    have ha : (tripleCharges (sourceA2344 + difference 0 2) (sourceB2344 + difference 2 0) sourceC2344) = raw17094 := by
      apply Matrix.ext; unfold tripleCharges sourceA2344 sourceB2344 sourceC2344 difference raw17094; decide +kernel
    rw [ha]
    exact (canonical17094 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2344 + difference 0 3) (sourceB2344 + difference 3 0) sourceC2344) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA2344 + difference 0 3) (sourceB2344 + difference 3 0) sourceC2344) = raw3145 := by
      apply Matrix.ext; unfold tripleCharges sourceA2344 sourceB2344 sourceC2344 difference raw3145; decide +kernel
    rw [ha]
    exact (canonical3145 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2344 + difference 0 4) (sourceB2344 + difference 4 0) sourceC2344) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5487) := by
    have ha : (tripleCharges (sourceA2344 + difference 0 4) (sourceB2344 + difference 4 0) sourceC2344) = raw17095 := by
      apply Matrix.ext; unfold tripleCharges sourceA2344 sourceB2344 sourceC2344 difference raw17095; decide +kernel
    rw [ha]
    exact (canonical17095 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2344 + difference 0 5) (sourceB2344 + difference 5 0) sourceC2344) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5486) := by
    have ha : (tripleCharges (sourceA2344 + difference 0 5) (sourceB2344 + difference 5 0) sourceC2344) = raw3135 := by
      apply Matrix.ext; unfold tripleCharges sourceA2344 sourceB2344 sourceC2344 difference raw3135; decide +kernel
    rw [ha]
    exact (canonical3135 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2344 + difference 1 0) (sourceB2344 + difference 0 1) sourceC2344) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA2344 + difference 1 0) (sourceB2344 + difference 0 1) sourceC2344) = raw9856 := by
      apply Matrix.ext; unfold tripleCharges sourceA2344 sourceB2344 sourceC2344 difference raw9856; decide +kernel
    rw [ha]
    exact (canonical9856 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2344 + difference 1 2) (sourceB2344 + difference 2 1) sourceC2344) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5073) := by
    have ha : (tripleCharges (sourceA2344 + difference 1 2) (sourceB2344 + difference 2 1) sourceC2344) = raw9858 := by
      apply Matrix.ext; unfold tripleCharges sourceA2344 sourceB2344 sourceC2344 difference raw9858; decide +kernel
    rw [ha]
    exact (canonical9858 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2344 + difference 1 3) (sourceB2344 + difference 3 1) sourceC2344) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA2344 + difference 1 3) (sourceB2344 + difference 3 1) sourceC2344) = raw3144 := by
      apply Matrix.ext; unfold tripleCharges sourceA2344 sourceB2344 sourceC2344 difference raw3144; decide +kernel
    rw [ha]
    exact (canonical3144 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2344 + difference 1 4) (sourceB2344 + difference 4 1) sourceC2344) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA2344 + difference 1 4) (sourceB2344 + difference 4 1) sourceC2344) = raw9859 := by
      apply Matrix.ext; unfold tripleCharges sourceA2344 sourceB2344 sourceC2344 difference raw9859; decide +kernel
    rw [ha]
    exact (canonical9859 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2344 + difference 1 5) (sourceB2344 + difference 5 1) sourceC2344) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA2344 + difference 1 5) (sourceB2344 + difference 5 1) sourceC2344) = raw3134 := by
      apply Matrix.ext; unfold tripleCharges sourceA2344 sourceB2344 sourceC2344 difference raw3134; decide +kernel
    rw [ha]
    exact (canonical3134 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2344 + difference 2 0) (sourceB2344 + difference 0 2) sourceC2344) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4344) := by
    have ha : (tripleCharges (sourceA2344 + difference 2 0) (sourceB2344 + difference 0 2) sourceC2344) = raw32086 := by
      apply Matrix.ext; unfold tripleCharges sourceA2344 sourceB2344 sourceC2344 difference raw32086; decide +kernel
    rw [ha]
    exact (canonical32086 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2344 + difference 2 1) (sourceB2344 + difference 1 2) sourceC2344) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4941) := by
    have ha : (tripleCharges (sourceA2344 + difference 2 1) (sourceB2344 + difference 1 2) sourceC2344) = raw32087 := by
      apply Matrix.ext; unfold tripleCharges sourceA2344 sourceB2344 sourceC2344 difference raw32087; decide +kernel
    rw [ha]
    exact (canonical32087 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2344 + difference 2 3) (sourceB2344 + difference 3 2) sourceC2344) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5137) := by
    have ha : (tripleCharges (sourceA2344 + difference 2 3) (sourceB2344 + difference 3 2) sourceC2344) = raw9853 := by
      apply Matrix.ext; unfold tripleCharges sourceA2344 sourceB2344 sourceC2344 difference raw9853; decide +kernel
    rw [ha]
    exact (canonical9853 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2344 + difference 2 4) (sourceB2344 + difference 4 2) sourceC2344) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA2344 + difference 2 4) (sourceB2344 + difference 4 2) sourceC2344) = raw32088 := by
      apply Matrix.ext; unfold tripleCharges sourceA2344 sourceB2344 sourceC2344 difference raw32088; decide +kernel
    rw [ha]
    exact (canonical32088 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2344 + difference 2 5) (sourceB2344 + difference 5 2) sourceC2344) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5167) := by
    have ha : (tripleCharges (sourceA2344 + difference 2 5) (sourceB2344 + difference 5 2) sourceC2344) = raw32089 := by
      apply Matrix.ext; unfold tripleCharges sourceA2344 sourceB2344 sourceC2344 difference raw32089; decide +kernel
    rw [ha]
    exact (canonical32089 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2344 + difference 3 0) (sourceB2344 + difference 0 3) sourceC2344) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4355) := by
    have ha : (tripleCharges (sourceA2344 + difference 3 0) (sourceB2344 + difference 0 3) sourceC2344) = raw32090 := by
      apply Matrix.ext; unfold tripleCharges sourceA2344 sourceB2344 sourceC2344 difference raw32090; decide +kernel
    rw [ha]
    exact (canonical32090 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2344 + difference 3 1) (sourceB2344 + difference 1 3) sourceC2344) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4950) := by
    have ha : (tripleCharges (sourceA2344 + difference 3 1) (sourceB2344 + difference 1 3) sourceC2344) = raw32091 := by
      apply Matrix.ext; unfold tripleCharges sourceA2344 sourceB2344 sourceC2344 difference raw32091; decide +kernel
    rw [ha]
    exact (canonical32091 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2344 + difference 3 2) (sourceB2344 + difference 2 3) sourceC2344) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5039) := by
    have ha : (tripleCharges (sourceA2344 + difference 3 2) (sourceB2344 + difference 2 3) sourceC2344) = raw32092 := by
      apply Matrix.ext; unfold tripleCharges sourceA2344 sourceB2344 sourceC2344 difference raw32092; decide +kernel
    rw [ha]
    exact (canonical32092 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2344 + difference 3 4) (sourceB2344 + difference 4 3) sourceC2344) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5177) := by
    have ha : (tripleCharges (sourceA2344 + difference 3 4) (sourceB2344 + difference 4 3) sourceC2344) = raw32093 := by
      apply Matrix.ext; unfold tripleCharges sourceA2344 sourceB2344 sourceC2344 difference raw32093; decide +kernel
    rw [ha]
    exact (canonical32093 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2344 + difference 3 5) (sourceB2344 + difference 5 3) sourceC2344) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA2344 + difference 3 5) (sourceB2344 + difference 5 3) sourceC2344) = raw32094 := by
      apply Matrix.ext; unfold tripleCharges sourceA2344 sourceB2344 sourceC2344 difference raw32094; decide +kernel
    rw [ha]
    exact (canonical32094 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2344 + difference 4 0) (sourceB2344 + difference 0 4) sourceC2344) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4349) := by
    have ha : (tripleCharges (sourceA2344 + difference 4 0) (sourceB2344 + difference 0 4) sourceC2344) = raw30143 := by
      apply Matrix.ext; unfold tripleCharges sourceA2344 sourceB2344 sourceC2344 difference raw30143; decide +kernel
    rw [ha]
    exact (canonical30143 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2344 + difference 4 1) (sourceB2344 + difference 1 4) sourceC2344) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4946) := by
    have ha : (tripleCharges (sourceA2344 + difference 4 1) (sourceB2344 + difference 1 4) sourceC2344) = raw30144 := by
      apply Matrix.ext; unfold tripleCharges sourceA2344 sourceB2344 sourceC2344 difference raw30144; decide +kernel
    rw [ha]
    exact (canonical30144 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2344 + difference 4 2) (sourceB2344 + difference 2 4) sourceC2344) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5036) := by
    have ha : (tripleCharges (sourceA2344 + difference 4 2) (sourceB2344 + difference 2 4) sourceC2344) = raw30145 := by
      apply Matrix.ext; unfold tripleCharges sourceA2344 sourceB2344 sourceC2344 difference raw30145; decide +kernel
    rw [ha]
    exact (canonical30145 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2344 + difference 4 3) (sourceB2344 + difference 3 4) sourceC2344) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA2344 + difference 4 3) (sourceB2344 + difference 3 4) sourceC2344) = raw9861 := by
      apply Matrix.ext; unfold tripleCharges sourceA2344 sourceB2344 sourceC2344 difference raw9861; decide +kernel
    rw [ha]
    exact (canonical9861 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2344 + difference 4 5) (sourceB2344 + difference 5 4) sourceC2344) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5168) := by
    have ha : (tripleCharges (sourceA2344 + difference 4 5) (sourceB2344 + difference 5 4) sourceC2344) = raw30146 := by
      apply Matrix.ext; unfold tripleCharges sourceA2344 sourceB2344 sourceC2344 difference raw30146; decide +kernel
    rw [ha]
    exact (canonical30146 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2344 + difference 5 0) (sourceB2344 + difference 0 5) sourceC2344) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4346) := by
    have ha : (tripleCharges (sourceA2344 + difference 5 0) (sourceB2344 + difference 0 5) sourceC2344) = raw28768 := by
      apply Matrix.ext; unfold tripleCharges sourceA2344 sourceB2344 sourceC2344 difference raw28768; decide +kernel
    rw [ha]
    exact (canonical28768 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2344 + difference 5 1) (sourceB2344 + difference 1 5) sourceC2344) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4943) := by
    have ha : (tripleCharges (sourceA2344 + difference 5 1) (sourceB2344 + difference 1 5) sourceC2344) = raw28769 := by
      apply Matrix.ext; unfold tripleCharges sourceA2344 sourceB2344 sourceC2344 difference raw28769; decide +kernel
    rw [ha]
    exact (canonical28769 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2344 + difference 5 2) (sourceB2344 + difference 2 5) sourceC2344) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5033) := by
    have ha : (tripleCharges (sourceA2344 + difference 5 2) (sourceB2344 + difference 2 5) sourceC2344) = raw28770 := by
      apply Matrix.ext; unfold tripleCharges sourceA2344 sourceB2344 sourceC2344 difference raw28770; decide +kernel
    rw [ha]
    exact (canonical28770 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2344 + difference 5 3) (sourceB2344 + difference 3 5) sourceC2344) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA2344 + difference 5 3) (sourceB2344 + difference 3 5) sourceC2344) = raw9865 := by
      apply Matrix.ext; unfold tripleCharges sourceA2344 sourceB2344 sourceC2344 difference raw9865; decide +kernel
    rw [ha]
    exact (canonical9865 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2344 + difference 5 4) (sourceB2344 + difference 4 5) sourceC2344) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5171) := by
    have ha : (tripleCharges (sourceA2344 + difference 5 4) (sourceB2344 + difference 4 5) sourceC2344) = raw28771 := by
      apply Matrix.ext; unfold tripleCharges sourceA2344 sourceB2344 sourceC2344 difference raw28771; decide +kernel
    rw [ha]
    exact (canonical28771 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2344 sourceB2344 sourceC2344
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2344, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2345 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2345 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC2345 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceForm2345 : Integer.Sparse Master := [(Sum.inr 922, 1), (Sum.inr 924, 1), (Sum.inr 927, 1), (Sum.inr 933, 1), (Sum.inr 1041, 1), (Sum.inr 2332, 1), (Sum.inr 2334, 1), (Sum.inr 2337, 1), (Sum.inr 2342, 1), (Sum.inr 2425, 1), (Sum.inr 2428, 1), (Sum.inr 2432, 1), (Sum.inr 2480, 1), (Sum.inr 2482, 1), (Sum.inr 2556, 1), (Sum.inr 2561, 1), (Sum.inr 2593, 1), (Sum.inr 2594, 1), (Sum.inr 2595, 2), (Sum.inr 2598, 1), (Sum.inr 2605, 1), (Sum.inr 2723, 1), (Sum.inr 2766, 1), (Sum.inr 2767, 1), (Sum.inr 3931, 1), (Sum.inr 3965, 1), (Sum.inr 3981, 1), (Sum.inr 3999, 1), (Sum.inr 4000, 1)]

theorem sourceEq2345 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2345 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2345 + difference 0 1) (sourceB2345 + difference 1 0) sourceC2345) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3931) := by
    have ha : (tripleCharges (sourceA2345 + difference 0 1) (sourceB2345 + difference 1 0) sourceC2345) = raw17110 := by
      apply Matrix.ext; unfold tripleCharges sourceA2345 sourceB2345 sourceC2345 difference raw17110; decide +kernel
    rw [ha]
    exact (canonical17110 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2345 + difference 0 2) (sourceB2345 + difference 2 0) sourceC2345) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3965) := by
    have ha : (tripleCharges (sourceA2345 + difference 0 2) (sourceB2345 + difference 2 0) sourceC2345) = raw17111 := by
      apply Matrix.ext; unfold tripleCharges sourceA2345 sourceB2345 sourceC2345 difference raw17111; decide +kernel
    rw [ha]
    exact (canonical17111 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2345 + difference 0 3) (sourceB2345 + difference 3 0) sourceC2345) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3981) := by
    have ha : (tripleCharges (sourceA2345 + difference 0 3) (sourceB2345 + difference 3 0) sourceC2345) = raw3175 := by
      apply Matrix.ext; unfold tripleCharges sourceA2345 sourceB2345 sourceC2345 difference raw3175; decide +kernel
    rw [ha]
    exact (canonical3175 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2345 + difference 0 4) (sourceB2345 + difference 4 0) sourceC2345) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4000) := by
    have ha : (tripleCharges (sourceA2345 + difference 0 4) (sourceB2345 + difference 4 0) sourceC2345) = raw17112 := by
      apply Matrix.ext; unfold tripleCharges sourceA2345 sourceB2345 sourceC2345 difference raw17112; decide +kernel
    rw [ha]
    exact (canonical17112 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2345 + difference 0 5) (sourceB2345 + difference 5 0) sourceC2345) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3999) := by
    have ha : (tripleCharges (sourceA2345 + difference 0 5) (sourceB2345 + difference 5 0) sourceC2345) = raw3165 := by
      apply Matrix.ext; unfold tripleCharges sourceA2345 sourceB2345 sourceC2345 difference raw3165; decide +kernel
    rw [ha]
    exact (canonical3165 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2345 + difference 1 0) (sourceB2345 + difference 0 1) sourceC2345) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1041) := by
    have ha : (tripleCharges (sourceA2345 + difference 1 0) (sourceB2345 + difference 0 1) sourceC2345) = raw9878 := by
      apply Matrix.ext; unfold tripleCharges sourceA2345 sourceB2345 sourceC2345 difference raw9878; decide +kernel
    rw [ha]
    exact (canonical9878 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2345 + difference 1 2) (sourceB2345 + difference 2 1) sourceC2345) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2480) := by
    have ha : (tripleCharges (sourceA2345 + difference 1 2) (sourceB2345 + difference 2 1) sourceC2345) = raw9880 := by
      apply Matrix.ext; unfold tripleCharges sourceA2345 sourceB2345 sourceC2345 difference raw9880; decide +kernel
    rw [ha]
    exact (canonical9880 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2345 + difference 1 3) (sourceB2345 + difference 3 1) sourceC2345) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA2345 + difference 1 3) (sourceB2345 + difference 3 1) sourceC2345) = raw3174 := by
      apply Matrix.ext; unfold tripleCharges sourceA2345 sourceB2345 sourceC2345 difference raw3174; decide +kernel
    rw [ha]
    exact (canonical3174 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2345 + difference 1 4) (sourceB2345 + difference 4 1) sourceC2345) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2767) := by
    have ha : (tripleCharges (sourceA2345 + difference 1 4) (sourceB2345 + difference 4 1) sourceC2345) = raw9881 := by
      apply Matrix.ext; unfold tripleCharges sourceA2345 sourceB2345 sourceC2345 difference raw9881; decide +kernel
    rw [ha]
    exact (canonical9881 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2345 + difference 1 5) (sourceB2345 + difference 5 1) sourceC2345) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2766) := by
    have ha : (tripleCharges (sourceA2345 + difference 1 5) (sourceB2345 + difference 5 1) sourceC2345) = raw3164 := by
      apply Matrix.ext; unfold tripleCharges sourceA2345 sourceB2345 sourceC2345 difference raw3164; decide +kernel
    rw [ha]
    exact (canonical3164 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2345 + difference 2 0) (sourceB2345 + difference 0 2) sourceC2345) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 922) := by
    have ha : (tripleCharges (sourceA2345 + difference 2 0) (sourceB2345 + difference 0 2) sourceC2345) = raw32095 := by
      apply Matrix.ext; unfold tripleCharges sourceA2345 sourceB2345 sourceC2345 difference raw32095; decide +kernel
    rw [ha]
    exact (canonical32095 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2345 + difference 2 1) (sourceB2345 + difference 1 2) sourceC2345) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2332) := by
    have ha : (tripleCharges (sourceA2345 + difference 2 1) (sourceB2345 + difference 1 2) sourceC2345) = raw32096 := by
      apply Matrix.ext; unfold tripleCharges sourceA2345 sourceB2345 sourceC2345 difference raw32096; decide +kernel
    rw [ha]
    exact (canonical32096 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2345 + difference 2 3) (sourceB2345 + difference 3 2) sourceC2345) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2556) := by
    have ha : (tripleCharges (sourceA2345 + difference 2 3) (sourceB2345 + difference 3 2) sourceC2345) = raw9875 := by
      apply Matrix.ext; unfold tripleCharges sourceA2345 sourceB2345 sourceC2345 difference raw9875; decide +kernel
    rw [ha]
    exact (canonical9875 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2345 + difference 2 4) (sourceB2345 + difference 4 2) sourceC2345) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2595) := by
    have ha : (tripleCharges (sourceA2345 + difference 2 4) (sourceB2345 + difference 4 2) sourceC2345) = raw32097 := by
      apply Matrix.ext; unfold tripleCharges sourceA2345 sourceB2345 sourceC2345 difference raw32097; decide +kernel
    rw [ha]
    exact (canonical32097 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2345 + difference 2 5) (sourceB2345 + difference 5 2) sourceC2345) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2593) := by
    have ha : (tripleCharges (sourceA2345 + difference 2 5) (sourceB2345 + difference 5 2) sourceC2345) = raw32098 := by
      apply Matrix.ext; unfold tripleCharges sourceA2345 sourceB2345 sourceC2345 difference raw32098; decide +kernel
    rw [ha]
    exact (canonical32098 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2345 + difference 3 0) (sourceB2345 + difference 0 3) sourceC2345) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 933) := by
    have ha : (tripleCharges (sourceA2345 + difference 3 0) (sourceB2345 + difference 0 3) sourceC2345) = raw32099 := by
      apply Matrix.ext; unfold tripleCharges sourceA2345 sourceB2345 sourceC2345 difference raw32099; decide +kernel
    rw [ha]
    exact (canonical32099 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2345 + difference 3 1) (sourceB2345 + difference 1 3) sourceC2345) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2342) := by
    have ha : (tripleCharges (sourceA2345 + difference 3 1) (sourceB2345 + difference 1 3) sourceC2345) = raw32100 := by
      apply Matrix.ext; unfold tripleCharges sourceA2345 sourceB2345 sourceC2345 difference raw32100; decide +kernel
    rw [ha]
    exact (canonical32100 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2345 + difference 3 2) (sourceB2345 + difference 2 3) sourceC2345) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2432) := by
    have ha : (tripleCharges (sourceA2345 + difference 3 2) (sourceB2345 + difference 2 3) sourceC2345) = raw32101 := by
      apply Matrix.ext; unfold tripleCharges sourceA2345 sourceB2345 sourceC2345 difference raw32101; decide +kernel
    rw [ha]
    exact (canonical32101 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2345 + difference 3 4) (sourceB2345 + difference 4 3) sourceC2345) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2605) := by
    have ha : (tripleCharges (sourceA2345 + difference 3 4) (sourceB2345 + difference 4 3) sourceC2345) = raw32102 := by
      apply Matrix.ext; unfold tripleCharges sourceA2345 sourceB2345 sourceC2345 difference raw32102; decide +kernel
    rw [ha]
    exact (canonical32102 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2345 + difference 3 5) (sourceB2345 + difference 5 3) sourceC2345) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2595) := by
    have ha : (tripleCharges (sourceA2345 + difference 3 5) (sourceB2345 + difference 5 3) sourceC2345) = raw32103 := by
      apply Matrix.ext; unfold tripleCharges sourceA2345 sourceB2345 sourceC2345 difference raw32103; decide +kernel
    rw [ha]
    exact (canonical32103 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2345 + difference 4 0) (sourceB2345 + difference 0 4) sourceC2345) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 927) := by
    have ha : (tripleCharges (sourceA2345 + difference 4 0) (sourceB2345 + difference 0 4) sourceC2345) = raw30156 := by
      apply Matrix.ext; unfold tripleCharges sourceA2345 sourceB2345 sourceC2345 difference raw30156; decide +kernel
    rw [ha]
    exact (canonical30156 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2345 + difference 4 1) (sourceB2345 + difference 1 4) sourceC2345) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2337) := by
    have ha : (tripleCharges (sourceA2345 + difference 4 1) (sourceB2345 + difference 1 4) sourceC2345) = raw30157 := by
      apply Matrix.ext; unfold tripleCharges sourceA2345 sourceB2345 sourceC2345 difference raw30157; decide +kernel
    rw [ha]
    exact (canonical30157 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2345 + difference 4 2) (sourceB2345 + difference 2 4) sourceC2345) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2428) := by
    have ha : (tripleCharges (sourceA2345 + difference 4 2) (sourceB2345 + difference 2 4) sourceC2345) = raw30158 := by
      apply Matrix.ext; unfold tripleCharges sourceA2345 sourceB2345 sourceC2345 difference raw30158; decide +kernel
    rw [ha]
    exact (canonical30158 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2345 + difference 4 3) (sourceB2345 + difference 3 4) sourceC2345) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2561) := by
    have ha : (tripleCharges (sourceA2345 + difference 4 3) (sourceB2345 + difference 3 4) sourceC2345) = raw9883 := by
      apply Matrix.ext; unfold tripleCharges sourceA2345 sourceB2345 sourceC2345 difference raw9883; decide +kernel
    rw [ha]
    exact (canonical9883 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2345 + difference 4 5) (sourceB2345 + difference 5 4) sourceC2345) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2594) := by
    have ha : (tripleCharges (sourceA2345 + difference 4 5) (sourceB2345 + difference 5 4) sourceC2345) = raw30159 := by
      apply Matrix.ext; unfold tripleCharges sourceA2345 sourceB2345 sourceC2345 difference raw30159; decide +kernel
    rw [ha]
    exact (canonical30159 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2345 + difference 5 0) (sourceB2345 + difference 0 5) sourceC2345) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 924) := by
    have ha : (tripleCharges (sourceA2345 + difference 5 0) (sourceB2345 + difference 0 5) sourceC2345) = raw28785 := by
      apply Matrix.ext; unfold tripleCharges sourceA2345 sourceB2345 sourceC2345 difference raw28785; decide +kernel
    rw [ha]
    exact (canonical28785 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2345 + difference 5 1) (sourceB2345 + difference 1 5) sourceC2345) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2334) := by
    have ha : (tripleCharges (sourceA2345 + difference 5 1) (sourceB2345 + difference 1 5) sourceC2345) = raw28786 := by
      apply Matrix.ext; unfold tripleCharges sourceA2345 sourceB2345 sourceC2345 difference raw28786; decide +kernel
    rw [ha]
    exact (canonical28786 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2345 + difference 5 2) (sourceB2345 + difference 2 5) sourceC2345) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2425) := by
    have ha : (tripleCharges (sourceA2345 + difference 5 2) (sourceB2345 + difference 2 5) sourceC2345) = raw28787 := by
      apply Matrix.ext; unfold tripleCharges sourceA2345 sourceB2345 sourceC2345 difference raw28787; decide +kernel
    rw [ha]
    exact (canonical28787 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2345 + difference 5 3) (sourceB2345 + difference 3 5) sourceC2345) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2482) := by
    have ha : (tripleCharges (sourceA2345 + difference 5 3) (sourceB2345 + difference 3 5) sourceC2345) = raw9887 := by
      apply Matrix.ext; unfold tripleCharges sourceA2345 sourceB2345 sourceC2345 difference raw9887; decide +kernel
    rw [ha]
    exact (canonical9887 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2345 + difference 5 4) (sourceB2345 + difference 4 5) sourceC2345) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2598) := by
    have ha : (tripleCharges (sourceA2345 + difference 5 4) (sourceB2345 + difference 4 5) sourceC2345) = raw28788 := by
      apply Matrix.ext; unfold tripleCharges sourceA2345 sourceB2345 sourceC2345 difference raw28788; decide +kernel
    rw [ha]
    exact (canonical28788 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2345 sourceB2345 sourceC2345
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2345, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2346 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2346 : Charge := ![1, 1, 0, -1, 1, -2]
def sourceC2346 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceForm2346 : Integer.Sparse Master := [(Sum.inr 4537, 1), (Sum.inr 4538, 1), (Sum.inr 4539, 1), (Sum.inr 4553, 1), (Sum.inr 4619, 1), (Sum.inr 4723, 1), (Sum.inr 4727, 1), (Sum.inr 4747, 1), (Sum.inr 4871, 1), (Sum.inr 4969, 1), (Sum.inr 4973, 1), (Sum.inr 4978, 1), (Sum.inr 5114, 1), (Sum.inr 5118, 1), (Sum.inr 5155, 1), (Sum.inr 5156, 1), (Sum.inr 5166, 1), (Sum.inr 5168, 1), (Sum.inr 5170, 3), (Sum.inr 5176, 1), (Sum.inr 5302, 1), (Sum.inr 5306, 1), (Sum.inr 5310, 1), (Sum.inr 5384, 1), (Sum.inr 5403, 1), (Sum.inr 5412, 1), (Sum.inr 5439, 1), (Sum.inr 5443, 1)]

theorem sourceEq2346 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2346 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2346 + difference 0 1) (sourceB2346 + difference 1 0) sourceC2346) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5384) := by
    have ha : (tripleCharges (sourceA2346 + difference 0 1) (sourceB2346 + difference 1 0) sourceC2346) = raw14883 := by
      apply Matrix.ext; unfold tripleCharges sourceA2346 sourceB2346 sourceC2346 difference raw14883; decide +kernel
    rw [ha]
    exact (canonical14883 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2346 + difference 0 2) (sourceB2346 + difference 2 0) sourceC2346) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5403) := by
    have ha : (tripleCharges (sourceA2346 + difference 0 2) (sourceB2346 + difference 2 0) sourceC2346) = raw14884 := by
      apply Matrix.ext; unfold tripleCharges sourceA2346 sourceB2346 sourceC2346 difference raw14884; decide +kernel
    rw [ha]
    exact (canonical14884 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2346 + difference 0 3) (sourceB2346 + difference 3 0) sourceC2346) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA2346 + difference 0 3) (sourceB2346 + difference 3 0) sourceC2346) = raw2652 := by
      apply Matrix.ext; unfold tripleCharges sourceA2346 sourceB2346 sourceC2346 difference raw2652; decide +kernel
    rw [ha]
    exact (canonical2652 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2346 + difference 0 4) (sourceB2346 + difference 4 0) sourceC2346) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5412) := by
    have ha : (tripleCharges (sourceA2346 + difference 0 4) (sourceB2346 + difference 4 0) sourceC2346) = raw2647 := by
      apply Matrix.ext; unfold tripleCharges sourceA2346 sourceB2346 sourceC2346 difference raw2647; decide +kernel
    rw [ha]
    exact (canonical2647 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2346 + difference 0 5) (sourceB2346 + difference 5 0) sourceC2346) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA2346 + difference 0 5) (sourceB2346 + difference 5 0) sourceC2346) = raw14885 := by
      apply Matrix.ext; unfold tripleCharges sourceA2346 sourceB2346 sourceC2346 difference raw14885; decide +kernel
    rw [ha]
    exact (canonical14885 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2346 + difference 1 0) (sourceB2346 + difference 0 1) sourceC2346) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4619) := by
    have ha : (tripleCharges (sourceA2346 + difference 1 0) (sourceB2346 + difference 0 1) sourceC2346) = raw7566 := by
      apply Matrix.ext; unfold tripleCharges sourceA2346 sourceB2346 sourceC2346 difference raw7566; decide +kernel
    rw [ha]
    exact (canonical7566 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2346 + difference 1 2) (sourceB2346 + difference 2 1) sourceC2346) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5170) := by
    have ha : (tripleCharges (sourceA2346 + difference 1 2) (sourceB2346 + difference 2 1) sourceC2346) = raw7568 := by
      apply Matrix.ext; unfold tripleCharges sourceA2346 sourceB2346 sourceC2346 difference raw7568; decide +kernel
    rw [ha]
    exact (canonical7568 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2346 + difference 1 3) (sourceB2346 + difference 3 1) sourceC2346) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5310) := by
    have ha : (tripleCharges (sourceA2346 + difference 1 3) (sourceB2346 + difference 3 1) sourceC2346) = raw2651 := by
      apply Matrix.ext; unfold tripleCharges sourceA2346 sourceB2346 sourceC2346 difference raw2651; decide +kernel
    rw [ha]
    exact (canonical2651 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2346 + difference 1 4) (sourceB2346 + difference 4 1) sourceC2346) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA2346 + difference 1 4) (sourceB2346 + difference 4 1) sourceC2346) = raw2646 := by
      apply Matrix.ext; unfold tripleCharges sourceA2346 sourceB2346 sourceC2346 difference raw2646; decide +kernel
    rw [ha]
    exact (canonical2646 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2346 + difference 1 5) (sourceB2346 + difference 5 1) sourceC2346) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5306) := by
    have ha : (tripleCharges (sourceA2346 + difference 1 5) (sourceB2346 + difference 5 1) sourceC2346) = raw7569 := by
      apply Matrix.ext; unfold tripleCharges sourceA2346 sourceB2346 sourceC2346 difference raw7569; decide +kernel
    rw [ha]
    exact (canonical7569 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2346 + difference 2 0) (sourceB2346 + difference 0 2) sourceC2346) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4537) := by
    have ha : (tripleCharges (sourceA2346 + difference 2 0) (sourceB2346 + difference 0 2) sourceC2346) = raw24275 := by
      apply Matrix.ext; unfold tripleCharges sourceA2346 sourceB2346 sourceC2346 difference raw24275; decide +kernel
    rw [ha]
    exact (canonical24275 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2346 + difference 2 1) (sourceB2346 + difference 1 2) sourceC2346) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4969) := by
    have ha : (tripleCharges (sourceA2346 + difference 2 1) (sourceB2346 + difference 1 2) sourceC2346) = raw32104 := by
      apply Matrix.ext; unfold tripleCharges sourceA2346 sourceB2346 sourceC2346 difference raw32104; decide +kernel
    rw [ha]
    exact (canonical32104 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2346 + difference 2 3) (sourceB2346 + difference 3 2) sourceC2346) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5170) := by
    have ha : (tripleCharges (sourceA2346 + difference 2 3) (sourceB2346 + difference 3 2) sourceC2346) = raw7563 := by
      apply Matrix.ext; unfold tripleCharges sourceA2346 sourceB2346 sourceC2346 difference raw7563; decide +kernel
    rw [ha]
    exact (canonical7563 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2346 + difference 2 4) (sourceB2346 + difference 4 2) sourceC2346) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5155) := by
    have ha : (tripleCharges (sourceA2346 + difference 2 4) (sourceB2346 + difference 4 2) sourceC2346) = raw32105 := by
      apply Matrix.ext; unfold tripleCharges sourceA2346 sourceB2346 sourceC2346 difference raw32105; decide +kernel
    rw [ha]
    exact (canonical32105 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2346 + difference 2 5) (sourceB2346 + difference 5 2) sourceC2346) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5166) := by
    have ha : (tripleCharges (sourceA2346 + difference 2 5) (sourceB2346 + difference 5 2) sourceC2346) = raw32106 := by
      apply Matrix.ext; unfold tripleCharges sourceA2346 sourceB2346 sourceC2346 difference raw32106; decide +kernel
    rw [ha]
    exact (canonical32106 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2346 + difference 3 0) (sourceB2346 + difference 0 3) sourceC2346) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4539) := by
    have ha : (tripleCharges (sourceA2346 + difference 3 0) (sourceB2346 + difference 0 3) sourceC2346) = raw24279 := by
      apply Matrix.ext; unfold tripleCharges sourceA2346 sourceB2346 sourceC2346 difference raw24279; decide +kernel
    rw [ha]
    exact (canonical24279 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2346 + difference 3 1) (sourceB2346 + difference 1 3) sourceC2346) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4978) := by
    have ha : (tripleCharges (sourceA2346 + difference 3 1) (sourceB2346 + difference 1 3) sourceC2346) = raw32107 := by
      apply Matrix.ext; unfold tripleCharges sourceA2346 sourceB2346 sourceC2346 difference raw32107; decide +kernel
    rw [ha]
    exact (canonical32107 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2346 + difference 3 2) (sourceB2346 + difference 2 3) sourceC2346) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5118) := by
    have ha : (tripleCharges (sourceA2346 + difference 3 2) (sourceB2346 + difference 2 3) sourceC2346) = raw32108 := by
      apply Matrix.ext; unfold tripleCharges sourceA2346 sourceB2346 sourceC2346 difference raw32108; decide +kernel
    rw [ha]
    exact (canonical32108 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2346 + difference 3 4) (sourceB2346 + difference 4 3) sourceC2346) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5156) := by
    have ha : (tripleCharges (sourceA2346 + difference 3 4) (sourceB2346 + difference 4 3) sourceC2346) = raw32109 := by
      apply Matrix.ext; unfold tripleCharges sourceA2346 sourceB2346 sourceC2346 difference raw32109; decide +kernel
    rw [ha]
    exact (canonical32109 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2346 + difference 3 5) (sourceB2346 + difference 5 3) sourceC2346) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5170) := by
    have ha : (tripleCharges (sourceA2346 + difference 3 5) (sourceB2346 + difference 5 3) sourceC2346) = raw32110 := by
      apply Matrix.ext; unfold tripleCharges sourceA2346 sourceB2346 sourceC2346 difference raw32110; decide +kernel
    rw [ha]
    exact (canonical32110 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2346 + difference 4 0) (sourceB2346 + difference 0 4) sourceC2346) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4553) := by
    have ha : (tripleCharges (sourceA2346 + difference 4 0) (sourceB2346 + difference 0 4) sourceC2346) = raw24284 := by
      apply Matrix.ext; unfold tripleCharges sourceA2346 sourceB2346 sourceC2346 difference raw24284; decide +kernel
    rw [ha]
    exact (canonical24284 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2346 + difference 4 1) (sourceB2346 + difference 1 4) sourceC2346) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4973) := by
    have ha : (tripleCharges (sourceA2346 + difference 4 1) (sourceB2346 + difference 1 4) sourceC2346) = raw32111 := by
      apply Matrix.ext; unfold tripleCharges sourceA2346 sourceB2346 sourceC2346 difference raw32111; decide +kernel
    rw [ha]
    exact (canonical32111 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2346 + difference 4 2) (sourceB2346 + difference 2 4) sourceC2346) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5114) := by
    have ha : (tripleCharges (sourceA2346 + difference 4 2) (sourceB2346 + difference 2 4) sourceC2346) = raw32112 := by
      apply Matrix.ext; unfold tripleCharges sourceA2346 sourceB2346 sourceC2346 difference raw32112; decide +kernel
    rw [ha]
    exact (canonical32112 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2346 + difference 4 3) (sourceB2346 + difference 3 4) sourceC2346) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5176) := by
    have ha : (tripleCharges (sourceA2346 + difference 4 3) (sourceB2346 + difference 3 4) sourceC2346) = raw7571 := by
      apply Matrix.ext; unfold tripleCharges sourceA2346 sourceB2346 sourceC2346 difference raw7571; decide +kernel
    rw [ha]
    exact (canonical7571 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2346 + difference 4 5) (sourceB2346 + difference 5 4) sourceC2346) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5168) := by
    have ha : (tripleCharges (sourceA2346 + difference 4 5) (sourceB2346 + difference 5 4) sourceC2346) = raw32113 := by
      apply Matrix.ext; unfold tripleCharges sourceA2346 sourceB2346 sourceC2346 difference raw32113; decide +kernel
    rw [ha]
    exact (canonical32113 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2346 + difference 5 0) (sourceB2346 + difference 0 5) sourceC2346) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4538) := by
    have ha : (tripleCharges (sourceA2346 + difference 5 0) (sourceB2346 + difference 0 5) sourceC2346) = raw20541 := by
      apply Matrix.ext; unfold tripleCharges sourceA2346 sourceB2346 sourceC2346 difference raw20541; decide +kernel
    rw [ha]
    exact (canonical20541 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2346 + difference 5 1) (sourceB2346 + difference 1 5) sourceC2346) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4727) := by
    have ha : (tripleCharges (sourceA2346 + difference 5 1) (sourceB2346 + difference 1 5) sourceC2346) = raw27670 := by
      apply Matrix.ext; unfold tripleCharges sourceA2346 sourceB2346 sourceC2346 difference raw27670; decide +kernel
    rw [ha]
    exact (canonical27670 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2346 + difference 5 2) (sourceB2346 + difference 2 5) sourceC2346) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4723) := by
    have ha : (tripleCharges (sourceA2346 + difference 5 2) (sourceB2346 + difference 2 5) sourceC2346) = raw27671 := by
      apply Matrix.ext; unfold tripleCharges sourceA2346 sourceB2346 sourceC2346 difference raw27671; decide +kernel
    rw [ha]
    exact (canonical27671 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2346 + difference 5 3) (sourceB2346 + difference 3 5) sourceC2346) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4871) := by
    have ha : (tripleCharges (sourceA2346 + difference 5 3) (sourceB2346 + difference 3 5) sourceC2346) = raw4393 := by
      apply Matrix.ext; unfold tripleCharges sourceA2346 sourceB2346 sourceC2346 difference raw4393; decide +kernel
    rw [ha]
    exact (canonical4393 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2346 + difference 5 4) (sourceB2346 + difference 4 5) sourceC2346) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4747) := by
    have ha : (tripleCharges (sourceA2346 + difference 5 4) (sourceB2346 + difference 4 5) sourceC2346) = raw4389 := by
      apply Matrix.ext; unfold tripleCharges sourceA2346 sourceB2346 sourceC2346 difference raw4389; decide +kernel
    rw [ha]
    exact (canonical4389 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2346 sourceB2346 sourceC2346
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2346, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2347 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2347 : Charge := ![1, 1, 0, -1, 1, -2]
def sourceC2347 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceForm2347 : Integer.Sparse Master := [(Sum.inr 1122, 1), (Sum.inr 1123, 1), (Sum.inr 1124, 1), (Sum.inr 1138, 1), (Sum.inr 1294, 1), (Sum.inr 1877, 1), (Sum.inr 1881, 1), (Sum.inr 1926, 1), (Sum.inr 2112, 1), (Sum.inr 2804, 1), (Sum.inr 2805, 1), (Sum.inr 2817, 1), (Sum.inr 2891, 1), (Sum.inr 2896, 1), (Sum.inr 2908, 1), (Sum.inr 2911, 1), (Sum.inr 2953, 1), (Sum.inr 2954, 3), (Sum.inr 2963, 1), (Sum.inr 2968, 1), (Sum.inr 3054, 1), (Sum.inr 3120, 1), (Sum.inr 3121, 1), (Sum.inr 3732, 1), (Sum.inr 3789, 1), (Sum.inr 3814, 1), (Sum.inr 3889, 1), (Sum.inr 4012, 1)]

theorem sourceEq2347 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2347 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2347 + difference 0 1) (sourceB2347 + difference 1 0) sourceC2347) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3732) := by
    have ha : (tripleCharges (sourceA2347 + difference 0 1) (sourceB2347 + difference 1 0) sourceC2347) = raw14902 := by
      apply Matrix.ext; unfold tripleCharges sourceA2347 sourceB2347 sourceC2347 difference raw14902; decide +kernel
    rw [ha]
    exact (canonical14902 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2347 + difference 0 2) (sourceB2347 + difference 2 0) sourceC2347) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3789) := by
    have ha : (tripleCharges (sourceA2347 + difference 0 2) (sourceB2347 + difference 2 0) sourceC2347) = raw14903 := by
      apply Matrix.ext; unfold tripleCharges sourceA2347 sourceB2347 sourceC2347 difference raw14903; decide +kernel
    rw [ha]
    exact (canonical14903 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2347 + difference 0 3) (sourceB2347 + difference 3 0) sourceC2347) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3889) := by
    have ha : (tripleCharges (sourceA2347 + difference 0 3) (sourceB2347 + difference 3 0) sourceC2347) = raw7575 := by
      apply Matrix.ext; unfold tripleCharges sourceA2347 sourceB2347 sourceC2347 difference raw7575; decide +kernel
    rw [ha]
    exact (canonical7575 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2347 + difference 0 4) (sourceB2347 + difference 4 0) sourceC2347) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3814) := by
    have ha : (tripleCharges (sourceA2347 + difference 0 4) (sourceB2347 + difference 4 0) sourceC2347) = raw14904 := by
      apply Matrix.ext; unfold tripleCharges sourceA2347 sourceB2347 sourceC2347 difference raw14904; decide +kernel
    rw [ha]
    exact (canonical14904 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2347 + difference 0 5) (sourceB2347 + difference 5 0) sourceC2347) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4012) := by
    have ha : (tripleCharges (sourceA2347 + difference 0 5) (sourceB2347 + difference 5 0) sourceC2347) = raw14905 := by
      apply Matrix.ext; unfold tripleCharges sourceA2347 sourceB2347 sourceC2347 difference raw14905; decide +kernel
    rw [ha]
    exact (canonical14905 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2347 + difference 1 0) (sourceB2347 + difference 0 1) sourceC2347) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1294) := by
    have ha : (tripleCharges (sourceA2347 + difference 1 0) (sourceB2347 + difference 0 1) sourceC2347) = raw7587 := by
      apply Matrix.ext; unfold tripleCharges sourceA2347 sourceB2347 sourceC2347 difference raw7587; decide +kernel
    rw [ha]
    exact (canonical7587 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2347 + difference 1 2) (sourceB2347 + difference 2 1) sourceC2347) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2954) := by
    have ha : (tripleCharges (sourceA2347 + difference 1 2) (sourceB2347 + difference 2 1) sourceC2347) = raw7589 := by
      apply Matrix.ext; unfold tripleCharges sourceA2347 sourceB2347 sourceC2347 difference raw7589; decide +kernel
    rw [ha]
    exact (canonical7589 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2347 + difference 1 3) (sourceB2347 + difference 3 1) sourceC2347) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3121) := by
    have ha : (tripleCharges (sourceA2347 + difference 1 3) (sourceB2347 + difference 3 1) sourceC2347) = raw4425 := by
      apply Matrix.ext; unfold tripleCharges sourceA2347 sourceB2347 sourceC2347 difference raw4425; decide +kernel
    rw [ha]
    exact (canonical4425 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2347 + difference 1 4) (sourceB2347 + difference 4 1) sourceC2347) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3054) := by
    have ha : (tripleCharges (sourceA2347 + difference 1 4) (sourceB2347 + difference 4 1) sourceC2347) = raw4420 := by
      apply Matrix.ext; unfold tripleCharges sourceA2347 sourceB2347 sourceC2347 difference raw4420; decide +kernel
    rw [ha]
    exact (canonical4420 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2347 + difference 1 5) (sourceB2347 + difference 5 1) sourceC2347) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3120) := by
    have ha : (tripleCharges (sourceA2347 + difference 1 5) (sourceB2347 + difference 5 1) sourceC2347) = raw7590 := by
      apply Matrix.ext; unfold tripleCharges sourceA2347 sourceB2347 sourceC2347 difference raw7590; decide +kernel
    rw [ha]
    exact (canonical7590 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2347 + difference 2 0) (sourceB2347 + difference 0 2) sourceC2347) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1122) := by
    have ha : (tripleCharges (sourceA2347 + difference 2 0) (sourceB2347 + difference 0 2) sourceC2347) = raw24292 := by
      apply Matrix.ext; unfold tripleCharges sourceA2347 sourceB2347 sourceC2347 difference raw24292; decide +kernel
    rw [ha]
    exact (canonical24292 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2347 + difference 2 1) (sourceB2347 + difference 1 2) sourceC2347) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2804) := by
    have ha : (tripleCharges (sourceA2347 + difference 2 1) (sourceB2347 + difference 1 2) sourceC2347) = raw32114 := by
      apply Matrix.ext; unfold tripleCharges sourceA2347 sourceB2347 sourceC2347 difference raw32114; decide +kernel
    rw [ha]
    exact (canonical32114 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2347 + difference 2 3) (sourceB2347 + difference 3 2) sourceC2347) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2954) := by
    have ha : (tripleCharges (sourceA2347 + difference 2 3) (sourceB2347 + difference 3 2) sourceC2347) = raw7584 := by
      apply Matrix.ext; unfold tripleCharges sourceA2347 sourceB2347 sourceC2347 difference raw7584; decide +kernel
    rw [ha]
    exact (canonical7584 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2347 + difference 2 4) (sourceB2347 + difference 4 2) sourceC2347) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2908) := by
    have ha : (tripleCharges (sourceA2347 + difference 2 4) (sourceB2347 + difference 4 2) sourceC2347) = raw32115 := by
      apply Matrix.ext; unfold tripleCharges sourceA2347 sourceB2347 sourceC2347 difference raw32115; decide +kernel
    rw [ha]
    exact (canonical32115 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2347 + difference 2 5) (sourceB2347 + difference 5 2) sourceC2347) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2953) := by
    have ha : (tripleCharges (sourceA2347 + difference 2 5) (sourceB2347 + difference 5 2) sourceC2347) = raw32116 := by
      apply Matrix.ext; unfold tripleCharges sourceA2347 sourceB2347 sourceC2347 difference raw32116; decide +kernel
    rw [ha]
    exact (canonical32116 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2347 + difference 3 0) (sourceB2347 + difference 0 3) sourceC2347) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1124) := by
    have ha : (tripleCharges (sourceA2347 + difference 3 0) (sourceB2347 + difference 0 3) sourceC2347) = raw24296 := by
      apply Matrix.ext; unfold tripleCharges sourceA2347 sourceB2347 sourceC2347 difference raw24296; decide +kernel
    rw [ha]
    exact (canonical24296 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2347 + difference 3 1) (sourceB2347 + difference 1 3) sourceC2347) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2805) := by
    have ha : (tripleCharges (sourceA2347 + difference 3 1) (sourceB2347 + difference 1 3) sourceC2347) = raw32117 := by
      apply Matrix.ext; unfold tripleCharges sourceA2347 sourceB2347 sourceC2347 difference raw32117; decide +kernel
    rw [ha]
    exact (canonical32117 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2347 + difference 3 2) (sourceB2347 + difference 2 3) sourceC2347) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2891) := by
    have ha : (tripleCharges (sourceA2347 + difference 3 2) (sourceB2347 + difference 2 3) sourceC2347) = raw32118 := by
      apply Matrix.ext; unfold tripleCharges sourceA2347 sourceB2347 sourceC2347 difference raw32118; decide +kernel
    rw [ha]
    exact (canonical32118 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2347 + difference 3 4) (sourceB2347 + difference 4 3) sourceC2347) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2911) := by
    have ha : (tripleCharges (sourceA2347 + difference 3 4) (sourceB2347 + difference 4 3) sourceC2347) = raw32119 := by
      apply Matrix.ext; unfold tripleCharges sourceA2347 sourceB2347 sourceC2347 difference raw32119; decide +kernel
    rw [ha]
    exact (canonical32119 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2347 + difference 3 5) (sourceB2347 + difference 5 3) sourceC2347) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2954) := by
    have ha : (tripleCharges (sourceA2347 + difference 3 5) (sourceB2347 + difference 5 3) sourceC2347) = raw32120 := by
      apply Matrix.ext; unfold tripleCharges sourceA2347 sourceB2347 sourceC2347 difference raw32120; decide +kernel
    rw [ha]
    exact (canonical32120 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2347 + difference 4 0) (sourceB2347 + difference 0 4) sourceC2347) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1138) := by
    have ha : (tripleCharges (sourceA2347 + difference 4 0) (sourceB2347 + difference 0 4) sourceC2347) = raw24301 := by
      apply Matrix.ext; unfold tripleCharges sourceA2347 sourceB2347 sourceC2347 difference raw24301; decide +kernel
    rw [ha]
    exact (canonical24301 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2347 + difference 4 1) (sourceB2347 + difference 1 4) sourceC2347) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2817) := by
    have ha : (tripleCharges (sourceA2347 + difference 4 1) (sourceB2347 + difference 1 4) sourceC2347) = raw32121 := by
      apply Matrix.ext; unfold tripleCharges sourceA2347 sourceB2347 sourceC2347 difference raw32121; decide +kernel
    rw [ha]
    exact (canonical32121 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2347 + difference 4 2) (sourceB2347 + difference 2 4) sourceC2347) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2896) := by
    have ha : (tripleCharges (sourceA2347 + difference 4 2) (sourceB2347 + difference 2 4) sourceC2347) = raw32122 := by
      apply Matrix.ext; unfold tripleCharges sourceA2347 sourceB2347 sourceC2347 difference raw32122; decide +kernel
    rw [ha]
    exact (canonical32122 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2347 + difference 4 3) (sourceB2347 + difference 3 4) sourceC2347) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2968) := by
    have ha : (tripleCharges (sourceA2347 + difference 4 3) (sourceB2347 + difference 3 4) sourceC2347) = raw7592 := by
      apply Matrix.ext; unfold tripleCharges sourceA2347 sourceB2347 sourceC2347 difference raw7592; decide +kernel
    rw [ha]
    exact (canonical7592 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2347 + difference 4 5) (sourceB2347 + difference 5 4) sourceC2347) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2963) := by
    have ha : (tripleCharges (sourceA2347 + difference 4 5) (sourceB2347 + difference 5 4) sourceC2347) = raw32123 := by
      apply Matrix.ext; unfold tripleCharges sourceA2347 sourceB2347 sourceC2347 difference raw32123; decide +kernel
    rw [ha]
    exact (canonical32123 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2347 + difference 5 0) (sourceB2347 + difference 0 5) sourceC2347) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1123) := by
    have ha : (tripleCharges (sourceA2347 + difference 5 0) (sourceB2347 + difference 0 5) sourceC2347) = raw20558 := by
      apply Matrix.ext; unfold tripleCharges sourceA2347 sourceB2347 sourceC2347 difference raw20558; decide +kernel
    rw [ha]
    exact (canonical20558 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2347 + difference 5 1) (sourceB2347 + difference 1 5) sourceC2347) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1881) := by
    have ha : (tripleCharges (sourceA2347 + difference 5 1) (sourceB2347 + difference 1 5) sourceC2347) = raw27680 := by
      apply Matrix.ext; unfold tripleCharges sourceA2347 sourceB2347 sourceC2347 difference raw27680; decide +kernel
    rw [ha]
    exact (canonical27680 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2347 + difference 5 2) (sourceB2347 + difference 2 5) sourceC2347) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1877) := by
    have ha : (tripleCharges (sourceA2347 + difference 5 2) (sourceB2347 + difference 2 5) sourceC2347) = raw27681 := by
      apply Matrix.ext; unfold tripleCharges sourceA2347 sourceB2347 sourceC2347 difference raw27681; decide +kernel
    rw [ha]
    exact (canonical27681 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2347 + difference 5 3) (sourceB2347 + difference 3 5) sourceC2347) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2112) := by
    have ha : (tripleCharges (sourceA2347 + difference 5 3) (sourceB2347 + difference 3 5) sourceC2347) = raw4422 := by
      apply Matrix.ext; unfold tripleCharges sourceA2347 sourceB2347 sourceC2347 difference raw4422; decide +kernel
    rw [ha]
    exact (canonical4422 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2347 + difference 5 4) (sourceB2347 + difference 4 5) sourceC2347) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1926) := by
    have ha : (tripleCharges (sourceA2347 + difference 5 4) (sourceB2347 + difference 4 5) sourceC2347) = raw4417 := by
      apply Matrix.ext; unfold tripleCharges sourceA2347 sourceB2347 sourceC2347 difference raw4417; decide +kernel
    rw [ha]
    exact (canonical4417 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2347 sourceB2347 sourceC2347
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2347, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2348 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2348 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC2348 : Charge := ![1, 1, 0, -1, 1, -2]
def sourceForm2348 : Integer.Sparse Master := [(Sum.inr 4345, 1), (Sum.inr 4347, 1), (Sum.inr 4348, 1), (Sum.inr 4357, 1), (Sum.inr 4459, 1), (Sum.inr 4942, 1), (Sum.inr 4944, 1), (Sum.inr 4945, 1), (Sum.inr 4951, 1), (Sum.inr 5034, 1), (Sum.inr 5035, 1), (Sum.inr 5040, 1), (Sum.inr 5074, 1), (Sum.inr 5078, 1), (Sum.inr 5138, 1), (Sum.inr 5139, 1), (Sum.inr 5140, 1), (Sum.inr 5149, 1), (Sum.inr 5152, 1), (Sum.inr 5160, 1), (Sum.inr 5161, 1), (Sum.inr 5164, 1), (Sum.inr 5260, 1), (Sum.inr 5284, 1), (Sum.inr 5289, 1), (Sum.inr 5401, 1), (Sum.inr 5404, 1), (Sum.inr 5410, 1), (Sum.inr 5438, 1), (Sum.inr 5484, 1)]

theorem sourceEq2348 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2348 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2348 + difference 0 1) (sourceB2348 + difference 1 0) sourceC2348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5404) := by
    have ha : (tripleCharges (sourceA2348 + difference 0 1) (sourceB2348 + difference 1 0) sourceC2348) = raw32124 := by
      apply Matrix.ext; unfold tripleCharges sourceA2348 sourceB2348 sourceC2348 difference raw32124; decide +kernel
    rw [ha]
    exact (canonical32124 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2348 + difference 0 2) (sourceB2348 + difference 2 0) sourceC2348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5401) := by
    have ha : (tripleCharges (sourceA2348 + difference 0 2) (sourceB2348 + difference 2 0) sourceC2348) = raw32125 := by
      apply Matrix.ext; unfold tripleCharges sourceA2348 sourceB2348 sourceC2348 difference raw32125; decide +kernel
    rw [ha]
    exact (canonical32125 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2348 + difference 0 3) (sourceB2348 + difference 3 0) sourceC2348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA2348 + difference 0 3) (sourceB2348 + difference 3 0) sourceC2348) = raw32126 := by
      apply Matrix.ext; unfold tripleCharges sourceA2348 sourceB2348 sourceC2348 difference raw32126; decide +kernel
    rw [ha]
    exact (canonical32126 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2348 + difference 0 4) (sourceB2348 + difference 4 0) sourceC2348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5410) := by
    have ha : (tripleCharges (sourceA2348 + difference 0 4) (sourceB2348 + difference 4 0) sourceC2348) = raw32127 := by
      apply Matrix.ext; unfold tripleCharges sourceA2348 sourceB2348 sourceC2348 difference raw32127; decide +kernel
    rw [ha]
    exact (canonical32127 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2348 + difference 0 5) (sourceB2348 + difference 5 0) sourceC2348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5484) := by
    have ha : (tripleCharges (sourceA2348 + difference 0 5) (sourceB2348 + difference 5 0) sourceC2348) = raw32128 := by
      apply Matrix.ext; unfold tripleCharges sourceA2348 sourceB2348 sourceC2348 difference raw32128; decide +kernel
    rw [ha]
    exact (canonical32128 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2348 + difference 1 0) (sourceB2348 + difference 0 1) sourceC2348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4459) := by
    have ha : (tripleCharges (sourceA2348 + difference 1 0) (sourceB2348 + difference 0 1) sourceC2348) = raw32129 := by
      apply Matrix.ext; unfold tripleCharges sourceA2348 sourceB2348 sourceC2348 difference raw32129; decide +kernel
    rw [ha]
    exact (canonical32129 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2348 + difference 1 2) (sourceB2348 + difference 2 1) sourceC2348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5074) := by
    have ha : (tripleCharges (sourceA2348 + difference 1 2) (sourceB2348 + difference 2 1) sourceC2348) = raw32130 := by
      apply Matrix.ext; unfold tripleCharges sourceA2348 sourceB2348 sourceC2348 difference raw32130; decide +kernel
    rw [ha]
    exact (canonical32130 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2348 + difference 1 3) (sourceB2348 + difference 3 1) sourceC2348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5260) := by
    have ha : (tripleCharges (sourceA2348 + difference 1 3) (sourceB2348 + difference 3 1) sourceC2348) = raw32131 := by
      apply Matrix.ext; unfold tripleCharges sourceA2348 sourceB2348 sourceC2348 difference raw32131; decide +kernel
    rw [ha]
    exact (canonical32131 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2348 + difference 1 4) (sourceB2348 + difference 4 1) sourceC2348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA2348 + difference 1 4) (sourceB2348 + difference 4 1) sourceC2348) = raw32132 := by
      apply Matrix.ext; unfold tripleCharges sourceA2348 sourceB2348 sourceC2348 difference raw32132; decide +kernel
    rw [ha]
    exact (canonical32132 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2348 + difference 1 5) (sourceB2348 + difference 5 1) sourceC2348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA2348 + difference 1 5) (sourceB2348 + difference 5 1) sourceC2348) = raw32133 := by
      apply Matrix.ext; unfold tripleCharges sourceA2348 sourceB2348 sourceC2348 difference raw32133; decide +kernel
    rw [ha]
    exact (canonical32133 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2348 + difference 2 0) (sourceB2348 + difference 0 2) sourceC2348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4345) := by
    have ha : (tripleCharges (sourceA2348 + difference 2 0) (sourceB2348 + difference 0 2) sourceC2348) = raw32134 := by
      apply Matrix.ext; unfold tripleCharges sourceA2348 sourceB2348 sourceC2348 difference raw32134; decide +kernel
    rw [ha]
    exact (canonical32134 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2348 + difference 2 1) (sourceB2348 + difference 1 2) sourceC2348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4942) := by
    have ha : (tripleCharges (sourceA2348 + difference 2 1) (sourceB2348 + difference 1 2) sourceC2348) = raw32135 := by
      apply Matrix.ext; unfold tripleCharges sourceA2348 sourceB2348 sourceC2348 difference raw32135; decide +kernel
    rw [ha]
    exact (canonical32135 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2348 + difference 2 3) (sourceB2348 + difference 3 2) sourceC2348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5138) := by
    have ha : (tripleCharges (sourceA2348 + difference 2 3) (sourceB2348 + difference 3 2) sourceC2348) = raw32136 := by
      apply Matrix.ext; unfold tripleCharges sourceA2348 sourceB2348 sourceC2348 difference raw32136; decide +kernel
    rw [ha]
    exact (canonical32136 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2348 + difference 2 4) (sourceB2348 + difference 4 2) sourceC2348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5149) := by
    have ha : (tripleCharges (sourceA2348 + difference 2 4) (sourceB2348 + difference 4 2) sourceC2348) = raw32137 := by
      apply Matrix.ext; unfold tripleCharges sourceA2348 sourceB2348 sourceC2348 difference raw32137; decide +kernel
    rw [ha]
    exact (canonical32137 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2348 + difference 2 5) (sourceB2348 + difference 5 2) sourceC2348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5160) := by
    have ha : (tripleCharges (sourceA2348 + difference 2 5) (sourceB2348 + difference 5 2) sourceC2348) = raw32138 := by
      apply Matrix.ext; unfold tripleCharges sourceA2348 sourceB2348 sourceC2348 difference raw32138; decide +kernel
    rw [ha]
    exact (canonical32138 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2348 + difference 3 0) (sourceB2348 + difference 0 3) sourceC2348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4357) := by
    have ha : (tripleCharges (sourceA2348 + difference 3 0) (sourceB2348 + difference 0 3) sourceC2348) = raw32139 := by
      apply Matrix.ext; unfold tripleCharges sourceA2348 sourceB2348 sourceC2348 difference raw32139; decide +kernel
    rw [ha]
    exact (canonical32139 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2348 + difference 3 1) (sourceB2348 + difference 1 3) sourceC2348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4951) := by
    have ha : (tripleCharges (sourceA2348 + difference 3 1) (sourceB2348 + difference 1 3) sourceC2348) = raw32140 := by
      apply Matrix.ext; unfold tripleCharges sourceA2348 sourceB2348 sourceC2348 difference raw32140; decide +kernel
    rw [ha]
    exact (canonical32140 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2348 + difference 3 2) (sourceB2348 + difference 2 3) sourceC2348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5040) := by
    have ha : (tripleCharges (sourceA2348 + difference 3 2) (sourceB2348 + difference 2 3) sourceC2348) = raw32141 := by
      apply Matrix.ext; unfold tripleCharges sourceA2348 sourceB2348 sourceC2348 difference raw32141; decide +kernel
    rw [ha]
    exact (canonical32141 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2348 + difference 3 4) (sourceB2348 + difference 4 3) sourceC2348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5152) := by
    have ha : (tripleCharges (sourceA2348 + difference 3 4) (sourceB2348 + difference 4 3) sourceC2348) = raw32142 := by
      apply Matrix.ext; unfold tripleCharges sourceA2348 sourceB2348 sourceC2348 difference raw32142; decide +kernel
    rw [ha]
    exact (canonical32142 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2348 + difference 3 5) (sourceB2348 + difference 5 3) sourceC2348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5164) := by
    have ha : (tripleCharges (sourceA2348 + difference 3 5) (sourceB2348 + difference 5 3) sourceC2348) = raw32143 := by
      apply Matrix.ext; unfold tripleCharges sourceA2348 sourceB2348 sourceC2348 difference raw32143; decide +kernel
    rw [ha]
    exact (canonical32143 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2348 + difference 4 0) (sourceB2348 + difference 0 4) sourceC2348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4348) := by
    have ha : (tripleCharges (sourceA2348 + difference 4 0) (sourceB2348 + difference 0 4) sourceC2348) = raw32144 := by
      apply Matrix.ext; unfold tripleCharges sourceA2348 sourceB2348 sourceC2348 difference raw32144; decide +kernel
    rw [ha]
    exact (canonical32144 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2348 + difference 4 1) (sourceB2348 + difference 1 4) sourceC2348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4945) := by
    have ha : (tripleCharges (sourceA2348 + difference 4 1) (sourceB2348 + difference 1 4) sourceC2348) = raw32145 := by
      apply Matrix.ext; unfold tripleCharges sourceA2348 sourceB2348 sourceC2348 difference raw32145; decide +kernel
    rw [ha]
    exact (canonical32145 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2348 + difference 4 2) (sourceB2348 + difference 2 4) sourceC2348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5035) := by
    have ha : (tripleCharges (sourceA2348 + difference 4 2) (sourceB2348 + difference 2 4) sourceC2348) = raw32146 := by
      apply Matrix.ext; unfold tripleCharges sourceA2348 sourceB2348 sourceC2348 difference raw32146; decide +kernel
    rw [ha]
    exact (canonical32146 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2348 + difference 4 3) (sourceB2348 + difference 3 4) sourceC2348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5140) := by
    have ha : (tripleCharges (sourceA2348 + difference 4 3) (sourceB2348 + difference 3 4) sourceC2348) = raw32147 := by
      apply Matrix.ext; unfold tripleCharges sourceA2348 sourceB2348 sourceC2348 difference raw32147; decide +kernel
    rw [ha]
    exact (canonical32147 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2348 + difference 4 5) (sourceB2348 + difference 5 4) sourceC2348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5161) := by
    have ha : (tripleCharges (sourceA2348 + difference 4 5) (sourceB2348 + difference 5 4) sourceC2348) = raw32148 := by
      apply Matrix.ext; unfold tripleCharges sourceA2348 sourceB2348 sourceC2348 difference raw32148; decide +kernel
    rw [ha]
    exact (canonical32148 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2348 + difference 5 0) (sourceB2348 + difference 0 5) sourceC2348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4347) := by
    have ha : (tripleCharges (sourceA2348 + difference 5 0) (sourceB2348 + difference 0 5) sourceC2348) = raw32149 := by
      apply Matrix.ext; unfold tripleCharges sourceA2348 sourceB2348 sourceC2348 difference raw32149; decide +kernel
    rw [ha]
    exact (canonical32149 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2348 + difference 5 1) (sourceB2348 + difference 1 5) sourceC2348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4944) := by
    have ha : (tripleCharges (sourceA2348 + difference 5 1) (sourceB2348 + difference 1 5) sourceC2348) = raw32150 := by
      apply Matrix.ext; unfold tripleCharges sourceA2348 sourceB2348 sourceC2348 difference raw32150; decide +kernel
    rw [ha]
    exact (canonical32150 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2348 + difference 5 2) (sourceB2348 + difference 2 5) sourceC2348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5034) := by
    have ha : (tripleCharges (sourceA2348 + difference 5 2) (sourceB2348 + difference 2 5) sourceC2348) = raw32151 := by
      apply Matrix.ext; unfold tripleCharges sourceA2348 sourceB2348 sourceC2348 difference raw32151; decide +kernel
    rw [ha]
    exact (canonical32151 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2348 + difference 5 3) (sourceB2348 + difference 3 5) sourceC2348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5139) := by
    have ha : (tripleCharges (sourceA2348 + difference 5 3) (sourceB2348 + difference 3 5) sourceC2348) = raw32152 := by
      apply Matrix.ext; unfold tripleCharges sourceA2348 sourceB2348 sourceC2348 difference raw32152; decide +kernel
    rw [ha]
    exact (canonical32152 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2348 + difference 5 4) (sourceB2348 + difference 4 5) sourceC2348) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5078) := by
    have ha : (tripleCharges (sourceA2348 + difference 5 4) (sourceB2348 + difference 4 5) sourceC2348) = raw32153 := by
      apply Matrix.ext; unfold tripleCharges sourceA2348 sourceB2348 sourceC2348 difference raw32153; decide +kernel
    rw [ha]
    exact (canonical32153 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2348 sourceB2348 sourceC2348
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2348, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2349 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2349 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC2349 : Charge := ![1, 1, 0, -1, 1, -2]
def sourceForm2349 : Integer.Sparse Master := [(Sum.inr 1668, 1), (Sum.inr 1669, 1), (Sum.inr 1676, 1), (Sum.inr 1682, 1), (Sum.inr 1714, 1), (Sum.inr 2652, 1), (Sum.inr 2658, 1), (Sum.inr 2670, 1), (Sum.inr 2719, 1), (Sum.inr 3407, 1), (Sum.inr 3413, 1), (Sum.inr 3418, 1), (Sum.inr 3451, 1), (Sum.inr 3454, 1), (Sum.inr 3463, 1), (Sum.inr 3481, 1), (Sum.inr 3517, 1), (Sum.inr 3523, 1), (Sum.inr 3540, 1), (Sum.inr 3558, 1), (Sum.inr 3565, 1), (Sum.inr 3572, 1), (Sum.inr 3605, 1), (Sum.inr 3612, 1), (Sum.inr 3625, 1), (Sum.inr 3804, 1), (Sum.inr 3815, 1), (Sum.inr 3816, 1), (Sum.inr 3857, 1), (Sum.inr 3983, 1)]

theorem sourceEq2349 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2349 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2349 + difference 0 1) (sourceB2349 + difference 1 0) sourceC2349) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3815) := by
    have ha : (tripleCharges (sourceA2349 + difference 0 1) (sourceB2349 + difference 1 0) sourceC2349) = raw32154 := by
      apply Matrix.ext; unfold tripleCharges sourceA2349 sourceB2349 sourceC2349 difference raw32154; decide +kernel
    rw [ha]
    exact (canonical32154 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2349 + difference 0 2) (sourceB2349 + difference 2 0) sourceC2349) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3804) := by
    have ha : (tripleCharges (sourceA2349 + difference 0 2) (sourceB2349 + difference 2 0) sourceC2349) = raw32155 := by
      apply Matrix.ext; unfold tripleCharges sourceA2349 sourceB2349 sourceC2349 difference raw32155; decide +kernel
    rw [ha]
    exact (canonical32155 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2349 + difference 0 3) (sourceB2349 + difference 3 0) sourceC2349) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3857) := by
    have ha : (tripleCharges (sourceA2349 + difference 0 3) (sourceB2349 + difference 3 0) sourceC2349) = raw32156 := by
      apply Matrix.ext; unfold tripleCharges sourceA2349 sourceB2349 sourceC2349 difference raw32156; decide +kernel
    rw [ha]
    exact (canonical32156 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2349 + difference 0 4) (sourceB2349 + difference 4 0) sourceC2349) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3816) := by
    have ha : (tripleCharges (sourceA2349 + difference 0 4) (sourceB2349 + difference 4 0) sourceC2349) = raw32157 := by
      apply Matrix.ext; unfold tripleCharges sourceA2349 sourceB2349 sourceC2349 difference raw32157; decide +kernel
    rw [ha]
    exact (canonical32157 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2349 + difference 0 5) (sourceB2349 + difference 5 0) sourceC2349) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3983) := by
    have ha : (tripleCharges (sourceA2349 + difference 0 5) (sourceB2349 + difference 5 0) sourceC2349) = raw32158 := by
      apply Matrix.ext; unfold tripleCharges sourceA2349 sourceB2349 sourceC2349 difference raw32158; decide +kernel
    rw [ha]
    exact (canonical32158 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2349 + difference 1 0) (sourceB2349 + difference 0 1) sourceC2349) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1714) := by
    have ha : (tripleCharges (sourceA2349 + difference 1 0) (sourceB2349 + difference 0 1) sourceC2349) = raw32159 := by
      apply Matrix.ext; unfold tripleCharges sourceA2349 sourceB2349 sourceC2349 difference raw32159; decide +kernel
    rw [ha]
    exact (canonical32159 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2349 + difference 1 2) (sourceB2349 + difference 2 1) sourceC2349) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3463) := by
    have ha : (tripleCharges (sourceA2349 + difference 1 2) (sourceB2349 + difference 2 1) sourceC2349) = raw32160 := by
      apply Matrix.ext; unfold tripleCharges sourceA2349 sourceB2349 sourceC2349 difference raw32160; decide +kernel
    rw [ha]
    exact (canonical32160 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2349 + difference 1 3) (sourceB2349 + difference 3 1) sourceC2349) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3540) := by
    have ha : (tripleCharges (sourceA2349 + difference 1 3) (sourceB2349 + difference 3 1) sourceC2349) = raw32161 := by
      apply Matrix.ext; unfold tripleCharges sourceA2349 sourceB2349 sourceC2349 difference raw32161; decide +kernel
    rw [ha]
    exact (canonical32161 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2349 + difference 1 4) (sourceB2349 + difference 4 1) sourceC2349) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3625) := by
    have ha : (tripleCharges (sourceA2349 + difference 1 4) (sourceB2349 + difference 4 1) sourceC2349) = raw32162 := by
      apply Matrix.ext; unfold tripleCharges sourceA2349 sourceB2349 sourceC2349 difference raw32162; decide +kernel
    rw [ha]
    exact (canonical32162 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2349 + difference 1 5) (sourceB2349 + difference 5 1) sourceC2349) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA2349 + difference 1 5) (sourceB2349 + difference 5 1) sourceC2349) = raw32163 := by
      apply Matrix.ext; unfold tripleCharges sourceA2349 sourceB2349 sourceC2349 difference raw32163; decide +kernel
    rw [ha]
    exact (canonical32163 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2349 + difference 2 0) (sourceB2349 + difference 0 2) sourceC2349) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1668) := by
    have ha : (tripleCharges (sourceA2349 + difference 2 0) (sourceB2349 + difference 0 2) sourceC2349) = raw32164 := by
      apply Matrix.ext; unfold tripleCharges sourceA2349 sourceB2349 sourceC2349 difference raw32164; decide +kernel
    rw [ha]
    exact (canonical32164 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2349 + difference 2 1) (sourceB2349 + difference 1 2) sourceC2349) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3407) := by
    have ha : (tripleCharges (sourceA2349 + difference 2 1) (sourceB2349 + difference 1 2) sourceC2349) = raw32165 := by
      apply Matrix.ext; unfold tripleCharges sourceA2349 sourceB2349 sourceC2349 difference raw32165; decide +kernel
    rw [ha]
    exact (canonical32165 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2349 + difference 2 3) (sourceB2349 + difference 3 2) sourceC2349) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3517) := by
    have ha : (tripleCharges (sourceA2349 + difference 2 3) (sourceB2349 + difference 3 2) sourceC2349) = raw32166 := by
      apply Matrix.ext; unfold tripleCharges sourceA2349 sourceB2349 sourceC2349 difference raw32166; decide +kernel
    rw [ha]
    exact (canonical32166 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2349 + difference 2 4) (sourceB2349 + difference 4 2) sourceC2349) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3605) := by
    have ha : (tripleCharges (sourceA2349 + difference 2 4) (sourceB2349 + difference 4 2) sourceC2349) = raw32167 := by
      apply Matrix.ext; unfold tripleCharges sourceA2349 sourceB2349 sourceC2349 difference raw32167; decide +kernel
    rw [ha]
    exact (canonical32167 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2349 + difference 2 5) (sourceB2349 + difference 5 2) sourceC2349) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3558) := by
    have ha : (tripleCharges (sourceA2349 + difference 2 5) (sourceB2349 + difference 5 2) sourceC2349) = raw32168 := by
      apply Matrix.ext; unfold tripleCharges sourceA2349 sourceB2349 sourceC2349 difference raw32168; decide +kernel
    rw [ha]
    exact (canonical32168 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2349 + difference 3 0) (sourceB2349 + difference 0 3) sourceC2349) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1682) := by
    have ha : (tripleCharges (sourceA2349 + difference 3 0) (sourceB2349 + difference 0 3) sourceC2349) = raw32169 := by
      apply Matrix.ext; unfold tripleCharges sourceA2349 sourceB2349 sourceC2349 difference raw32169; decide +kernel
    rw [ha]
    exact (canonical32169 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2349 + difference 3 1) (sourceB2349 + difference 1 3) sourceC2349) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3418) := by
    have ha : (tripleCharges (sourceA2349 + difference 3 1) (sourceB2349 + difference 1 3) sourceC2349) = raw32170 := by
      apply Matrix.ext; unfold tripleCharges sourceA2349 sourceB2349 sourceC2349 difference raw32170; decide +kernel
    rw [ha]
    exact (canonical32170 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2349 + difference 3 2) (sourceB2349 + difference 2 3) sourceC2349) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3454) := by
    have ha : (tripleCharges (sourceA2349 + difference 3 2) (sourceB2349 + difference 2 3) sourceC2349) = raw32171 := by
      apply Matrix.ext; unfold tripleCharges sourceA2349 sourceB2349 sourceC2349 difference raw32171; decide +kernel
    rw [ha]
    exact (canonical32171 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2349 + difference 3 4) (sourceB2349 + difference 4 3) sourceC2349) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3612) := by
    have ha : (tripleCharges (sourceA2349 + difference 3 4) (sourceB2349 + difference 4 3) sourceC2349) = raw32172 := by
      apply Matrix.ext; unfold tripleCharges sourceA2349 sourceB2349 sourceC2349 difference raw32172; decide +kernel
    rw [ha]
    exact (canonical32172 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2349 + difference 3 5) (sourceB2349 + difference 5 3) sourceC2349) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3565) := by
    have ha : (tripleCharges (sourceA2349 + difference 3 5) (sourceB2349 + difference 5 3) sourceC2349) = raw32173 := by
      apply Matrix.ext; unfold tripleCharges sourceA2349 sourceB2349 sourceC2349 difference raw32173; decide +kernel
    rw [ha]
    exact (canonical32173 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2349 + difference 4 0) (sourceB2349 + difference 0 4) sourceC2349) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1669) := by
    have ha : (tripleCharges (sourceA2349 + difference 4 0) (sourceB2349 + difference 0 4) sourceC2349) = raw32174 := by
      apply Matrix.ext; unfold tripleCharges sourceA2349 sourceB2349 sourceC2349 difference raw32174; decide +kernel
    rw [ha]
    exact (canonical32174 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2349 + difference 4 1) (sourceB2349 + difference 1 4) sourceC2349) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2658) := by
    have ha : (tripleCharges (sourceA2349 + difference 4 1) (sourceB2349 + difference 1 4) sourceC2349) = raw32175 := by
      apply Matrix.ext; unfold tripleCharges sourceA2349 sourceB2349 sourceC2349 difference raw32175; decide +kernel
    rw [ha]
    exact (canonical32175 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2349 + difference 4 2) (sourceB2349 + difference 2 4) sourceC2349) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2652) := by
    have ha : (tripleCharges (sourceA2349 + difference 4 2) (sourceB2349 + difference 2 4) sourceC2349) = raw32176 := by
      apply Matrix.ext; unfold tripleCharges sourceA2349 sourceB2349 sourceC2349 difference raw32176; decide +kernel
    rw [ha]
    exact (canonical32176 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2349 + difference 4 3) (sourceB2349 + difference 3 4) sourceC2349) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2670) := by
    have ha : (tripleCharges (sourceA2349 + difference 4 3) (sourceB2349 + difference 3 4) sourceC2349) = raw32177 := by
      apply Matrix.ext; unfold tripleCharges sourceA2349 sourceB2349 sourceC2349 difference raw32177; decide +kernel
    rw [ha]
    exact (canonical32177 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2349 + difference 4 5) (sourceB2349 + difference 5 4) sourceC2349) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2719) := by
    have ha : (tripleCharges (sourceA2349 + difference 4 5) (sourceB2349 + difference 5 4) sourceC2349) = raw32178 := by
      apply Matrix.ext; unfold tripleCharges sourceA2349 sourceB2349 sourceC2349 difference raw32178; decide +kernel
    rw [ha]
    exact (canonical32178 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2349 + difference 5 0) (sourceB2349 + difference 0 5) sourceC2349) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1676) := by
    have ha : (tripleCharges (sourceA2349 + difference 5 0) (sourceB2349 + difference 0 5) sourceC2349) = raw32179 := by
      apply Matrix.ext; unfold tripleCharges sourceA2349 sourceB2349 sourceC2349 difference raw32179; decide +kernel
    rw [ha]
    exact (canonical32179 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2349 + difference 5 1) (sourceB2349 + difference 1 5) sourceC2349) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3413) := by
    have ha : (tripleCharges (sourceA2349 + difference 5 1) (sourceB2349 + difference 1 5) sourceC2349) = raw32180 := by
      apply Matrix.ext; unfold tripleCharges sourceA2349 sourceB2349 sourceC2349 difference raw32180; decide +kernel
    rw [ha]
    exact (canonical32180 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2349 + difference 5 2) (sourceB2349 + difference 2 5) sourceC2349) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3451) := by
    have ha : (tripleCharges (sourceA2349 + difference 5 2) (sourceB2349 + difference 2 5) sourceC2349) = raw32181 := by
      apply Matrix.ext; unfold tripleCharges sourceA2349 sourceB2349 sourceC2349 difference raw32181; decide +kernel
    rw [ha]
    exact (canonical32181 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2349 + difference 5 3) (sourceB2349 + difference 3 5) sourceC2349) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3523) := by
    have ha : (tripleCharges (sourceA2349 + difference 5 3) (sourceB2349 + difference 3 5) sourceC2349) = raw32182 := by
      apply Matrix.ext; unfold tripleCharges sourceA2349 sourceB2349 sourceC2349 difference raw32182; decide +kernel
    rw [ha]
    exact (canonical32182 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2349 + difference 5 4) (sourceB2349 + difference 4 5) sourceC2349) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3481) := by
    have ha : (tripleCharges (sourceA2349 + difference 5 4) (sourceB2349 + difference 4 5) sourceC2349) = raw32183 := by
      apply Matrix.ext; unfold tripleCharges sourceA2349 sourceB2349 sourceC2349 difference raw32183; decide +kernel
    rw [ha]
    exact (canonical32183 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2349 sourceB2349 sourceC2349
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2349, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2350 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2350 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC2350 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceForm2350 : Integer.Sparse Master := [(Sum.inr 4541, 1), (Sum.inr 4543, 1), (Sum.inr 4549, 2), (Sum.inr 4623, 1), (Sum.inr 4764, 1), (Sum.inr 4770, 1), (Sum.inr 4807, 2), (Sum.inr 4971, 1), (Sum.inr 4977, 2), (Sum.inr 5117, 2), (Sum.inr 5149, 2), (Sum.inr 5152, 2), (Sum.inr 5167, 1), (Sum.inr 5169, 2), (Sum.inr 5172, 1), (Sum.inr 5294, 2), (Sum.inr 5307, 1), (Sum.inr 5387, 1), (Sum.inr 5417, 1), (Sum.inr 5435, 2), (Sum.inr 5440, 1)]

theorem sourceEq2350 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2350 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2350 + difference 0 1) (sourceB2350 + difference 1 0) sourceC2350) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5387) := by
    have ha : (tripleCharges (sourceA2350 + difference 0 1) (sourceB2350 + difference 1 0) sourceC2350) = raw15174 := by
      apply Matrix.ext; unfold tripleCharges sourceA2350 sourceB2350 sourceC2350 difference raw15174; decide +kernel
    rw [ha]
    exact (canonical15174 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2350 + difference 0 2) (sourceB2350 + difference 2 0) sourceC2350) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5417) := by
    have ha : (tripleCharges (sourceA2350 + difference 0 2) (sourceB2350 + difference 2 0) sourceC2350) = raw15175 := by
      apply Matrix.ext; unfold tripleCharges sourceA2350 sourceB2350 sourceC2350 difference raw15175; decide +kernel
    rw [ha]
    exact (canonical15175 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2350 + difference 0 3) (sourceB2350 + difference 3 0) sourceC2350) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA2350 + difference 0 3) (sourceB2350 + difference 3 0) sourceC2350) = raw2682 := by
      apply Matrix.ext; unfold tripleCharges sourceA2350 sourceB2350 sourceC2350 difference raw2682; decide +kernel
    rw [ha]
    exact (canonical2682 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2350 + difference 0 4) (sourceB2350 + difference 4 0) sourceC2350) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA2350 + difference 0 4) (sourceB2350 + difference 4 0) sourceC2350) = raw2677 := by
      apply Matrix.ext; unfold tripleCharges sourceA2350 sourceB2350 sourceC2350 difference raw2677; decide +kernel
    rw [ha]
    exact (canonical2677 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2350 + difference 0 5) (sourceB2350 + difference 5 0) sourceC2350) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5440) := by
    have ha : (tripleCharges (sourceA2350 + difference 0 5) (sourceB2350 + difference 5 0) sourceC2350) = raw14053 := by
      apply Matrix.ext; unfold tripleCharges sourceA2350 sourceB2350 sourceC2350 difference raw14053; decide +kernel
    rw [ha]
    exact (canonical14053 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2350 + difference 1 0) (sourceB2350 + difference 0 1) sourceC2350) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4623) := by
    have ha : (tripleCharges (sourceA2350 + difference 1 0) (sourceB2350 + difference 0 1) sourceC2350) = raw7976 := by
      apply Matrix.ext; unfold tripleCharges sourceA2350 sourceB2350 sourceC2350 difference raw7976; decide +kernel
    rw [ha]
    exact (canonical7976 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2350 + difference 1 2) (sourceB2350 + difference 2 1) sourceC2350) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5172) := by
    have ha : (tripleCharges (sourceA2350 + difference 1 2) (sourceB2350 + difference 2 1) sourceC2350) = raw7978 := by
      apply Matrix.ext; unfold tripleCharges sourceA2350 sourceB2350 sourceC2350 difference raw7978; decide +kernel
    rw [ha]
    exact (canonical7978 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2350 + difference 1 3) (sourceB2350 + difference 3 1) sourceC2350) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA2350 + difference 1 3) (sourceB2350 + difference 3 1) sourceC2350) = raw2681 := by
      apply Matrix.ext; unfold tripleCharges sourceA2350 sourceB2350 sourceC2350 difference raw2681; decide +kernel
    rw [ha]
    exact (canonical2681 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2350 + difference 1 4) (sourceB2350 + difference 4 1) sourceC2350) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA2350 + difference 1 4) (sourceB2350 + difference 4 1) sourceC2350) = raw2676 := by
      apply Matrix.ext; unfold tripleCharges sourceA2350 sourceB2350 sourceC2350 difference raw2676; decide +kernel
    rw [ha]
    exact (canonical2676 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2350 + difference 1 5) (sourceB2350 + difference 5 1) sourceC2350) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5307) := by
    have ha : (tripleCharges (sourceA2350 + difference 1 5) (sourceB2350 + difference 5 1) sourceC2350) = raw7979 := by
      apply Matrix.ext; unfold tripleCharges sourceA2350 sourceB2350 sourceC2350 difference raw7979; decide +kernel
    rw [ha]
    exact (canonical7979 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2350 + difference 2 0) (sourceB2350 + difference 0 2) sourceC2350) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4541) := by
    have ha : (tripleCharges (sourceA2350 + difference 2 0) (sourceB2350 + difference 0 2) sourceC2350) = raw24126 := by
      apply Matrix.ext; unfold tripleCharges sourceA2350 sourceB2350 sourceC2350 difference raw24126; decide +kernel
    rw [ha]
    exact (canonical24126 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2350 + difference 2 1) (sourceB2350 + difference 1 2) sourceC2350) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4971) := by
    have ha : (tripleCharges (sourceA2350 + difference 2 1) (sourceB2350 + difference 1 2) sourceC2350) = raw32184 := by
      apply Matrix.ext; unfold tripleCharges sourceA2350 sourceB2350 sourceC2350 difference raw32184; decide +kernel
    rw [ha]
    exact (canonical32184 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2350 + difference 2 3) (sourceB2350 + difference 3 2) sourceC2350) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5149) := by
    have ha : (tripleCharges (sourceA2350 + difference 2 3) (sourceB2350 + difference 3 2) sourceC2350) = raw7973 := by
      apply Matrix.ext; unfold tripleCharges sourceA2350 sourceB2350 sourceC2350 difference raw7973; decide +kernel
    rw [ha]
    exact (canonical7973 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2350 + difference 2 4) (sourceB2350 + difference 4 2) sourceC2350) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5149) := by
    have ha : (tripleCharges (sourceA2350 + difference 2 4) (sourceB2350 + difference 4 2) sourceC2350) = raw32185 := by
      apply Matrix.ext; unfold tripleCharges sourceA2350 sourceB2350 sourceC2350 difference raw32185; decide +kernel
    rw [ha]
    exact (canonical32185 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2350 + difference 2 5) (sourceB2350 + difference 5 2) sourceC2350) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5167) := by
    have ha : (tripleCharges (sourceA2350 + difference 2 5) (sourceB2350 + difference 5 2) sourceC2350) = raw14061 := by
      apply Matrix.ext; unfold tripleCharges sourceA2350 sourceB2350 sourceC2350 difference raw14061; decide +kernel
    rw [ha]
    exact (canonical14061 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2350 + difference 3 0) (sourceB2350 + difference 0 3) sourceC2350) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4549) := by
    have ha : (tripleCharges (sourceA2350 + difference 3 0) (sourceB2350 + difference 0 3) sourceC2350) = raw24129 := by
      apply Matrix.ext; unfold tripleCharges sourceA2350 sourceB2350 sourceC2350 difference raw24129; decide +kernel
    rw [ha]
    exact (canonical24129 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2350 + difference 3 1) (sourceB2350 + difference 1 3) sourceC2350) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4977) := by
    have ha : (tripleCharges (sourceA2350 + difference 3 1) (sourceB2350 + difference 1 3) sourceC2350) = raw32186 := by
      apply Matrix.ext; unfold tripleCharges sourceA2350 sourceB2350 sourceC2350 difference raw32186; decide +kernel
    rw [ha]
    exact (canonical32186 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2350 + difference 3 2) (sourceB2350 + difference 2 3) sourceC2350) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5117) := by
    have ha : (tripleCharges (sourceA2350 + difference 3 2) (sourceB2350 + difference 2 3) sourceC2350) = raw32187 := by
      apply Matrix.ext; unfold tripleCharges sourceA2350 sourceB2350 sourceC2350 difference raw32187; decide +kernel
    rw [ha]
    exact (canonical32187 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2350 + difference 3 4) (sourceB2350 + difference 4 3) sourceC2350) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5152) := by
    have ha : (tripleCharges (sourceA2350 + difference 3 4) (sourceB2350 + difference 4 3) sourceC2350) = raw32188 := by
      apply Matrix.ext; unfold tripleCharges sourceA2350 sourceB2350 sourceC2350 difference raw32188; decide +kernel
    rw [ha]
    exact (canonical32188 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2350 + difference 3 5) (sourceB2350 + difference 5 3) sourceC2350) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA2350 + difference 3 5) (sourceB2350 + difference 5 3) sourceC2350) = raw14065 := by
      apply Matrix.ext; unfold tripleCharges sourceA2350 sourceB2350 sourceC2350 difference raw14065; decide +kernel
    rw [ha]
    exact (canonical14065 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2350 + difference 4 0) (sourceB2350 + difference 0 4) sourceC2350) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4549) := by
    have ha : (tripleCharges (sourceA2350 + difference 4 0) (sourceB2350 + difference 0 4) sourceC2350) = raw24133 := by
      apply Matrix.ext; unfold tripleCharges sourceA2350 sourceB2350 sourceC2350 difference raw24133; decide +kernel
    rw [ha]
    exact (canonical24133 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2350 + difference 4 1) (sourceB2350 + difference 1 4) sourceC2350) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4977) := by
    have ha : (tripleCharges (sourceA2350 + difference 4 1) (sourceB2350 + difference 1 4) sourceC2350) = raw32189 := by
      apply Matrix.ext; unfold tripleCharges sourceA2350 sourceB2350 sourceC2350 difference raw32189; decide +kernel
    rw [ha]
    exact (canonical32189 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2350 + difference 4 2) (sourceB2350 + difference 2 4) sourceC2350) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5117) := by
    have ha : (tripleCharges (sourceA2350 + difference 4 2) (sourceB2350 + difference 2 4) sourceC2350) = raw32190 := by
      apply Matrix.ext; unfold tripleCharges sourceA2350 sourceB2350 sourceC2350 difference raw32190; decide +kernel
    rw [ha]
    exact (canonical32190 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2350 + difference 4 3) (sourceB2350 + difference 3 4) sourceC2350) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5152) := by
    have ha : (tripleCharges (sourceA2350 + difference 4 3) (sourceB2350 + difference 3 4) sourceC2350) = raw7981 := by
      apply Matrix.ext; unfold tripleCharges sourceA2350 sourceB2350 sourceC2350 difference raw7981; decide +kernel
    rw [ha]
    exact (canonical7981 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2350 + difference 4 5) (sourceB2350 + difference 5 4) sourceC2350) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA2350 + difference 4 5) (sourceB2350 + difference 5 4) sourceC2350) = raw14070 := by
      apply Matrix.ext; unfold tripleCharges sourceA2350 sourceB2350 sourceC2350 difference raw14070; decide +kernel
    rw [ha]
    exact (canonical14070 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2350 + difference 5 0) (sourceB2350 + difference 0 5) sourceC2350) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4543) := by
    have ha : (tripleCharges (sourceA2350 + difference 5 0) (sourceB2350 + difference 0 5) sourceC2350) = raw20937 := by
      apply Matrix.ext; unfold tripleCharges sourceA2350 sourceB2350 sourceC2350 difference raw20937; decide +kernel
    rw [ha]
    exact (canonical20937 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2350 + difference 5 1) (sourceB2350 + difference 1 5) sourceC2350) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4770) := by
    have ha : (tripleCharges (sourceA2350 + difference 5 1) (sourceB2350 + difference 1 5) sourceC2350) = raw28002 := by
      apply Matrix.ext; unfold tripleCharges sourceA2350 sourceB2350 sourceC2350 difference raw28002; decide +kernel
    rw [ha]
    exact (canonical28002 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2350 + difference 5 2) (sourceB2350 + difference 2 5) sourceC2350) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4764) := by
    have ha : (tripleCharges (sourceA2350 + difference 5 2) (sourceB2350 + difference 2 5) sourceC2350) = raw28003 := by
      apply Matrix.ext; unfold tripleCharges sourceA2350 sourceB2350 sourceC2350 difference raw28003; decide +kernel
    rw [ha]
    exact (canonical28003 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2350 + difference 5 3) (sourceB2350 + difference 3 5) sourceC2350) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA2350 + difference 5 3) (sourceB2350 + difference 3 5) sourceC2350) = raw4618 := by
      apply Matrix.ext; unfold tripleCharges sourceA2350 sourceB2350 sourceC2350 difference raw4618; decide +kernel
    rw [ha]
    exact (canonical4618 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2350 + difference 5 4) (sourceB2350 + difference 4 5) sourceC2350) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA2350 + difference 5 4) (sourceB2350 + difference 4 5) sourceC2350) = raw4614 := by
      apply Matrix.ext; unfold tripleCharges sourceA2350 sourceB2350 sourceC2350 difference raw4614; decide +kernel
    rw [ha]
    exact (canonical4614 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2350 sourceB2350 sourceC2350
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2350, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2351 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2351 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC2351 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceForm2351 : Integer.Sparse Master := [(Sum.inr 1126, 1), (Sum.inr 1128, 1), (Sum.inr 1134, 2), (Sum.inr 1300, 1), (Sum.inr 1964, 1), (Sum.inr 1970, 1), (Sum.inr 2025, 2), (Sum.inr 2807, 1), (Sum.inr 2813, 2), (Sum.inr 2893, 2), (Sum.inr 2924, 2), (Sum.inr 2931, 2), (Sum.inr 2958, 1), (Sum.inr 2959, 1), (Sum.inr 2960, 2), (Sum.inr 3101, 2), (Sum.inr 3122, 1), (Sum.inr 3736, 1), (Sum.inr 3823, 1), (Sum.inr 3853, 2), (Sum.inr 4036, 1)]

theorem sourceEq2351 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2351 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2351 + difference 0 1) (sourceB2351 + difference 1 0) sourceC2351) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3736) := by
    have ha : (tripleCharges (sourceA2351 + difference 0 1) (sourceB2351 + difference 1 0) sourceC2351) = raw15190 := by
      apply Matrix.ext; unfold tripleCharges sourceA2351 sourceB2351 sourceC2351 difference raw15190; decide +kernel
    rw [ha]
    exact (canonical15190 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2351 + difference 0 2) (sourceB2351 + difference 2 0) sourceC2351) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3823) := by
    have ha : (tripleCharges (sourceA2351 + difference 0 2) (sourceB2351 + difference 2 0) sourceC2351) = raw15191 := by
      apply Matrix.ext; unfold tripleCharges sourceA2351 sourceB2351 sourceC2351 difference raw15191; decide +kernel
    rw [ha]
    exact (canonical15191 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2351 + difference 0 3) (sourceB2351 + difference 3 0) sourceC2351) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3853) := by
    have ha : (tripleCharges (sourceA2351 + difference 0 3) (sourceB2351 + difference 3 0) sourceC2351) = raw2712 := by
      apply Matrix.ext; unfold tripleCharges sourceA2351 sourceB2351 sourceC2351 difference raw2712; decide +kernel
    rw [ha]
    exact (canonical2712 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2351 + difference 0 4) (sourceB2351 + difference 4 0) sourceC2351) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3853) := by
    have ha : (tripleCharges (sourceA2351 + difference 0 4) (sourceB2351 + difference 4 0) sourceC2351) = raw2707 := by
      apply Matrix.ext; unfold tripleCharges sourceA2351 sourceB2351 sourceC2351 difference raw2707; decide +kernel
    rw [ha]
    exact (canonical2707 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2351 + difference 0 5) (sourceB2351 + difference 5 0) sourceC2351) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4036) := by
    have ha : (tripleCharges (sourceA2351 + difference 0 5) (sourceB2351 + difference 5 0) sourceC2351) = raw15192 := by
      apply Matrix.ext; unfold tripleCharges sourceA2351 sourceB2351 sourceC2351 difference raw15192; decide +kernel
    rw [ha]
    exact (canonical15192 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2351 + difference 1 0) (sourceB2351 + difference 0 1) sourceC2351) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1300) := by
    have ha : (tripleCharges (sourceA2351 + difference 1 0) (sourceB2351 + difference 0 1) sourceC2351) = raw7993 := by
      apply Matrix.ext; unfold tripleCharges sourceA2351 sourceB2351 sourceC2351 difference raw7993; decide +kernel
    rw [ha]
    exact (canonical7993 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2351 + difference 1 2) (sourceB2351 + difference 2 1) sourceC2351) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2959) := by
    have ha : (tripleCharges (sourceA2351 + difference 1 2) (sourceB2351 + difference 2 1) sourceC2351) = raw7995 := by
      apply Matrix.ext; unfold tripleCharges sourceA2351 sourceB2351 sourceC2351 difference raw7995; decide +kernel
    rw [ha]
    exact (canonical7995 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2351 + difference 1 3) (sourceB2351 + difference 3 1) sourceC2351) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3101) := by
    have ha : (tripleCharges (sourceA2351 + difference 1 3) (sourceB2351 + difference 3 1) sourceC2351) = raw2711 := by
      apply Matrix.ext; unfold tripleCharges sourceA2351 sourceB2351 sourceC2351 difference raw2711; decide +kernel
    rw [ha]
    exact (canonical2711 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2351 + difference 1 4) (sourceB2351 + difference 4 1) sourceC2351) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3101) := by
    have ha : (tripleCharges (sourceA2351 + difference 1 4) (sourceB2351 + difference 4 1) sourceC2351) = raw2706 := by
      apply Matrix.ext; unfold tripleCharges sourceA2351 sourceB2351 sourceC2351 difference raw2706; decide +kernel
    rw [ha]
    exact (canonical2706 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2351 + difference 1 5) (sourceB2351 + difference 5 1) sourceC2351) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3122) := by
    have ha : (tripleCharges (sourceA2351 + difference 1 5) (sourceB2351 + difference 5 1) sourceC2351) = raw7996 := by
      apply Matrix.ext; unfold tripleCharges sourceA2351 sourceB2351 sourceC2351 difference raw7996; decide +kernel
    rw [ha]
    exact (canonical7996 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2351 + difference 2 0) (sourceB2351 + difference 0 2) sourceC2351) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1126) := by
    have ha : (tripleCharges (sourceA2351 + difference 2 0) (sourceB2351 + difference 0 2) sourceC2351) = raw24140 := by
      apply Matrix.ext; unfold tripleCharges sourceA2351 sourceB2351 sourceC2351 difference raw24140; decide +kernel
    rw [ha]
    exact (canonical24140 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2351 + difference 2 1) (sourceB2351 + difference 1 2) sourceC2351) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2807) := by
    have ha : (tripleCharges (sourceA2351 + difference 2 1) (sourceB2351 + difference 1 2) sourceC2351) = raw32191 := by
      apply Matrix.ext; unfold tripleCharges sourceA2351 sourceB2351 sourceC2351 difference raw32191; decide +kernel
    rw [ha]
    exact (canonical32191 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2351 + difference 2 3) (sourceB2351 + difference 3 2) sourceC2351) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2924) := by
    have ha : (tripleCharges (sourceA2351 + difference 2 3) (sourceB2351 + difference 3 2) sourceC2351) = raw7990 := by
      apply Matrix.ext; unfold tripleCharges sourceA2351 sourceB2351 sourceC2351 difference raw7990; decide +kernel
    rw [ha]
    exact (canonical7990 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2351 + difference 2 4) (sourceB2351 + difference 4 2) sourceC2351) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2924) := by
    have ha : (tripleCharges (sourceA2351 + difference 2 4) (sourceB2351 + difference 4 2) sourceC2351) = raw32192 := by
      apply Matrix.ext; unfold tripleCharges sourceA2351 sourceB2351 sourceC2351 difference raw32192; decide +kernel
    rw [ha]
    exact (canonical32192 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2351 + difference 2 5) (sourceB2351 + difference 5 2) sourceC2351) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2958) := by
    have ha : (tripleCharges (sourceA2351 + difference 2 5) (sourceB2351 + difference 5 2) sourceC2351) = raw32193 := by
      apply Matrix.ext; unfold tripleCharges sourceA2351 sourceB2351 sourceC2351 difference raw32193; decide +kernel
    rw [ha]
    exact (canonical32193 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2351 + difference 3 0) (sourceB2351 + difference 0 3) sourceC2351) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1134) := by
    have ha : (tripleCharges (sourceA2351 + difference 3 0) (sourceB2351 + difference 0 3) sourceC2351) = raw24144 := by
      apply Matrix.ext; unfold tripleCharges sourceA2351 sourceB2351 sourceC2351 difference raw24144; decide +kernel
    rw [ha]
    exact (canonical24144 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2351 + difference 3 1) (sourceB2351 + difference 1 3) sourceC2351) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2813) := by
    have ha : (tripleCharges (sourceA2351 + difference 3 1) (sourceB2351 + difference 1 3) sourceC2351) = raw32194 := by
      apply Matrix.ext; unfold tripleCharges sourceA2351 sourceB2351 sourceC2351 difference raw32194; decide +kernel
    rw [ha]
    exact (canonical32194 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2351 + difference 3 2) (sourceB2351 + difference 2 3) sourceC2351) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2893) := by
    have ha : (tripleCharges (sourceA2351 + difference 3 2) (sourceB2351 + difference 2 3) sourceC2351) = raw32195 := by
      apply Matrix.ext; unfold tripleCharges sourceA2351 sourceB2351 sourceC2351 difference raw32195; decide +kernel
    rw [ha]
    exact (canonical32195 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2351 + difference 3 4) (sourceB2351 + difference 4 3) sourceC2351) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2931) := by
    have ha : (tripleCharges (sourceA2351 + difference 3 4) (sourceB2351 + difference 4 3) sourceC2351) = raw32196 := by
      apply Matrix.ext; unfold tripleCharges sourceA2351 sourceB2351 sourceC2351 difference raw32196; decide +kernel
    rw [ha]
    exact (canonical32196 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2351 + difference 3 5) (sourceB2351 + difference 5 3) sourceC2351) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2960) := by
    have ha : (tripleCharges (sourceA2351 + difference 3 5) (sourceB2351 + difference 5 3) sourceC2351) = raw32197 := by
      apply Matrix.ext; unfold tripleCharges sourceA2351 sourceB2351 sourceC2351 difference raw32197; decide +kernel
    rw [ha]
    exact (canonical32197 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2351 + difference 4 0) (sourceB2351 + difference 0 4) sourceC2351) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1134) := by
    have ha : (tripleCharges (sourceA2351 + difference 4 0) (sourceB2351 + difference 0 4) sourceC2351) = raw24149 := by
      apply Matrix.ext; unfold tripleCharges sourceA2351 sourceB2351 sourceC2351 difference raw24149; decide +kernel
    rw [ha]
    exact (canonical24149 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2351 + difference 4 1) (sourceB2351 + difference 1 4) sourceC2351) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2813) := by
    have ha : (tripleCharges (sourceA2351 + difference 4 1) (sourceB2351 + difference 1 4) sourceC2351) = raw32198 := by
      apply Matrix.ext; unfold tripleCharges sourceA2351 sourceB2351 sourceC2351 difference raw32198; decide +kernel
    rw [ha]
    exact (canonical32198 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2351 + difference 4 2) (sourceB2351 + difference 2 4) sourceC2351) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2893) := by
    have ha : (tripleCharges (sourceA2351 + difference 4 2) (sourceB2351 + difference 2 4) sourceC2351) = raw32199 := by
      apply Matrix.ext; unfold tripleCharges sourceA2351 sourceB2351 sourceC2351 difference raw32199; decide +kernel
    rw [ha]
    exact (canonical32199 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2351 + difference 4 3) (sourceB2351 + difference 3 4) sourceC2351) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2931) := by
    have ha : (tripleCharges (sourceA2351 + difference 4 3) (sourceB2351 + difference 3 4) sourceC2351) = raw7998 := by
      apply Matrix.ext; unfold tripleCharges sourceA2351 sourceB2351 sourceC2351 difference raw7998; decide +kernel
    rw [ha]
    exact (canonical7998 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2351 + difference 4 5) (sourceB2351 + difference 5 4) sourceC2351) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2960) := by
    have ha : (tripleCharges (sourceA2351 + difference 4 5) (sourceB2351 + difference 5 4) sourceC2351) = raw32200 := by
      apply Matrix.ext; unfold tripleCharges sourceA2351 sourceB2351 sourceC2351 difference raw32200; decide +kernel
    rw [ha]
    exact (canonical32200 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2351 + difference 5 0) (sourceB2351 + difference 0 5) sourceC2351) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1128) := by
    have ha : (tripleCharges (sourceA2351 + difference 5 0) (sourceB2351 + difference 0 5) sourceC2351) = raw20954 := by
      apply Matrix.ext; unfold tripleCharges sourceA2351 sourceB2351 sourceC2351 difference raw20954; decide +kernel
    rw [ha]
    exact (canonical20954 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2351 + difference 5 1) (sourceB2351 + difference 1 5) sourceC2351) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1970) := by
    have ha : (tripleCharges (sourceA2351 + difference 5 1) (sourceB2351 + difference 1 5) sourceC2351) = raw28012 := by
      apply Matrix.ext; unfold tripleCharges sourceA2351 sourceB2351 sourceC2351 difference raw28012; decide +kernel
    rw [ha]
    exact (canonical28012 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2351 + difference 5 2) (sourceB2351 + difference 2 5) sourceC2351) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1964) := by
    have ha : (tripleCharges (sourceA2351 + difference 5 2) (sourceB2351 + difference 2 5) sourceC2351) = raw28013 := by
      apply Matrix.ext; unfold tripleCharges sourceA2351 sourceB2351 sourceC2351 difference raw28013; decide +kernel
    rw [ha]
    exact (canonical28013 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2351 + difference 5 3) (sourceB2351 + difference 3 5) sourceC2351) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2025) := by
    have ha : (tripleCharges (sourceA2351 + difference 5 3) (sourceB2351 + difference 3 5) sourceC2351) = raw4640 := by
      apply Matrix.ext; unfold tripleCharges sourceA2351 sourceB2351 sourceC2351 difference raw4640; decide +kernel
    rw [ha]
    exact (canonical4640 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2351 + difference 5 4) (sourceB2351 + difference 4 5) sourceC2351) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2025) := by
    have ha : (tripleCharges (sourceA2351 + difference 5 4) (sourceB2351 + difference 4 5) sourceC2351) = raw4636 := by
      apply Matrix.ext; unfold tripleCharges sourceA2351 sourceB2351 sourceC2351 difference raw4636; decide +kernel
    rw [ha]
    exact (canonical4636 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2351 sourceB2351 sourceC2351
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2351, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2352 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2352 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC2352 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceForm2352 : Integer.Sparse Master := [(Sum.inr 4351, 1), (Sum.inr 4352, 1), (Sum.inr 4354, 2), (Sum.inr 4461, 1), (Sum.inr 4947, 1), (Sum.inr 4948, 1), (Sum.inr 4949, 2), (Sum.inr 5037, 1), (Sum.inr 5038, 2), (Sum.inr 5076, 1), (Sum.inr 5162, 1), (Sum.inr 5163, 2), (Sum.inr 5172, 2), (Sum.inr 5174, 2), (Sum.inr 5176, 2), (Sum.inr 5290, 1), (Sum.inr 5294, 2), (Sum.inr 5416, 1), (Sum.inr 5418, 1), (Sum.inr 5442, 2), (Sum.inr 5485, 1)]

theorem sourceEq2352 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2352 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2352 + difference 0 1) (sourceB2352 + difference 1 0) sourceC2352) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5418) := by
    have ha : (tripleCharges (sourceA2352 + difference 0 1) (sourceB2352 + difference 1 0) sourceC2352) = raw17691 := by
      apply Matrix.ext; unfold tripleCharges sourceA2352 sourceB2352 sourceC2352 difference raw17691; decide +kernel
    rw [ha]
    exact (canonical17691 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2352 + difference 0 2) (sourceB2352 + difference 2 0) sourceC2352) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5416) := by
    have ha : (tripleCharges (sourceA2352 + difference 0 2) (sourceB2352 + difference 2 0) sourceC2352) = raw17692 := by
      apply Matrix.ext; unfold tripleCharges sourceA2352 sourceB2352 sourceC2352 difference raw17692; decide +kernel
    rw [ha]
    exact (canonical17692 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2352 + difference 0 3) (sourceB2352 + difference 3 0) sourceC2352) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5442) := by
    have ha : (tripleCharges (sourceA2352 + difference 0 3) (sourceB2352 + difference 3 0) sourceC2352) = raw3055 := by
      apply Matrix.ext; unfold tripleCharges sourceA2352 sourceB2352 sourceC2352 difference raw3055; decide +kernel
    rw [ha]
    exact (canonical3055 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2352 + difference 0 4) (sourceB2352 + difference 4 0) sourceC2352) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5442) := by
    have ha : (tripleCharges (sourceA2352 + difference 0 4) (sourceB2352 + difference 4 0) sourceC2352) = raw17693 := by
      apply Matrix.ext; unfold tripleCharges sourceA2352 sourceB2352 sourceC2352 difference raw17693; decide +kernel
    rw [ha]
    exact (canonical17693 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2352 + difference 0 5) (sourceB2352 + difference 5 0) sourceC2352) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA2352 + difference 0 5) (sourceB2352 + difference 5 0) sourceC2352) = raw3045 := by
      apply Matrix.ext; unfold tripleCharges sourceA2352 sourceB2352 sourceC2352 difference raw3045; decide +kernel
    rw [ha]
    exact (canonical3045 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2352 + difference 1 0) (sourceB2352 + difference 0 1) sourceC2352) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4461) := by
    have ha : (tripleCharges (sourceA2352 + difference 1 0) (sourceB2352 + difference 0 1) sourceC2352) = raw13591 := by
      apply Matrix.ext; unfold tripleCharges sourceA2352 sourceB2352 sourceC2352 difference raw13591; decide +kernel
    rw [ha]
    exact (canonical13591 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2352 + difference 1 2) (sourceB2352 + difference 2 1) sourceC2352) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5076) := by
    have ha : (tripleCharges (sourceA2352 + difference 1 2) (sourceB2352 + difference 2 1) sourceC2352) = raw13593 := by
      apply Matrix.ext; unfold tripleCharges sourceA2352 sourceB2352 sourceC2352 difference raw13593; decide +kernel
    rw [ha]
    exact (canonical13593 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2352 + difference 1 3) (sourceB2352 + difference 3 1) sourceC2352) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA2352 + difference 1 3) (sourceB2352 + difference 3 1) sourceC2352) = raw3054 := by
      apply Matrix.ext; unfold tripleCharges sourceA2352 sourceB2352 sourceC2352 difference raw3054; decide +kernel
    rw [ha]
    exact (canonical3054 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2352 + difference 1 4) (sourceB2352 + difference 4 1) sourceC2352) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA2352 + difference 1 4) (sourceB2352 + difference 4 1) sourceC2352) = raw13594 := by
      apply Matrix.ext; unfold tripleCharges sourceA2352 sourceB2352 sourceC2352 difference raw13594; decide +kernel
    rw [ha]
    exact (canonical13594 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2352 + difference 1 5) (sourceB2352 + difference 5 1) sourceC2352) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA2352 + difference 1 5) (sourceB2352 + difference 5 1) sourceC2352) = raw3044 := by
      apply Matrix.ext; unfold tripleCharges sourceA2352 sourceB2352 sourceC2352 difference raw3044; decide +kernel
    rw [ha]
    exact (canonical3044 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2352 + difference 2 0) (sourceB2352 + difference 0 2) sourceC2352) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4351) := by
    have ha : (tripleCharges (sourceA2352 + difference 2 0) (sourceB2352 + difference 0 2) sourceC2352) = raw25071 := by
      apply Matrix.ext; unfold tripleCharges sourceA2352 sourceB2352 sourceC2352 difference raw25071; decide +kernel
    rw [ha]
    exact (canonical25071 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2352 + difference 2 1) (sourceB2352 + difference 1 2) sourceC2352) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4947) := by
    have ha : (tripleCharges (sourceA2352 + difference 2 1) (sourceB2352 + difference 1 2) sourceC2352) = raw32201 := by
      apply Matrix.ext; unfold tripleCharges sourceA2352 sourceB2352 sourceC2352 difference raw32201; decide +kernel
    rw [ha]
    exact (canonical32201 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2352 + difference 2 3) (sourceB2352 + difference 3 2) sourceC2352) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5172) := by
    have ha : (tripleCharges (sourceA2352 + difference 2 3) (sourceB2352 + difference 3 2) sourceC2352) = raw17687 := by
      apply Matrix.ext; unfold tripleCharges sourceA2352 sourceB2352 sourceC2352 difference raw17687; decide +kernel
    rw [ha]
    exact (canonical17687 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2352 + difference 2 4) (sourceB2352 + difference 4 2) sourceC2352) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5172) := by
    have ha : (tripleCharges (sourceA2352 + difference 2 4) (sourceB2352 + difference 4 2) sourceC2352) = raw32202 := by
      apply Matrix.ext; unfold tripleCharges sourceA2352 sourceB2352 sourceC2352 difference raw32202; decide +kernel
    rw [ha]
    exact (canonical32202 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2352 + difference 2 5) (sourceB2352 + difference 5 2) sourceC2352) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5162) := by
    have ha : (tripleCharges (sourceA2352 + difference 2 5) (sourceB2352 + difference 5 2) sourceC2352) = raw13579 := by
      apply Matrix.ext; unfold tripleCharges sourceA2352 sourceB2352 sourceC2352 difference raw13579; decide +kernel
    rw [ha]
    exact (canonical13579 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2352 + difference 3 0) (sourceB2352 + difference 0 3) sourceC2352) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4354) := by
    have ha : (tripleCharges (sourceA2352 + difference 3 0) (sourceB2352 + difference 0 3) sourceC2352) = raw25074 := by
      apply Matrix.ext; unfold tripleCharges sourceA2352 sourceB2352 sourceC2352 difference raw25074; decide +kernel
    rw [ha]
    exact (canonical25074 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2352 + difference 3 1) (sourceB2352 + difference 1 3) sourceC2352) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4949) := by
    have ha : (tripleCharges (sourceA2352 + difference 3 1) (sourceB2352 + difference 1 3) sourceC2352) = raw32203 := by
      apply Matrix.ext; unfold tripleCharges sourceA2352 sourceB2352 sourceC2352 difference raw32203; decide +kernel
    rw [ha]
    exact (canonical32203 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2352 + difference 3 2) (sourceB2352 + difference 2 3) sourceC2352) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5038) := by
    have ha : (tripleCharges (sourceA2352 + difference 3 2) (sourceB2352 + difference 2 3) sourceC2352) = raw32204 := by
      apply Matrix.ext; unfold tripleCharges sourceA2352 sourceB2352 sourceC2352 difference raw32204; decide +kernel
    rw [ha]
    exact (canonical32204 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2352 + difference 3 4) (sourceB2352 + difference 4 3) sourceC2352) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5176) := by
    have ha : (tripleCharges (sourceA2352 + difference 3 4) (sourceB2352 + difference 4 3) sourceC2352) = raw32205 := by
      apply Matrix.ext; unfold tripleCharges sourceA2352 sourceB2352 sourceC2352 difference raw32205; decide +kernel
    rw [ha]
    exact (canonical32205 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2352 + difference 3 5) (sourceB2352 + difference 5 3) sourceC2352) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5163) := by
    have ha : (tripleCharges (sourceA2352 + difference 3 5) (sourceB2352 + difference 5 3) sourceC2352) = raw13583 := by
      apply Matrix.ext; unfold tripleCharges sourceA2352 sourceB2352 sourceC2352 difference raw13583; decide +kernel
    rw [ha]
    exact (canonical13583 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2352 + difference 4 0) (sourceB2352 + difference 0 4) sourceC2352) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4354) := by
    have ha : (tripleCharges (sourceA2352 + difference 4 0) (sourceB2352 + difference 0 4) sourceC2352) = raw23047 := by
      apply Matrix.ext; unfold tripleCharges sourceA2352 sourceB2352 sourceC2352 difference raw23047; decide +kernel
    rw [ha]
    exact (canonical23047 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2352 + difference 4 1) (sourceB2352 + difference 1 4) sourceC2352) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4949) := by
    have ha : (tripleCharges (sourceA2352 + difference 4 1) (sourceB2352 + difference 1 4) sourceC2352) = raw32206 := by
      apply Matrix.ext; unfold tripleCharges sourceA2352 sourceB2352 sourceC2352 difference raw32206; decide +kernel
    rw [ha]
    exact (canonical32206 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2352 + difference 4 2) (sourceB2352 + difference 2 4) sourceC2352) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5038) := by
    have ha : (tripleCharges (sourceA2352 + difference 4 2) (sourceB2352 + difference 2 4) sourceC2352) = raw32207 := by
      apply Matrix.ext; unfold tripleCharges sourceA2352 sourceB2352 sourceC2352 difference raw32207; decide +kernel
    rw [ha]
    exact (canonical32207 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2352 + difference 4 3) (sourceB2352 + difference 3 4) sourceC2352) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5176) := by
    have ha : (tripleCharges (sourceA2352 + difference 4 3) (sourceB2352 + difference 3 4) sourceC2352) = raw17694 := by
      apply Matrix.ext; unfold tripleCharges sourceA2352 sourceB2352 sourceC2352 difference raw17694; decide +kernel
    rw [ha]
    exact (canonical17694 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2352 + difference 4 5) (sourceB2352 + difference 5 4) sourceC2352) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5163) := by
    have ha : (tripleCharges (sourceA2352 + difference 4 5) (sourceB2352 + difference 5 4) sourceC2352) = raw13588 := by
      apply Matrix.ext; unfold tripleCharges sourceA2352 sourceB2352 sourceC2352 difference raw13588; decide +kernel
    rw [ha]
    exact (canonical13588 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2352 + difference 5 0) (sourceB2352 + difference 0 5) sourceC2352) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4352) := by
    have ha : (tripleCharges (sourceA2352 + difference 5 0) (sourceB2352 + difference 0 5) sourceC2352) = raw21250 := by
      apply Matrix.ext; unfold tripleCharges sourceA2352 sourceB2352 sourceC2352 difference raw21250; decide +kernel
    rw [ha]
    exact (canonical21250 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2352 + difference 5 1) (sourceB2352 + difference 1 5) sourceC2352) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4948) := by
    have ha : (tripleCharges (sourceA2352 + difference 5 1) (sourceB2352 + difference 1 5) sourceC2352) = raw32208 := by
      apply Matrix.ext; unfold tripleCharges sourceA2352 sourceB2352 sourceC2352 difference raw32208; decide +kernel
    rw [ha]
    exact (canonical32208 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2352 + difference 5 2) (sourceB2352 + difference 2 5) sourceC2352) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5037) := by
    have ha : (tripleCharges (sourceA2352 + difference 5 2) (sourceB2352 + difference 2 5) sourceC2352) = raw32209 := by
      apply Matrix.ext; unfold tripleCharges sourceA2352 sourceB2352 sourceC2352 difference raw32209; decide +kernel
    rw [ha]
    exact (canonical32209 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2352 + difference 5 3) (sourceB2352 + difference 3 5) sourceC2352) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5174) := by
    have ha : (tripleCharges (sourceA2352 + difference 5 3) (sourceB2352 + difference 3 5) sourceC2352) = raw17698 := by
      apply Matrix.ext; unfold tripleCharges sourceA2352 sourceB2352 sourceC2352 difference raw17698; decide +kernel
    rw [ha]
    exact (canonical17698 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2352 + difference 5 4) (sourceB2352 + difference 4 5) sourceC2352) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5174) := by
    have ha : (tripleCharges (sourceA2352 + difference 5 4) (sourceB2352 + difference 4 5) sourceC2352) = raw32210 := by
      apply Matrix.ext; unfold tripleCharges sourceA2352 sourceB2352 sourceC2352 difference raw32210; decide +kernel
    rw [ha]
    exact (canonical32210 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2352 sourceB2352 sourceC2352
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2352, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2353 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2353 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC2353 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceForm2353 : Integer.Sparse Master := [(Sum.inr 929, 1), (Sum.inr 930, 1), (Sum.inr 932, 2), (Sum.inr 1044, 1), (Sum.inr 2338, 1), (Sum.inr 2339, 1), (Sum.inr 2341, 2), (Sum.inr 2429, 1), (Sum.inr 2431, 2), (Sum.inr 2483, 1), (Sum.inr 2589, 1), (Sum.inr 2590, 2), (Sum.inr 2599, 2), (Sum.inr 2601, 2), (Sum.inr 2604, 2), (Sum.inr 2764, 1), (Sum.inr 2768, 2), (Sum.inr 3933, 1), (Sum.inr 3967, 1), (Sum.inr 3998, 1), (Sum.inr 4001, 2)]

theorem sourceEq2353 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2353 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2353 + difference 0 1) (sourceB2353 + difference 1 0) sourceC2353) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3933) := by
    have ha : (tripleCharges (sourceA2353 + difference 0 1) (sourceB2353 + difference 1 0) sourceC2353) = raw32211 := by
      apply Matrix.ext; unfold tripleCharges sourceA2353 sourceB2353 sourceC2353 difference raw32211; decide +kernel
    rw [ha]
    exact (canonical32211 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2353 + difference 0 2) (sourceB2353 + difference 2 0) sourceC2353) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3967) := by
    have ha : (tripleCharges (sourceA2353 + difference 0 2) (sourceB2353 + difference 2 0) sourceC2353) = raw32212 := by
      apply Matrix.ext; unfold tripleCharges sourceA2353 sourceB2353 sourceC2353 difference raw32212; decide +kernel
    rw [ha]
    exact (canonical32212 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2353 + difference 0 3) (sourceB2353 + difference 3 0) sourceC2353) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4001) := by
    have ha : (tripleCharges (sourceA2353 + difference 0 3) (sourceB2353 + difference 3 0) sourceC2353) = raw3085 := by
      apply Matrix.ext; unfold tripleCharges sourceA2353 sourceB2353 sourceC2353 difference raw3085; decide +kernel
    rw [ha]
    exact (canonical3085 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2353 + difference 0 4) (sourceB2353 + difference 4 0) sourceC2353) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4001) := by
    have ha : (tripleCharges (sourceA2353 + difference 0 4) (sourceB2353 + difference 4 0) sourceC2353) = raw32213 := by
      apply Matrix.ext; unfold tripleCharges sourceA2353 sourceB2353 sourceC2353 difference raw32213; decide +kernel
    rw [ha]
    exact (canonical32213 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2353 + difference 0 5) (sourceB2353 + difference 5 0) sourceC2353) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3998) := by
    have ha : (tripleCharges (sourceA2353 + difference 0 5) (sourceB2353 + difference 5 0) sourceC2353) = raw3075 := by
      apply Matrix.ext; unfold tripleCharges sourceA2353 sourceB2353 sourceC2353 difference raw3075; decide +kernel
    rw [ha]
    exact (canonical3075 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2353 + difference 1 0) (sourceB2353 + difference 0 1) sourceC2353) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1044) := by
    have ha : (tripleCharges (sourceA2353 + difference 1 0) (sourceB2353 + difference 0 1) sourceC2353) = raw13613 := by
      apply Matrix.ext; unfold tripleCharges sourceA2353 sourceB2353 sourceC2353 difference raw13613; decide +kernel
    rw [ha]
    exact (canonical13613 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2353 + difference 1 2) (sourceB2353 + difference 2 1) sourceC2353) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2483) := by
    have ha : (tripleCharges (sourceA2353 + difference 1 2) (sourceB2353 + difference 2 1) sourceC2353) = raw13615 := by
      apply Matrix.ext; unfold tripleCharges sourceA2353 sourceB2353 sourceC2353 difference raw13615; decide +kernel
    rw [ha]
    exact (canonical13615 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2353 + difference 1 3) (sourceB2353 + difference 3 1) sourceC2353) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2768) := by
    have ha : (tripleCharges (sourceA2353 + difference 1 3) (sourceB2353 + difference 3 1) sourceC2353) = raw3084 := by
      apply Matrix.ext; unfold tripleCharges sourceA2353 sourceB2353 sourceC2353 difference raw3084; decide +kernel
    rw [ha]
    exact (canonical3084 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2353 + difference 1 4) (sourceB2353 + difference 4 1) sourceC2353) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2768) := by
    have ha : (tripleCharges (sourceA2353 + difference 1 4) (sourceB2353 + difference 4 1) sourceC2353) = raw13616 := by
      apply Matrix.ext; unfold tripleCharges sourceA2353 sourceB2353 sourceC2353 difference raw13616; decide +kernel
    rw [ha]
    exact (canonical13616 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2353 + difference 1 5) (sourceB2353 + difference 5 1) sourceC2353) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2764) := by
    have ha : (tripleCharges (sourceA2353 + difference 1 5) (sourceB2353 + difference 5 1) sourceC2353) = raw3074 := by
      apply Matrix.ext; unfold tripleCharges sourceA2353 sourceB2353 sourceC2353 difference raw3074; decide +kernel
    rw [ha]
    exact (canonical3074 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2353 + difference 2 0) (sourceB2353 + difference 0 2) sourceC2353) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 929) := by
    have ha : (tripleCharges (sourceA2353 + difference 2 0) (sourceB2353 + difference 0 2) sourceC2353) = raw25081 := by
      apply Matrix.ext; unfold tripleCharges sourceA2353 sourceB2353 sourceC2353 difference raw25081; decide +kernel
    rw [ha]
    exact (canonical25081 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2353 + difference 2 1) (sourceB2353 + difference 1 2) sourceC2353) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2338) := by
    have ha : (tripleCharges (sourceA2353 + difference 2 1) (sourceB2353 + difference 1 2) sourceC2353) = raw32214 := by
      apply Matrix.ext; unfold tripleCharges sourceA2353 sourceB2353 sourceC2353 difference raw32214; decide +kernel
    rw [ha]
    exact (canonical32214 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2353 + difference 2 3) (sourceB2353 + difference 3 2) sourceC2353) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2599) := by
    have ha : (tripleCharges (sourceA2353 + difference 2 3) (sourceB2353 + difference 3 2) sourceC2353) = raw32215 := by
      apply Matrix.ext; unfold tripleCharges sourceA2353 sourceB2353 sourceC2353 difference raw32215; decide +kernel
    rw [ha]
    exact (canonical32215 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2353 + difference 2 4) (sourceB2353 + difference 4 2) sourceC2353) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2599) := by
    have ha : (tripleCharges (sourceA2353 + difference 2 4) (sourceB2353 + difference 4 2) sourceC2353) = raw32216 := by
      apply Matrix.ext; unfold tripleCharges sourceA2353 sourceB2353 sourceC2353 difference raw32216; decide +kernel
    rw [ha]
    exact (canonical32216 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2353 + difference 2 5) (sourceB2353 + difference 5 2) sourceC2353) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2589) := by
    have ha : (tripleCharges (sourceA2353 + difference 2 5) (sourceB2353 + difference 5 2) sourceC2353) = raw13601 := by
      apply Matrix.ext; unfold tripleCharges sourceA2353 sourceB2353 sourceC2353 difference raw13601; decide +kernel
    rw [ha]
    exact (canonical13601 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2353 + difference 3 0) (sourceB2353 + difference 0 3) sourceC2353) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 932) := by
    have ha : (tripleCharges (sourceA2353 + difference 3 0) (sourceB2353 + difference 0 3) sourceC2353) = raw25084 := by
      apply Matrix.ext; unfold tripleCharges sourceA2353 sourceB2353 sourceC2353 difference raw25084; decide +kernel
    rw [ha]
    exact (canonical25084 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2353 + difference 3 1) (sourceB2353 + difference 1 3) sourceC2353) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2341) := by
    have ha : (tripleCharges (sourceA2353 + difference 3 1) (sourceB2353 + difference 1 3) sourceC2353) = raw32217 := by
      apply Matrix.ext; unfold tripleCharges sourceA2353 sourceB2353 sourceC2353 difference raw32217; decide +kernel
    rw [ha]
    exact (canonical32217 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2353 + difference 3 2) (sourceB2353 + difference 2 3) sourceC2353) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2431) := by
    have ha : (tripleCharges (sourceA2353 + difference 3 2) (sourceB2353 + difference 2 3) sourceC2353) = raw32218 := by
      apply Matrix.ext; unfold tripleCharges sourceA2353 sourceB2353 sourceC2353 difference raw32218; decide +kernel
    rw [ha]
    exact (canonical32218 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2353 + difference 3 4) (sourceB2353 + difference 4 3) sourceC2353) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2604) := by
    have ha : (tripleCharges (sourceA2353 + difference 3 4) (sourceB2353 + difference 4 3) sourceC2353) = raw32219 := by
      apply Matrix.ext; unfold tripleCharges sourceA2353 sourceB2353 sourceC2353 difference raw32219; decide +kernel
    rw [ha]
    exact (canonical32219 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2353 + difference 3 5) (sourceB2353 + difference 5 3) sourceC2353) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2590) := by
    have ha : (tripleCharges (sourceA2353 + difference 3 5) (sourceB2353 + difference 5 3) sourceC2353) = raw13605 := by
      apply Matrix.ext; unfold tripleCharges sourceA2353 sourceB2353 sourceC2353 difference raw13605; decide +kernel
    rw [ha]
    exact (canonical13605 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2353 + difference 4 0) (sourceB2353 + difference 0 4) sourceC2353) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 932) := by
    have ha : (tripleCharges (sourceA2353 + difference 4 0) (sourceB2353 + difference 0 4) sourceC2353) = raw23067 := by
      apply Matrix.ext; unfold tripleCharges sourceA2353 sourceB2353 sourceC2353 difference raw23067; decide +kernel
    rw [ha]
    exact (canonical23067 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2353 + difference 4 1) (sourceB2353 + difference 1 4) sourceC2353) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2341) := by
    have ha : (tripleCharges (sourceA2353 + difference 4 1) (sourceB2353 + difference 1 4) sourceC2353) = raw32220 := by
      apply Matrix.ext; unfold tripleCharges sourceA2353 sourceB2353 sourceC2353 difference raw32220; decide +kernel
    rw [ha]
    exact (canonical32220 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2353 + difference 4 2) (sourceB2353 + difference 2 4) sourceC2353) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2431) := by
    have ha : (tripleCharges (sourceA2353 + difference 4 2) (sourceB2353 + difference 2 4) sourceC2353) = raw32221 := by
      apply Matrix.ext; unfold tripleCharges sourceA2353 sourceB2353 sourceC2353 difference raw32221; decide +kernel
    rw [ha]
    exact (canonical32221 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2353 + difference 4 3) (sourceB2353 + difference 3 4) sourceC2353) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2604) := by
    have ha : (tripleCharges (sourceA2353 + difference 4 3) (sourceB2353 + difference 3 4) sourceC2353) = raw23055 := by
      apply Matrix.ext; unfold tripleCharges sourceA2353 sourceB2353 sourceC2353 difference raw23055; decide +kernel
    rw [ha]
    exact (canonical23055 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2353 + difference 4 5) (sourceB2353 + difference 5 4) sourceC2353) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2590) := by
    have ha : (tripleCharges (sourceA2353 + difference 4 5) (sourceB2353 + difference 5 4) sourceC2353) = raw13610 := by
      apply Matrix.ext; unfold tripleCharges sourceA2353 sourceB2353 sourceC2353 difference raw13610; decide +kernel
    rw [ha]
    exact (canonical13610 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2353 + difference 5 0) (sourceB2353 + difference 0 5) sourceC2353) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 930) := by
    have ha : (tripleCharges (sourceA2353 + difference 5 0) (sourceB2353 + difference 0 5) sourceC2353) = raw21278 := by
      apply Matrix.ext; unfold tripleCharges sourceA2353 sourceB2353 sourceC2353 difference raw21278; decide +kernel
    rw [ha]
    exact (canonical21278 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2353 + difference 5 1) (sourceB2353 + difference 1 5) sourceC2353) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2339) := by
    have ha : (tripleCharges (sourceA2353 + difference 5 1) (sourceB2353 + difference 1 5) sourceC2353) = raw32222 := by
      apply Matrix.ext; unfold tripleCharges sourceA2353 sourceB2353 sourceC2353 difference raw32222; decide +kernel
    rw [ha]
    exact (canonical32222 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2353 + difference 5 2) (sourceB2353 + difference 2 5) sourceC2353) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2429) := by
    have ha : (tripleCharges (sourceA2353 + difference 5 2) (sourceB2353 + difference 2 5) sourceC2353) = raw32223 := by
      apply Matrix.ext; unfold tripleCharges sourceA2353 sourceB2353 sourceC2353 difference raw32223; decide +kernel
    rw [ha]
    exact (canonical32223 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2353 + difference 5 3) (sourceB2353 + difference 3 5) sourceC2353) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2601) := by
    have ha : (tripleCharges (sourceA2353 + difference 5 3) (sourceB2353 + difference 3 5) sourceC2353) = raw21263 := by
      apply Matrix.ext; unfold tripleCharges sourceA2353 sourceB2353 sourceC2353 difference raw21263; decide +kernel
    rw [ha]
    exact (canonical21263 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2353 + difference 5 4) (sourceB2353 + difference 4 5) sourceC2353) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2601) := by
    have ha : (tripleCharges (sourceA2353 + difference 5 4) (sourceB2353 + difference 4 5) sourceC2353) = raw32224 := by
      apply Matrix.ext; unfold tripleCharges sourceA2353 sourceB2353 sourceC2353 difference raw32224; decide +kernel
    rw [ha]
    exact (canonical32224 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2353 sourceB2353 sourceC2353
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2353, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2354 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceB2354 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC2354 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceForm2354 : Integer.Sparse Master := [(Sum.inr 4805, 1), (Sum.inr 4838, 1), (Sum.inr 4839, 2), (Sum.inr 4869, 1), (Sum.inr 5072, 1), (Sum.inr 5076, 1), (Sum.inr 5099, 1), (Sum.inr 5101, 2), (Sum.inr 5104, 1), (Sum.inr 5105, 2), (Sum.inr 5137, 1), (Sum.inr 5138, 2), (Sum.inr 5149, 2), (Sum.inr 5150, 1), (Sum.inr 5168, 1), (Sum.inr 5169, 2), (Sum.inr 5170, 2), (Sum.inr 5173, 2), (Sum.inr 5187, 1), (Sum.inr 5204, 2), (Sum.inr 5205, 1)]

theorem sourceEq2354 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2354 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2354 + difference 0 1) (sourceB2354 + difference 1 0) sourceC2354) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5168) := by
    have ha : (tripleCharges (sourceA2354 + difference 0 1) (sourceB2354 + difference 1 0) sourceC2354) = raw32225 := by
      apply Matrix.ext; unfold tripleCharges sourceA2354 sourceB2354 sourceC2354 difference raw32225; decide +kernel
    rw [ha]
    exact (canonical32225 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2354 + difference 0 2) (sourceB2354 + difference 2 0) sourceC2354) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5072) := by
    have ha : (tripleCharges (sourceA2354 + difference 0 2) (sourceB2354 + difference 2 0) sourceC2354) = raw32226 := by
      apply Matrix.ext; unfold tripleCharges sourceA2354 sourceB2354 sourceC2354 difference raw32226; decide +kernel
    rw [ha]
    exact (canonical32226 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2354 + difference 0 3) (sourceB2354 + difference 3 0) sourceC2354) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5101) := by
    have ha : (tripleCharges (sourceA2354 + difference 0 3) (sourceB2354 + difference 3 0) sourceC2354) = raw32227 := by
      apply Matrix.ext; unfold tripleCharges sourceA2354 sourceB2354 sourceC2354 difference raw32227; decide +kernel
    rw [ha]
    exact (canonical32227 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2354 + difference 0 4) (sourceB2354 + difference 4 0) sourceC2354) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5101) := by
    have ha : (tripleCharges (sourceA2354 + difference 0 4) (sourceB2354 + difference 4 0) sourceC2354) = raw32228 := by
      apply Matrix.ext; unfold tripleCharges sourceA2354 sourceB2354 sourceC2354 difference raw32228; decide +kernel
    rw [ha]
    exact (canonical32228 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2354 + difference 0 5) (sourceB2354 + difference 5 0) sourceC2354) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5099) := by
    have ha : (tripleCharges (sourceA2354 + difference 0 5) (sourceB2354 + difference 5 0) sourceC2354) = raw32229 := by
      apply Matrix.ext; unfold tripleCharges sourceA2354 sourceB2354 sourceC2354 difference raw32229; decide +kernel
    rw [ha]
    exact (canonical32229 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2354 + difference 1 0) (sourceB2354 + difference 0 1) sourceC2354) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4869) := by
    have ha : (tripleCharges (sourceA2354 + difference 1 0) (sourceB2354 + difference 0 1) sourceC2354) = raw32230 := by
      apply Matrix.ext; unfold tripleCharges sourceA2354 sourceB2354 sourceC2354 difference raw32230; decide +kernel
    rw [ha]
    exact (canonical32230 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2354 + difference 1 2) (sourceB2354 + difference 2 1) sourceC2354) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5187) := by
    have ha : (tripleCharges (sourceA2354 + difference 1 2) (sourceB2354 + difference 2 1) sourceC2354) = raw32231 := by
      apply Matrix.ext; unfold tripleCharges sourceA2354 sourceB2354 sourceC2354 difference raw32231; decide +kernel
    rw [ha]
    exact (canonical32231 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2354 + difference 1 3) (sourceB2354 + difference 3 1) sourceC2354) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5204) := by
    have ha : (tripleCharges (sourceA2354 + difference 1 3) (sourceB2354 + difference 3 1) sourceC2354) = raw32232 := by
      apply Matrix.ext; unfold tripleCharges sourceA2354 sourceB2354 sourceC2354 difference raw32232; decide +kernel
    rw [ha]
    exact (canonical32232 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2354 + difference 1 4) (sourceB2354 + difference 4 1) sourceC2354) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5204) := by
    have ha : (tripleCharges (sourceA2354 + difference 1 4) (sourceB2354 + difference 4 1) sourceC2354) = raw32233 := by
      apply Matrix.ext; unfold tripleCharges sourceA2354 sourceB2354 sourceC2354 difference raw32233; decide +kernel
    rw [ha]
    exact (canonical32233 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2354 + difference 1 5) (sourceB2354 + difference 5 1) sourceC2354) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5205) := by
    have ha : (tripleCharges (sourceA2354 + difference 1 5) (sourceB2354 + difference 5 1) sourceC2354) = raw32234 := by
      apply Matrix.ext; unfold tripleCharges sourceA2354 sourceB2354 sourceC2354 difference raw32234; decide +kernel
    rw [ha]
    exact (canonical32234 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2354 + difference 2 0) (sourceB2354 + difference 0 2) sourceC2354) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4805) := by
    have ha : (tripleCharges (sourceA2354 + difference 2 0) (sourceB2354 + difference 0 2) sourceC2354) = raw32235 := by
      apply Matrix.ext; unfold tripleCharges sourceA2354 sourceB2354 sourceC2354 difference raw32235; decide +kernel
    rw [ha]
    exact (canonical32235 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2354 + difference 2 1) (sourceB2354 + difference 1 2) sourceC2354) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5076) := by
    have ha : (tripleCharges (sourceA2354 + difference 2 1) (sourceB2354 + difference 1 2) sourceC2354) = raw32236 := by
      apply Matrix.ext; unfold tripleCharges sourceA2354 sourceB2354 sourceC2354 difference raw32236; decide +kernel
    rw [ha]
    exact (canonical32236 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2354 + difference 2 3) (sourceB2354 + difference 3 2) sourceC2354) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5149) := by
    have ha : (tripleCharges (sourceA2354 + difference 2 3) (sourceB2354 + difference 3 2) sourceC2354) = raw32237 := by
      apply Matrix.ext; unfold tripleCharges sourceA2354 sourceB2354 sourceC2354 difference raw32237; decide +kernel
    rw [ha]
    exact (canonical32237 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2354 + difference 2 4) (sourceB2354 + difference 4 2) sourceC2354) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5149) := by
    have ha : (tripleCharges (sourceA2354 + difference 2 4) (sourceB2354 + difference 4 2) sourceC2354) = raw32238 := by
      apply Matrix.ext; unfold tripleCharges sourceA2354 sourceB2354 sourceC2354 difference raw32238; decide +kernel
    rw [ha]
    exact (canonical32238 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2354 + difference 2 5) (sourceB2354 + difference 5 2) sourceC2354) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5150) := by
    have ha : (tripleCharges (sourceA2354 + difference 2 5) (sourceB2354 + difference 5 2) sourceC2354) = raw32239 := by
      apply Matrix.ext; unfold tripleCharges sourceA2354 sourceB2354 sourceC2354 difference raw32239; decide +kernel
    rw [ha]
    exact (canonical32239 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2354 + difference 3 0) (sourceB2354 + difference 0 3) sourceC2354) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4839) := by
    have ha : (tripleCharges (sourceA2354 + difference 3 0) (sourceB2354 + difference 0 3) sourceC2354) = raw32240 := by
      apply Matrix.ext; unfold tripleCharges sourceA2354 sourceB2354 sourceC2354 difference raw32240; decide +kernel
    rw [ha]
    exact (canonical32240 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2354 + difference 3 1) (sourceB2354 + difference 1 3) sourceC2354) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5105) := by
    have ha : (tripleCharges (sourceA2354 + difference 3 1) (sourceB2354 + difference 1 3) sourceC2354) = raw32241 := by
      apply Matrix.ext; unfold tripleCharges sourceA2354 sourceB2354 sourceC2354 difference raw32241; decide +kernel
    rw [ha]
    exact (canonical32241 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2354 + difference 3 2) (sourceB2354 + difference 2 3) sourceC2354) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5138) := by
    have ha : (tripleCharges (sourceA2354 + difference 3 2) (sourceB2354 + difference 2 3) sourceC2354) = raw32242 := by
      apply Matrix.ext; unfold tripleCharges sourceA2354 sourceB2354 sourceC2354 difference raw32242; decide +kernel
    rw [ha]
    exact (canonical32242 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2354 + difference 3 4) (sourceB2354 + difference 4 3) sourceC2354) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5170) := by
    have ha : (tripleCharges (sourceA2354 + difference 3 4) (sourceB2354 + difference 4 3) sourceC2354) = raw32243 := by
      apply Matrix.ext; unfold tripleCharges sourceA2354 sourceB2354 sourceC2354 difference raw32243; decide +kernel
    rw [ha]
    exact (canonical32243 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2354 + difference 3 5) (sourceB2354 + difference 5 3) sourceC2354) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5173) := by
    have ha : (tripleCharges (sourceA2354 + difference 3 5) (sourceB2354 + difference 5 3) sourceC2354) = raw32244 := by
      apply Matrix.ext; unfold tripleCharges sourceA2354 sourceB2354 sourceC2354 difference raw32244; decide +kernel
    rw [ha]
    exact (canonical32244 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2354 + difference 4 0) (sourceB2354 + difference 0 4) sourceC2354) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4839) := by
    have ha : (tripleCharges (sourceA2354 + difference 4 0) (sourceB2354 + difference 0 4) sourceC2354) = raw32245 := by
      apply Matrix.ext; unfold tripleCharges sourceA2354 sourceB2354 sourceC2354 difference raw32245; decide +kernel
    rw [ha]
    exact (canonical32245 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2354 + difference 4 1) (sourceB2354 + difference 1 4) sourceC2354) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5105) := by
    have ha : (tripleCharges (sourceA2354 + difference 4 1) (sourceB2354 + difference 1 4) sourceC2354) = raw32246 := by
      apply Matrix.ext; unfold tripleCharges sourceA2354 sourceB2354 sourceC2354 difference raw32246; decide +kernel
    rw [ha]
    exact (canonical32246 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2354 + difference 4 2) (sourceB2354 + difference 2 4) sourceC2354) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5138) := by
    have ha : (tripleCharges (sourceA2354 + difference 4 2) (sourceB2354 + difference 2 4) sourceC2354) = raw32247 := by
      apply Matrix.ext; unfold tripleCharges sourceA2354 sourceB2354 sourceC2354 difference raw32247; decide +kernel
    rw [ha]
    exact (canonical32247 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2354 + difference 4 3) (sourceB2354 + difference 3 4) sourceC2354) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5170) := by
    have ha : (tripleCharges (sourceA2354 + difference 4 3) (sourceB2354 + difference 3 4) sourceC2354) = raw32248 := by
      apply Matrix.ext; unfold tripleCharges sourceA2354 sourceB2354 sourceC2354 difference raw32248; decide +kernel
    rw [ha]
    exact (canonical32248 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2354 + difference 4 5) (sourceB2354 + difference 5 4) sourceC2354) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5173) := by
    have ha : (tripleCharges (sourceA2354 + difference 4 5) (sourceB2354 + difference 5 4) sourceC2354) = raw32249 := by
      apply Matrix.ext; unfold tripleCharges sourceA2354 sourceB2354 sourceC2354 difference raw32249; decide +kernel
    rw [ha]
    exact (canonical32249 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2354 + difference 5 0) (sourceB2354 + difference 0 5) sourceC2354) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4838) := by
    have ha : (tripleCharges (sourceA2354 + difference 5 0) (sourceB2354 + difference 0 5) sourceC2354) = raw32250 := by
      apply Matrix.ext; unfold tripleCharges sourceA2354 sourceB2354 sourceC2354 difference raw32250; decide +kernel
    rw [ha]
    exact (canonical32250 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2354 + difference 5 1) (sourceB2354 + difference 1 5) sourceC2354) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5104) := by
    have ha : (tripleCharges (sourceA2354 + difference 5 1) (sourceB2354 + difference 1 5) sourceC2354) = raw32251 := by
      apply Matrix.ext; unfold tripleCharges sourceA2354 sourceB2354 sourceC2354 difference raw32251; decide +kernel
    rw [ha]
    exact (canonical32251 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2354 + difference 5 2) (sourceB2354 + difference 2 5) sourceC2354) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5137) := by
    have ha : (tripleCharges (sourceA2354 + difference 5 2) (sourceB2354 + difference 2 5) sourceC2354) = raw32252 := by
      apply Matrix.ext; unfold tripleCharges sourceA2354 sourceB2354 sourceC2354 difference raw32252; decide +kernel
    rw [ha]
    exact (canonical32252 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2354 + difference 5 3) (sourceB2354 + difference 3 5) sourceC2354) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA2354 + difference 5 3) (sourceB2354 + difference 3 5) sourceC2354) = raw32253 := by
      apply Matrix.ext; unfold tripleCharges sourceA2354 sourceB2354 sourceC2354 difference raw32253; decide +kernel
    rw [ha]
    exact (canonical32253 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2354 + difference 5 4) (sourceB2354 + difference 4 5) sourceC2354) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA2354 + difference 5 4) (sourceB2354 + difference 4 5) sourceC2354) = raw32254 := by
      apply Matrix.ext; unfold tripleCharges sourceA2354 sourceB2354 sourceC2354 difference raw32254; decide +kernel
    rw [ha]
    exact (canonical32254 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2354 sourceB2354 sourceC2354
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2354, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2355 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2355 : Charge := ![1, 1, 1, -2, -1, 0]
def sourceC2355 : Charge := ![2, 0, -1, 1, 0, -2]
def sourceForm2355 : Integer.Sparse Master := [(Sum.inr 1156, 1), (Sum.inr 2353, 1), (Sum.inr 2553, 1), (Sum.inr 2566, 1), (Sum.inr 2587, 1), (Sum.inr 2590, 1), (Sum.inr 4092, -1)]

theorem sourceEq2355 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2355 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2355 + difference 2 0) (sourceB2355 + difference 0 2) sourceC2355) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1156) := by
    have ha : (tripleCharges (sourceA2355 + difference 2 0) (sourceB2355 + difference 0 2) sourceC2355) = raw32255 := by
      apply Matrix.ext; unfold tripleCharges sourceA2355 sourceB2355 sourceC2355 difference raw32255; decide +kernel
    rw [ha]
    exact (canonical32255 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2355 + difference 2 1) (sourceB2355 + difference 1 2) sourceC2355) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2353) := by
    have ha : (tripleCharges (sourceA2355 + difference 2 1) (sourceB2355 + difference 1 2) sourceC2355) = raw32256 := by
      apply Matrix.ext; unfold tripleCharges sourceA2355 sourceB2355 sourceC2355 difference raw32256; decide +kernel
    rw [ha]
    exact (canonical32256 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2355 + difference 2 2) (sourceB2355 + difference 2 2) sourceC2355) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2566) := by
    have ha : (tripleCharges (sourceA2355 + difference 2 2) (sourceB2355 + difference 2 2) sourceC2355) = raw12335 := by
      apply Matrix.ext; unfold tripleCharges sourceA2355 sourceB2355 sourceC2355 difference raw12335; decide +kernel
    rw [ha]
    exact (canonical12335 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2355 + difference 2 3) (sourceB2355 + difference 3 2) sourceC2355) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2553) := by
    have ha : (tripleCharges (sourceA2355 + difference 2 3) (sourceB2355 + difference 3 2) sourceC2355) = raw32257 := by
      apply Matrix.ext; unfold tripleCharges sourceA2355 sourceB2355 sourceC2355 difference raw32257; decide +kernel
    rw [ha]
    exact (canonical32257 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2355 + difference 2 4) (sourceB2355 + difference 4 2) sourceC2355) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2590) := by
    have ha : (tripleCharges (sourceA2355 + difference 2 4) (sourceB2355 + difference 4 2) sourceC2355) = raw32258 := by
      apply Matrix.ext; unfold tripleCharges sourceA2355 sourceB2355 sourceC2355 difference raw32258; decide +kernel
    rw [ha]
    exact (canonical32258 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2355 + difference 2 5) (sourceB2355 + difference 5 2) sourceC2355) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2587) := by
    have ha : (tripleCharges (sourceA2355 + difference 2 5) (sourceB2355 + difference 5 2) sourceC2355) = raw12332 := by
      apply Matrix.ext; unfold tripleCharges sourceA2355 sourceB2355 sourceC2355 difference raw12332; decide +kernel
    rw [ha]
    exact (canonical12332 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2355 + sourceB2355) sourceC2355) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2355 + sourceB2355) sourceC2355) = raw12326 := by
      apply Matrix.ext; unfold doubleCharges sourceA2355 sourceB2355 sourceC2355 raw12326; decide +kernel
    rw [ha]
    exact (canonical12326 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2355 sourceB2355 sourceC2355
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2355, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2356 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2356 : Charge := ![2, 0, -1, 1, 0, -2]
def sourceC2356 : Charge := ![1, 1, 1, -2, -1, 0]
def sourceForm2356 : Integer.Sparse Master := [(Sum.inr 2895, 1), (Sum.inr 2896, 1), (Sum.inr 2898, 1), (Sum.inr 2928, 2), (Sum.inr 3964, 1), (Sum.inr 4091, -1)]

theorem sourceEq2356 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2356 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2356 + difference 0 2) (sourceB2356 + difference 2 0) sourceC2356) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3964) := by
    have ha : (tripleCharges (sourceA2356 + difference 0 2) (sourceB2356 + difference 2 0) sourceC2356) = raw32259 := by
      apply Matrix.ext; unfold tripleCharges sourceA2356 sourceB2356 sourceC2356 difference raw32259; decide +kernel
    rw [ha]
    exact (canonical32259 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2356 + difference 1 2) (sourceB2356 + difference 2 1) sourceC2356) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2928) := by
    have ha : (tripleCharges (sourceA2356 + difference 1 2) (sourceB2356 + difference 2 1) sourceC2356) = raw32260 := by
      apply Matrix.ext; unfold tripleCharges sourceA2356 sourceB2356 sourceC2356 difference raw32260; decide +kernel
    rw [ha]
    exact (canonical32260 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2356 + difference 2 2) (sourceB2356 + difference 2 2) sourceC2356) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2928) := by
    have ha : (tripleCharges (sourceA2356 + difference 2 2) (sourceB2356 + difference 2 2) sourceC2356) = raw13314 := by
      apply Matrix.ext; unfold tripleCharges sourceA2356 sourceB2356 sourceC2356 difference raw13314; decide +kernel
    rw [ha]
    exact (canonical13314 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2356 + difference 3 2) (sourceB2356 + difference 2 3) sourceC2356) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2896) := by
    have ha : (tripleCharges (sourceA2356 + difference 3 2) (sourceB2356 + difference 2 3) sourceC2356) = raw32261 := by
      apply Matrix.ext; unfold tripleCharges sourceA2356 sourceB2356 sourceC2356 difference raw32261; decide +kernel
    rw [ha]
    exact (canonical32261 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2356 + difference 4 2) (sourceB2356 + difference 2 4) sourceC2356) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2898) := by
    have ha : (tripleCharges (sourceA2356 + difference 4 2) (sourceB2356 + difference 2 4) sourceC2356) = raw32262 := by
      apply Matrix.ext; unfold tripleCharges sourceA2356 sourceB2356 sourceC2356 difference raw32262; decide +kernel
    rw [ha]
    exact (canonical32262 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2356 + difference 5 2) (sourceB2356 + difference 2 5) sourceC2356) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2895) := by
    have ha : (tripleCharges (sourceA2356 + difference 5 2) (sourceB2356 + difference 2 5) sourceC2356) = raw32263 := by
      apply Matrix.ext; unfold tripleCharges sourceA2356 sourceB2356 sourceC2356 difference raw32263; decide +kernel
    rw [ha]
    exact (canonical32263 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2356 + sourceB2356) sourceC2356) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA2356 + sourceB2356) sourceC2356) = raw13305 := by
      apply Matrix.ext; unfold doubleCharges sourceA2356 sourceB2356 sourceC2356 raw13305; decide +kernel
    rw [ha]
    exact (canonical13305 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2356 sourceB2356 sourceC2356
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2356, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2357 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2357 : Charge := ![1, 1, 1, -2, 0, -1]
def sourceC2357 : Charge := ![2, 0, -1, 1, -1, -1]
def sourceForm2357 : Integer.Sparse Master := [(Sum.inr 1158, 1), (Sum.inr 2354, 1), (Sum.inr 2556, 1), (Sum.inr 2567, 2), (Sum.inr 2589, 1), (Sum.inr 4091, -1)]

theorem sourceEq2357 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2357 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2357 + difference 2 0) (sourceB2357 + difference 0 2) sourceC2357) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1158) := by
    have ha : (tripleCharges (sourceA2357 + difference 2 0) (sourceB2357 + difference 0 2) sourceC2357) = raw32264 := by
      apply Matrix.ext; unfold tripleCharges sourceA2357 sourceB2357 sourceC2357 difference raw32264; decide +kernel
    rw [ha]
    exact (canonical32264 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2357 + difference 2 1) (sourceB2357 + difference 1 2) sourceC2357) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2354) := by
    have ha : (tripleCharges (sourceA2357 + difference 2 1) (sourceB2357 + difference 1 2) sourceC2357) = raw32265 := by
      apply Matrix.ext; unfold tripleCharges sourceA2357 sourceB2357 sourceC2357 difference raw32265; decide +kernel
    rw [ha]
    exact (canonical32265 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2357 + difference 2 2) (sourceB2357 + difference 2 2) sourceC2357) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2567) := by
    have ha : (tripleCharges (sourceA2357 + difference 2 2) (sourceB2357 + difference 2 2) sourceC2357) = raw32266 := by
      apply Matrix.ext; unfold tripleCharges sourceA2357 sourceB2357 sourceC2357 difference raw32266; decide +kernel
    rw [ha]
    exact (canonical32266 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2357 + difference 2 3) (sourceB2357 + difference 3 2) sourceC2357) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2556) := by
    have ha : (tripleCharges (sourceA2357 + difference 2 3) (sourceB2357 + difference 3 2) sourceC2357) = raw32267 := by
      apply Matrix.ext; unfold tripleCharges sourceA2357 sourceB2357 sourceC2357 difference raw32267; decide +kernel
    rw [ha]
    exact (canonical32267 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2357 + difference 2 4) (sourceB2357 + difference 4 2) sourceC2357) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2567) := by
    have ha : (tripleCharges (sourceA2357 + difference 2 4) (sourceB2357 + difference 4 2) sourceC2357) = raw32268 := by
      apply Matrix.ext; unfold tripleCharges sourceA2357 sourceB2357 sourceC2357 difference raw32268; decide +kernel
    rw [ha]
    exact (canonical32268 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2357 + difference 2 5) (sourceB2357 + difference 5 2) sourceC2357) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2589) := by
    have ha : (tripleCharges (sourceA2357 + difference 2 5) (sourceB2357 + difference 5 2) sourceC2357) = raw32269 := by
      apply Matrix.ext; unfold tripleCharges sourceA2357 sourceB2357 sourceC2357 difference raw32269; decide +kernel
    rw [ha]
    exact (canonical32269 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2357 + sourceB2357) sourceC2357) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA2357 + sourceB2357) sourceC2357) = raw32270 := by
      apply Matrix.ext; unfold doubleCharges sourceA2357 sourceB2357 sourceC2357 raw32270; decide +kernel
    rw [ha]
    exact (canonical32270 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2357 sourceB2357 sourceC2357
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2357, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2358 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2358 : Charge := ![2, 0, -1, 1, -1, -1]
def sourceC2358 : Charge := ![1, 1, 1, -2, 0, -1]
def sourceForm2358 : Integer.Sparse Master := [(Sum.inr 2847, 1), (Sum.inr 2893, 1), (Sum.inr 2898, 1), (Sum.inr 2925, 2), (Sum.inr 3945, 1), (Sum.inr 4091, -1)]

theorem sourceEq2358 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2358 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2358 + difference 0 2) (sourceB2358 + difference 2 0) sourceC2358) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3945) := by
    have ha : (tripleCharges (sourceA2358 + difference 0 2) (sourceB2358 + difference 2 0) sourceC2358) = raw17026 := by
      apply Matrix.ext; unfold tripleCharges sourceA2358 sourceB2358 sourceC2358 difference raw17026; decide +kernel
    rw [ha]
    exact (canonical17026 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2358 + difference 1 2) (sourceB2358 + difference 2 1) sourceC2358) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2925) := by
    have ha : (tripleCharges (sourceA2358 + difference 1 2) (sourceB2358 + difference 2 1) sourceC2358) = raw32271 := by
      apply Matrix.ext; unfold tripleCharges sourceA2358 sourceB2358 sourceC2358 difference raw32271; decide +kernel
    rw [ha]
    exact (canonical32271 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2358 + difference 2 2) (sourceB2358 + difference 2 2) sourceC2358) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2925) := by
    have ha : (tripleCharges (sourceA2358 + difference 2 2) (sourceB2358 + difference 2 2) sourceC2358) = raw17020 := by
      apply Matrix.ext; unfold tripleCharges sourceA2358 sourceB2358 sourceC2358 difference raw17020; decide +kernel
    rw [ha]
    exact (canonical17020 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2358 + difference 3 2) (sourceB2358 + difference 2 3) sourceC2358) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2893) := by
    have ha : (tripleCharges (sourceA2358 + difference 3 2) (sourceB2358 + difference 2 3) sourceC2358) = raw32272 := by
      apply Matrix.ext; unfold tripleCharges sourceA2358 sourceB2358 sourceC2358 difference raw32272; decide +kernel
    rw [ha]
    exact (canonical32272 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2358 + difference 4 2) (sourceB2358 + difference 2 4) sourceC2358) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2898) := by
    have ha : (tripleCharges (sourceA2358 + difference 4 2) (sourceB2358 + difference 2 4) sourceC2358) = raw32273 := by
      apply Matrix.ext; unfold tripleCharges sourceA2358 sourceB2358 sourceC2358 difference raw32273; decide +kernel
    rw [ha]
    exact (canonical32273 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2358 + difference 5 2) (sourceB2358 + difference 2 5) sourceC2358) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2847) := by
    have ha : (tripleCharges (sourceA2358 + difference 5 2) (sourceB2358 + difference 2 5) sourceC2358) = raw32274 := by
      apply Matrix.ext; unfold tripleCharges sourceA2358 sourceB2358 sourceC2358 difference raw32274; decide +kernel
    rw [ha]
    exact (canonical32274 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2358 + sourceB2358) sourceC2358) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA2358 + sourceB2358) sourceC2358) = raw17023 := by
      apply Matrix.ext; unfold doubleCharges sourceA2358 sourceB2358 sourceC2358 raw17023; decide +kernel
    rw [ha]
    exact (canonical17023 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2358 sourceB2358 sourceC2358
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2358, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2359 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2359 : Charge := ![2, 0, -1, 1, -2, 0]
def sourceC2359 : Charge := ![1, 1, 1, -2, 1, -2]
def sourceForm2359 : Integer.Sparse Master := [(Sum.inr 2922, 1), (Sum.inr 3748, 1), (Sum.inr 3751, 1), (Sum.inr 3758, 1), (Sum.inr 3866, 1), (Sum.inr 3973, 1), (Sum.inr 4087, -1)]

theorem sourceEq2359 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2359 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2359 + difference 0 0) (sourceB2359 + difference 0 0) sourceC2359) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2922) := by
    have ha : (tripleCharges (sourceA2359 + difference 0 0) (sourceB2359 + difference 0 0) sourceC2359) = raw32275 := by
      apply Matrix.ext; unfold tripleCharges sourceA2359 sourceB2359 sourceC2359 difference raw32275; decide +kernel
    rw [ha]
    exact (canonical32275 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2359 + difference 0 1) (sourceB2359 + difference 1 0) sourceC2359) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3748) := by
    have ha : (tripleCharges (sourceA2359 + difference 0 1) (sourceB2359 + difference 1 0) sourceC2359) = raw32276 := by
      apply Matrix.ext; unfold tripleCharges sourceA2359 sourceB2359 sourceC2359 difference raw32276; decide +kernel
    rw [ha]
    exact (canonical32276 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2359 + difference 0 2) (sourceB2359 + difference 2 0) sourceC2359) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3751) := by
    have ha : (tripleCharges (sourceA2359 + difference 0 2) (sourceB2359 + difference 2 0) sourceC2359) = raw32277 := by
      apply Matrix.ext; unfold tripleCharges sourceA2359 sourceB2359 sourceC2359 difference raw32277; decide +kernel
    rw [ha]
    exact (canonical32277 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2359 + difference 0 3) (sourceB2359 + difference 3 0) sourceC2359) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3866) := by
    have ha : (tripleCharges (sourceA2359 + difference 0 3) (sourceB2359 + difference 3 0) sourceC2359) = raw32278 := by
      apply Matrix.ext; unfold tripleCharges sourceA2359 sourceB2359 sourceC2359 difference raw32278; decide +kernel
    rw [ha]
    exact (canonical32278 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2359 + difference 0 4) (sourceB2359 + difference 4 0) sourceC2359) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3758) := by
    have ha : (tripleCharges (sourceA2359 + difference 0 4) (sourceB2359 + difference 4 0) sourceC2359) = raw32279 := by
      apply Matrix.ext; unfold tripleCharges sourceA2359 sourceB2359 sourceC2359 difference raw32279; decide +kernel
    rw [ha]
    exact (canonical32279 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2359 + difference 0 5) (sourceB2359 + difference 5 0) sourceC2359) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3973) := by
    have ha : (tripleCharges (sourceA2359 + difference 0 5) (sourceB2359 + difference 5 0) sourceC2359) = raw32280 := by
      apply Matrix.ext; unfold tripleCharges sourceA2359 sourceB2359 sourceC2359 difference raw32280; decide +kernel
    rw [ha]
    exact (canonical32280 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2359 + sourceB2359) sourceC2359) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4087) := by
    have ha : (doubleCharges (sourceA2359 + sourceB2359) sourceC2359) = raw32281 := by
      apply Matrix.ext; unfold doubleCharges sourceA2359 sourceB2359 sourceC2359 raw32281; decide +kernel
    rw [ha]
    exact (canonical32281 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2359 sourceB2359 sourceC2359
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2359, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2360 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2360 : Charge := ![1, 1, 1, -1, -1, -1]
def sourceC2360 : Charge := ![2, 0, -1, 0, 0, -1]
def sourceForm2360 : Integer.Sparse Master := [(Sum.inr 4523, 1), (Sum.inr 4524, 2), (Sum.inr 4544, 1), (Sum.inr 4606, 1), (Sum.inr 4960, 1), (Sum.inr 4961, 2), (Sum.inr 4968, 1), (Sum.inr 5027, 1), (Sum.inr 5078, 2), (Sum.inr 5119, 2), (Sum.inr 5149, 2), (Sum.inr 5152, 2), (Sum.inr 5167, 1), (Sum.inr 5169, 2), (Sum.inr 5203, 1), (Sum.inr 5292, 1), (Sum.inr 5293, 2), (Sum.inr 5380, 1), (Sum.inr 5422, 1), (Sum.inr 5433, 1), (Sum.inr 5434, 2)]

theorem sourceEq2360 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2360 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2360 + difference 0 1) (sourceB2360 + difference 1 0) sourceC2360) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5380) := by
    have ha : (tripleCharges (sourceA2360 + difference 0 1) (sourceB2360 + difference 1 0) sourceC2360) = raw18377 := by
      apply Matrix.ext; unfold tripleCharges sourceA2360 sourceB2360 sourceC2360 difference raw18377; decide +kernel
    rw [ha]
    exact (canonical18377 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2360 + difference 0 2) (sourceB2360 + difference 2 0) sourceC2360) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5422) := by
    have ha : (tripleCharges (sourceA2360 + difference 0 2) (sourceB2360 + difference 2 0) sourceC2360) = raw18378 := by
      apply Matrix.ext; unfold tripleCharges sourceA2360 sourceB2360 sourceC2360 difference raw18378; decide +kernel
    rw [ha]
    exact (canonical18378 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2360 + difference 0 3) (sourceB2360 + difference 3 0) sourceC2360) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA2360 + difference 0 3) (sourceB2360 + difference 3 0) sourceC2360) = raw18379 := by
      apply Matrix.ext; unfold tripleCharges sourceA2360 sourceB2360 sourceC2360 difference raw18379; decide +kernel
    rw [ha]
    exact (canonical18379 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2360 + difference 0 4) (sourceB2360 + difference 4 0) sourceC2360) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA2360 + difference 0 4) (sourceB2360 + difference 4 0) sourceC2360) = raw18380 := by
      apply Matrix.ext; unfold tripleCharges sourceA2360 sourceB2360 sourceC2360 difference raw18380; decide +kernel
    rw [ha]
    exact (canonical18380 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2360 + difference 0 5) (sourceB2360 + difference 5 0) sourceC2360) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA2360 + difference 0 5) (sourceB2360 + difference 5 0) sourceC2360) = raw12531 := by
      apply Matrix.ext; unfold tripleCharges sourceA2360 sourceB2360 sourceC2360 difference raw12531; decide +kernel
    rw [ha]
    exact (canonical12531 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2360 + difference 1 0) (sourceB2360 + difference 0 1) sourceC2360) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4606) := by
    have ha : (tripleCharges (sourceA2360 + difference 1 0) (sourceB2360 + difference 0 1) sourceC2360) = raw12556 := by
      apply Matrix.ext; unfold tripleCharges sourceA2360 sourceB2360 sourceC2360 difference raw12556; decide +kernel
    rw [ha]
    exact (canonical12556 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2360 + difference 1 2) (sourceB2360 + difference 2 1) sourceC2360) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5203) := by
    have ha : (tripleCharges (sourceA2360 + difference 1 2) (sourceB2360 + difference 2 1) sourceC2360) = raw12558 := by
      apply Matrix.ext; unfold tripleCharges sourceA2360 sourceB2360 sourceC2360 difference raw12558; decide +kernel
    rw [ha]
    exact (canonical12558 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2360 + difference 1 3) (sourceB2360 + difference 3 1) sourceC2360) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA2360 + difference 1 3) (sourceB2360 + difference 3 1) sourceC2360) = raw12559 := by
      apply Matrix.ext; unfold tripleCharges sourceA2360 sourceB2360 sourceC2360 difference raw12559; decide +kernel
    rw [ha]
    exact (canonical12559 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2360 + difference 1 4) (sourceB2360 + difference 4 1) sourceC2360) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA2360 + difference 1 4) (sourceB2360 + difference 4 1) sourceC2360) = raw12560 := by
      apply Matrix.ext; unfold tripleCharges sourceA2360 sourceB2360 sourceC2360 difference raw12560; decide +kernel
    rw [ha]
    exact (canonical12560 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2360 + difference 1 5) (sourceB2360 + difference 5 1) sourceC2360) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA2360 + difference 1 5) (sourceB2360 + difference 5 1) sourceC2360) = raw18364 := by
      apply Matrix.ext; unfold tripleCharges sourceA2360 sourceB2360 sourceC2360 difference raw18364; decide +kernel
    rw [ha]
    exact (canonical18364 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2360 + difference 2 0) (sourceB2360 + difference 0 2) sourceC2360) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4544) := by
    have ha : (tripleCharges (sourceA2360 + difference 2 0) (sourceB2360 + difference 0 2) sourceC2360) = raw24563 := by
      apply Matrix.ext; unfold tripleCharges sourceA2360 sourceB2360 sourceC2360 difference raw24563; decide +kernel
    rw [ha]
    exact (canonical24563 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2360 + difference 2 1) (sourceB2360 + difference 1 2) sourceC2360) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4968) := by
    have ha : (tripleCharges (sourceA2360 + difference 2 1) (sourceB2360 + difference 1 2) sourceC2360) = raw32282 := by
      apply Matrix.ext; unfold tripleCharges sourceA2360 sourceB2360 sourceC2360 difference raw32282; decide +kernel
    rw [ha]
    exact (canonical32282 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2360 + difference 2 3) (sourceB2360 + difference 3 2) sourceC2360) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA2360 + difference 2 3) (sourceB2360 + difference 3 2) sourceC2360) = raw32283 := by
      apply Matrix.ext; unfold tripleCharges sourceA2360 sourceB2360 sourceC2360 difference raw32283; decide +kernel
    rw [ha]
    exact (canonical32283 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2360 + difference 2 4) (sourceB2360 + difference 4 2) sourceC2360) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA2360 + difference 2 4) (sourceB2360 + difference 4 2) sourceC2360) = raw32284 := by
      apply Matrix.ext; unfold tripleCharges sourceA2360 sourceB2360 sourceC2360 difference raw32284; decide +kernel
    rw [ha]
    exact (canonical32284 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2360 + difference 2 5) (sourceB2360 + difference 5 2) sourceC2360) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5167) := by
    have ha : (tripleCharges (sourceA2360 + difference 2 5) (sourceB2360 + difference 5 2) sourceC2360) = raw12542 := by
      apply Matrix.ext; unfold tripleCharges sourceA2360 sourceB2360 sourceC2360 difference raw12542; decide +kernel
    rw [ha]
    exact (canonical12542 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2360 + difference 3 0) (sourceB2360 + difference 0 3) sourceC2360) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4524) := by
    have ha : (tripleCharges (sourceA2360 + difference 3 0) (sourceB2360 + difference 0 3) sourceC2360) = raw24567 := by
      apply Matrix.ext; unfold tripleCharges sourceA2360 sourceB2360 sourceC2360 difference raw24567; decide +kernel
    rw [ha]
    exact (canonical24567 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2360 + difference 3 1) (sourceB2360 + difference 1 3) sourceC2360) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4961) := by
    have ha : (tripleCharges (sourceA2360 + difference 3 1) (sourceB2360 + difference 1 3) sourceC2360) = raw32285 := by
      apply Matrix.ext; unfold tripleCharges sourceA2360 sourceB2360 sourceC2360 difference raw32285; decide +kernel
    rw [ha]
    exact (canonical32285 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2360 + difference 3 2) (sourceB2360 + difference 2 3) sourceC2360) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5119) := by
    have ha : (tripleCharges (sourceA2360 + difference 3 2) (sourceB2360 + difference 2 3) sourceC2360) = raw32286 := by
      apply Matrix.ext; unfold tripleCharges sourceA2360 sourceB2360 sourceC2360 difference raw32286; decide +kernel
    rw [ha]
    exact (canonical32286 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2360 + difference 3 4) (sourceB2360 + difference 4 3) sourceC2360) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5152) := by
    have ha : (tripleCharges (sourceA2360 + difference 3 4) (sourceB2360 + difference 4 3) sourceC2360) = raw32287 := by
      apply Matrix.ext; unfold tripleCharges sourceA2360 sourceB2360 sourceC2360 difference raw32287; decide +kernel
    rw [ha]
    exact (canonical32287 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2360 + difference 3 5) (sourceB2360 + difference 5 3) sourceC2360) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5149) := by
    have ha : (tripleCharges (sourceA2360 + difference 3 5) (sourceB2360 + difference 5 3) sourceC2360) = raw12547 := by
      apply Matrix.ext; unfold tripleCharges sourceA2360 sourceB2360 sourceC2360 difference raw12547; decide +kernel
    rw [ha]
    exact (canonical12547 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2360 + difference 4 0) (sourceB2360 + difference 0 4) sourceC2360) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4524) := by
    have ha : (tripleCharges (sourceA2360 + difference 4 0) (sourceB2360 + difference 0 4) sourceC2360) = raw24571 := by
      apply Matrix.ext; unfold tripleCharges sourceA2360 sourceB2360 sourceC2360 difference raw24571; decide +kernel
    rw [ha]
    exact (canonical24571 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2360 + difference 4 1) (sourceB2360 + difference 1 4) sourceC2360) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4961) := by
    have ha : (tripleCharges (sourceA2360 + difference 4 1) (sourceB2360 + difference 1 4) sourceC2360) = raw32288 := by
      apply Matrix.ext; unfold tripleCharges sourceA2360 sourceB2360 sourceC2360 difference raw32288; decide +kernel
    rw [ha]
    exact (canonical32288 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2360 + difference 4 2) (sourceB2360 + difference 2 4) sourceC2360) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5119) := by
    have ha : (tripleCharges (sourceA2360 + difference 4 2) (sourceB2360 + difference 2 4) sourceC2360) = raw32289 := by
      apply Matrix.ext; unfold tripleCharges sourceA2360 sourceB2360 sourceC2360 difference raw32289; decide +kernel
    rw [ha]
    exact (canonical32289 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2360 + difference 4 3) (sourceB2360 + difference 3 4) sourceC2360) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5152) := by
    have ha : (tripleCharges (sourceA2360 + difference 4 3) (sourceB2360 + difference 3 4) sourceC2360) = raw32290 := by
      apply Matrix.ext; unfold tripleCharges sourceA2360 sourceB2360 sourceC2360 difference raw32290; decide +kernel
    rw [ha]
    exact (canonical32290 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2360 + difference 4 5) (sourceB2360 + difference 5 4) sourceC2360) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5149) := by
    have ha : (tripleCharges (sourceA2360 + difference 4 5) (sourceB2360 + difference 5 4) sourceC2360) = raw12552 := by
      apply Matrix.ext; unfold tripleCharges sourceA2360 sourceB2360 sourceC2360 difference raw12552; decide +kernel
    rw [ha]
    exact (canonical12552 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2360 + difference 5 0) (sourceB2360 + difference 0 5) sourceC2360) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4523) := by
    have ha : (tripleCharges (sourceA2360 + difference 5 0) (sourceB2360 + difference 0 5) sourceC2360) = raw24575 := by
      apply Matrix.ext; unfold tripleCharges sourceA2360 sourceB2360 sourceC2360 difference raw24575; decide +kernel
    rw [ha]
    exact (canonical24575 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2360 + difference 5 1) (sourceB2360 + difference 1 5) sourceC2360) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4960) := by
    have ha : (tripleCharges (sourceA2360 + difference 5 1) (sourceB2360 + difference 1 5) sourceC2360) = raw32291 := by
      apply Matrix.ext; unfold tripleCharges sourceA2360 sourceB2360 sourceC2360 difference raw32291; decide +kernel
    rw [ha]
    exact (canonical32291 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2360 + difference 5 2) (sourceB2360 + difference 2 5) sourceC2360) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5027) := by
    have ha : (tripleCharges (sourceA2360 + difference 5 2) (sourceB2360 + difference 2 5) sourceC2360) = raw32292 := by
      apply Matrix.ext; unfold tripleCharges sourceA2360 sourceB2360 sourceC2360 difference raw32292; decide +kernel
    rw [ha]
    exact (canonical32292 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2360 + difference 5 3) (sourceB2360 + difference 3 5) sourceC2360) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5078) := by
    have ha : (tripleCharges (sourceA2360 + difference 5 3) (sourceB2360 + difference 3 5) sourceC2360) = raw32293 := by
      apply Matrix.ext; unfold tripleCharges sourceA2360 sourceB2360 sourceC2360 difference raw32293; decide +kernel
    rw [ha]
    exact (canonical32293 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2360 + difference 5 4) (sourceB2360 + difference 4 5) sourceC2360) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5078) := by
    have ha : (tripleCharges (sourceA2360 + difference 5 4) (sourceB2360 + difference 4 5) sourceC2360) = raw32294 := by
      apply Matrix.ext; unfold tripleCharges sourceA2360 sourceB2360 sourceC2360 difference raw32294; decide +kernel
    rw [ha]
    exact (canonical32294 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2360 sourceB2360 sourceC2360
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2360, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2361 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2361 : Charge := ![1, 1, 1, -1, -1, -1]
def sourceC2361 : Charge := ![2, 0, -1, 0, 0, -1]
def sourceForm2361 : Integer.Sparse Master := [(Sum.inr 1107, 1), (Sum.inr 1108, 2), (Sum.inr 1129, 1), (Sum.inr 1240, 1), (Sum.inr 2412, 1), (Sum.inr 2416, 1), (Sum.inr 2485, 2), (Sum.inr 2796, 2), (Sum.inr 2809, 1), (Sum.inr 2845, 2), (Sum.inr 2884, 1), (Sum.inr 2924, 2), (Sum.inr 2931, 2), (Sum.inr 2958, 1), (Sum.inr 2960, 2), (Sum.inr 3100, 1), (Sum.inr 3102, 2), (Sum.inr 3721, 1), (Sum.inr 3964, 1), (Sum.inr 3982, 2), (Sum.inr 4033, 1)]

theorem sourceEq2361 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2361 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2361 + difference 0 1) (sourceB2361 + difference 1 0) sourceC2361) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3721) := by
    have ha : (tripleCharges (sourceA2361 + difference 0 1) (sourceB2361 + difference 1 0) sourceC2361) = raw32295 := by
      apply Matrix.ext; unfold tripleCharges sourceA2361 sourceB2361 sourceC2361 difference raw32295; decide +kernel
    rw [ha]
    exact (canonical32295 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2361 + difference 0 2) (sourceB2361 + difference 2 0) sourceC2361) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3964) := by
    have ha : (tripleCharges (sourceA2361 + difference 0 2) (sourceB2361 + difference 2 0) sourceC2361) = raw32296 := by
      apply Matrix.ext; unfold tripleCharges sourceA2361 sourceB2361 sourceC2361 difference raw32296; decide +kernel
    rw [ha]
    exact (canonical32296 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2361 + difference 0 3) (sourceB2361 + difference 3 0) sourceC2361) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3982) := by
    have ha : (tripleCharges (sourceA2361 + difference 0 3) (sourceB2361 + difference 3 0) sourceC2361) = raw32297 := by
      apply Matrix.ext; unfold tripleCharges sourceA2361 sourceB2361 sourceC2361 difference raw32297; decide +kernel
    rw [ha]
    exact (canonical32297 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2361 + difference 0 4) (sourceB2361 + difference 4 0) sourceC2361) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3982) := by
    have ha : (tripleCharges (sourceA2361 + difference 0 4) (sourceB2361 + difference 4 0) sourceC2361) = raw32298 := by
      apply Matrix.ext; unfold tripleCharges sourceA2361 sourceB2361 sourceC2361 difference raw32298; decide +kernel
    rw [ha]
    exact (canonical32298 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2361 + difference 0 5) (sourceB2361 + difference 5 0) sourceC2361) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4033) := by
    have ha : (tripleCharges (sourceA2361 + difference 0 5) (sourceB2361 + difference 5 0) sourceC2361) = raw12561 := by
      apply Matrix.ext; unfold tripleCharges sourceA2361 sourceB2361 sourceC2361 difference raw12561; decide +kernel
    rw [ha]
    exact (canonical12561 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2361 + difference 1 0) (sourceB2361 + difference 0 1) sourceC2361) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1240) := by
    have ha : (tripleCharges (sourceA2361 + difference 1 0) (sourceB2361 + difference 0 1) sourceC2361) = raw12586 := by
      apply Matrix.ext; unfold tripleCharges sourceA2361 sourceB2361 sourceC2361 difference raw12586; decide +kernel
    rw [ha]
    exact (canonical12586 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2361 + difference 1 2) (sourceB2361 + difference 2 1) sourceC2361) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2884) := by
    have ha : (tripleCharges (sourceA2361 + difference 1 2) (sourceB2361 + difference 2 1) sourceC2361) = raw12588 := by
      apply Matrix.ext; unfold tripleCharges sourceA2361 sourceB2361 sourceC2361 difference raw12588; decide +kernel
    rw [ha]
    exact (canonical12588 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2361 + difference 1 3) (sourceB2361 + difference 3 1) sourceC2361) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3102) := by
    have ha : (tripleCharges (sourceA2361 + difference 1 3) (sourceB2361 + difference 3 1) sourceC2361) = raw12589 := by
      apply Matrix.ext; unfold tripleCharges sourceA2361 sourceB2361 sourceC2361 difference raw12589; decide +kernel
    rw [ha]
    exact (canonical12589 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2361 + difference 1 4) (sourceB2361 + difference 4 1) sourceC2361) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3102) := by
    have ha : (tripleCharges (sourceA2361 + difference 1 4) (sourceB2361 + difference 4 1) sourceC2361) = raw12590 := by
      apply Matrix.ext; unfold tripleCharges sourceA2361 sourceB2361 sourceC2361 difference raw12590; decide +kernel
    rw [ha]
    exact (canonical12590 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2361 + difference 1 5) (sourceB2361 + difference 5 1) sourceC2361) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3100) := by
    have ha : (tripleCharges (sourceA2361 + difference 1 5) (sourceB2361 + difference 5 1) sourceC2361) = raw24579 := by
      apply Matrix.ext; unfold tripleCharges sourceA2361 sourceB2361 sourceC2361 difference raw24579; decide +kernel
    rw [ha]
    exact (canonical24579 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2361 + difference 2 0) (sourceB2361 + difference 0 2) sourceC2361) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1129) := by
    have ha : (tripleCharges (sourceA2361 + difference 2 0) (sourceB2361 + difference 0 2) sourceC2361) = raw24585 := by
      apply Matrix.ext; unfold tripleCharges sourceA2361 sourceB2361 sourceC2361 difference raw24585; decide +kernel
    rw [ha]
    exact (canonical24585 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2361 + difference 2 1) (sourceB2361 + difference 1 2) sourceC2361) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2809) := by
    have ha : (tripleCharges (sourceA2361 + difference 2 1) (sourceB2361 + difference 1 2) sourceC2361) = raw32299 := by
      apply Matrix.ext; unfold tripleCharges sourceA2361 sourceB2361 sourceC2361 difference raw32299; decide +kernel
    rw [ha]
    exact (canonical32299 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2361 + difference 2 3) (sourceB2361 + difference 3 2) sourceC2361) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2960) := by
    have ha : (tripleCharges (sourceA2361 + difference 2 3) (sourceB2361 + difference 3 2) sourceC2361) = raw32300 := by
      apply Matrix.ext; unfold tripleCharges sourceA2361 sourceB2361 sourceC2361 difference raw32300; decide +kernel
    rw [ha]
    exact (canonical32300 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2361 + difference 2 4) (sourceB2361 + difference 4 2) sourceC2361) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2960) := by
    have ha : (tripleCharges (sourceA2361 + difference 2 4) (sourceB2361 + difference 4 2) sourceC2361) = raw32301 := by
      apply Matrix.ext; unfold tripleCharges sourceA2361 sourceB2361 sourceC2361 difference raw32301; decide +kernel
    rw [ha]
    exact (canonical32301 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2361 + difference 2 5) (sourceB2361 + difference 5 2) sourceC2361) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2958) := by
    have ha : (tripleCharges (sourceA2361 + difference 2 5) (sourceB2361 + difference 5 2) sourceC2361) = raw12572 := by
      apply Matrix.ext; unfold tripleCharges sourceA2361 sourceB2361 sourceC2361 difference raw12572; decide +kernel
    rw [ha]
    exact (canonical12572 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2361 + difference 3 0) (sourceB2361 + difference 0 3) sourceC2361) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1108) := by
    have ha : (tripleCharges (sourceA2361 + difference 3 0) (sourceB2361 + difference 0 3) sourceC2361) = raw24589 := by
      apply Matrix.ext; unfold tripleCharges sourceA2361 sourceB2361 sourceC2361 difference raw24589; decide +kernel
    rw [ha]
    exact (canonical24589 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2361 + difference 3 1) (sourceB2361 + difference 1 3) sourceC2361) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2796) := by
    have ha : (tripleCharges (sourceA2361 + difference 3 1) (sourceB2361 + difference 1 3) sourceC2361) = raw32302 := by
      apply Matrix.ext; unfold tripleCharges sourceA2361 sourceB2361 sourceC2361 difference raw32302; decide +kernel
    rw [ha]
    exact (canonical32302 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2361 + difference 3 2) (sourceB2361 + difference 2 3) sourceC2361) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2845) := by
    have ha : (tripleCharges (sourceA2361 + difference 3 2) (sourceB2361 + difference 2 3) sourceC2361) = raw32303 := by
      apply Matrix.ext; unfold tripleCharges sourceA2361 sourceB2361 sourceC2361 difference raw32303; decide +kernel
    rw [ha]
    exact (canonical32303 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2361 + difference 3 4) (sourceB2361 + difference 4 3) sourceC2361) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2931) := by
    have ha : (tripleCharges (sourceA2361 + difference 3 4) (sourceB2361 + difference 4 3) sourceC2361) = raw32304 := by
      apply Matrix.ext; unfold tripleCharges sourceA2361 sourceB2361 sourceC2361 difference raw32304; decide +kernel
    rw [ha]
    exact (canonical32304 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2361 + difference 3 5) (sourceB2361 + difference 5 3) sourceC2361) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2924) := by
    have ha : (tripleCharges (sourceA2361 + difference 3 5) (sourceB2361 + difference 5 3) sourceC2361) = raw12577 := by
      apply Matrix.ext; unfold tripleCharges sourceA2361 sourceB2361 sourceC2361 difference raw12577; decide +kernel
    rw [ha]
    exact (canonical12577 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2361 + difference 4 0) (sourceB2361 + difference 0 4) sourceC2361) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1108) := by
    have ha : (tripleCharges (sourceA2361 + difference 4 0) (sourceB2361 + difference 0 4) sourceC2361) = raw24593 := by
      apply Matrix.ext; unfold tripleCharges sourceA2361 sourceB2361 sourceC2361 difference raw24593; decide +kernel
    rw [ha]
    exact (canonical24593 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2361 + difference 4 1) (sourceB2361 + difference 1 4) sourceC2361) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2796) := by
    have ha : (tripleCharges (sourceA2361 + difference 4 1) (sourceB2361 + difference 1 4) sourceC2361) = raw32305 := by
      apply Matrix.ext; unfold tripleCharges sourceA2361 sourceB2361 sourceC2361 difference raw32305; decide +kernel
    rw [ha]
    exact (canonical32305 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2361 + difference 4 2) (sourceB2361 + difference 2 4) sourceC2361) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2845) := by
    have ha : (tripleCharges (sourceA2361 + difference 4 2) (sourceB2361 + difference 2 4) sourceC2361) = raw32306 := by
      apply Matrix.ext; unfold tripleCharges sourceA2361 sourceB2361 sourceC2361 difference raw32306; decide +kernel
    rw [ha]
    exact (canonical32306 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2361 + difference 4 3) (sourceB2361 + difference 3 4) sourceC2361) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2931) := by
    have ha : (tripleCharges (sourceA2361 + difference 4 3) (sourceB2361 + difference 3 4) sourceC2361) = raw32307 := by
      apply Matrix.ext; unfold tripleCharges sourceA2361 sourceB2361 sourceC2361 difference raw32307; decide +kernel
    rw [ha]
    exact (canonical32307 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2361 + difference 4 5) (sourceB2361 + difference 5 4) sourceC2361) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2924) := by
    have ha : (tripleCharges (sourceA2361 + difference 4 5) (sourceB2361 + difference 5 4) sourceC2361) = raw12582 := by
      apply Matrix.ext; unfold tripleCharges sourceA2361 sourceB2361 sourceC2361 difference raw12582; decide +kernel
    rw [ha]
    exact (canonical12582 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2361 + difference 5 0) (sourceB2361 + difference 0 5) sourceC2361) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1107) := by
    have ha : (tripleCharges (sourceA2361 + difference 5 0) (sourceB2361 + difference 0 5) sourceC2361) = raw24597 := by
      apply Matrix.ext; unfold tripleCharges sourceA2361 sourceB2361 sourceC2361 difference raw24597; decide +kernel
    rw [ha]
    exact (canonical24597 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2361 + difference 5 1) (sourceB2361 + difference 1 5) sourceC2361) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2412) := by
    have ha : (tripleCharges (sourceA2361 + difference 5 1) (sourceB2361 + difference 1 5) sourceC2361) = raw32308 := by
      apply Matrix.ext; unfold tripleCharges sourceA2361 sourceB2361 sourceC2361 difference raw32308; decide +kernel
    rw [ha]
    exact (canonical32308 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2361 + difference 5 2) (sourceB2361 + difference 2 5) sourceC2361) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2416) := by
    have ha : (tripleCharges (sourceA2361 + difference 5 2) (sourceB2361 + difference 2 5) sourceC2361) = raw32309 := by
      apply Matrix.ext; unfold tripleCharges sourceA2361 sourceB2361 sourceC2361 difference raw32309; decide +kernel
    rw [ha]
    exact (canonical32309 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2361 + difference 5 3) (sourceB2361 + difference 3 5) sourceC2361) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2485) := by
    have ha : (tripleCharges (sourceA2361 + difference 5 3) (sourceB2361 + difference 3 5) sourceC2361) = raw32310 := by
      apply Matrix.ext; unfold tripleCharges sourceA2361 sourceB2361 sourceC2361 difference raw32310; decide +kernel
    rw [ha]
    exact (canonical32310 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2361 + difference 5 4) (sourceB2361 + difference 4 5) sourceC2361) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2485) := by
    have ha : (tripleCharges (sourceA2361 + difference 5 4) (sourceB2361 + difference 4 5) sourceC2361) = raw32311 := by
      apply Matrix.ext; unfold tripleCharges sourceA2361 sourceB2361 sourceC2361 difference raw32311; decide +kernel
    rw [ha]
    exact (canonical32311 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2361 sourceB2361 sourceC2361
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2361, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2362 : Charge := ![1, 1, 1, -1, -1, -1]
def sourceB2362 : Charge := ![2, 0, -1, 0, 0, -1]
def sourceC2362 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceForm2362 : Integer.Sparse Master := [(Sum.inr 4801, 1), (Sum.inr 4802, 2), (Sum.inr 4815, 1), (Sum.inr 4851, 1), (Sum.inr 5058, 1), (Sum.inr 5059, 2), (Sum.inr 5072, 1), (Sum.inr 5073, 2), (Sum.inr 5085, 1), (Sum.inr 5104, 1), (Sum.inr 5137, 1), (Sum.inr 5144, 2), (Sum.inr 5145, 2), (Sum.inr 5149, 2), (Sum.inr 5153, 2), (Sum.inr 5155, 1), (Sum.inr 5168, 1), (Sum.inr 5169, 2), (Sum.inr 5190, 2), (Sum.inr 5192, 1), (Sum.inr 5203, 1)]

theorem sourceEq2362 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2362 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2362 + difference 0 1) (sourceB2362 + difference 1 0) sourceC2362) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5137) := by
    have ha : (tripleCharges (sourceA2362 + difference 0 1) (sourceB2362 + difference 1 0) sourceC2362) = raw32312 := by
      apply Matrix.ext; unfold tripleCharges sourceA2362 sourceB2362 sourceC2362 difference raw32312; decide +kernel
    rw [ha]
    exact (canonical32312 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2362 + difference 0 2) (sourceB2362 + difference 2 0) sourceC2362) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5104) := by
    have ha : (tripleCharges (sourceA2362 + difference 0 2) (sourceB2362 + difference 2 0) sourceC2362) = raw32313 := by
      apply Matrix.ext; unfold tripleCharges sourceA2362 sourceB2362 sourceC2362 difference raw32313; decide +kernel
    rw [ha]
    exact (canonical32313 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2362 + difference 0 3) (sourceB2362 + difference 3 0) sourceC2362) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5059) := by
    have ha : (tripleCharges (sourceA2362 + difference 0 3) (sourceB2362 + difference 3 0) sourceC2362) = raw32314 := by
      apply Matrix.ext; unfold tripleCharges sourceA2362 sourceB2362 sourceC2362 difference raw32314; decide +kernel
    rw [ha]
    exact (canonical32314 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2362 + difference 0 4) (sourceB2362 + difference 4 0) sourceC2362) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5059) := by
    have ha : (tripleCharges (sourceA2362 + difference 0 4) (sourceB2362 + difference 4 0) sourceC2362) = raw32315 := by
      apply Matrix.ext; unfold tripleCharges sourceA2362 sourceB2362 sourceC2362 difference raw32315; decide +kernel
    rw [ha]
    exact (canonical32315 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2362 + difference 0 5) (sourceB2362 + difference 5 0) sourceC2362) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5058) := by
    have ha : (tripleCharges (sourceA2362 + difference 0 5) (sourceB2362 + difference 5 0) sourceC2362) = raw32316 := by
      apply Matrix.ext; unfold tripleCharges sourceA2362 sourceB2362 sourceC2362 difference raw32316; decide +kernel
    rw [ha]
    exact (canonical32316 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2362 + difference 1 0) (sourceB2362 + difference 0 1) sourceC2362) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4851) := by
    have ha : (tripleCharges (sourceA2362 + difference 1 0) (sourceB2362 + difference 0 1) sourceC2362) = raw32317 := by
      apply Matrix.ext; unfold tripleCharges sourceA2362 sourceB2362 sourceC2362 difference raw32317; decide +kernel
    rw [ha]
    exact (canonical32317 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2362 + difference 1 2) (sourceB2362 + difference 2 1) sourceC2362) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5203) := by
    have ha : (tripleCharges (sourceA2362 + difference 1 2) (sourceB2362 + difference 2 1) sourceC2362) = raw32318 := by
      apply Matrix.ext; unfold tripleCharges sourceA2362 sourceB2362 sourceC2362 difference raw32318; decide +kernel
    rw [ha]
    exact (canonical32318 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2362 + difference 1 3) (sourceB2362 + difference 3 1) sourceC2362) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5190) := by
    have ha : (tripleCharges (sourceA2362 + difference 1 3) (sourceB2362 + difference 3 1) sourceC2362) = raw32319 := by
      apply Matrix.ext; unfold tripleCharges sourceA2362 sourceB2362 sourceC2362 difference raw32319; decide +kernel
    rw [ha]
    exact (canonical32319 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2362 + difference 1 4) (sourceB2362 + difference 4 1) sourceC2362) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5190) := by
    have ha : (tripleCharges (sourceA2362 + difference 1 4) (sourceB2362 + difference 4 1) sourceC2362) = raw32320 := by
      apply Matrix.ext; unfold tripleCharges sourceA2362 sourceB2362 sourceC2362 difference raw32320; decide +kernel
    rw [ha]
    exact (canonical32320 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2362 + difference 1 5) (sourceB2362 + difference 5 1) sourceC2362) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5192) := by
    have ha : (tripleCharges (sourceA2362 + difference 1 5) (sourceB2362 + difference 5 1) sourceC2362) = raw32321 := by
      apply Matrix.ext; unfold tripleCharges sourceA2362 sourceB2362 sourceC2362 difference raw32321; decide +kernel
    rw [ha]
    exact (canonical32321 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2362 + difference 2 0) (sourceB2362 + difference 0 2) sourceC2362) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4815) := by
    have ha : (tripleCharges (sourceA2362 + difference 2 0) (sourceB2362 + difference 0 2) sourceC2362) = raw32322 := by
      apply Matrix.ext; unfold tripleCharges sourceA2362 sourceB2362 sourceC2362 difference raw32322; decide +kernel
    rw [ha]
    exact (canonical32322 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2362 + difference 2 1) (sourceB2362 + difference 1 2) sourceC2362) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5085) := by
    have ha : (tripleCharges (sourceA2362 + difference 2 1) (sourceB2362 + difference 1 2) sourceC2362) = raw32323 := by
      apply Matrix.ext; unfold tripleCharges sourceA2362 sourceB2362 sourceC2362 difference raw32323; decide +kernel
    rw [ha]
    exact (canonical32323 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2362 + difference 2 3) (sourceB2362 + difference 3 2) sourceC2362) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5153) := by
    have ha : (tripleCharges (sourceA2362 + difference 2 3) (sourceB2362 + difference 3 2) sourceC2362) = raw32324 := by
      apply Matrix.ext; unfold tripleCharges sourceA2362 sourceB2362 sourceC2362 difference raw32324; decide +kernel
    rw [ha]
    exact (canonical32324 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2362 + difference 2 4) (sourceB2362 + difference 4 2) sourceC2362) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5153) := by
    have ha : (tripleCharges (sourceA2362 + difference 2 4) (sourceB2362 + difference 4 2) sourceC2362) = raw32325 := by
      apply Matrix.ext; unfold tripleCharges sourceA2362 sourceB2362 sourceC2362 difference raw32325; decide +kernel
    rw [ha]
    exact (canonical32325 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2362 + difference 2 5) (sourceB2362 + difference 5 2) sourceC2362) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5155) := by
    have ha : (tripleCharges (sourceA2362 + difference 2 5) (sourceB2362 + difference 5 2) sourceC2362) = raw32326 := by
      apply Matrix.ext; unfold tripleCharges sourceA2362 sourceB2362 sourceC2362 difference raw32326; decide +kernel
    rw [ha]
    exact (canonical32326 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2362 + difference 3 0) (sourceB2362 + difference 0 3) sourceC2362) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA2362 + difference 3 0) (sourceB2362 + difference 0 3) sourceC2362) = raw32327 := by
      apply Matrix.ext; unfold tripleCharges sourceA2362 sourceB2362 sourceC2362 difference raw32327; decide +kernel
    rw [ha]
    exact (canonical32327 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2362 + difference 3 1) (sourceB2362 + difference 1 3) sourceC2362) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5073) := by
    have ha : (tripleCharges (sourceA2362 + difference 3 1) (sourceB2362 + difference 1 3) sourceC2362) = raw32328 := by
      apply Matrix.ext; unfold tripleCharges sourceA2362 sourceB2362 sourceC2362 difference raw32328; decide +kernel
    rw [ha]
    exact (canonical32328 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2362 + difference 3 2) (sourceB2362 + difference 2 3) sourceC2362) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA2362 + difference 3 2) (sourceB2362 + difference 2 3) sourceC2362) = raw32254 := by
      apply Matrix.ext; unfold tripleCharges sourceA2362 sourceB2362 sourceC2362 difference raw32254; decide +kernel
    rw [ha]
    exact (canonical32254 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2362 + difference 3 4) (sourceB2362 + difference 4 3) sourceC2362) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5145) := by
    have ha : (tripleCharges (sourceA2362 + difference 3 4) (sourceB2362 + difference 4 3) sourceC2362) = raw32329 := by
      apply Matrix.ext; unfold tripleCharges sourceA2362 sourceB2362 sourceC2362 difference raw32329; decide +kernel
    rw [ha]
    exact (canonical32329 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2362 + difference 3 5) (sourceB2362 + difference 5 3) sourceC2362) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5149) := by
    have ha : (tripleCharges (sourceA2362 + difference 3 5) (sourceB2362 + difference 5 3) sourceC2362) = raw32238 := by
      apply Matrix.ext; unfold tripleCharges sourceA2362 sourceB2362 sourceC2362 difference raw32238; decide +kernel
    rw [ha]
    exact (canonical32238 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2362 + difference 4 0) (sourceB2362 + difference 0 4) sourceC2362) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA2362 + difference 4 0) (sourceB2362 + difference 0 4) sourceC2362) = raw32330 := by
      apply Matrix.ext; unfold tripleCharges sourceA2362 sourceB2362 sourceC2362 difference raw32330; decide +kernel
    rw [ha]
    exact (canonical32330 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2362 + difference 4 1) (sourceB2362 + difference 1 4) sourceC2362) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5073) := by
    have ha : (tripleCharges (sourceA2362 + difference 4 1) (sourceB2362 + difference 1 4) sourceC2362) = raw32331 := by
      apply Matrix.ext; unfold tripleCharges sourceA2362 sourceB2362 sourceC2362 difference raw32331; decide +kernel
    rw [ha]
    exact (canonical32331 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2362 + difference 4 2) (sourceB2362 + difference 2 4) sourceC2362) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA2362 + difference 4 2) (sourceB2362 + difference 2 4) sourceC2362) = raw32253 := by
      apply Matrix.ext; unfold tripleCharges sourceA2362 sourceB2362 sourceC2362 difference raw32253; decide +kernel
    rw [ha]
    exact (canonical32253 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2362 + difference 4 3) (sourceB2362 + difference 3 4) sourceC2362) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5145) := by
    have ha : (tripleCharges (sourceA2362 + difference 4 3) (sourceB2362 + difference 3 4) sourceC2362) = raw32332 := by
      apply Matrix.ext; unfold tripleCharges sourceA2362 sourceB2362 sourceC2362 difference raw32332; decide +kernel
    rw [ha]
    exact (canonical32332 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2362 + difference 4 5) (sourceB2362 + difference 5 4) sourceC2362) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5149) := by
    have ha : (tripleCharges (sourceA2362 + difference 4 5) (sourceB2362 + difference 5 4) sourceC2362) = raw32237 := by
      apply Matrix.ext; unfold tripleCharges sourceA2362 sourceB2362 sourceC2362 difference raw32237; decide +kernel
    rw [ha]
    exact (canonical32237 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2362 + difference 5 0) (sourceB2362 + difference 0 5) sourceC2362) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4801) := by
    have ha : (tripleCharges (sourceA2362 + difference 5 0) (sourceB2362 + difference 0 5) sourceC2362) = raw32333 := by
      apply Matrix.ext; unfold tripleCharges sourceA2362 sourceB2362 sourceC2362 difference raw32333; decide +kernel
    rw [ha]
    exact (canonical32333 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2362 + difference 5 1) (sourceB2362 + difference 1 5) sourceC2362) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5072) := by
    have ha : (tripleCharges (sourceA2362 + difference 5 1) (sourceB2362 + difference 1 5) sourceC2362) = raw32334 := by
      apply Matrix.ext; unfold tripleCharges sourceA2362 sourceB2362 sourceC2362 difference raw32334; decide +kernel
    rw [ha]
    exact (canonical32334 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2362 + difference 5 2) (sourceB2362 + difference 2 5) sourceC2362) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5168) := by
    have ha : (tripleCharges (sourceA2362 + difference 5 2) (sourceB2362 + difference 2 5) sourceC2362) = raw32335 := by
      apply Matrix.ext; unfold tripleCharges sourceA2362 sourceB2362 sourceC2362 difference raw32335; decide +kernel
    rw [ha]
    exact (canonical32335 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2362 + difference 5 3) (sourceB2362 + difference 3 5) sourceC2362) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5144) := by
    have ha : (tripleCharges (sourceA2362 + difference 5 3) (sourceB2362 + difference 3 5) sourceC2362) = raw32336 := by
      apply Matrix.ext; unfold tripleCharges sourceA2362 sourceB2362 sourceC2362 difference raw32336; decide +kernel
    rw [ha]
    exact (canonical32336 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2362 + difference 5 4) (sourceB2362 + difference 4 5) sourceC2362) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5144) := by
    have ha : (tripleCharges (sourceA2362 + difference 5 4) (sourceB2362 + difference 4 5) sourceC2362) = raw32337 := by
      apply Matrix.ext; unfold tripleCharges sourceA2362 sourceB2362 sourceC2362 difference raw32337; decide +kernel
    rw [ha]
    exact (canonical32337 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2362 sourceB2362 sourceC2362
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2362, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2363 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2363 : Charge := ![1, 1, 1, -1, 0, -2]
def sourceC2363 : Charge := ![2, 0, -1, 0, -1, 0]
def sourceForm2363 : Integer.Sparse Master := [(Sum.inr 4521, 1), (Sum.inr 4522, 1), (Sum.inr 4524, 1), (Sum.inr 4541, 1), (Sum.inr 4602, 1), (Sum.inr 4707, 1), (Sum.inr 4713, 1), (Sum.inr 4729, 1), (Sum.inr 4807, 1), (Sum.inr 4961, 1), (Sum.inr 4962, 1), (Sum.inr 4971, 1), (Sum.inr 5119, 1), (Sum.inr 5120, 1), (Sum.inr 5142, 1), (Sum.inr 5148, 1), (Sum.inr 5149, 2), (Sum.inr 5152, 1), (Sum.inr 5167, 1), (Sum.inr 5172, 1), (Sum.inr 5204, 1), (Sum.inr 5284, 1), (Sum.inr 5292, 1), (Sum.inr 5294, 1), (Sum.inr 5378, 1), (Sum.inr 5397, 1), (Sum.inr 5406, 1), (Sum.inr 5433, 1), (Sum.inr 5435, 1)]

theorem sourceEq2363 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2363 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2363 + difference 0 1) (sourceB2363 + difference 1 0) sourceC2363) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA2363 + difference 0 1) (sourceB2363 + difference 1 0) sourceC2363) = raw32338 := by
      apply Matrix.ext; unfold tripleCharges sourceA2363 sourceB2363 sourceC2363 difference raw32338; decide +kernel
    rw [ha]
    exact (canonical32338 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2363 + difference 0 2) (sourceB2363 + difference 2 0) sourceC2363) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5397) := by
    have ha : (tripleCharges (sourceA2363 + difference 0 2) (sourceB2363 + difference 2 0) sourceC2363) = raw32339 := by
      apply Matrix.ext; unfold tripleCharges sourceA2363 sourceB2363 sourceC2363 difference raw32339; decide +kernel
    rw [ha]
    exact (canonical32339 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2363 + difference 0 3) (sourceB2363 + difference 3 0) sourceC2363) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA2363 + difference 0 3) (sourceB2363 + difference 3 0) sourceC2363) = raw32340 := by
      apply Matrix.ext; unfold tripleCharges sourceA2363 sourceB2363 sourceC2363 difference raw32340; decide +kernel
    rw [ha]
    exact (canonical32340 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2363 + difference 0 4) (sourceB2363 + difference 4 0) sourceC2363) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5406) := by
    have ha : (tripleCharges (sourceA2363 + difference 0 4) (sourceB2363 + difference 4 0) sourceC2363) = raw32341 := by
      apply Matrix.ext; unfold tripleCharges sourceA2363 sourceB2363 sourceC2363 difference raw32341; decide +kernel
    rw [ha]
    exact (canonical32341 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2363 + difference 0 5) (sourceB2363 + difference 5 0) sourceC2363) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA2363 + difference 0 5) (sourceB2363 + difference 5 0) sourceC2363) = raw32342 := by
      apply Matrix.ext; unfold tripleCharges sourceA2363 sourceB2363 sourceC2363 difference raw32342; decide +kernel
    rw [ha]
    exact (canonical32342 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2363 + difference 1 0) (sourceB2363 + difference 0 1) sourceC2363) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA2363 + difference 1 0) (sourceB2363 + difference 0 1) sourceC2363) = raw32343 := by
      apply Matrix.ext; unfold tripleCharges sourceA2363 sourceB2363 sourceC2363 difference raw32343; decide +kernel
    rw [ha]
    exact (canonical32343 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2363 + difference 1 2) (sourceB2363 + difference 2 1) sourceC2363) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5204) := by
    have ha : (tripleCharges (sourceA2363 + difference 1 2) (sourceB2363 + difference 2 1) sourceC2363) = raw24753 := by
      apply Matrix.ext; unfold tripleCharges sourceA2363 sourceB2363 sourceC2363 difference raw24753; decide +kernel
    rw [ha]
    exact (canonical24753 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2363 + difference 1 3) (sourceB2363 + difference 3 1) sourceC2363) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA2363 + difference 1 3) (sourceB2363 + difference 3 1) sourceC2363) = raw24754 := by
      apply Matrix.ext; unfold tripleCharges sourceA2363 sourceB2363 sourceC2363 difference raw24754; decide +kernel
    rw [ha]
    exact (canonical24754 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2363 + difference 1 4) (sourceB2363 + difference 4 1) sourceC2363) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA2363 + difference 1 4) (sourceB2363 + difference 4 1) sourceC2363) = raw24755 := by
      apply Matrix.ext; unfold tripleCharges sourceA2363 sourceB2363 sourceC2363 difference raw24755; decide +kernel
    rw [ha]
    exact (canonical24755 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2363 + difference 1 5) (sourceB2363 + difference 5 1) sourceC2363) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA2363 + difference 1 5) (sourceB2363 + difference 5 1) sourceC2363) = raw24756 := by
      apply Matrix.ext; unfold tripleCharges sourceA2363 sourceB2363 sourceC2363 difference raw24756; decide +kernel
    rw [ha]
    exact (canonical24756 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2363 + difference 2 0) (sourceB2363 + difference 0 2) sourceC2363) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4541) := by
    have ha : (tripleCharges (sourceA2363 + difference 2 0) (sourceB2363 + difference 0 2) sourceC2363) = raw24763 := by
      apply Matrix.ext; unfold tripleCharges sourceA2363 sourceB2363 sourceC2363 difference raw24763; decide +kernel
    rw [ha]
    exact (canonical24763 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2363 + difference 2 1) (sourceB2363 + difference 1 2) sourceC2363) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4971) := by
    have ha : (tripleCharges (sourceA2363 + difference 2 1) (sourceB2363 + difference 1 2) sourceC2363) = raw32344 := by
      apply Matrix.ext; unfold tripleCharges sourceA2363 sourceB2363 sourceC2363 difference raw32344; decide +kernel
    rw [ha]
    exact (canonical32344 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2363 + difference 2 3) (sourceB2363 + difference 3 2) sourceC2363) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5172) := by
    have ha : (tripleCharges (sourceA2363 + difference 2 3) (sourceB2363 + difference 3 2) sourceC2363) = raw32345 := by
      apply Matrix.ext; unfold tripleCharges sourceA2363 sourceB2363 sourceC2363 difference raw32345; decide +kernel
    rw [ha]
    exact (canonical32345 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2363 + difference 2 4) (sourceB2363 + difference 4 2) sourceC2363) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5149) := by
    have ha : (tripleCharges (sourceA2363 + difference 2 4) (sourceB2363 + difference 4 2) sourceC2363) = raw32346 := by
      apply Matrix.ext; unfold tripleCharges sourceA2363 sourceB2363 sourceC2363 difference raw32346; decide +kernel
    rw [ha]
    exact (canonical32346 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2363 + difference 2 5) (sourceB2363 + difference 5 2) sourceC2363) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5167) := by
    have ha : (tripleCharges (sourceA2363 + difference 2 5) (sourceB2363 + difference 5 2) sourceC2363) = raw32347 := by
      apply Matrix.ext; unfold tripleCharges sourceA2363 sourceB2363 sourceC2363 difference raw32347; decide +kernel
    rw [ha]
    exact (canonical32347 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2363 + difference 3 0) (sourceB2363 + difference 0 3) sourceC2363) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4522) := by
    have ha : (tripleCharges (sourceA2363 + difference 3 0) (sourceB2363 + difference 0 3) sourceC2363) = raw24768 := by
      apply Matrix.ext; unfold tripleCharges sourceA2363 sourceB2363 sourceC2363 difference raw24768; decide +kernel
    rw [ha]
    exact (canonical24768 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2363 + difference 3 1) (sourceB2363 + difference 1 3) sourceC2363) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4962) := by
    have ha : (tripleCharges (sourceA2363 + difference 3 1) (sourceB2363 + difference 1 3) sourceC2363) = raw32348 := by
      apply Matrix.ext; unfold tripleCharges sourceA2363 sourceB2363 sourceC2363 difference raw32348; decide +kernel
    rw [ha]
    exact (canonical32348 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2363 + difference 3 2) (sourceB2363 + difference 2 3) sourceC2363) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5120) := by
    have ha : (tripleCharges (sourceA2363 + difference 3 2) (sourceB2363 + difference 2 3) sourceC2363) = raw32349 := by
      apply Matrix.ext; unfold tripleCharges sourceA2363 sourceB2363 sourceC2363 difference raw32349; decide +kernel
    rw [ha]
    exact (canonical32349 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2363 + difference 3 4) (sourceB2363 + difference 4 3) sourceC2363) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5142) := by
    have ha : (tripleCharges (sourceA2363 + difference 3 4) (sourceB2363 + difference 4 3) sourceC2363) = raw32350 := by
      apply Matrix.ext; unfold tripleCharges sourceA2363 sourceB2363 sourceC2363 difference raw32350; decide +kernel
    rw [ha]
    exact (canonical32350 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2363 + difference 3 5) (sourceB2363 + difference 5 3) sourceC2363) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5149) := by
    have ha : (tripleCharges (sourceA2363 + difference 3 5) (sourceB2363 + difference 5 3) sourceC2363) = raw32351 := by
      apply Matrix.ext; unfold tripleCharges sourceA2363 sourceB2363 sourceC2363 difference raw32351; decide +kernel
    rw [ha]
    exact (canonical32351 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2363 + difference 4 0) (sourceB2363 + difference 0 4) sourceC2363) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4524) := by
    have ha : (tripleCharges (sourceA2363 + difference 4 0) (sourceB2363 + difference 0 4) sourceC2363) = raw24773 := by
      apply Matrix.ext; unfold tripleCharges sourceA2363 sourceB2363 sourceC2363 difference raw24773; decide +kernel
    rw [ha]
    exact (canonical24773 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2363 + difference 4 1) (sourceB2363 + difference 1 4) sourceC2363) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4961) := by
    have ha : (tripleCharges (sourceA2363 + difference 4 1) (sourceB2363 + difference 1 4) sourceC2363) = raw32352 := by
      apply Matrix.ext; unfold tripleCharges sourceA2363 sourceB2363 sourceC2363 difference raw32352; decide +kernel
    rw [ha]
    exact (canonical32352 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2363 + difference 4 2) (sourceB2363 + difference 2 4) sourceC2363) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5119) := by
    have ha : (tripleCharges (sourceA2363 + difference 4 2) (sourceB2363 + difference 2 4) sourceC2363) = raw32353 := by
      apply Matrix.ext; unfold tripleCharges sourceA2363 sourceB2363 sourceC2363 difference raw32353; decide +kernel
    rw [ha]
    exact (canonical32353 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2363 + difference 4 3) (sourceB2363 + difference 3 4) sourceC2363) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5152) := by
    have ha : (tripleCharges (sourceA2363 + difference 4 3) (sourceB2363 + difference 3 4) sourceC2363) = raw32354 := by
      apply Matrix.ext; unfold tripleCharges sourceA2363 sourceB2363 sourceC2363 difference raw32354; decide +kernel
    rw [ha]
    exact (canonical32354 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2363 + difference 4 5) (sourceB2363 + difference 5 4) sourceC2363) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5148) := by
    have ha : (tripleCharges (sourceA2363 + difference 4 5) (sourceB2363 + difference 5 4) sourceC2363) = raw32355 := by
      apply Matrix.ext; unfold tripleCharges sourceA2363 sourceB2363 sourceC2363 difference raw32355; decide +kernel
    rw [ha]
    exact (canonical32355 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2363 + difference 5 0) (sourceB2363 + difference 0 5) sourceC2363) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4521) := by
    have ha : (tripleCharges (sourceA2363 + difference 5 0) (sourceB2363 + difference 0 5) sourceC2363) = raw24778 := by
      apply Matrix.ext; unfold tripleCharges sourceA2363 sourceB2363 sourceC2363 difference raw24778; decide +kernel
    rw [ha]
    exact (canonical24778 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2363 + difference 5 1) (sourceB2363 + difference 1 5) sourceC2363) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4707) := by
    have ha : (tripleCharges (sourceA2363 + difference 5 1) (sourceB2363 + difference 1 5) sourceC2363) = raw32356 := by
      apply Matrix.ext; unfold tripleCharges sourceA2363 sourceB2363 sourceC2363 difference raw32356; decide +kernel
    rw [ha]
    exact (canonical32356 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2363 + difference 5 2) (sourceB2363 + difference 2 5) sourceC2363) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4713) := by
    have ha : (tripleCharges (sourceA2363 + difference 5 2) (sourceB2363 + difference 2 5) sourceC2363) = raw32357 := by
      apply Matrix.ext; unfold tripleCharges sourceA2363 sourceB2363 sourceC2363 difference raw32357; decide +kernel
    rw [ha]
    exact (canonical32357 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2363 + difference 5 3) (sourceB2363 + difference 3 5) sourceC2363) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA2363 + difference 5 3) (sourceB2363 + difference 3 5) sourceC2363) = raw32358 := by
      apply Matrix.ext; unfold tripleCharges sourceA2363 sourceB2363 sourceC2363 difference raw32358; decide +kernel
    rw [ha]
    exact (canonical32358 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2363 + difference 5 4) (sourceB2363 + difference 4 5) sourceC2363) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4729) := by
    have ha : (tripleCharges (sourceA2363 + difference 5 4) (sourceB2363 + difference 4 5) sourceC2363) = raw32359 := by
      apply Matrix.ext; unfold tripleCharges sourceA2363 sourceB2363 sourceC2363 difference raw32359; decide +kernel
    rw [ha]
    exact (canonical32359 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2363 sourceB2363 sourceC2363
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2363, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2364 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2364 : Charge := ![1, 1, 1, -1, 0, -2]
def sourceC2364 : Charge := ![2, 0, -1, 0, -1, 0]
def sourceForm2364 : Integer.Sparse Master := [(Sum.inr 1105, 1), (Sum.inr 1106, 1), (Sum.inr 1108, 1), (Sum.inr 1126, 1), (Sum.inr 1236, 1), (Sum.inr 1861, 1), (Sum.inr 1867, 1), (Sum.inr 1898, 1), (Sum.inr 2025, 1), (Sum.inr 2795, 1), (Sum.inr 2796, 1), (Sum.inr 2807, 1), (Sum.inr 2844, 1), (Sum.inr 2845, 1), (Sum.inr 2881, 1), (Sum.inr 2913, 1), (Sum.inr 2924, 2), (Sum.inr 2927, 1), (Sum.inr 2931, 1), (Sum.inr 2958, 1), (Sum.inr 2959, 1), (Sum.inr 3077, 1), (Sum.inr 3100, 1), (Sum.inr 3101, 1), (Sum.inr 3719, 1), (Sum.inr 3782, 1), (Sum.inr 3801, 1), (Sum.inr 3853, 1), (Sum.inr 4033, 1)]

theorem sourceEq2364 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2364 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2364 + difference 0 1) (sourceB2364 + difference 1 0) sourceC2364) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3719) := by
    have ha : (tripleCharges (sourceA2364 + difference 0 1) (sourceB2364 + difference 1 0) sourceC2364) = raw32360 := by
      apply Matrix.ext; unfold tripleCharges sourceA2364 sourceB2364 sourceC2364 difference raw32360; decide +kernel
    rw [ha]
    exact (canonical32360 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2364 + difference 0 2) (sourceB2364 + difference 2 0) sourceC2364) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3782) := by
    have ha : (tripleCharges (sourceA2364 + difference 0 2) (sourceB2364 + difference 2 0) sourceC2364) = raw32361 := by
      apply Matrix.ext; unfold tripleCharges sourceA2364 sourceB2364 sourceC2364 difference raw32361; decide +kernel
    rw [ha]
    exact (canonical32361 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2364 + difference 0 3) (sourceB2364 + difference 3 0) sourceC2364) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3853) := by
    have ha : (tripleCharges (sourceA2364 + difference 0 3) (sourceB2364 + difference 3 0) sourceC2364) = raw32362 := by
      apply Matrix.ext; unfold tripleCharges sourceA2364 sourceB2364 sourceC2364 difference raw32362; decide +kernel
    rw [ha]
    exact (canonical32362 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2364 + difference 0 4) (sourceB2364 + difference 4 0) sourceC2364) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3801) := by
    have ha : (tripleCharges (sourceA2364 + difference 0 4) (sourceB2364 + difference 4 0) sourceC2364) = raw32363 := by
      apply Matrix.ext; unfold tripleCharges sourceA2364 sourceB2364 sourceC2364 difference raw32363; decide +kernel
    rw [ha]
    exact (canonical32363 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2364 + difference 0 5) (sourceB2364 + difference 5 0) sourceC2364) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4033) := by
    have ha : (tripleCharges (sourceA2364 + difference 0 5) (sourceB2364 + difference 5 0) sourceC2364) = raw32364 := by
      apply Matrix.ext; unfold tripleCharges sourceA2364 sourceB2364 sourceC2364 difference raw32364; decide +kernel
    rw [ha]
    exact (canonical32364 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2364 + difference 1 0) (sourceB2364 + difference 0 1) sourceC2364) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1236) := by
    have ha : (tripleCharges (sourceA2364 + difference 1 0) (sourceB2364 + difference 0 1) sourceC2364) = raw32365 := by
      apply Matrix.ext; unfold tripleCharges sourceA2364 sourceB2364 sourceC2364 difference raw32365; decide +kernel
    rw [ha]
    exact (canonical32365 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2364 + difference 1 2) (sourceB2364 + difference 2 1) sourceC2364) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2881) := by
    have ha : (tripleCharges (sourceA2364 + difference 1 2) (sourceB2364 + difference 2 1) sourceC2364) = raw24783 := by
      apply Matrix.ext; unfold tripleCharges sourceA2364 sourceB2364 sourceC2364 difference raw24783; decide +kernel
    rw [ha]
    exact (canonical24783 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2364 + difference 1 3) (sourceB2364 + difference 3 1) sourceC2364) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3101) := by
    have ha : (tripleCharges (sourceA2364 + difference 1 3) (sourceB2364 + difference 3 1) sourceC2364) = raw24784 := by
      apply Matrix.ext; unfold tripleCharges sourceA2364 sourceB2364 sourceC2364 difference raw24784; decide +kernel
    rw [ha]
    exact (canonical24784 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2364 + difference 1 4) (sourceB2364 + difference 4 1) sourceC2364) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3077) := by
    have ha : (tripleCharges (sourceA2364 + difference 1 4) (sourceB2364 + difference 4 1) sourceC2364) = raw24785 := by
      apply Matrix.ext; unfold tripleCharges sourceA2364 sourceB2364 sourceC2364 difference raw24785; decide +kernel
    rw [ha]
    exact (canonical24785 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2364 + difference 1 5) (sourceB2364 + difference 5 1) sourceC2364) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3100) := by
    have ha : (tripleCharges (sourceA2364 + difference 1 5) (sourceB2364 + difference 5 1) sourceC2364) = raw24786 := by
      apply Matrix.ext; unfold tripleCharges sourceA2364 sourceB2364 sourceC2364 difference raw24786; decide +kernel
    rw [ha]
    exact (canonical24786 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2364 + difference 2 0) (sourceB2364 + difference 0 2) sourceC2364) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1126) := by
    have ha : (tripleCharges (sourceA2364 + difference 2 0) (sourceB2364 + difference 0 2) sourceC2364) = raw24793 := by
      apply Matrix.ext; unfold tripleCharges sourceA2364 sourceB2364 sourceC2364 difference raw24793; decide +kernel
    rw [ha]
    exact (canonical24793 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2364 + difference 2 1) (sourceB2364 + difference 1 2) sourceC2364) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2807) := by
    have ha : (tripleCharges (sourceA2364 + difference 2 1) (sourceB2364 + difference 1 2) sourceC2364) = raw32366 := by
      apply Matrix.ext; unfold tripleCharges sourceA2364 sourceB2364 sourceC2364 difference raw32366; decide +kernel
    rw [ha]
    exact (canonical32366 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2364 + difference 2 3) (sourceB2364 + difference 3 2) sourceC2364) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2959) := by
    have ha : (tripleCharges (sourceA2364 + difference 2 3) (sourceB2364 + difference 3 2) sourceC2364) = raw32367 := by
      apply Matrix.ext; unfold tripleCharges sourceA2364 sourceB2364 sourceC2364 difference raw32367; decide +kernel
    rw [ha]
    exact (canonical32367 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2364 + difference 2 4) (sourceB2364 + difference 4 2) sourceC2364) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2924) := by
    have ha : (tripleCharges (sourceA2364 + difference 2 4) (sourceB2364 + difference 4 2) sourceC2364) = raw32368 := by
      apply Matrix.ext; unfold tripleCharges sourceA2364 sourceB2364 sourceC2364 difference raw32368; decide +kernel
    rw [ha]
    exact (canonical32368 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2364 + difference 2 5) (sourceB2364 + difference 5 2) sourceC2364) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2958) := by
    have ha : (tripleCharges (sourceA2364 + difference 2 5) (sourceB2364 + difference 5 2) sourceC2364) = raw32369 := by
      apply Matrix.ext; unfold tripleCharges sourceA2364 sourceB2364 sourceC2364 difference raw32369; decide +kernel
    rw [ha]
    exact (canonical32369 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2364 + difference 3 0) (sourceB2364 + difference 0 3) sourceC2364) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1106) := by
    have ha : (tripleCharges (sourceA2364 + difference 3 0) (sourceB2364 + difference 0 3) sourceC2364) = raw24798 := by
      apply Matrix.ext; unfold tripleCharges sourceA2364 sourceB2364 sourceC2364 difference raw24798; decide +kernel
    rw [ha]
    exact (canonical24798 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2364 + difference 3 1) (sourceB2364 + difference 1 3) sourceC2364) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2795) := by
    have ha : (tripleCharges (sourceA2364 + difference 3 1) (sourceB2364 + difference 1 3) sourceC2364) = raw32370 := by
      apply Matrix.ext; unfold tripleCharges sourceA2364 sourceB2364 sourceC2364 difference raw32370; decide +kernel
    rw [ha]
    exact (canonical32370 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2364 + difference 3 2) (sourceB2364 + difference 2 3) sourceC2364) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2844) := by
    have ha : (tripleCharges (sourceA2364 + difference 3 2) (sourceB2364 + difference 2 3) sourceC2364) = raw32371 := by
      apply Matrix.ext; unfold tripleCharges sourceA2364 sourceB2364 sourceC2364 difference raw32371; decide +kernel
    rw [ha]
    exact (canonical32371 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2364 + difference 3 4) (sourceB2364 + difference 4 3) sourceC2364) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2913) := by
    have ha : (tripleCharges (sourceA2364 + difference 3 4) (sourceB2364 + difference 4 3) sourceC2364) = raw32372 := by
      apply Matrix.ext; unfold tripleCharges sourceA2364 sourceB2364 sourceC2364 difference raw32372; decide +kernel
    rw [ha]
    exact (canonical32372 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2364 + difference 3 5) (sourceB2364 + difference 5 3) sourceC2364) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2924) := by
    have ha : (tripleCharges (sourceA2364 + difference 3 5) (sourceB2364 + difference 5 3) sourceC2364) = raw32373 := by
      apply Matrix.ext; unfold tripleCharges sourceA2364 sourceB2364 sourceC2364 difference raw32373; decide +kernel
    rw [ha]
    exact (canonical32373 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2364 + difference 4 0) (sourceB2364 + difference 0 4) sourceC2364) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1108) := by
    have ha : (tripleCharges (sourceA2364 + difference 4 0) (sourceB2364 + difference 0 4) sourceC2364) = raw24803 := by
      apply Matrix.ext; unfold tripleCharges sourceA2364 sourceB2364 sourceC2364 difference raw24803; decide +kernel
    rw [ha]
    exact (canonical24803 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2364 + difference 4 1) (sourceB2364 + difference 1 4) sourceC2364) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2796) := by
    have ha : (tripleCharges (sourceA2364 + difference 4 1) (sourceB2364 + difference 1 4) sourceC2364) = raw32374 := by
      apply Matrix.ext; unfold tripleCharges sourceA2364 sourceB2364 sourceC2364 difference raw32374; decide +kernel
    rw [ha]
    exact (canonical32374 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2364 + difference 4 2) (sourceB2364 + difference 2 4) sourceC2364) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2845) := by
    have ha : (tripleCharges (sourceA2364 + difference 4 2) (sourceB2364 + difference 2 4) sourceC2364) = raw32375 := by
      apply Matrix.ext; unfold tripleCharges sourceA2364 sourceB2364 sourceC2364 difference raw32375; decide +kernel
    rw [ha]
    exact (canonical32375 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2364 + difference 4 3) (sourceB2364 + difference 3 4) sourceC2364) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2931) := by
    have ha : (tripleCharges (sourceA2364 + difference 4 3) (sourceB2364 + difference 3 4) sourceC2364) = raw32376 := by
      apply Matrix.ext; unfold tripleCharges sourceA2364 sourceB2364 sourceC2364 difference raw32376; decide +kernel
    rw [ha]
    exact (canonical32376 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2364 + difference 4 5) (sourceB2364 + difference 5 4) sourceC2364) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2927) := by
    have ha : (tripleCharges (sourceA2364 + difference 4 5) (sourceB2364 + difference 5 4) sourceC2364) = raw32377 := by
      apply Matrix.ext; unfold tripleCharges sourceA2364 sourceB2364 sourceC2364 difference raw32377; decide +kernel
    rw [ha]
    exact (canonical32377 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2364 + difference 5 0) (sourceB2364 + difference 0 5) sourceC2364) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1105) := by
    have ha : (tripleCharges (sourceA2364 + difference 5 0) (sourceB2364 + difference 0 5) sourceC2364) = raw24808 := by
      apply Matrix.ext; unfold tripleCharges sourceA2364 sourceB2364 sourceC2364 difference raw24808; decide +kernel
    rw [ha]
    exact (canonical24808 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2364 + difference 5 1) (sourceB2364 + difference 1 5) sourceC2364) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1861) := by
    have ha : (tripleCharges (sourceA2364 + difference 5 1) (sourceB2364 + difference 1 5) sourceC2364) = raw32378 := by
      apply Matrix.ext; unfold tripleCharges sourceA2364 sourceB2364 sourceC2364 difference raw32378; decide +kernel
    rw [ha]
    exact (canonical32378 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2364 + difference 5 2) (sourceB2364 + difference 2 5) sourceC2364) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1867) := by
    have ha : (tripleCharges (sourceA2364 + difference 5 2) (sourceB2364 + difference 2 5) sourceC2364) = raw32379 := by
      apply Matrix.ext; unfold tripleCharges sourceA2364 sourceB2364 sourceC2364 difference raw32379; decide +kernel
    rw [ha]
    exact (canonical32379 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2364 + difference 5 3) (sourceB2364 + difference 3 5) sourceC2364) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2025) := by
    have ha : (tripleCharges (sourceA2364 + difference 5 3) (sourceB2364 + difference 3 5) sourceC2364) = raw32380 := by
      apply Matrix.ext; unfold tripleCharges sourceA2364 sourceB2364 sourceC2364 difference raw32380; decide +kernel
    rw [ha]
    exact (canonical32380 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2364 + difference 5 4) (sourceB2364 + difference 4 5) sourceC2364) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1898) := by
    have ha : (tripleCharges (sourceA2364 + difference 5 4) (sourceB2364 + difference 4 5) sourceC2364) = raw32381 := by
      apply Matrix.ext; unfold tripleCharges sourceA2364 sourceB2364 sourceC2364 difference raw32381; decide +kernel
    rw [ha]
    exact (canonical32381 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2364 sourceB2364 sourceC2364
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2364, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2365 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2365 : Charge := ![2, 0, -1, 0, -1, 0]
def sourceC2365 : Charge := ![1, 1, 1, -1, 0, -2]
def sourceForm2365 : Integer.Sparse Master := [(Sum.inr 4327, 1), (Sum.inr 4328, 1), (Sum.inr 4332, 1), (Sum.inr 4345, 1), (Sum.inr 4439, 1), (Sum.inr 4930, 1), (Sum.inr 4931, 1), (Sum.inr 4933, 1), (Sum.inr 4942, 1), (Sum.inr 5037, 1), (Sum.inr 5078, 1), (Sum.inr 5114, 1), (Sum.inr 5117, 1), (Sum.inr 5128, 1), (Sum.inr 5129, 1), (Sum.inr 5138, 1), (Sum.inr 5144, 1), (Sum.inr 5145, 1), (Sum.inr 5149, 1), (Sum.inr 5152, 1), (Sum.inr 5160, 1), (Sum.inr 5170, 1), (Sum.inr 5251, 1), (Sum.inr 5281, 1), (Sum.inr 5284, 1), (Sum.inr 5393, 1), (Sum.inr 5396, 1), (Sum.inr 5410, 1), (Sum.inr 5424, 1), (Sum.inr 5478, 1)]

theorem sourceEq2365 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2365 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2365 + difference 0 1) (sourceB2365 + difference 1 0) sourceC2365) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5393) := by
    have ha : (tripleCharges (sourceA2365 + difference 0 1) (sourceB2365 + difference 1 0) sourceC2365) = raw32382 := by
      apply Matrix.ext; unfold tripleCharges sourceA2365 sourceB2365 sourceC2365 difference raw32382; decide +kernel
    rw [ha]
    exact (canonical32382 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2365 + difference 0 2) (sourceB2365 + difference 2 0) sourceC2365) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5396) := by
    have ha : (tripleCharges (sourceA2365 + difference 0 2) (sourceB2365 + difference 2 0) sourceC2365) = raw32383 := by
      apply Matrix.ext; unfold tripleCharges sourceA2365 sourceB2365 sourceC2365 difference raw32383; decide +kernel
    rw [ha]
    exact (canonical32383 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2365 + difference 0 3) (sourceB2365 + difference 3 0) sourceC2365) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA2365 + difference 0 3) (sourceB2365 + difference 3 0) sourceC2365) = raw32384 := by
      apply Matrix.ext; unfold tripleCharges sourceA2365 sourceB2365 sourceC2365 difference raw32384; decide +kernel
    rw [ha]
    exact (canonical32384 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2365 + difference 0 4) (sourceB2365 + difference 4 0) sourceC2365) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5410) := by
    have ha : (tripleCharges (sourceA2365 + difference 0 4) (sourceB2365 + difference 4 0) sourceC2365) = raw32385 := by
      apply Matrix.ext; unfold tripleCharges sourceA2365 sourceB2365 sourceC2365 difference raw32385; decide +kernel
    rw [ha]
    exact (canonical32385 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2365 + difference 0 5) (sourceB2365 + difference 5 0) sourceC2365) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5478) := by
    have ha : (tripleCharges (sourceA2365 + difference 0 5) (sourceB2365 + difference 5 0) sourceC2365) = raw32386 := by
      apply Matrix.ext; unfold tripleCharges sourceA2365 sourceB2365 sourceC2365 difference raw32386; decide +kernel
    rw [ha]
    exact (canonical32386 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2365 + difference 1 0) (sourceB2365 + difference 0 1) sourceC2365) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4439) := by
    have ha : (tripleCharges (sourceA2365 + difference 1 0) (sourceB2365 + difference 0 1) sourceC2365) = raw32387 := by
      apply Matrix.ext; unfold tripleCharges sourceA2365 sourceB2365 sourceC2365 difference raw32387; decide +kernel
    rw [ha]
    exact (canonical32387 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2365 + difference 1 2) (sourceB2365 + difference 2 1) sourceC2365) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5149) := by
    have ha : (tripleCharges (sourceA2365 + difference 1 2) (sourceB2365 + difference 2 1) sourceC2365) = raw32388 := by
      apply Matrix.ext; unfold tripleCharges sourceA2365 sourceB2365 sourceC2365 difference raw32388; decide +kernel
    rw [ha]
    exact (canonical32388 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2365 + difference 1 3) (sourceB2365 + difference 3 1) sourceC2365) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5251) := by
    have ha : (tripleCharges (sourceA2365 + difference 1 3) (sourceB2365 + difference 3 1) sourceC2365) = raw32389 := by
      apply Matrix.ext; unfold tripleCharges sourceA2365 sourceB2365 sourceC2365 difference raw32389; decide +kernel
    rw [ha]
    exact (canonical32389 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2365 + difference 1 4) (sourceB2365 + difference 4 1) sourceC2365) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA2365 + difference 1 4) (sourceB2365 + difference 4 1) sourceC2365) = raw32390 := by
      apply Matrix.ext; unfold tripleCharges sourceA2365 sourceB2365 sourceC2365 difference raw32390; decide +kernel
    rw [ha]
    exact (canonical32390 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2365 + difference 1 5) (sourceB2365 + difference 5 1) sourceC2365) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5281) := by
    have ha : (tripleCharges (sourceA2365 + difference 1 5) (sourceB2365 + difference 5 1) sourceC2365) = raw32391 := by
      apply Matrix.ext; unfold tripleCharges sourceA2365 sourceB2365 sourceC2365 difference raw32391; decide +kernel
    rw [ha]
    exact (canonical32391 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2365 + difference 2 0) (sourceB2365 + difference 0 2) sourceC2365) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4345) := by
    have ha : (tripleCharges (sourceA2365 + difference 2 0) (sourceB2365 + difference 0 2) sourceC2365) = raw32392 := by
      apply Matrix.ext; unfold tripleCharges sourceA2365 sourceB2365 sourceC2365 difference raw32392; decide +kernel
    rw [ha]
    exact (canonical32392 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2365 + difference 2 1) (sourceB2365 + difference 1 2) sourceC2365) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4942) := by
    have ha : (tripleCharges (sourceA2365 + difference 2 1) (sourceB2365 + difference 1 2) sourceC2365) = raw32393 := by
      apply Matrix.ext; unfold tripleCharges sourceA2365 sourceB2365 sourceC2365 difference raw32393; decide +kernel
    rw [ha]
    exact (canonical32393 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2365 + difference 2 3) (sourceB2365 + difference 3 2) sourceC2365) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5138) := by
    have ha : (tripleCharges (sourceA2365 + difference 2 3) (sourceB2365 + difference 3 2) sourceC2365) = raw32394 := by
      apply Matrix.ext; unfold tripleCharges sourceA2365 sourceB2365 sourceC2365 difference raw32394; decide +kernel
    rw [ha]
    exact (canonical32394 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2365 + difference 2 4) (sourceB2365 + difference 4 2) sourceC2365) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5170) := by
    have ha : (tripleCharges (sourceA2365 + difference 2 4) (sourceB2365 + difference 4 2) sourceC2365) = raw32395 := by
      apply Matrix.ext; unfold tripleCharges sourceA2365 sourceB2365 sourceC2365 difference raw32395; decide +kernel
    rw [ha]
    exact (canonical32395 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2365 + difference 2 5) (sourceB2365 + difference 5 2) sourceC2365) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5160) := by
    have ha : (tripleCharges (sourceA2365 + difference 2 5) (sourceB2365 + difference 5 2) sourceC2365) = raw32396 := by
      apply Matrix.ext; unfold tripleCharges sourceA2365 sourceB2365 sourceC2365 difference raw32396; decide +kernel
    rw [ha]
    exact (canonical32396 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2365 + difference 3 0) (sourceB2365 + difference 0 3) sourceC2365) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4332) := by
    have ha : (tripleCharges (sourceA2365 + difference 3 0) (sourceB2365 + difference 0 3) sourceC2365) = raw32397 := by
      apply Matrix.ext; unfold tripleCharges sourceA2365 sourceB2365 sourceC2365 difference raw32397; decide +kernel
    rw [ha]
    exact (canonical32397 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2365 + difference 3 1) (sourceB2365 + difference 1 3) sourceC2365) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4933) := by
    have ha : (tripleCharges (sourceA2365 + difference 3 1) (sourceB2365 + difference 1 3) sourceC2365) = raw32398 := by
      apply Matrix.ext; unfold tripleCharges sourceA2365 sourceB2365 sourceC2365 difference raw32398; decide +kernel
    rw [ha]
    exact (canonical32398 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2365 + difference 3 2) (sourceB2365 + difference 2 3) sourceC2365) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5117) := by
    have ha : (tripleCharges (sourceA2365 + difference 3 2) (sourceB2365 + difference 2 3) sourceC2365) = raw32399 := by
      apply Matrix.ext; unfold tripleCharges sourceA2365 sourceB2365 sourceC2365 difference raw32399; decide +kernel
    rw [ha]
    exact (canonical32399 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2365 + difference 3 4) (sourceB2365 + difference 4 3) sourceC2365) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5152) := by
    have ha : (tripleCharges (sourceA2365 + difference 3 4) (sourceB2365 + difference 4 3) sourceC2365) = raw32400 := by
      apply Matrix.ext; unfold tripleCharges sourceA2365 sourceB2365 sourceC2365 difference raw32400; decide +kernel
    rw [ha]
    exact (canonical32400 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2365 + difference 3 5) (sourceB2365 + difference 5 3) sourceC2365) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5145) := by
    have ha : (tripleCharges (sourceA2365 + difference 3 5) (sourceB2365 + difference 5 3) sourceC2365) = raw32401 := by
      apply Matrix.ext; unfold tripleCharges sourceA2365 sourceB2365 sourceC2365 difference raw32401; decide +kernel
    rw [ha]
    exact (canonical32401 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2365 + difference 4 0) (sourceB2365 + difference 0 4) sourceC2365) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4328) := by
    have ha : (tripleCharges (sourceA2365 + difference 4 0) (sourceB2365 + difference 0 4) sourceC2365) = raw32402 := by
      apply Matrix.ext; unfold tripleCharges sourceA2365 sourceB2365 sourceC2365 difference raw32402; decide +kernel
    rw [ha]
    exact (canonical32402 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2365 + difference 4 1) (sourceB2365 + difference 1 4) sourceC2365) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4931) := by
    have ha : (tripleCharges (sourceA2365 + difference 4 1) (sourceB2365 + difference 1 4) sourceC2365) = raw32403 := by
      apply Matrix.ext; unfold tripleCharges sourceA2365 sourceB2365 sourceC2365 difference raw32403; decide +kernel
    rw [ha]
    exact (canonical32403 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2365 + difference 4 2) (sourceB2365 + difference 2 4) sourceC2365) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5114) := by
    have ha : (tripleCharges (sourceA2365 + difference 4 2) (sourceB2365 + difference 2 4) sourceC2365) = raw32404 := by
      apply Matrix.ext; unfold tripleCharges sourceA2365 sourceB2365 sourceC2365 difference raw32404; decide +kernel
    rw [ha]
    exact (canonical32404 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2365 + difference 4 3) (sourceB2365 + difference 3 4) sourceC2365) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5129) := by
    have ha : (tripleCharges (sourceA2365 + difference 4 3) (sourceB2365 + difference 3 4) sourceC2365) = raw32405 := by
      apply Matrix.ext; unfold tripleCharges sourceA2365 sourceB2365 sourceC2365 difference raw32405; decide +kernel
    rw [ha]
    exact (canonical32405 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2365 + difference 4 5) (sourceB2365 + difference 5 4) sourceC2365) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5144) := by
    have ha : (tripleCharges (sourceA2365 + difference 4 5) (sourceB2365 + difference 5 4) sourceC2365) = raw32406 := by
      apply Matrix.ext; unfold tripleCharges sourceA2365 sourceB2365 sourceC2365 difference raw32406; decide +kernel
    rw [ha]
    exact (canonical32406 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2365 + difference 5 0) (sourceB2365 + difference 0 5) sourceC2365) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4327) := by
    have ha : (tripleCharges (sourceA2365 + difference 5 0) (sourceB2365 + difference 0 5) sourceC2365) = raw32407 := by
      apply Matrix.ext; unfold tripleCharges sourceA2365 sourceB2365 sourceC2365 difference raw32407; decide +kernel
    rw [ha]
    exact (canonical32407 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2365 + difference 5 1) (sourceB2365 + difference 1 5) sourceC2365) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4930) := by
    have ha : (tripleCharges (sourceA2365 + difference 5 1) (sourceB2365 + difference 1 5) sourceC2365) = raw32408 := by
      apply Matrix.ext; unfold tripleCharges sourceA2365 sourceB2365 sourceC2365 difference raw32408; decide +kernel
    rw [ha]
    exact (canonical32408 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2365 + difference 5 2) (sourceB2365 + difference 2 5) sourceC2365) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5037) := by
    have ha : (tripleCharges (sourceA2365 + difference 5 2) (sourceB2365 + difference 2 5) sourceC2365) = raw32409 := by
      apply Matrix.ext; unfold tripleCharges sourceA2365 sourceB2365 sourceC2365 difference raw32409; decide +kernel
    rw [ha]
    exact (canonical32409 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2365 + difference 5 3) (sourceB2365 + difference 3 5) sourceC2365) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5128) := by
    have ha : (tripleCharges (sourceA2365 + difference 5 3) (sourceB2365 + difference 3 5) sourceC2365) = raw32410 := by
      apply Matrix.ext; unfold tripleCharges sourceA2365 sourceB2365 sourceC2365 difference raw32410; decide +kernel
    rw [ha]
    exact (canonical32410 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2365 + difference 5 4) (sourceB2365 + difference 4 5) sourceC2365) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5078) := by
    have ha : (tripleCharges (sourceA2365 + difference 5 4) (sourceB2365 + difference 4 5) sourceC2365) = raw32411 := by
      apply Matrix.ext; unfold tripleCharges sourceA2365 sourceB2365 sourceC2365 difference raw32411; decide +kernel
    rw [ha]
    exact (canonical32411 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2365 sourceB2365 sourceC2365
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2365, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2366 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2366 : Charge := ![2, 0, -1, 0, -1, 0]
def sourceC2366 : Charge := ![1, 1, 1, -1, 0, -2]
def sourceForm2366 : Integer.Sparse Master := [(Sum.inr 905, 1), (Sum.inr 906, 1), (Sum.inr 910, 1), (Sum.inr 923, 1), (Sum.inr 1021, 1), (Sum.inr 2320, 1), (Sum.inr 2321, 1), (Sum.inr 2324, 1), (Sum.inr 2333, 1), (Sum.inr 2526, 1), (Sum.inr 2527, 1), (Sum.inr 2530, 1), (Sum.inr 2543, 1), (Sum.inr 2545, 1), (Sum.inr 2557, 1), (Sum.inr 2566, 1), (Sum.inr 2567, 1), (Sum.inr 2570, 1), (Sum.inr 2572, 1), (Sum.inr 2576, 1), (Sum.inr 2587, 1), (Sum.inr 2596, 1), (Sum.inr 2710, 1), (Sum.inr 2750, 1), (Sum.inr 2753, 1), (Sum.inr 3925, 1), (Sum.inr 3988, 1), (Sum.inr 3990, 1), (Sum.inr 3994, 1), (Sum.inr 3996, 1)]

theorem sourceEq2366 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2366 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2366 + difference 0 1) (sourceB2366 + difference 1 0) sourceC2366) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3925) := by
    have ha : (tripleCharges (sourceA2366 + difference 0 1) (sourceB2366 + difference 1 0) sourceC2366) = raw32412 := by
      apply Matrix.ext; unfold tripleCharges sourceA2366 sourceB2366 sourceC2366 difference raw32412; decide +kernel
    rw [ha]
    exact (canonical32412 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2366 + difference 0 2) (sourceB2366 + difference 2 0) sourceC2366) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3988) := by
    have ha : (tripleCharges (sourceA2366 + difference 0 2) (sourceB2366 + difference 2 0) sourceC2366) = raw32413 := by
      apply Matrix.ext; unfold tripleCharges sourceA2366 sourceB2366 sourceC2366 difference raw32413; decide +kernel
    rw [ha]
    exact (canonical32413 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2366 + difference 0 3) (sourceB2366 + difference 3 0) sourceC2366) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3990) := by
    have ha : (tripleCharges (sourceA2366 + difference 0 3) (sourceB2366 + difference 3 0) sourceC2366) = raw32414 := by
      apply Matrix.ext; unfold tripleCharges sourceA2366 sourceB2366 sourceC2366 difference raw32414; decide +kernel
    rw [ha]
    exact (canonical32414 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2366 + difference 0 4) (sourceB2366 + difference 4 0) sourceC2366) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3996) := by
    have ha : (tripleCharges (sourceA2366 + difference 0 4) (sourceB2366 + difference 4 0) sourceC2366) = raw32415 := by
      apply Matrix.ext; unfold tripleCharges sourceA2366 sourceB2366 sourceC2366 difference raw32415; decide +kernel
    rw [ha]
    exact (canonical32415 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2366 + difference 0 5) (sourceB2366 + difference 5 0) sourceC2366) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3994) := by
    have ha : (tripleCharges (sourceA2366 + difference 0 5) (sourceB2366 + difference 5 0) sourceC2366) = raw32416 := by
      apply Matrix.ext; unfold tripleCharges sourceA2366 sourceB2366 sourceC2366 difference raw32416; decide +kernel
    rw [ha]
    exact (canonical32416 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2366 + difference 1 0) (sourceB2366 + difference 0 1) sourceC2366) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1021) := by
    have ha : (tripleCharges (sourceA2366 + difference 1 0) (sourceB2366 + difference 0 1) sourceC2366) = raw32417 := by
      apply Matrix.ext; unfold tripleCharges sourceA2366 sourceB2366 sourceC2366 difference raw32417; decide +kernel
    rw [ha]
    exact (canonical32417 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2366 + difference 1 2) (sourceB2366 + difference 2 1) sourceC2366) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2570) := by
    have ha : (tripleCharges (sourceA2366 + difference 1 2) (sourceB2366 + difference 2 1) sourceC2366) = raw32418 := by
      apply Matrix.ext; unfold tripleCharges sourceA2366 sourceB2366 sourceC2366 difference raw32418; decide +kernel
    rw [ha]
    exact (canonical32418 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2366 + difference 1 3) (sourceB2366 + difference 3 1) sourceC2366) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2710) := by
    have ha : (tripleCharges (sourceA2366 + difference 1 3) (sourceB2366 + difference 3 1) sourceC2366) = raw32419 := by
      apply Matrix.ext; unfold tripleCharges sourceA2366 sourceB2366 sourceC2366 difference raw32419; decide +kernel
    rw [ha]
    exact (canonical32419 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2366 + difference 1 4) (sourceB2366 + difference 4 1) sourceC2366) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2753) := by
    have ha : (tripleCharges (sourceA2366 + difference 1 4) (sourceB2366 + difference 4 1) sourceC2366) = raw32420 := by
      apply Matrix.ext; unfold tripleCharges sourceA2366 sourceB2366 sourceC2366 difference raw32420; decide +kernel
    rw [ha]
    exact (canonical32420 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2366 + difference 1 5) (sourceB2366 + difference 5 1) sourceC2366) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2750) := by
    have ha : (tripleCharges (sourceA2366 + difference 1 5) (sourceB2366 + difference 5 1) sourceC2366) = raw32421 := by
      apply Matrix.ext; unfold tripleCharges sourceA2366 sourceB2366 sourceC2366 difference raw32421; decide +kernel
    rw [ha]
    exact (canonical32421 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2366 + difference 2 0) (sourceB2366 + difference 0 2) sourceC2366) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 923) := by
    have ha : (tripleCharges (sourceA2366 + difference 2 0) (sourceB2366 + difference 0 2) sourceC2366) = raw32422 := by
      apply Matrix.ext; unfold tripleCharges sourceA2366 sourceB2366 sourceC2366 difference raw32422; decide +kernel
    rw [ha]
    exact (canonical32422 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2366 + difference 2 1) (sourceB2366 + difference 1 2) sourceC2366) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2333) := by
    have ha : (tripleCharges (sourceA2366 + difference 2 1) (sourceB2366 + difference 1 2) sourceC2366) = raw32423 := by
      apply Matrix.ext; unfold tripleCharges sourceA2366 sourceB2366 sourceC2366 difference raw32423; decide +kernel
    rw [ha]
    exact (canonical32423 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2366 + difference 2 3) (sourceB2366 + difference 3 2) sourceC2366) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2557) := by
    have ha : (tripleCharges (sourceA2366 + difference 2 3) (sourceB2366 + difference 3 2) sourceC2366) = raw32424 := by
      apply Matrix.ext; unfold tripleCharges sourceA2366 sourceB2366 sourceC2366 difference raw32424; decide +kernel
    rw [ha]
    exact (canonical32424 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2366 + difference 2 4) (sourceB2366 + difference 4 2) sourceC2366) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2596) := by
    have ha : (tripleCharges (sourceA2366 + difference 2 4) (sourceB2366 + difference 4 2) sourceC2366) = raw32425 := by
      apply Matrix.ext; unfold tripleCharges sourceA2366 sourceB2366 sourceC2366 difference raw32425; decide +kernel
    rw [ha]
    exact (canonical32425 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2366 + difference 2 5) (sourceB2366 + difference 5 2) sourceC2366) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2587) := by
    have ha : (tripleCharges (sourceA2366 + difference 2 5) (sourceB2366 + difference 5 2) sourceC2366) = raw32426 := by
      apply Matrix.ext; unfold tripleCharges sourceA2366 sourceB2366 sourceC2366 difference raw32426; decide +kernel
    rw [ha]
    exact (canonical32426 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2366 + difference 3 0) (sourceB2366 + difference 0 3) sourceC2366) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 910) := by
    have ha : (tripleCharges (sourceA2366 + difference 3 0) (sourceB2366 + difference 0 3) sourceC2366) = raw32427 := by
      apply Matrix.ext; unfold tripleCharges sourceA2366 sourceB2366 sourceC2366 difference raw32427; decide +kernel
    rw [ha]
    exact (canonical32427 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2366 + difference 3 1) (sourceB2366 + difference 1 3) sourceC2366) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2324) := by
    have ha : (tripleCharges (sourceA2366 + difference 3 1) (sourceB2366 + difference 1 3) sourceC2366) = raw32428 := by
      apply Matrix.ext; unfold tripleCharges sourceA2366 sourceB2366 sourceC2366 difference raw32428; decide +kernel
    rw [ha]
    exact (canonical32428 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2366 + difference 3 2) (sourceB2366 + difference 2 3) sourceC2366) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2530) := by
    have ha : (tripleCharges (sourceA2366 + difference 3 2) (sourceB2366 + difference 2 3) sourceC2366) = raw32429 := by
      apply Matrix.ext; unfold tripleCharges sourceA2366 sourceB2366 sourceC2366 difference raw32429; decide +kernel
    rw [ha]
    exact (canonical32429 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2366 + difference 3 4) (sourceB2366 + difference 4 3) sourceC2366) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2576) := by
    have ha : (tripleCharges (sourceA2366 + difference 3 4) (sourceB2366 + difference 4 3) sourceC2366) = raw32430 := by
      apply Matrix.ext; unfold tripleCharges sourceA2366 sourceB2366 sourceC2366 difference raw32430; decide +kernel
    rw [ha]
    exact (canonical32430 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2366 + difference 3 5) (sourceB2366 + difference 5 3) sourceC2366) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2567) := by
    have ha : (tripleCharges (sourceA2366 + difference 3 5) (sourceB2366 + difference 5 3) sourceC2366) = raw32431 := by
      apply Matrix.ext; unfold tripleCharges sourceA2366 sourceB2366 sourceC2366 difference raw32431; decide +kernel
    rw [ha]
    exact (canonical32431 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2366 + difference 4 0) (sourceB2366 + difference 0 4) sourceC2366) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 906) := by
    have ha : (tripleCharges (sourceA2366 + difference 4 0) (sourceB2366 + difference 0 4) sourceC2366) = raw32432 := by
      apply Matrix.ext; unfold tripleCharges sourceA2366 sourceB2366 sourceC2366 difference raw32432; decide +kernel
    rw [ha]
    exact (canonical32432 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2366 + difference 4 1) (sourceB2366 + difference 1 4) sourceC2366) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2321) := by
    have ha : (tripleCharges (sourceA2366 + difference 4 1) (sourceB2366 + difference 1 4) sourceC2366) = raw32433 := by
      apply Matrix.ext; unfold tripleCharges sourceA2366 sourceB2366 sourceC2366 difference raw32433; decide +kernel
    rw [ha]
    exact (canonical32433 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2366 + difference 4 2) (sourceB2366 + difference 2 4) sourceC2366) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2527) := by
    have ha : (tripleCharges (sourceA2366 + difference 4 2) (sourceB2366 + difference 2 4) sourceC2366) = raw32434 := by
      apply Matrix.ext; unfold tripleCharges sourceA2366 sourceB2366 sourceC2366 difference raw32434; decide +kernel
    rw [ha]
    exact (canonical32434 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2366 + difference 4 3) (sourceB2366 + difference 3 4) sourceC2366) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2545) := by
    have ha : (tripleCharges (sourceA2366 + difference 4 3) (sourceB2366 + difference 3 4) sourceC2366) = raw32435 := by
      apply Matrix.ext; unfold tripleCharges sourceA2366 sourceB2366 sourceC2366 difference raw32435; decide +kernel
    rw [ha]
    exact (canonical32435 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2366 + difference 4 5) (sourceB2366 + difference 5 4) sourceC2366) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2566) := by
    have ha : (tripleCharges (sourceA2366 + difference 4 5) (sourceB2366 + difference 5 4) sourceC2366) = raw32436 := by
      apply Matrix.ext; unfold tripleCharges sourceA2366 sourceB2366 sourceC2366 difference raw32436; decide +kernel
    rw [ha]
    exact (canonical32436 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2366 + difference 5 0) (sourceB2366 + difference 0 5) sourceC2366) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 905) := by
    have ha : (tripleCharges (sourceA2366 + difference 5 0) (sourceB2366 + difference 0 5) sourceC2366) = raw32437 := by
      apply Matrix.ext; unfold tripleCharges sourceA2366 sourceB2366 sourceC2366 difference raw32437; decide +kernel
    rw [ha]
    exact (canonical32437 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2366 + difference 5 1) (sourceB2366 + difference 1 5) sourceC2366) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2320) := by
    have ha : (tripleCharges (sourceA2366 + difference 5 1) (sourceB2366 + difference 1 5) sourceC2366) = raw32438 := by
      apply Matrix.ext; unfold tripleCharges sourceA2366 sourceB2366 sourceC2366 difference raw32438; decide +kernel
    rw [ha]
    exact (canonical32438 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2366 + difference 5 2) (sourceB2366 + difference 2 5) sourceC2366) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2526) := by
    have ha : (tripleCharges (sourceA2366 + difference 5 2) (sourceB2366 + difference 2 5) sourceC2366) = raw32439 := by
      apply Matrix.ext; unfold tripleCharges sourceA2366 sourceB2366 sourceC2366 difference raw32439; decide +kernel
    rw [ha]
    exact (canonical32439 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2366 + difference 5 3) (sourceB2366 + difference 3 5) sourceC2366) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2543) := by
    have ha : (tripleCharges (sourceA2366 + difference 5 3) (sourceB2366 + difference 3 5) sourceC2366) = raw32440 := by
      apply Matrix.ext; unfold tripleCharges sourceA2366 sourceB2366 sourceC2366 difference raw32440; decide +kernel
    rw [ha]
    exact (canonical32440 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2366 + difference 5 4) (sourceB2366 + difference 4 5) sourceC2366) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2572) := by
    have ha : (tripleCharges (sourceA2366 + difference 5 4) (sourceB2366 + difference 4 5) sourceC2366) = raw32441 := by
      apply Matrix.ext; unfold tripleCharges sourceA2366 sourceB2366 sourceC2366 difference raw32441; decide +kernel
    rw [ha]
    exact (canonical32441 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2366 sourceB2366 sourceC2366
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2366, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2367 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2367 : Charge := ![2, 0, -1, 0, -1, 0]
def sourceC2367 : Charge := ![1, 1, 1, -1, 0, -2]
def sourceForm2367 : Integer.Sparse Master := [(Sum.inr 1667, 1), (Sum.inr 1668, 1), (Sum.inr 1670, 1), (Sum.inr 1678, 1), (Sum.inr 1713, 1), (Sum.inr 3406, 1), (Sum.inr 3407, 1), (Sum.inr 3408, 1), (Sum.inr 3414, 1), (Sum.inr 3455, 1), (Sum.inr 3481, 1), (Sum.inr 3516, 1), (Sum.inr 3517, 1), (Sum.inr 3519, 1), (Sum.inr 3539, 1), (Sum.inr 3557, 1), (Sum.inr 3558, 1), (Sum.inr 3562, 1), (Sum.inr 3571, 1), (Sum.inr 3597, 1), (Sum.inr 3599, 1), (Sum.inr 3605, 1), (Sum.inr 3606, 1), (Sum.inr 3612, 1), (Sum.inr 3625, 1), (Sum.inr 3797, 1), (Sum.inr 3798, 1), (Sum.inr 3816, 1), (Sum.inr 3843, 1), (Sum.inr 3974, 1)]

theorem sourceEq2367 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2367 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2367 + difference 0 1) (sourceB2367 + difference 1 0) sourceC2367) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3797) := by
    have ha : (tripleCharges (sourceA2367 + difference 0 1) (sourceB2367 + difference 1 0) sourceC2367) = raw32442 := by
      apply Matrix.ext; unfold tripleCharges sourceA2367 sourceB2367 sourceC2367 difference raw32442; decide +kernel
    rw [ha]
    exact (canonical32442 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2367 + difference 0 2) (sourceB2367 + difference 2 0) sourceC2367) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3798) := by
    have ha : (tripleCharges (sourceA2367 + difference 0 2) (sourceB2367 + difference 2 0) sourceC2367) = raw32443 := by
      apply Matrix.ext; unfold tripleCharges sourceA2367 sourceB2367 sourceC2367 difference raw32443; decide +kernel
    rw [ha]
    exact (canonical32443 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2367 + difference 0 3) (sourceB2367 + difference 3 0) sourceC2367) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3843) := by
    have ha : (tripleCharges (sourceA2367 + difference 0 3) (sourceB2367 + difference 3 0) sourceC2367) = raw32444 := by
      apply Matrix.ext; unfold tripleCharges sourceA2367 sourceB2367 sourceC2367 difference raw32444; decide +kernel
    rw [ha]
    exact (canonical32444 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2367 + difference 0 4) (sourceB2367 + difference 4 0) sourceC2367) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3816) := by
    have ha : (tripleCharges (sourceA2367 + difference 0 4) (sourceB2367 + difference 4 0) sourceC2367) = raw32445 := by
      apply Matrix.ext; unfold tripleCharges sourceA2367 sourceB2367 sourceC2367 difference raw32445; decide +kernel
    rw [ha]
    exact (canonical32445 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2367 + difference 0 5) (sourceB2367 + difference 5 0) sourceC2367) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3974) := by
    have ha : (tripleCharges (sourceA2367 + difference 0 5) (sourceB2367 + difference 5 0) sourceC2367) = raw32446 := by
      apply Matrix.ext; unfold tripleCharges sourceA2367 sourceB2367 sourceC2367 difference raw32446; decide +kernel
    rw [ha]
    exact (canonical32446 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2367 + difference 1 0) (sourceB2367 + difference 0 1) sourceC2367) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1713) := by
    have ha : (tripleCharges (sourceA2367 + difference 1 0) (sourceB2367 + difference 0 1) sourceC2367) = raw32447 := by
      apply Matrix.ext; unfold tripleCharges sourceA2367 sourceB2367 sourceC2367 difference raw32447; decide +kernel
    rw [ha]
    exact (canonical32447 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2367 + difference 1 2) (sourceB2367 + difference 2 1) sourceC2367) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3605) := by
    have ha : (tripleCharges (sourceA2367 + difference 1 2) (sourceB2367 + difference 2 1) sourceC2367) = raw32448 := by
      apply Matrix.ext; unfold tripleCharges sourceA2367 sourceB2367 sourceC2367 difference raw32448; decide +kernel
    rw [ha]
    exact (canonical32448 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2367 + difference 1 3) (sourceB2367 + difference 3 1) sourceC2367) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3539) := by
    have ha : (tripleCharges (sourceA2367 + difference 1 3) (sourceB2367 + difference 3 1) sourceC2367) = raw32449 := by
      apply Matrix.ext; unfold tripleCharges sourceA2367 sourceB2367 sourceC2367 difference raw32449; decide +kernel
    rw [ha]
    exact (canonical32449 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2367 + difference 1 4) (sourceB2367 + difference 4 1) sourceC2367) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3625) := by
    have ha : (tripleCharges (sourceA2367 + difference 1 4) (sourceB2367 + difference 4 1) sourceC2367) = raw32450 := by
      apply Matrix.ext; unfold tripleCharges sourceA2367 sourceB2367 sourceC2367 difference raw32450; decide +kernel
    rw [ha]
    exact (canonical32450 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2367 + difference 1 5) (sourceB2367 + difference 5 1) sourceC2367) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3571) := by
    have ha : (tripleCharges (sourceA2367 + difference 1 5) (sourceB2367 + difference 5 1) sourceC2367) = raw32451 := by
      apply Matrix.ext; unfold tripleCharges sourceA2367 sourceB2367 sourceC2367 difference raw32451; decide +kernel
    rw [ha]
    exact (canonical32451 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2367 + difference 2 0) (sourceB2367 + difference 0 2) sourceC2367) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1668) := by
    have ha : (tripleCharges (sourceA2367 + difference 2 0) (sourceB2367 + difference 0 2) sourceC2367) = raw32452 := by
      apply Matrix.ext; unfold tripleCharges sourceA2367 sourceB2367 sourceC2367 difference raw32452; decide +kernel
    rw [ha]
    exact (canonical32452 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2367 + difference 2 1) (sourceB2367 + difference 1 2) sourceC2367) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3407) := by
    have ha : (tripleCharges (sourceA2367 + difference 2 1) (sourceB2367 + difference 1 2) sourceC2367) = raw32453 := by
      apply Matrix.ext; unfold tripleCharges sourceA2367 sourceB2367 sourceC2367 difference raw32453; decide +kernel
    rw [ha]
    exact (canonical32453 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2367 + difference 2 3) (sourceB2367 + difference 3 2) sourceC2367) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3517) := by
    have ha : (tripleCharges (sourceA2367 + difference 2 3) (sourceB2367 + difference 3 2) sourceC2367) = raw32454 := by
      apply Matrix.ext; unfold tripleCharges sourceA2367 sourceB2367 sourceC2367 difference raw32454; decide +kernel
    rw [ha]
    exact (canonical32454 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2367 + difference 2 4) (sourceB2367 + difference 4 2) sourceC2367) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3606) := by
    have ha : (tripleCharges (sourceA2367 + difference 2 4) (sourceB2367 + difference 4 2) sourceC2367) = raw32455 := by
      apply Matrix.ext; unfold tripleCharges sourceA2367 sourceB2367 sourceC2367 difference raw32455; decide +kernel
    rw [ha]
    exact (canonical32455 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2367 + difference 2 5) (sourceB2367 + difference 5 2) sourceC2367) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3558) := by
    have ha : (tripleCharges (sourceA2367 + difference 2 5) (sourceB2367 + difference 5 2) sourceC2367) = raw32456 := by
      apply Matrix.ext; unfold tripleCharges sourceA2367 sourceB2367 sourceC2367 difference raw32456; decide +kernel
    rw [ha]
    exact (canonical32456 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2367 + difference 3 0) (sourceB2367 + difference 0 3) sourceC2367) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1678) := by
    have ha : (tripleCharges (sourceA2367 + difference 3 0) (sourceB2367 + difference 0 3) sourceC2367) = raw32457 := by
      apply Matrix.ext; unfold tripleCharges sourceA2367 sourceB2367 sourceC2367 difference raw32457; decide +kernel
    rw [ha]
    exact (canonical32457 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2367 + difference 3 1) (sourceB2367 + difference 1 3) sourceC2367) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3414) := by
    have ha : (tripleCharges (sourceA2367 + difference 3 1) (sourceB2367 + difference 1 3) sourceC2367) = raw32458 := by
      apply Matrix.ext; unfold tripleCharges sourceA2367 sourceB2367 sourceC2367 difference raw32458; decide +kernel
    rw [ha]
    exact (canonical32458 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2367 + difference 3 2) (sourceB2367 + difference 2 3) sourceC2367) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3599) := by
    have ha : (tripleCharges (sourceA2367 + difference 3 2) (sourceB2367 + difference 2 3) sourceC2367) = raw32459 := by
      apply Matrix.ext; unfold tripleCharges sourceA2367 sourceB2367 sourceC2367 difference raw32459; decide +kernel
    rw [ha]
    exact (canonical32459 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2367 + difference 3 4) (sourceB2367 + difference 4 3) sourceC2367) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3612) := by
    have ha : (tripleCharges (sourceA2367 + difference 3 4) (sourceB2367 + difference 4 3) sourceC2367) = raw32460 := by
      apply Matrix.ext; unfold tripleCharges sourceA2367 sourceB2367 sourceC2367 difference raw32460; decide +kernel
    rw [ha]
    exact (canonical32460 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2367 + difference 3 5) (sourceB2367 + difference 5 3) sourceC2367) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3562) := by
    have ha : (tripleCharges (sourceA2367 + difference 3 5) (sourceB2367 + difference 5 3) sourceC2367) = raw32461 := by
      apply Matrix.ext; unfold tripleCharges sourceA2367 sourceB2367 sourceC2367 difference raw32461; decide +kernel
    rw [ha]
    exact (canonical32461 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2367 + difference 4 0) (sourceB2367 + difference 0 4) sourceC2367) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1667) := by
    have ha : (tripleCharges (sourceA2367 + difference 4 0) (sourceB2367 + difference 0 4) sourceC2367) = raw32462 := by
      apply Matrix.ext; unfold tripleCharges sourceA2367 sourceB2367 sourceC2367 difference raw32462; decide +kernel
    rw [ha]
    exact (canonical32462 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2367 + difference 4 1) (sourceB2367 + difference 1 4) sourceC2367) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3406) := by
    have ha : (tripleCharges (sourceA2367 + difference 4 1) (sourceB2367 + difference 1 4) sourceC2367) = raw32463 := by
      apply Matrix.ext; unfold tripleCharges sourceA2367 sourceB2367 sourceC2367 difference raw32463; decide +kernel
    rw [ha]
    exact (canonical32463 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2367 + difference 4 2) (sourceB2367 + difference 2 4) sourceC2367) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3597) := by
    have ha : (tripleCharges (sourceA2367 + difference 4 2) (sourceB2367 + difference 2 4) sourceC2367) = raw32464 := by
      apply Matrix.ext; unfold tripleCharges sourceA2367 sourceB2367 sourceC2367 difference raw32464; decide +kernel
    rw [ha]
    exact (canonical32464 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2367 + difference 4 3) (sourceB2367 + difference 3 4) sourceC2367) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3516) := by
    have ha : (tripleCharges (sourceA2367 + difference 4 3) (sourceB2367 + difference 3 4) sourceC2367) = raw32465 := by
      apply Matrix.ext; unfold tripleCharges sourceA2367 sourceB2367 sourceC2367 difference raw32465; decide +kernel
    rw [ha]
    exact (canonical32465 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2367 + difference 4 5) (sourceB2367 + difference 5 4) sourceC2367) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3557) := by
    have ha : (tripleCharges (sourceA2367 + difference 4 5) (sourceB2367 + difference 5 4) sourceC2367) = raw32466 := by
      apply Matrix.ext; unfold tripleCharges sourceA2367 sourceB2367 sourceC2367 difference raw32466; decide +kernel
    rw [ha]
    exact (canonical32466 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2367 + difference 5 0) (sourceB2367 + difference 0 5) sourceC2367) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1670) := by
    have ha : (tripleCharges (sourceA2367 + difference 5 0) (sourceB2367 + difference 0 5) sourceC2367) = raw32467 := by
      apply Matrix.ext; unfold tripleCharges sourceA2367 sourceB2367 sourceC2367 difference raw32467; decide +kernel
    rw [ha]
    exact (canonical32467 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2367 + difference 5 1) (sourceB2367 + difference 1 5) sourceC2367) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3408) := by
    have ha : (tripleCharges (sourceA2367 + difference 5 1) (sourceB2367 + difference 1 5) sourceC2367) = raw32468 := by
      apply Matrix.ext; unfold tripleCharges sourceA2367 sourceB2367 sourceC2367 difference raw32468; decide +kernel
    rw [ha]
    exact (canonical32468 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2367 + difference 5 2) (sourceB2367 + difference 2 5) sourceC2367) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3455) := by
    have ha : (tripleCharges (sourceA2367 + difference 5 2) (sourceB2367 + difference 2 5) sourceC2367) = raw32469 := by
      apply Matrix.ext; unfold tripleCharges sourceA2367 sourceB2367 sourceC2367 difference raw32469; decide +kernel
    rw [ha]
    exact (canonical32469 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2367 + difference 5 3) (sourceB2367 + difference 3 5) sourceC2367) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3519) := by
    have ha : (tripleCharges (sourceA2367 + difference 5 3) (sourceB2367 + difference 3 5) sourceC2367) = raw32470 := by
      apply Matrix.ext; unfold tripleCharges sourceA2367 sourceB2367 sourceC2367 difference raw32470; decide +kernel
    rw [ha]
    exact (canonical32470 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2367 + difference 5 4) (sourceB2367 + difference 4 5) sourceC2367) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3481) := by
    have ha : (tripleCharges (sourceA2367 + difference 5 4) (sourceB2367 + difference 4 5) sourceC2367) = raw32471 := by
      apply Matrix.ext; unfold tripleCharges sourceA2367 sourceB2367 sourceC2367 difference raw32471; decide +kernel
    rw [ha]
    exact (canonical32471 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2367 sourceB2367 sourceC2367
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2367, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
