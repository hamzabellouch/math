import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical126
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical127
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical133
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical140
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical164
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical175
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical176
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical177
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical178
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical220
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical224
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical226
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical229
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical230
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical231
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical233
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical234
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical235
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical236

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA2176 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2176 : Charge := ![2, -1, 1, 0, -1, -1]
def sourceC2176 : Charge := ![1, 2, -1, 0, -1, -1]
def sourceForm2176 : Integer.Sparse Master := [(Sum.inr 1322, 1), (Sum.inr 2818, 1), (Sum.inr 2849, 1), (Sum.inr 2868, 1), (Sum.inr 2884, 2), (Sum.inr 4091, -1)]

theorem sourceEq2176 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2176 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2176 + difference 2 0) (sourceB2176 + difference 0 2) sourceC2176) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1322) := by
    have ha : (tripleCharges (sourceA2176 + difference 2 0) (sourceB2176 + difference 0 2) sourceC2176) = raw29934 := by
      apply Matrix.ext; unfold tripleCharges sourceA2176 sourceB2176 sourceC2176 difference raw29934; decide +kernel
    rw [ha]
    exact (canonical29934 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2176 + difference 2 1) (sourceB2176 + difference 1 2) sourceC2176) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2818) := by
    have ha : (tripleCharges (sourceA2176 + difference 2 1) (sourceB2176 + difference 1 2) sourceC2176) = raw29929 := by
      apply Matrix.ext; unfold tripleCharges sourceA2176 sourceB2176 sourceC2176 difference raw29929; decide +kernel
    rw [ha]
    exact (canonical29929 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2176 + difference 2 2) (sourceB2176 + difference 2 2) sourceC2176) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2868) := by
    have ha : (tripleCharges (sourceA2176 + difference 2 2) (sourceB2176 + difference 2 2) sourceC2176) = raw29928 := by
      apply Matrix.ext; unfold tripleCharges sourceA2176 sourceB2176 sourceC2176 difference raw29928; decide +kernel
    rw [ha]
    exact (canonical29928 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2176 + difference 2 3) (sourceB2176 + difference 3 2) sourceC2176) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2849) := by
    have ha : (tripleCharges (sourceA2176 + difference 2 3) (sourceB2176 + difference 3 2) sourceC2176) = raw29935 := by
      apply Matrix.ext; unfold tripleCharges sourceA2176 sourceB2176 sourceC2176 difference raw29935; decide +kernel
    rw [ha]
    exact (canonical29935 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2176 + difference 2 4) (sourceB2176 + difference 4 2) sourceC2176) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2884) := by
    have ha : (tripleCharges (sourceA2176 + difference 2 4) (sourceB2176 + difference 4 2) sourceC2176) = raw29936 := by
      apply Matrix.ext; unfold tripleCharges sourceA2176 sourceB2176 sourceC2176 difference raw29936; decide +kernel
    rw [ha]
    exact (canonical29936 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2176 + difference 2 5) (sourceB2176 + difference 5 2) sourceC2176) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2884) := by
    have ha : (tripleCharges (sourceA2176 + difference 2 5) (sourceB2176 + difference 5 2) sourceC2176) = raw29937 := by
      apply Matrix.ext; unfold tripleCharges sourceA2176 sourceB2176 sourceC2176 difference raw29937; decide +kernel
    rw [ha]
    exact (canonical29937 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2176 + sourceB2176) sourceC2176) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA2176 + sourceB2176) sourceC2176) = raw29933 := by
      apply Matrix.ext; unfold doubleCharges sourceA2176 sourceB2176 sourceC2176 raw29933; decide +kernel
    rw [ha]
    exact (canonical29933 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2176 sourceB2176 sourceC2176
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2176, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2177 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2177 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceC2177 : Charge := ![1, 2, 0, 0, -3, 0]
def sourceForm2177 : Integer.Sparse Master := [(Sum.inr 1819, 1), (Sum.inr 2812, 2), (Sum.inr 2821, 1), (Sum.inr 2888, 1), (Sum.inr 3397, 1), (Sum.inr 4084, -1)]

theorem sourceEq2177 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2177 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2177 + difference 0 1) (sourceB2177 + difference 1 0) sourceC2177) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3397) := by
    have ha : (tripleCharges (sourceA2177 + difference 0 1) (sourceB2177 + difference 1 0) sourceC2177) = raw29938 := by
      apply Matrix.ext; unfold tripleCharges sourceA2177 sourceB2177 sourceC2177 difference raw29938; decide +kernel
    rw [ha]
    exact (canonical29938 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2177 + difference 1 1) (sourceB2177 + difference 1 1) sourceC2177) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2888) := by
    have ha : (tripleCharges (sourceA2177 + difference 1 1) (sourceB2177 + difference 1 1) sourceC2177) = raw29939 := by
      apply Matrix.ext; unfold tripleCharges sourceA2177 sourceB2177 sourceC2177 difference raw29939; decide +kernel
    rw [ha]
    exact (canonical29939 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2177 + difference 2 1) (sourceB2177 + difference 1 2) sourceC2177) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2812) := by
    have ha : (tripleCharges (sourceA2177 + difference 2 1) (sourceB2177 + difference 1 2) sourceC2177) = raw29940 := by
      apply Matrix.ext; unfold tripleCharges sourceA2177 sourceB2177 sourceC2177 difference raw29940; decide +kernel
    rw [ha]
    exact (canonical29940 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2177 + difference 3 1) (sourceB2177 + difference 1 3) sourceC2177) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2812) := by
    have ha : (tripleCharges (sourceA2177 + difference 3 1) (sourceB2177 + difference 1 3) sourceC2177) = raw29941 := by
      apply Matrix.ext; unfold tripleCharges sourceA2177 sourceB2177 sourceC2177 difference raw29941; decide +kernel
    rw [ha]
    exact (canonical29941 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2177 + difference 4 1) (sourceB2177 + difference 1 4) sourceC2177) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1819) := by
    have ha : (tripleCharges (sourceA2177 + difference 4 1) (sourceB2177 + difference 1 4) sourceC2177) = raw29942 := by
      apply Matrix.ext; unfold tripleCharges sourceA2177 sourceB2177 sourceC2177 difference raw29942; decide +kernel
    rw [ha]
    exact (canonical29942 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2177 + difference 5 1) (sourceB2177 + difference 1 5) sourceC2177) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2821) := by
    have ha : (tripleCharges (sourceA2177 + difference 5 1) (sourceB2177 + difference 1 5) sourceC2177) = raw29943 := by
      apply Matrix.ext; unfold tripleCharges sourceA2177 sourceB2177 sourceC2177 difference raw29943; decide +kernel
    rw [ha]
    exact (canonical29943 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2177 + sourceB2177) sourceC2177) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA2177 + sourceB2177) sourceC2177) = raw29944 := by
      apply Matrix.ext; unfold doubleCharges sourceA2177 sourceB2177 sourceC2177 raw29944; decide +kernel
    rw [ha]
    exact (canonical29944 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2177 sourceB2177 sourceC2177
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2177, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2178 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2178 : Charge := ![1, 2, 0, 0, -2, -1]
def sourceC2178 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceForm2178 : Integer.Sparse Master := [(Sum.inr 4518, 2), (Sum.inr 4519, 1), (Sum.inr 4520, 1), (Sum.inr 4612, 1), (Sum.inr 4650, 2), (Sum.inr 4657, 1), (Sum.inr 4843, 1), (Sum.inr 4919, 2), (Sum.inr 4925, 1), (Sum.inr 4983, 2), (Sum.inr 5109, 1), (Sum.inr 5119, 2), (Sum.inr 5152, 2), (Sum.inr 5203, 2), (Sum.inr 5204, 2), (Sum.inr 5238, 1), (Sum.inr 5293, 1), (Sum.inr 5294, 1), (Sum.inr 5370, 2), (Sum.inr 5443, 1), (Sum.inr 5451, 1)]

theorem sourceEq2178 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2178 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2178 + difference 0 1) (sourceB2178 + difference 1 0) sourceC2178) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5238) := by
    have ha : (tripleCharges (sourceA2178 + difference 0 1) (sourceB2178 + difference 1 0) sourceC2178) = raw16240 := by
      apply Matrix.ext; unfold tripleCharges sourceA2178 sourceB2178 sourceC2178 difference raw16240; decide +kernel
    rw [ha]
    exact (canonical16240 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2178 + difference 0 2) (sourceB2178 + difference 2 0) sourceC2178) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5370) := by
    have ha : (tripleCharges (sourceA2178 + difference 0 2) (sourceB2178 + difference 2 0) sourceC2178) = raw16241 := by
      apply Matrix.ext; unfold tripleCharges sourceA2178 sourceB2178 sourceC2178 difference raw16241; decide +kernel
    rw [ha]
    exact (canonical16241 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2178 + difference 0 3) (sourceB2178 + difference 3 0) sourceC2178) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5370) := by
    have ha : (tripleCharges (sourceA2178 + difference 0 3) (sourceB2178 + difference 3 0) sourceC2178) = raw16242 := by
      apply Matrix.ext; unfold tripleCharges sourceA2178 sourceB2178 sourceC2178 difference raw16242; decide +kernel
    rw [ha]
    exact (canonical16242 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2178 + difference 0 4) (sourceB2178 + difference 4 0) sourceC2178) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA2178 + difference 0 4) (sourceB2178 + difference 4 0) sourceC2178) = raw28233 := by
      apply Matrix.ext; unfold tripleCharges sourceA2178 sourceB2178 sourceC2178 difference raw28233; decide +kernel
    rw [ha]
    exact (canonical28233 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2178 + difference 0 5) (sourceB2178 + difference 5 0) sourceC2178) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA2178 + difference 0 5) (sourceB2178 + difference 5 0) sourceC2178) = raw16243 := by
      apply Matrix.ext; unfold tripleCharges sourceA2178 sourceB2178 sourceC2178 difference raw16243; decide +kernel
    rw [ha]
    exact (canonical16243 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2178 + difference 1 0) (sourceB2178 + difference 0 1) sourceC2178) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA2178 + difference 1 0) (sourceB2178 + difference 0 1) sourceC2178) = raw29945 := by
      apply Matrix.ext; unfold tripleCharges sourceA2178 sourceB2178 sourceC2178 difference raw29945; decide +kernel
    rw [ha]
    exact (canonical29945 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2178 + difference 1 2) (sourceB2178 + difference 2 1) sourceC2178) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5152) := by
    have ha : (tripleCharges (sourceA2178 + difference 1 2) (sourceB2178 + difference 2 1) sourceC2178) = raw29946 := by
      apply Matrix.ext; unfold tripleCharges sourceA2178 sourceB2178 sourceC2178 difference raw29946; decide +kernel
    rw [ha]
    exact (canonical29946 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2178 + difference 1 3) (sourceB2178 + difference 3 1) sourceC2178) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5152) := by
    have ha : (tripleCharges (sourceA2178 + difference 1 3) (sourceB2178 + difference 3 1) sourceC2178) = raw29947 := by
      apply Matrix.ext; unfold tripleCharges sourceA2178 sourceB2178 sourceC2178 difference raw29947; decide +kernel
    rw [ha]
    exact (canonical29947 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2178 + difference 1 4) (sourceB2178 + difference 4 1) sourceC2178) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA2178 + difference 1 4) (sourceB2178 + difference 4 1) sourceC2178) = raw16224 := by
      apply Matrix.ext; unfold tripleCharges sourceA2178 sourceB2178 sourceC2178 difference raw16224; decide +kernel
    rw [ha]
    exact (canonical16224 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2178 + difference 1 5) (sourceB2178 + difference 5 1) sourceC2178) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA2178 + difference 1 5) (sourceB2178 + difference 5 1) sourceC2178) = raw29948 := by
      apply Matrix.ext; unfold tripleCharges sourceA2178 sourceB2178 sourceC2178 difference raw29948; decide +kernel
    rw [ha]
    exact (canonical29948 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2178 + difference 2 0) (sourceB2178 + difference 0 2) sourceC2178) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4518) := by
    have ha : (tripleCharges (sourceA2178 + difference 2 0) (sourceB2178 + difference 0 2) sourceC2178) = raw29949 := by
      apply Matrix.ext; unfold tripleCharges sourceA2178 sourceB2178 sourceC2178 difference raw29949; decide +kernel
    rw [ha]
    exact (canonical29949 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2178 + difference 2 1) (sourceB2178 + difference 1 2) sourceC2178) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4983) := by
    have ha : (tripleCharges (sourceA2178 + difference 2 1) (sourceB2178 + difference 1 2) sourceC2178) = raw29950 := by
      apply Matrix.ext; unfold tripleCharges sourceA2178 sourceB2178 sourceC2178 difference raw29950; decide +kernel
    rw [ha]
    exact (canonical29950 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2178 + difference 2 3) (sourceB2178 + difference 3 2) sourceC2178) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5119) := by
    have ha : (tripleCharges (sourceA2178 + difference 2 3) (sourceB2178 + difference 3 2) sourceC2178) = raw29951 := by
      apply Matrix.ext; unfold tripleCharges sourceA2178 sourceB2178 sourceC2178 difference raw29951; decide +kernel
    rw [ha]
    exact (canonical29951 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2178 + difference 2 4) (sourceB2178 + difference 4 2) sourceC2178) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5203) := by
    have ha : (tripleCharges (sourceA2178 + difference 2 4) (sourceB2178 + difference 4 2) sourceC2178) = raw16229 := by
      apply Matrix.ext; unfold tripleCharges sourceA2178 sourceB2178 sourceC2178 difference raw16229; decide +kernel
    rw [ha]
    exact (canonical16229 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2178 + difference 2 5) (sourceB2178 + difference 5 2) sourceC2178) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5204) := by
    have ha : (tripleCharges (sourceA2178 + difference 2 5) (sourceB2178 + difference 5 2) sourceC2178) = raw29952 := by
      apply Matrix.ext; unfold tripleCharges sourceA2178 sourceB2178 sourceC2178 difference raw29952; decide +kernel
    rw [ha]
    exact (canonical29952 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2178 + difference 3 0) (sourceB2178 + difference 0 3) sourceC2178) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4518) := by
    have ha : (tripleCharges (sourceA2178 + difference 3 0) (sourceB2178 + difference 0 3) sourceC2178) = raw29953 := by
      apply Matrix.ext; unfold tripleCharges sourceA2178 sourceB2178 sourceC2178 difference raw29953; decide +kernel
    rw [ha]
    exact (canonical29953 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2178 + difference 3 1) (sourceB2178 + difference 1 3) sourceC2178) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4983) := by
    have ha : (tripleCharges (sourceA2178 + difference 3 1) (sourceB2178 + difference 1 3) sourceC2178) = raw29954 := by
      apply Matrix.ext; unfold tripleCharges sourceA2178 sourceB2178 sourceC2178 difference raw29954; decide +kernel
    rw [ha]
    exact (canonical29954 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2178 + difference 3 2) (sourceB2178 + difference 2 3) sourceC2178) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5119) := by
    have ha : (tripleCharges (sourceA2178 + difference 3 2) (sourceB2178 + difference 2 3) sourceC2178) = raw29955 := by
      apply Matrix.ext; unfold tripleCharges sourceA2178 sourceB2178 sourceC2178 difference raw29955; decide +kernel
    rw [ha]
    exact (canonical29955 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2178 + difference 3 4) (sourceB2178 + difference 4 3) sourceC2178) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5203) := by
    have ha : (tripleCharges (sourceA2178 + difference 3 4) (sourceB2178 + difference 4 3) sourceC2178) = raw16234 := by
      apply Matrix.ext; unfold tripleCharges sourceA2178 sourceB2178 sourceC2178 difference raw16234; decide +kernel
    rw [ha]
    exact (canonical16234 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2178 + difference 3 5) (sourceB2178 + difference 5 3) sourceC2178) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5204) := by
    have ha : (tripleCharges (sourceA2178 + difference 3 5) (sourceB2178 + difference 5 3) sourceC2178) = raw29956 := by
      apply Matrix.ext; unfold tripleCharges sourceA2178 sourceB2178 sourceC2178 difference raw29956; decide +kernel
    rw [ha]
    exact (canonical29956 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2178 + difference 4 0) (sourceB2178 + difference 0 4) sourceC2178) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4519) := by
    have ha : (tripleCharges (sourceA2178 + difference 4 0) (sourceB2178 + difference 0 4) sourceC2178) = raw29957 := by
      apply Matrix.ext; unfold tripleCharges sourceA2178 sourceB2178 sourceC2178 difference raw29957; decide +kernel
    rw [ha]
    exact (canonical29957 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2178 + difference 4 1) (sourceB2178 + difference 1 4) sourceC2178) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4657) := by
    have ha : (tripleCharges (sourceA2178 + difference 4 1) (sourceB2178 + difference 1 4) sourceC2178) = raw29958 := by
      apply Matrix.ext; unfold tripleCharges sourceA2178 sourceB2178 sourceC2178 difference raw29958; decide +kernel
    rw [ha]
    exact (canonical29958 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2178 + difference 4 2) (sourceB2178 + difference 2 4) sourceC2178) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4650) := by
    have ha : (tripleCharges (sourceA2178 + difference 4 2) (sourceB2178 + difference 2 4) sourceC2178) = raw29959 := by
      apply Matrix.ext; unfold tripleCharges sourceA2178 sourceB2178 sourceC2178 difference raw29959; decide +kernel
    rw [ha]
    exact (canonical29959 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2178 + difference 4 3) (sourceB2178 + difference 3 4) sourceC2178) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4650) := by
    have ha : (tripleCharges (sourceA2178 + difference 4 3) (sourceB2178 + difference 3 4) sourceC2178) = raw29960 := by
      apply Matrix.ext; unfold tripleCharges sourceA2178 sourceB2178 sourceC2178 difference raw29960; decide +kernel
    rw [ha]
    exact (canonical29960 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2178 + difference 4 5) (sourceB2178 + difference 5 4) sourceC2178) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4843) := by
    have ha : (tripleCharges (sourceA2178 + difference 4 5) (sourceB2178 + difference 5 4) sourceC2178) = raw29961 := by
      apply Matrix.ext; unfold tripleCharges sourceA2178 sourceB2178 sourceC2178 difference raw29961; decide +kernel
    rw [ha]
    exact (canonical29961 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2178 + difference 5 0) (sourceB2178 + difference 0 5) sourceC2178) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4520) := by
    have ha : (tripleCharges (sourceA2178 + difference 5 0) (sourceB2178 + difference 0 5) sourceC2178) = raw28246 := by
      apply Matrix.ext; unfold tripleCharges sourceA2178 sourceB2178 sourceC2178 difference raw28246; decide +kernel
    rw [ha]
    exact (canonical28246 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2178 + difference 5 1) (sourceB2178 + difference 1 5) sourceC2178) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4925) := by
    have ha : (tripleCharges (sourceA2178 + difference 5 1) (sourceB2178 + difference 1 5) sourceC2178) = raw28247 := by
      apply Matrix.ext; unfold tripleCharges sourceA2178 sourceB2178 sourceC2178 difference raw28247; decide +kernel
    rw [ha]
    exact (canonical28247 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2178 + difference 5 2) (sourceB2178 + difference 2 5) sourceC2178) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4919) := by
    have ha : (tripleCharges (sourceA2178 + difference 5 2) (sourceB2178 + difference 2 5) sourceC2178) = raw28248 := by
      apply Matrix.ext; unfold tripleCharges sourceA2178 sourceB2178 sourceC2178 difference raw28248; decide +kernel
    rw [ha]
    exact (canonical28248 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2178 + difference 5 3) (sourceB2178 + difference 3 5) sourceC2178) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4919) := by
    have ha : (tripleCharges (sourceA2178 + difference 5 3) (sourceB2178 + difference 3 5) sourceC2178) = raw28249 := by
      apply Matrix.ext; unfold tripleCharges sourceA2178 sourceB2178 sourceC2178 difference raw28249; decide +kernel
    rw [ha]
    exact (canonical28249 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2178 + difference 5 4) (sourceB2178 + difference 4 5) sourceC2178) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5109) := by
    have ha : (tripleCharges (sourceA2178 + difference 5 4) (sourceB2178 + difference 4 5) sourceC2178) = raw16244 := by
      apply Matrix.ext; unfold tripleCharges sourceA2178 sourceB2178 sourceC2178 difference raw16244; decide +kernel
    rw [ha]
    exact (canonical16244 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2178 sourceB2178 sourceC2178
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2178, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2179 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2179 : Charge := ![1, 2, 0, 0, -2, -1]
def sourceC2179 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceForm2179 : Integer.Sparse Master := [(Sum.inr 1102, 2), (Sum.inr 1103, 1), (Sum.inr 1104, 1), (Sum.inr 1246, 1), (Sum.inr 1778, 2), (Sum.inr 1783, 1), (Sum.inr 2062, 1), (Sum.inr 2310, 2), (Sum.inr 2315, 1), (Sum.inr 2519, 1), (Sum.inr 2794, 2), (Sum.inr 2845, 2), (Sum.inr 2881, 2), (Sum.inr 2884, 2), (Sum.inr 2931, 2), (Sum.inr 3101, 1), (Sum.inr 3102, 1), (Sum.inr 3397, 1), (Sum.inr 3706, 2), (Sum.inr 3862, 1), (Sum.inr 3987, 1)]

theorem sourceEq2179 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2179 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2179 + difference 0 1) (sourceB2179 + difference 1 0) sourceC2179) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3397) := by
    have ha : (tripleCharges (sourceA2179 + difference 0 1) (sourceB2179 + difference 1 0) sourceC2179) = raw16270 := by
      apply Matrix.ext; unfold tripleCharges sourceA2179 sourceB2179 sourceC2179 difference raw16270; decide +kernel
    rw [ha]
    exact (canonical16270 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2179 + difference 0 2) (sourceB2179 + difference 2 0) sourceC2179) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3706) := by
    have ha : (tripleCharges (sourceA2179 + difference 0 2) (sourceB2179 + difference 2 0) sourceC2179) = raw16271 := by
      apply Matrix.ext; unfold tripleCharges sourceA2179 sourceB2179 sourceC2179 difference raw16271; decide +kernel
    rw [ha]
    exact (canonical16271 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2179 + difference 0 3) (sourceB2179 + difference 3 0) sourceC2179) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3706) := by
    have ha : (tripleCharges (sourceA2179 + difference 0 3) (sourceB2179 + difference 3 0) sourceC2179) = raw16272 := by
      apply Matrix.ext; unfold tripleCharges sourceA2179 sourceB2179 sourceC2179 difference raw16272; decide +kernel
    rw [ha]
    exact (canonical16272 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2179 + difference 0 4) (sourceB2179 + difference 4 0) sourceC2179) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3987) := by
    have ha : (tripleCharges (sourceA2179 + difference 0 4) (sourceB2179 + difference 4 0) sourceC2179) = raw28255 := by
      apply Matrix.ext; unfold tripleCharges sourceA2179 sourceB2179 sourceC2179 difference raw28255; decide +kernel
    rw [ha]
    exact (canonical28255 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2179 + difference 0 5) (sourceB2179 + difference 5 0) sourceC2179) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3862) := by
    have ha : (tripleCharges (sourceA2179 + difference 0 5) (sourceB2179 + difference 5 0) sourceC2179) = raw16273 := by
      apply Matrix.ext; unfold tripleCharges sourceA2179 sourceB2179 sourceC2179 difference raw16273; decide +kernel
    rw [ha]
    exact (canonical16273 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2179 + difference 1 0) (sourceB2179 + difference 0 1) sourceC2179) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1246) := by
    have ha : (tripleCharges (sourceA2179 + difference 1 0) (sourceB2179 + difference 0 1) sourceC2179) = raw29962 := by
      apply Matrix.ext; unfold tripleCharges sourceA2179 sourceB2179 sourceC2179 difference raw29962; decide +kernel
    rw [ha]
    exact (canonical29962 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2179 + difference 1 2) (sourceB2179 + difference 2 1) sourceC2179) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2931) := by
    have ha : (tripleCharges (sourceA2179 + difference 1 2) (sourceB2179 + difference 2 1) sourceC2179) = raw29963 := by
      apply Matrix.ext; unfold tripleCharges sourceA2179 sourceB2179 sourceC2179 difference raw29963; decide +kernel
    rw [ha]
    exact (canonical29963 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2179 + difference 1 3) (sourceB2179 + difference 3 1) sourceC2179) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2931) := by
    have ha : (tripleCharges (sourceA2179 + difference 1 3) (sourceB2179 + difference 3 1) sourceC2179) = raw29964 := by
      apply Matrix.ext; unfold tripleCharges sourceA2179 sourceB2179 sourceC2179 difference raw29964; decide +kernel
    rw [ha]
    exact (canonical29964 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2179 + difference 1 4) (sourceB2179 + difference 4 1) sourceC2179) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3102) := by
    have ha : (tripleCharges (sourceA2179 + difference 1 4) (sourceB2179 + difference 4 1) sourceC2179) = raw16254 := by
      apply Matrix.ext; unfold tripleCharges sourceA2179 sourceB2179 sourceC2179 difference raw16254; decide +kernel
    rw [ha]
    exact (canonical16254 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2179 + difference 1 5) (sourceB2179 + difference 5 1) sourceC2179) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3101) := by
    have ha : (tripleCharges (sourceA2179 + difference 1 5) (sourceB2179 + difference 5 1) sourceC2179) = raw29965 := by
      apply Matrix.ext; unfold tripleCharges sourceA2179 sourceB2179 sourceC2179 difference raw29965; decide +kernel
    rw [ha]
    exact (canonical29965 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2179 + difference 2 0) (sourceB2179 + difference 0 2) sourceC2179) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1102) := by
    have ha : (tripleCharges (sourceA2179 + difference 2 0) (sourceB2179 + difference 0 2) sourceC2179) = raw29966 := by
      apply Matrix.ext; unfold tripleCharges sourceA2179 sourceB2179 sourceC2179 difference raw29966; decide +kernel
    rw [ha]
    exact (canonical29966 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2179 + difference 2 1) (sourceB2179 + difference 1 2) sourceC2179) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2794) := by
    have ha : (tripleCharges (sourceA2179 + difference 2 1) (sourceB2179 + difference 1 2) sourceC2179) = raw29967 := by
      apply Matrix.ext; unfold tripleCharges sourceA2179 sourceB2179 sourceC2179 difference raw29967; decide +kernel
    rw [ha]
    exact (canonical29967 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2179 + difference 2 3) (sourceB2179 + difference 3 2) sourceC2179) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2845) := by
    have ha : (tripleCharges (sourceA2179 + difference 2 3) (sourceB2179 + difference 3 2) sourceC2179) = raw29968 := by
      apply Matrix.ext; unfold tripleCharges sourceA2179 sourceB2179 sourceC2179 difference raw29968; decide +kernel
    rw [ha]
    exact (canonical29968 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2179 + difference 2 4) (sourceB2179 + difference 4 2) sourceC2179) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2884) := by
    have ha : (tripleCharges (sourceA2179 + difference 2 4) (sourceB2179 + difference 4 2) sourceC2179) = raw16259 := by
      apply Matrix.ext; unfold tripleCharges sourceA2179 sourceB2179 sourceC2179 difference raw16259; decide +kernel
    rw [ha]
    exact (canonical16259 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2179 + difference 2 5) (sourceB2179 + difference 5 2) sourceC2179) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2881) := by
    have ha : (tripleCharges (sourceA2179 + difference 2 5) (sourceB2179 + difference 5 2) sourceC2179) = raw29969 := by
      apply Matrix.ext; unfold tripleCharges sourceA2179 sourceB2179 sourceC2179 difference raw29969; decide +kernel
    rw [ha]
    exact (canonical29969 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2179 + difference 3 0) (sourceB2179 + difference 0 3) sourceC2179) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1102) := by
    have ha : (tripleCharges (sourceA2179 + difference 3 0) (sourceB2179 + difference 0 3) sourceC2179) = raw29970 := by
      apply Matrix.ext; unfold tripleCharges sourceA2179 sourceB2179 sourceC2179 difference raw29970; decide +kernel
    rw [ha]
    exact (canonical29970 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2179 + difference 3 1) (sourceB2179 + difference 1 3) sourceC2179) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2794) := by
    have ha : (tripleCharges (sourceA2179 + difference 3 1) (sourceB2179 + difference 1 3) sourceC2179) = raw29971 := by
      apply Matrix.ext; unfold tripleCharges sourceA2179 sourceB2179 sourceC2179 difference raw29971; decide +kernel
    rw [ha]
    exact (canonical29971 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2179 + difference 3 2) (sourceB2179 + difference 2 3) sourceC2179) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2845) := by
    have ha : (tripleCharges (sourceA2179 + difference 3 2) (sourceB2179 + difference 2 3) sourceC2179) = raw29972 := by
      apply Matrix.ext; unfold tripleCharges sourceA2179 sourceB2179 sourceC2179 difference raw29972; decide +kernel
    rw [ha]
    exact (canonical29972 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2179 + difference 3 4) (sourceB2179 + difference 4 3) sourceC2179) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2884) := by
    have ha : (tripleCharges (sourceA2179 + difference 3 4) (sourceB2179 + difference 4 3) sourceC2179) = raw16264 := by
      apply Matrix.ext; unfold tripleCharges sourceA2179 sourceB2179 sourceC2179 difference raw16264; decide +kernel
    rw [ha]
    exact (canonical16264 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2179 + difference 3 5) (sourceB2179 + difference 5 3) sourceC2179) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2881) := by
    have ha : (tripleCharges (sourceA2179 + difference 3 5) (sourceB2179 + difference 5 3) sourceC2179) = raw29973 := by
      apply Matrix.ext; unfold tripleCharges sourceA2179 sourceB2179 sourceC2179 difference raw29973; decide +kernel
    rw [ha]
    exact (canonical29973 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2179 + difference 4 0) (sourceB2179 + difference 0 4) sourceC2179) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1103) := by
    have ha : (tripleCharges (sourceA2179 + difference 4 0) (sourceB2179 + difference 0 4) sourceC2179) = raw29974 := by
      apply Matrix.ext; unfold tripleCharges sourceA2179 sourceB2179 sourceC2179 difference raw29974; decide +kernel
    rw [ha]
    exact (canonical29974 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2179 + difference 4 1) (sourceB2179 + difference 1 4) sourceC2179) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1783) := by
    have ha : (tripleCharges (sourceA2179 + difference 4 1) (sourceB2179 + difference 1 4) sourceC2179) = raw29975 := by
      apply Matrix.ext; unfold tripleCharges sourceA2179 sourceB2179 sourceC2179 difference raw29975; decide +kernel
    rw [ha]
    exact (canonical29975 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2179 + difference 4 2) (sourceB2179 + difference 2 4) sourceC2179) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1778) := by
    have ha : (tripleCharges (sourceA2179 + difference 4 2) (sourceB2179 + difference 2 4) sourceC2179) = raw29976 := by
      apply Matrix.ext; unfold tripleCharges sourceA2179 sourceB2179 sourceC2179 difference raw29976; decide +kernel
    rw [ha]
    exact (canonical29976 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2179 + difference 4 3) (sourceB2179 + difference 3 4) sourceC2179) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1778) := by
    have ha : (tripleCharges (sourceA2179 + difference 4 3) (sourceB2179 + difference 3 4) sourceC2179) = raw29977 := by
      apply Matrix.ext; unfold tripleCharges sourceA2179 sourceB2179 sourceC2179 difference raw29977; decide +kernel
    rw [ha]
    exact (canonical29977 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2179 + difference 4 5) (sourceB2179 + difference 5 4) sourceC2179) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2062) := by
    have ha : (tripleCharges (sourceA2179 + difference 4 5) (sourceB2179 + difference 5 4) sourceC2179) = raw29978 := by
      apply Matrix.ext; unfold tripleCharges sourceA2179 sourceB2179 sourceC2179 difference raw29978; decide +kernel
    rw [ha]
    exact (canonical29978 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2179 + difference 5 0) (sourceB2179 + difference 0 5) sourceC2179) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1104) := by
    have ha : (tripleCharges (sourceA2179 + difference 5 0) (sourceB2179 + difference 0 5) sourceC2179) = raw28268 := by
      apply Matrix.ext; unfold tripleCharges sourceA2179 sourceB2179 sourceC2179 difference raw28268; decide +kernel
    rw [ha]
    exact (canonical28268 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2179 + difference 5 1) (sourceB2179 + difference 1 5) sourceC2179) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2315) := by
    have ha : (tripleCharges (sourceA2179 + difference 5 1) (sourceB2179 + difference 1 5) sourceC2179) = raw28269 := by
      apply Matrix.ext; unfold tripleCharges sourceA2179 sourceB2179 sourceC2179 difference raw28269; decide +kernel
    rw [ha]
    exact (canonical28269 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2179 + difference 5 2) (sourceB2179 + difference 2 5) sourceC2179) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2310) := by
    have ha : (tripleCharges (sourceA2179 + difference 5 2) (sourceB2179 + difference 2 5) sourceC2179) = raw28270 := by
      apply Matrix.ext; unfold tripleCharges sourceA2179 sourceB2179 sourceC2179 difference raw28270; decide +kernel
    rw [ha]
    exact (canonical28270 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2179 + difference 5 3) (sourceB2179 + difference 3 5) sourceC2179) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2310) := by
    have ha : (tripleCharges (sourceA2179 + difference 5 3) (sourceB2179 + difference 3 5) sourceC2179) = raw28271 := by
      apply Matrix.ext; unfold tripleCharges sourceA2179 sourceB2179 sourceC2179 difference raw28271; decide +kernel
    rw [ha]
    exact (canonical28271 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2179 + difference 5 4) (sourceB2179 + difference 4 5) sourceC2179) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2519) := by
    have ha : (tripleCharges (sourceA2179 + difference 5 4) (sourceB2179 + difference 4 5) sourceC2179) = raw16274 := by
      apply Matrix.ext; unfold tripleCharges sourceA2179 sourceB2179 sourceC2179 difference raw16274; decide +kernel
    rw [ha]
    exact (canonical16274 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2179 sourceB2179 sourceC2179
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2179, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2180 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2180 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC2180 : Charge := ![1, 2, 0, 0, -2, -1]
def sourceForm2180 : Integer.Sparse Master := [(Sum.inr 4372, 2), (Sum.inr 4373, 1), (Sum.inr 4374, 1), (Sum.inr 4480, 1), (Sum.inr 4944, 2), (Sum.inr 4953, 1), (Sum.inr 4965, 2), (Sum.inr 4977, 2), (Sum.inr 4979, 1), (Sum.inr 5044, 2), (Sum.inr 5090, 2), (Sum.inr 5109, 1), (Sum.inr 5199, 2), (Sum.inr 5201, 1), (Sum.inr 5204, 2), (Sum.inr 5300, 1), (Sum.inr 5302, 1), (Sum.inr 5368, 2), (Sum.inr 5371, 1), (Sum.inr 5413, 1), (Sum.inr 5475, 1)]

theorem sourceEq2180 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2180 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2180 + difference 0 1) (sourceB2180 + difference 1 0) sourceC2180) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5371) := by
    have ha : (tripleCharges (sourceA2180 + difference 0 1) (sourceB2180 + difference 1 0) sourceC2180) = raw17999 := by
      apply Matrix.ext; unfold tripleCharges sourceA2180 sourceB2180 sourceC2180 difference raw17999; decide +kernel
    rw [ha]
    exact (canonical17999 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2180 + difference 0 2) (sourceB2180 + difference 2 0) sourceC2180) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5368) := by
    have ha : (tripleCharges (sourceA2180 + difference 0 2) (sourceB2180 + difference 2 0) sourceC2180) = raw18000 := by
      apply Matrix.ext; unfold tripleCharges sourceA2180 sourceB2180 sourceC2180 difference raw18000; decide +kernel
    rw [ha]
    exact (canonical18000 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2180 + difference 0 3) (sourceB2180 + difference 3 0) sourceC2180) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5368) := by
    have ha : (tripleCharges (sourceA2180 + difference 0 3) (sourceB2180 + difference 3 0) sourceC2180) = raw18001 := by
      apply Matrix.ext; unfold tripleCharges sourceA2180 sourceB2180 sourceC2180 difference raw18001; decide +kernel
    rw [ha]
    exact (canonical18001 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2180 + difference 0 4) (sourceB2180 + difference 4 0) sourceC2180) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5475) := by
    have ha : (tripleCharges (sourceA2180 + difference 0 4) (sourceB2180 + difference 4 0) sourceC2180) = raw29979 := by
      apply Matrix.ext; unfold tripleCharges sourceA2180 sourceB2180 sourceC2180 difference raw29979; decide +kernel
    rw [ha]
    exact (canonical29979 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2180 + difference 0 5) (sourceB2180 + difference 5 0) sourceC2180) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5413) := by
    have ha : (tripleCharges (sourceA2180 + difference 0 5) (sourceB2180 + difference 5 0) sourceC2180) = raw18002 := by
      apply Matrix.ext; unfold tripleCharges sourceA2180 sourceB2180 sourceC2180 difference raw18002; decide +kernel
    rw [ha]
    exact (canonical18002 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2180 + difference 1 0) (sourceB2180 + difference 0 1) sourceC2180) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4480) := by
    have ha : (tripleCharges (sourceA2180 + difference 1 0) (sourceB2180 + difference 0 1) sourceC2180) = raw29980 := by
      apply Matrix.ext; unfold tripleCharges sourceA2180 sourceB2180 sourceC2180 difference raw29980; decide +kernel
    rw [ha]
    exact (canonical29980 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2180 + difference 1 2) (sourceB2180 + difference 2 1) sourceC2180) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5090) := by
    have ha : (tripleCharges (sourceA2180 + difference 1 2) (sourceB2180 + difference 2 1) sourceC2180) = raw29981 := by
      apply Matrix.ext; unfold tripleCharges sourceA2180 sourceB2180 sourceC2180 difference raw29981; decide +kernel
    rw [ha]
    exact (canonical29981 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2180 + difference 1 3) (sourceB2180 + difference 3 1) sourceC2180) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5090) := by
    have ha : (tripleCharges (sourceA2180 + difference 1 3) (sourceB2180 + difference 3 1) sourceC2180) = raw29982 := by
      apply Matrix.ext; unfold tripleCharges sourceA2180 sourceB2180 sourceC2180 difference raw29982; decide +kernel
    rw [ha]
    exact (canonical29982 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2180 + difference 1 4) (sourceB2180 + difference 4 1) sourceC2180) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5300) := by
    have ha : (tripleCharges (sourceA2180 + difference 1 4) (sourceB2180 + difference 4 1) sourceC2180) = raw17983 := by
      apply Matrix.ext; unfold tripleCharges sourceA2180 sourceB2180 sourceC2180 difference raw17983; decide +kernel
    rw [ha]
    exact (canonical17983 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2180 + difference 1 5) (sourceB2180 + difference 5 1) sourceC2180) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA2180 + difference 1 5) (sourceB2180 + difference 5 1) sourceC2180) = raw29983 := by
      apply Matrix.ext; unfold tripleCharges sourceA2180 sourceB2180 sourceC2180 difference raw29983; decide +kernel
    rw [ha]
    exact (canonical29983 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2180 + difference 2 0) (sourceB2180 + difference 0 2) sourceC2180) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4372) := by
    have ha : (tripleCharges (sourceA2180 + difference 2 0) (sourceB2180 + difference 0 2) sourceC2180) = raw29984 := by
      apply Matrix.ext; unfold tripleCharges sourceA2180 sourceB2180 sourceC2180 difference raw29984; decide +kernel
    rw [ha]
    exact (canonical29984 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2180 + difference 2 1) (sourceB2180 + difference 1 2) sourceC2180) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4977) := by
    have ha : (tripleCharges (sourceA2180 + difference 2 1) (sourceB2180 + difference 1 2) sourceC2180) = raw29985 := by
      apply Matrix.ext; unfold tripleCharges sourceA2180 sourceB2180 sourceC2180 difference raw29985; decide +kernel
    rw [ha]
    exact (canonical29985 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2180 + difference 2 3) (sourceB2180 + difference 3 2) sourceC2180) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5044) := by
    have ha : (tripleCharges (sourceA2180 + difference 2 3) (sourceB2180 + difference 3 2) sourceC2180) = raw29986 := by
      apply Matrix.ext; unfold tripleCharges sourceA2180 sourceB2180 sourceC2180 difference raw29986; decide +kernel
    rw [ha]
    exact (canonical29986 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2180 + difference 2 4) (sourceB2180 + difference 4 2) sourceC2180) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5199) := by
    have ha : (tripleCharges (sourceA2180 + difference 2 4) (sourceB2180 + difference 4 2) sourceC2180) = raw17988 := by
      apply Matrix.ext; unfold tripleCharges sourceA2180 sourceB2180 sourceC2180 difference raw17988; decide +kernel
    rw [ha]
    exact (canonical17988 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2180 + difference 2 5) (sourceB2180 + difference 5 2) sourceC2180) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5204) := by
    have ha : (tripleCharges (sourceA2180 + difference 2 5) (sourceB2180 + difference 5 2) sourceC2180) = raw29987 := by
      apply Matrix.ext; unfold tripleCharges sourceA2180 sourceB2180 sourceC2180 difference raw29987; decide +kernel
    rw [ha]
    exact (canonical29987 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2180 + difference 3 0) (sourceB2180 + difference 0 3) sourceC2180) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4372) := by
    have ha : (tripleCharges (sourceA2180 + difference 3 0) (sourceB2180 + difference 0 3) sourceC2180) = raw29988 := by
      apply Matrix.ext; unfold tripleCharges sourceA2180 sourceB2180 sourceC2180 difference raw29988; decide +kernel
    rw [ha]
    exact (canonical29988 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2180 + difference 3 1) (sourceB2180 + difference 1 3) sourceC2180) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4977) := by
    have ha : (tripleCharges (sourceA2180 + difference 3 1) (sourceB2180 + difference 1 3) sourceC2180) = raw29989 := by
      apply Matrix.ext; unfold tripleCharges sourceA2180 sourceB2180 sourceC2180 difference raw29989; decide +kernel
    rw [ha]
    exact (canonical29989 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2180 + difference 3 2) (sourceB2180 + difference 2 3) sourceC2180) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5044) := by
    have ha : (tripleCharges (sourceA2180 + difference 3 2) (sourceB2180 + difference 2 3) sourceC2180) = raw29990 := by
      apply Matrix.ext; unfold tripleCharges sourceA2180 sourceB2180 sourceC2180 difference raw29990; decide +kernel
    rw [ha]
    exact (canonical29990 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2180 + difference 3 4) (sourceB2180 + difference 4 3) sourceC2180) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5199) := by
    have ha : (tripleCharges (sourceA2180 + difference 3 4) (sourceB2180 + difference 4 3) sourceC2180) = raw17993 := by
      apply Matrix.ext; unfold tripleCharges sourceA2180 sourceB2180 sourceC2180 difference raw17993; decide +kernel
    rw [ha]
    exact (canonical17993 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2180 + difference 3 5) (sourceB2180 + difference 5 3) sourceC2180) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5204) := by
    have ha : (tripleCharges (sourceA2180 + difference 3 5) (sourceB2180 + difference 5 3) sourceC2180) = raw29991 := by
      apply Matrix.ext; unfold tripleCharges sourceA2180 sourceB2180 sourceC2180 difference raw29991; decide +kernel
    rw [ha]
    exact (canonical29991 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2180 + difference 4 0) (sourceB2180 + difference 0 4) sourceC2180) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4374) := by
    have ha : (tripleCharges (sourceA2180 + difference 4 0) (sourceB2180 + difference 0 4) sourceC2180) = raw29992 := by
      apply Matrix.ext; unfold tripleCharges sourceA2180 sourceB2180 sourceC2180 difference raw29992; decide +kernel
    rw [ha]
    exact (canonical29992 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2180 + difference 4 1) (sourceB2180 + difference 1 4) sourceC2180) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4953) := by
    have ha : (tripleCharges (sourceA2180 + difference 4 1) (sourceB2180 + difference 1 4) sourceC2180) = raw29993 := by
      apply Matrix.ext; unfold tripleCharges sourceA2180 sourceB2180 sourceC2180 difference raw29993; decide +kernel
    rw [ha]
    exact (canonical29993 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2180 + difference 4 2) (sourceB2180 + difference 2 4) sourceC2180) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4944) := by
    have ha : (tripleCharges (sourceA2180 + difference 4 2) (sourceB2180 + difference 2 4) sourceC2180) = raw29994 := by
      apply Matrix.ext; unfold tripleCharges sourceA2180 sourceB2180 sourceC2180 difference raw29994; decide +kernel
    rw [ha]
    exact (canonical29994 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2180 + difference 4 3) (sourceB2180 + difference 3 4) sourceC2180) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4944) := by
    have ha : (tripleCharges (sourceA2180 + difference 4 3) (sourceB2180 + difference 3 4) sourceC2180) = raw29995 := by
      apply Matrix.ext; unfold tripleCharges sourceA2180 sourceB2180 sourceC2180 difference raw29995; decide +kernel
    rw [ha]
    exact (canonical29995 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2180 + difference 4 5) (sourceB2180 + difference 5 4) sourceC2180) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5109) := by
    have ha : (tripleCharges (sourceA2180 + difference 4 5) (sourceB2180 + difference 5 4) sourceC2180) = raw29996 := by
      apply Matrix.ext; unfold tripleCharges sourceA2180 sourceB2180 sourceC2180 difference raw29996; decide +kernel
    rw [ha]
    exact (canonical29996 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2180 + difference 5 0) (sourceB2180 + difference 0 5) sourceC2180) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4373) := by
    have ha : (tripleCharges (sourceA2180 + difference 5 0) (sourceB2180 + difference 0 5) sourceC2180) = raw29997 := by
      apply Matrix.ext; unfold tripleCharges sourceA2180 sourceB2180 sourceC2180 difference raw29997; decide +kernel
    rw [ha]
    exact (canonical29997 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2180 + difference 5 1) (sourceB2180 + difference 1 5) sourceC2180) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4979) := by
    have ha : (tripleCharges (sourceA2180 + difference 5 1) (sourceB2180 + difference 1 5) sourceC2180) = raw29998 := by
      apply Matrix.ext; unfold tripleCharges sourceA2180 sourceB2180 sourceC2180 difference raw29998; decide +kernel
    rw [ha]
    exact (canonical29998 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2180 + difference 5 2) (sourceB2180 + difference 2 5) sourceC2180) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4965) := by
    have ha : (tripleCharges (sourceA2180 + difference 5 2) (sourceB2180 + difference 2 5) sourceC2180) = raw29999 := by
      apply Matrix.ext; unfold tripleCharges sourceA2180 sourceB2180 sourceC2180 difference raw29999; decide +kernel
    rw [ha]
    exact (canonical29999 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2180 + difference 5 3) (sourceB2180 + difference 3 5) sourceC2180) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4965) := by
    have ha : (tripleCharges (sourceA2180 + difference 5 3) (sourceB2180 + difference 3 5) sourceC2180) = raw30000 := by
      apply Matrix.ext; unfold tripleCharges sourceA2180 sourceB2180 sourceC2180 difference raw30000; decide +kernel
    rw [ha]
    exact (canonical30000 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2180 + difference 5 4) (sourceB2180 + difference 4 5) sourceC2180) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5201) := by
    have ha : (tripleCharges (sourceA2180 + difference 5 4) (sourceB2180 + difference 4 5) sourceC2180) = raw18003 := by
      apply Matrix.ext; unfold tripleCharges sourceA2180 sourceB2180 sourceC2180 difference raw18003; decide +kernel
    rw [ha]
    exact (canonical18003 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2180 sourceB2180 sourceC2180
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2180, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2181 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2181 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC2181 : Charge := ![1, 2, 0, 0, -2, -1]
def sourceForm2181 : Integer.Sparse Master := [(Sum.inr 1734, 2), (Sum.inr 1735, 1), (Sum.inr 1740, 1), (Sum.inr 1748, 1), (Sum.inr 3413, 2), (Sum.inr 3423, 1), (Sum.inr 3474, 2), (Sum.inr 3475, 2), (Sum.inr 3480, 2), (Sum.inr 3486, 1), (Sum.inr 3578, 2), (Sum.inr 3579, 1), (Sum.inr 3584, 1), (Sum.inr 3595, 2), (Sum.inr 3596, 1), (Sum.inr 3624, 2), (Sum.inr 3626, 1), (Sum.inr 3767, 2), (Sum.inr 3775, 1), (Sum.inr 3817, 1), (Sum.inr 3963, 1)]

theorem sourceEq2181 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2181 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2181 + difference 0 1) (sourceB2181 + difference 1 0) sourceC2181) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3775) := by
    have ha : (tripleCharges (sourceA2181 + difference 0 1) (sourceB2181 + difference 1 0) sourceC2181) = raw18029 := by
      apply Matrix.ext; unfold tripleCharges sourceA2181 sourceB2181 sourceC2181 difference raw18029; decide +kernel
    rw [ha]
    exact (canonical18029 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2181 + difference 0 2) (sourceB2181 + difference 2 0) sourceC2181) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3767) := by
    have ha : (tripleCharges (sourceA2181 + difference 0 2) (sourceB2181 + difference 2 0) sourceC2181) = raw18030 := by
      apply Matrix.ext; unfold tripleCharges sourceA2181 sourceB2181 sourceC2181 difference raw18030; decide +kernel
    rw [ha]
    exact (canonical18030 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2181 + difference 0 3) (sourceB2181 + difference 3 0) sourceC2181) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3767) := by
    have ha : (tripleCharges (sourceA2181 + difference 0 3) (sourceB2181 + difference 3 0) sourceC2181) = raw18031 := by
      apply Matrix.ext; unfold tripleCharges sourceA2181 sourceB2181 sourceC2181 difference raw18031; decide +kernel
    rw [ha]
    exact (canonical18031 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2181 + difference 0 4) (sourceB2181 + difference 4 0) sourceC2181) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3963) := by
    have ha : (tripleCharges (sourceA2181 + difference 0 4) (sourceB2181 + difference 4 0) sourceC2181) = raw30001 := by
      apply Matrix.ext; unfold tripleCharges sourceA2181 sourceB2181 sourceC2181 difference raw30001; decide +kernel
    rw [ha]
    exact (canonical30001 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2181 + difference 0 5) (sourceB2181 + difference 5 0) sourceC2181) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3817) := by
    have ha : (tripleCharges (sourceA2181 + difference 0 5) (sourceB2181 + difference 5 0) sourceC2181) = raw18032 := by
      apply Matrix.ext; unfold tripleCharges sourceA2181 sourceB2181 sourceC2181 difference raw18032; decide +kernel
    rw [ha]
    exact (canonical18032 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2181 + difference 1 0) (sourceB2181 + difference 0 1) sourceC2181) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1740) := by
    have ha : (tripleCharges (sourceA2181 + difference 1 0) (sourceB2181 + difference 0 1) sourceC2181) = raw30002 := by
      apply Matrix.ext; unfold tripleCharges sourceA2181 sourceB2181 sourceC2181 difference raw30002; decide +kernel
    rw [ha]
    exact (canonical30002 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2181 + difference 1 2) (sourceB2181 + difference 2 1) sourceC2181) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3480) := by
    have ha : (tripleCharges (sourceA2181 + difference 1 2) (sourceB2181 + difference 2 1) sourceC2181) = raw30003 := by
      apply Matrix.ext; unfold tripleCharges sourceA2181 sourceB2181 sourceC2181 difference raw30003; decide +kernel
    rw [ha]
    exact (canonical30003 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2181 + difference 1 3) (sourceB2181 + difference 3 1) sourceC2181) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3480) := by
    have ha : (tripleCharges (sourceA2181 + difference 1 3) (sourceB2181 + difference 3 1) sourceC2181) = raw30004 := by
      apply Matrix.ext; unfold tripleCharges sourceA2181 sourceB2181 sourceC2181 difference raw30004; decide +kernel
    rw [ha]
    exact (canonical30004 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2181 + difference 1 4) (sourceB2181 + difference 4 1) sourceC2181) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3584) := by
    have ha : (tripleCharges (sourceA2181 + difference 1 4) (sourceB2181 + difference 4 1) sourceC2181) = raw18013 := by
      apply Matrix.ext; unfold tripleCharges sourceA2181 sourceB2181 sourceC2181 difference raw18013; decide +kernel
    rw [ha]
    exact (canonical18013 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2181 + difference 1 5) (sourceB2181 + difference 5 1) sourceC2181) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3626) := by
    have ha : (tripleCharges (sourceA2181 + difference 1 5) (sourceB2181 + difference 5 1) sourceC2181) = raw30005 := by
      apply Matrix.ext; unfold tripleCharges sourceA2181 sourceB2181 sourceC2181 difference raw30005; decide +kernel
    rw [ha]
    exact (canonical30005 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2181 + difference 2 0) (sourceB2181 + difference 0 2) sourceC2181) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1734) := by
    have ha : (tripleCharges (sourceA2181 + difference 2 0) (sourceB2181 + difference 0 2) sourceC2181) = raw30006 := by
      apply Matrix.ext; unfold tripleCharges sourceA2181 sourceB2181 sourceC2181 difference raw30006; decide +kernel
    rw [ha]
    exact (canonical30006 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2181 + difference 2 1) (sourceB2181 + difference 1 2) sourceC2181) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3595) := by
    have ha : (tripleCharges (sourceA2181 + difference 2 1) (sourceB2181 + difference 1 2) sourceC2181) = raw30007 := by
      apply Matrix.ext; unfold tripleCharges sourceA2181 sourceB2181 sourceC2181 difference raw30007; decide +kernel
    rw [ha]
    exact (canonical30007 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2181 + difference 2 3) (sourceB2181 + difference 3 2) sourceC2181) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3474) := by
    have ha : (tripleCharges (sourceA2181 + difference 2 3) (sourceB2181 + difference 3 2) sourceC2181) = raw30008 := by
      apply Matrix.ext; unfold tripleCharges sourceA2181 sourceB2181 sourceC2181 difference raw30008; decide +kernel
    rw [ha]
    exact (canonical30008 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2181 + difference 2 4) (sourceB2181 + difference 4 2) sourceC2181) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3578) := by
    have ha : (tripleCharges (sourceA2181 + difference 2 4) (sourceB2181 + difference 4 2) sourceC2181) = raw18018 := by
      apply Matrix.ext; unfold tripleCharges sourceA2181 sourceB2181 sourceC2181 difference raw18018; decide +kernel
    rw [ha]
    exact (canonical18018 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2181 + difference 2 5) (sourceB2181 + difference 5 2) sourceC2181) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3624) := by
    have ha : (tripleCharges (sourceA2181 + difference 2 5) (sourceB2181 + difference 5 2) sourceC2181) = raw30009 := by
      apply Matrix.ext; unfold tripleCharges sourceA2181 sourceB2181 sourceC2181 difference raw30009; decide +kernel
    rw [ha]
    exact (canonical30009 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2181 + difference 3 0) (sourceB2181 + difference 0 3) sourceC2181) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1734) := by
    have ha : (tripleCharges (sourceA2181 + difference 3 0) (sourceB2181 + difference 0 3) sourceC2181) = raw30010 := by
      apply Matrix.ext; unfold tripleCharges sourceA2181 sourceB2181 sourceC2181 difference raw30010; decide +kernel
    rw [ha]
    exact (canonical30010 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2181 + difference 3 1) (sourceB2181 + difference 1 3) sourceC2181) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3595) := by
    have ha : (tripleCharges (sourceA2181 + difference 3 1) (sourceB2181 + difference 1 3) sourceC2181) = raw30011 := by
      apply Matrix.ext; unfold tripleCharges sourceA2181 sourceB2181 sourceC2181 difference raw30011; decide +kernel
    rw [ha]
    exact (canonical30011 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2181 + difference 3 2) (sourceB2181 + difference 2 3) sourceC2181) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3474) := by
    have ha : (tripleCharges (sourceA2181 + difference 3 2) (sourceB2181 + difference 2 3) sourceC2181) = raw30012 := by
      apply Matrix.ext; unfold tripleCharges sourceA2181 sourceB2181 sourceC2181 difference raw30012; decide +kernel
    rw [ha]
    exact (canonical30012 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2181 + difference 3 4) (sourceB2181 + difference 4 3) sourceC2181) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3578) := by
    have ha : (tripleCharges (sourceA2181 + difference 3 4) (sourceB2181 + difference 4 3) sourceC2181) = raw18023 := by
      apply Matrix.ext; unfold tripleCharges sourceA2181 sourceB2181 sourceC2181 difference raw18023; decide +kernel
    rw [ha]
    exact (canonical18023 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2181 + difference 3 5) (sourceB2181 + difference 5 3) sourceC2181) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3624) := by
    have ha : (tripleCharges (sourceA2181 + difference 3 5) (sourceB2181 + difference 5 3) sourceC2181) = raw30013 := by
      apply Matrix.ext; unfold tripleCharges sourceA2181 sourceB2181 sourceC2181 difference raw30013; decide +kernel
    rw [ha]
    exact (canonical30013 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2181 + difference 4 0) (sourceB2181 + difference 0 4) sourceC2181) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1748) := by
    have ha : (tripleCharges (sourceA2181 + difference 4 0) (sourceB2181 + difference 0 4) sourceC2181) = raw30014 := by
      apply Matrix.ext; unfold tripleCharges sourceA2181 sourceB2181 sourceC2181 difference raw30014; decide +kernel
    rw [ha]
    exact (canonical30014 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2181 + difference 4 1) (sourceB2181 + difference 1 4) sourceC2181) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3423) := by
    have ha : (tripleCharges (sourceA2181 + difference 4 1) (sourceB2181 + difference 1 4) sourceC2181) = raw30015 := by
      apply Matrix.ext; unfold tripleCharges sourceA2181 sourceB2181 sourceC2181 difference raw30015; decide +kernel
    rw [ha]
    exact (canonical30015 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2181 + difference 4 2) (sourceB2181 + difference 2 4) sourceC2181) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3413) := by
    have ha : (tripleCharges (sourceA2181 + difference 4 2) (sourceB2181 + difference 2 4) sourceC2181) = raw30016 := by
      apply Matrix.ext; unfold tripleCharges sourceA2181 sourceB2181 sourceC2181 difference raw30016; decide +kernel
    rw [ha]
    exact (canonical30016 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2181 + difference 4 3) (sourceB2181 + difference 3 4) sourceC2181) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3413) := by
    have ha : (tripleCharges (sourceA2181 + difference 4 3) (sourceB2181 + difference 3 4) sourceC2181) = raw30017 := by
      apply Matrix.ext; unfold tripleCharges sourceA2181 sourceB2181 sourceC2181 difference raw30017; decide +kernel
    rw [ha]
    exact (canonical30017 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2181 + difference 4 5) (sourceB2181 + difference 5 4) sourceC2181) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3486) := by
    have ha : (tripleCharges (sourceA2181 + difference 4 5) (sourceB2181 + difference 5 4) sourceC2181) = raw30018 := by
      apply Matrix.ext; unfold tripleCharges sourceA2181 sourceB2181 sourceC2181 difference raw30018; decide +kernel
    rw [ha]
    exact (canonical30018 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2181 + difference 5 0) (sourceB2181 + difference 0 5) sourceC2181) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1735) := by
    have ha : (tripleCharges (sourceA2181 + difference 5 0) (sourceB2181 + difference 0 5) sourceC2181) = raw30019 := by
      apply Matrix.ext; unfold tripleCharges sourceA2181 sourceB2181 sourceC2181 difference raw30019; decide +kernel
    rw [ha]
    exact (canonical30019 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2181 + difference 5 1) (sourceB2181 + difference 1 5) sourceC2181) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3596) := by
    have ha : (tripleCharges (sourceA2181 + difference 5 1) (sourceB2181 + difference 1 5) sourceC2181) = raw30020 := by
      apply Matrix.ext; unfold tripleCharges sourceA2181 sourceB2181 sourceC2181 difference raw30020; decide +kernel
    rw [ha]
    exact (canonical30020 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2181 + difference 5 2) (sourceB2181 + difference 2 5) sourceC2181) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3475) := by
    have ha : (tripleCharges (sourceA2181 + difference 5 2) (sourceB2181 + difference 2 5) sourceC2181) = raw30021 := by
      apply Matrix.ext; unfold tripleCharges sourceA2181 sourceB2181 sourceC2181 difference raw30021; decide +kernel
    rw [ha]
    exact (canonical30021 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2181 + difference 5 3) (sourceB2181 + difference 3 5) sourceC2181) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3475) := by
    have ha : (tripleCharges (sourceA2181 + difference 5 3) (sourceB2181 + difference 3 5) sourceC2181) = raw30022 := by
      apply Matrix.ext; unfold tripleCharges sourceA2181 sourceB2181 sourceC2181 difference raw30022; decide +kernel
    rw [ha]
    exact (canonical30022 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2181 + difference 5 4) (sourceB2181 + difference 4 5) sourceC2181) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3579) := by
    have ha : (tripleCharges (sourceA2181 + difference 5 4) (sourceB2181 + difference 4 5) sourceC2181) = raw18033 := by
      apply Matrix.ext; unfold tripleCharges sourceA2181 sourceB2181 sourceC2181 difference raw18033; decide +kernel
    rw [ha]
    exact (canonical18033 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2181 sourceB2181 sourceC2181
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2181, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2182 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2182 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC2182 : Charge := ![1, 2, 0, 0, -2, -1]
def sourceForm2182 : Integer.Sparse Master := [(Sum.inr 2345, 1), (Sum.inr 2813, 2), (Sum.inr 2820, 1), (Sum.inr 2889, 1), (Sum.inr 3707, 1), (Sum.inr 4092, -1)]

theorem sourceEq2182 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2182 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2182 + difference 0 1) (sourceB2182 + difference 1 0) sourceC2182) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3707) := by
    have ha : (tripleCharges (sourceA2182 + difference 0 1) (sourceB2182 + difference 1 0) sourceC2182) = raw30023 := by
      apply Matrix.ext; unfold tripleCharges sourceA2182 sourceB2182 sourceC2182 difference raw30023; decide +kernel
    rw [ha]
    exact (canonical30023 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2182 + difference 1 1) (sourceB2182 + difference 1 1) sourceC2182) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2889) := by
    have ha : (tripleCharges (sourceA2182 + difference 1 1) (sourceB2182 + difference 1 1) sourceC2182) = raw30024 := by
      apply Matrix.ext; unfold tripleCharges sourceA2182 sourceB2182 sourceC2182 difference raw30024; decide +kernel
    rw [ha]
    exact (canonical30024 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2182 + difference 2 1) (sourceB2182 + difference 1 2) sourceC2182) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2813) := by
    have ha : (tripleCharges (sourceA2182 + difference 2 1) (sourceB2182 + difference 1 2) sourceC2182) = raw30025 := by
      apply Matrix.ext; unfold tripleCharges sourceA2182 sourceB2182 sourceC2182 difference raw30025; decide +kernel
    rw [ha]
    exact (canonical30025 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2182 + difference 3 1) (sourceB2182 + difference 1 3) sourceC2182) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2813) := by
    have ha : (tripleCharges (sourceA2182 + difference 3 1) (sourceB2182 + difference 1 3) sourceC2182) = raw30026 := by
      apply Matrix.ext; unfold tripleCharges sourceA2182 sourceB2182 sourceC2182 difference raw30026; decide +kernel
    rw [ha]
    exact (canonical30026 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2182 + difference 4 1) (sourceB2182 + difference 1 4) sourceC2182) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2345) := by
    have ha : (tripleCharges (sourceA2182 + difference 4 1) (sourceB2182 + difference 1 4) sourceC2182) = raw30027 := by
      apply Matrix.ext; unfold tripleCharges sourceA2182 sourceB2182 sourceC2182 difference raw30027; decide +kernel
    rw [ha]
    exact (canonical30027 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2182 + difference 5 1) (sourceB2182 + difference 1 5) sourceC2182) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2820) := by
    have ha : (tripleCharges (sourceA2182 + difference 5 1) (sourceB2182 + difference 1 5) sourceC2182) = raw28230 := by
      apply Matrix.ext; unfold tripleCharges sourceA2182 sourceB2182 sourceC2182 difference raw28230; decide +kernel
    rw [ha]
    exact (canonical28230 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2182 + sourceB2182) sourceC2182) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2182 + sourceB2182) sourceC2182) = raw28232 := by
      apply Matrix.ext; unfold doubleCharges sourceA2182 sourceB2182 sourceC2182 raw28232; decide +kernel
    rw [ha]
    exact (canonical28232 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2182 sourceB2182 sourceC2182
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2182, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2183 : Charge := ![1, 2, 0, 0, -2, -1]
def sourceB2183 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC2183 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceForm2183 : Integer.Sparse Master := [(Sum.inr 4856, 2), (Sum.inr 4874, 1), (Sum.inr 4875, 1), (Sum.inr 4884, 1), (Sum.inr 5003, 2), (Sum.inr 5016, 2), (Sum.inr 5022, 1), (Sum.inr 5023, 1), (Sum.inr 5024, 1), (Sum.inr 5111, 1), (Sum.inr 5152, 2), (Sum.inr 5176, 1), (Sum.inr 5177, 1), (Sum.inr 5182, 2), (Sum.inr 5188, 2), (Sum.inr 5189, 2), (Sum.inr 5193, 2), (Sum.inr 5206, 1), (Sum.inr 5207, 1), (Sum.inr 5210, 2), (Sum.inr 5214, 1)]

theorem sourceEq2183 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2183 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2183 + difference 0 1) (sourceB2183 + difference 1 0) sourceC2183) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5111) := by
    have ha : (tripleCharges (sourceA2183 + difference 0 1) (sourceB2183 + difference 1 0) sourceC2183) = raw29566 := by
      apply Matrix.ext; unfold tripleCharges sourceA2183 sourceB2183 sourceC2183 difference raw29566; decide +kernel
    rw [ha]
    exact (canonical29566 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2183 + difference 0 2) (sourceB2183 + difference 2 0) sourceC2183) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5003) := by
    have ha : (tripleCharges (sourceA2183 + difference 0 2) (sourceB2183 + difference 2 0) sourceC2183) = raw30028 := by
      apply Matrix.ext; unfold tripleCharges sourceA2183 sourceB2183 sourceC2183 difference raw30028; decide +kernel
    rw [ha]
    exact (canonical30028 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2183 + difference 0 3) (sourceB2183 + difference 3 0) sourceC2183) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5003) := by
    have ha : (tripleCharges (sourceA2183 + difference 0 3) (sourceB2183 + difference 3 0) sourceC2183) = raw30029 := by
      apply Matrix.ext; unfold tripleCharges sourceA2183 sourceB2183 sourceC2183 difference raw30029; decide +kernel
    rw [ha]
    exact (canonical30029 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2183 + difference 0 4) (sourceB2183 + difference 4 0) sourceC2183) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5023) := by
    have ha : (tripleCharges (sourceA2183 + difference 0 4) (sourceB2183 + difference 4 0) sourceC2183) = raw30030 := by
      apply Matrix.ext; unfold tripleCharges sourceA2183 sourceB2183 sourceC2183 difference raw30030; decide +kernel
    rw [ha]
    exact (canonical30030 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2183 + difference 0 5) (sourceB2183 + difference 5 0) sourceC2183) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5024) := by
    have ha : (tripleCharges (sourceA2183 + difference 0 5) (sourceB2183 + difference 5 0) sourceC2183) = raw30031 := by
      apply Matrix.ext; unfold tripleCharges sourceA2183 sourceB2183 sourceC2183 difference raw30031; decide +kernel
    rw [ha]
    exact (canonical30031 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2183 + difference 1 0) (sourceB2183 + difference 0 1) sourceC2183) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4884) := by
    have ha : (tripleCharges (sourceA2183 + difference 1 0) (sourceB2183 + difference 0 1) sourceC2183) = raw30032 := by
      apply Matrix.ext; unfold tripleCharges sourceA2183 sourceB2183 sourceC2183 difference raw30032; decide +kernel
    rw [ha]
    exact (canonical30032 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2183 + difference 1 2) (sourceB2183 + difference 2 1) sourceC2183) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5210) := by
    have ha : (tripleCharges (sourceA2183 + difference 1 2) (sourceB2183 + difference 2 1) sourceC2183) = raw30033 := by
      apply Matrix.ext; unfold tripleCharges sourceA2183 sourceB2183 sourceC2183 difference raw30033; decide +kernel
    rw [ha]
    exact (canonical30033 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2183 + difference 1 3) (sourceB2183 + difference 3 1) sourceC2183) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5210) := by
    have ha : (tripleCharges (sourceA2183 + difference 1 3) (sourceB2183 + difference 3 1) sourceC2183) = raw30034 := by
      apply Matrix.ext; unfold tripleCharges sourceA2183 sourceB2183 sourceC2183 difference raw30034; decide +kernel
    rw [ha]
    exact (canonical30034 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2183 + difference 1 4) (sourceB2183 + difference 4 1) sourceC2183) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5022) := by
    have ha : (tripleCharges (sourceA2183 + difference 1 4) (sourceB2183 + difference 4 1) sourceC2183) = raw30035 := by
      apply Matrix.ext; unfold tripleCharges sourceA2183 sourceB2183 sourceC2183 difference raw30035; decide +kernel
    rw [ha]
    exact (canonical30035 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2183 + difference 1 5) (sourceB2183 + difference 5 1) sourceC2183) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5214) := by
    have ha : (tripleCharges (sourceA2183 + difference 1 5) (sourceB2183 + difference 5 1) sourceC2183) = raw30036 := by
      apply Matrix.ext; unfold tripleCharges sourceA2183 sourceB2183 sourceC2183 difference raw30036; decide +kernel
    rw [ha]
    exact (canonical30036 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2183 + difference 2 0) (sourceB2183 + difference 0 2) sourceC2183) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4856) := by
    have ha : (tripleCharges (sourceA2183 + difference 2 0) (sourceB2183 + difference 0 2) sourceC2183) = raw30037 := by
      apply Matrix.ext; unfold tripleCharges sourceA2183 sourceB2183 sourceC2183 difference raw30037; decide +kernel
    rw [ha]
    exact (canonical30037 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2183 + difference 2 1) (sourceB2183 + difference 1 2) sourceC2183) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5152) := by
    have ha : (tripleCharges (sourceA2183 + difference 2 1) (sourceB2183 + difference 1 2) sourceC2183) = raw29576 := by
      apply Matrix.ext; unfold tripleCharges sourceA2183 sourceB2183 sourceC2183 difference raw29576; decide +kernel
    rw [ha]
    exact (canonical29576 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2183 + difference 2 3) (sourceB2183 + difference 3 2) sourceC2183) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5182) := by
    have ha : (tripleCharges (sourceA2183 + difference 2 3) (sourceB2183 + difference 3 2) sourceC2183) = raw30038 := by
      apply Matrix.ext; unfold tripleCharges sourceA2183 sourceB2183 sourceC2183 difference raw30038; decide +kernel
    rw [ha]
    exact (canonical30038 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2183 + difference 2 4) (sourceB2183 + difference 4 2) sourceC2183) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5016) := by
    have ha : (tripleCharges (sourceA2183 + difference 2 4) (sourceB2183 + difference 4 2) sourceC2183) = raw30039 := by
      apply Matrix.ext; unfold tripleCharges sourceA2183 sourceB2183 sourceC2183 difference raw30039; decide +kernel
    rw [ha]
    exact (canonical30039 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2183 + difference 2 5) (sourceB2183 + difference 5 2) sourceC2183) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5193) := by
    have ha : (tripleCharges (sourceA2183 + difference 2 5) (sourceB2183 + difference 5 2) sourceC2183) = raw30040 := by
      apply Matrix.ext; unfold tripleCharges sourceA2183 sourceB2183 sourceC2183 difference raw30040; decide +kernel
    rw [ha]
    exact (canonical30040 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2183 + difference 3 0) (sourceB2183 + difference 0 3) sourceC2183) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4856) := by
    have ha : (tripleCharges (sourceA2183 + difference 3 0) (sourceB2183 + difference 0 3) sourceC2183) = raw29825 := by
      apply Matrix.ext; unfold tripleCharges sourceA2183 sourceB2183 sourceC2183 difference raw29825; decide +kernel
    rw [ha]
    exact (canonical29825 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2183 + difference 3 1) (sourceB2183 + difference 1 3) sourceC2183) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5152) := by
    have ha : (tripleCharges (sourceA2183 + difference 3 1) (sourceB2183 + difference 1 3) sourceC2183) = raw29581 := by
      apply Matrix.ext; unfold tripleCharges sourceA2183 sourceB2183 sourceC2183 difference raw29581; decide +kernel
    rw [ha]
    exact (canonical29581 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2183 + difference 3 2) (sourceB2183 + difference 2 3) sourceC2183) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5182) := by
    have ha : (tripleCharges (sourceA2183 + difference 3 2) (sourceB2183 + difference 2 3) sourceC2183) = raw29826 := by
      apply Matrix.ext; unfold tripleCharges sourceA2183 sourceB2183 sourceC2183 difference raw29826; decide +kernel
    rw [ha]
    exact (canonical29826 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2183 + difference 3 4) (sourceB2183 + difference 4 3) sourceC2183) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5016) := by
    have ha : (tripleCharges (sourceA2183 + difference 3 4) (sourceB2183 + difference 4 3) sourceC2183) = raw29827 := by
      apply Matrix.ext; unfold tripleCharges sourceA2183 sourceB2183 sourceC2183 difference raw29827; decide +kernel
    rw [ha]
    exact (canonical29827 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2183 + difference 3 5) (sourceB2183 + difference 5 3) sourceC2183) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5193) := by
    have ha : (tripleCharges (sourceA2183 + difference 3 5) (sourceB2183 + difference 5 3) sourceC2183) = raw29828 := by
      apply Matrix.ext; unfold tripleCharges sourceA2183 sourceB2183 sourceC2183 difference raw29828; decide +kernel
    rw [ha]
    exact (canonical29828 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2183 + difference 4 0) (sourceB2183 + difference 0 4) sourceC2183) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4875) := by
    have ha : (tripleCharges (sourceA2183 + difference 4 0) (sourceB2183 + difference 0 4) sourceC2183) = raw29678 := by
      apply Matrix.ext; unfold tripleCharges sourceA2183 sourceB2183 sourceC2183 difference raw29678; decide +kernel
    rw [ha]
    exact (canonical29678 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2183 + difference 4 1) (sourceB2183 + difference 1 4) sourceC2183) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5177) := by
    have ha : (tripleCharges (sourceA2183 + difference 4 1) (sourceB2183 + difference 1 4) sourceC2183) = raw29586 := by
      apply Matrix.ext; unfold tripleCharges sourceA2183 sourceB2183 sourceC2183 difference raw29586; decide +kernel
    rw [ha]
    exact (canonical29586 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2183 + difference 4 2) (sourceB2183 + difference 2 4) sourceC2183) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5189) := by
    have ha : (tripleCharges (sourceA2183 + difference 4 2) (sourceB2183 + difference 2 4) sourceC2183) = raw29679 := by
      apply Matrix.ext; unfold tripleCharges sourceA2183 sourceB2183 sourceC2183 difference raw29679; decide +kernel
    rw [ha]
    exact (canonical29679 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2183 + difference 4 3) (sourceB2183 + difference 3 4) sourceC2183) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5189) := by
    have ha : (tripleCharges (sourceA2183 + difference 4 3) (sourceB2183 + difference 3 4) sourceC2183) = raw29680 := by
      apply Matrix.ext; unfold tripleCharges sourceA2183 sourceB2183 sourceC2183 difference raw29680; decide +kernel
    rw [ha]
    exact (canonical29680 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2183 + difference 4 5) (sourceB2183 + difference 5 4) sourceC2183) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5207) := by
    have ha : (tripleCharges (sourceA2183 + difference 4 5) (sourceB2183 + difference 5 4) sourceC2183) = raw29681 := by
      apply Matrix.ext; unfold tripleCharges sourceA2183 sourceB2183 sourceC2183 difference raw29681; decide +kernel
    rw [ha]
    exact (canonical29681 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2183 + difference 5 0) (sourceB2183 + difference 0 5) sourceC2183) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4874) := by
    have ha : (tripleCharges (sourceA2183 + difference 5 0) (sourceB2183 + difference 0 5) sourceC2183) = raw29567 := by
      apply Matrix.ext; unfold tripleCharges sourceA2183 sourceB2183 sourceC2183 difference raw29567; decide +kernel
    rw [ha]
    exact (canonical29567 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2183 + difference 5 1) (sourceB2183 + difference 1 5) sourceC2183) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5176) := by
    have ha : (tripleCharges (sourceA2183 + difference 5 1) (sourceB2183 + difference 1 5) sourceC2183) = raw29695 := by
      apply Matrix.ext; unfold tripleCharges sourceA2183 sourceB2183 sourceC2183 difference raw29695; decide +kernel
    rw [ha]
    exact (canonical29695 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2183 + difference 5 2) (sourceB2183 + difference 2 5) sourceC2183) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5188) := by
    have ha : (tripleCharges (sourceA2183 + difference 5 2) (sourceB2183 + difference 2 5) sourceC2183) = raw29568 := by
      apply Matrix.ext; unfold tripleCharges sourceA2183 sourceB2183 sourceC2183 difference raw29568; decide +kernel
    rw [ha]
    exact (canonical29568 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2183 + difference 5 3) (sourceB2183 + difference 3 5) sourceC2183) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5188) := by
    have ha : (tripleCharges (sourceA2183 + difference 5 3) (sourceB2183 + difference 3 5) sourceC2183) = raw29569 := by
      apply Matrix.ext; unfold tripleCharges sourceA2183 sourceB2183 sourceC2183 difference raw29569; decide +kernel
    rw [ha]
    exact (canonical29569 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2183 + difference 5 4) (sourceB2183 + difference 4 5) sourceC2183) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5206) := by
    have ha : (tripleCharges (sourceA2183 + difference 5 4) (sourceB2183 + difference 4 5) sourceC2183) = raw29570 := by
      apply Matrix.ext; unfold tripleCharges sourceA2183 sourceB2183 sourceC2183 difference raw29570; decide +kernel
    rw [ha]
    exact (canonical29570 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2183 sourceB2183 sourceC2183
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2183, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2184 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2184 : Charge := ![2, -1, 0, -1, 0, 0]
def sourceC2184 : Charge := ![1, 2, 0, 1, -2, -2]
def sourceForm2184 : Integer.Sparse Master := [(Sum.inr 2301, 2), (Sum.inr 2795, 1), (Sum.inr 2805, 1), (Sum.inr 2856, 1), (Sum.inr 3654, 1), (Sum.inr 4088, -1)]

theorem sourceEq2184 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2184 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2184 + difference 0 1) (sourceB2184 + difference 1 0) sourceC2184) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3654) := by
    have ha : (tripleCharges (sourceA2184 + difference 0 1) (sourceB2184 + difference 1 0) sourceC2184) = raw30041 := by
      apply Matrix.ext; unfold tripleCharges sourceA2184 sourceB2184 sourceC2184 difference raw30041; decide +kernel
    rw [ha]
    exact (canonical30041 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2184 + difference 1 1) (sourceB2184 + difference 1 1) sourceC2184) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2856) := by
    have ha : (tripleCharges (sourceA2184 + difference 1 1) (sourceB2184 + difference 1 1) sourceC2184) = raw30042 := by
      apply Matrix.ext; unfold tripleCharges sourceA2184 sourceB2184 sourceC2184 difference raw30042; decide +kernel
    rw [ha]
    exact (canonical30042 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2184 + difference 2 1) (sourceB2184 + difference 1 2) sourceC2184) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2795) := by
    have ha : (tripleCharges (sourceA2184 + difference 2 1) (sourceB2184 + difference 1 2) sourceC2184) = raw30043 := by
      apply Matrix.ext; unfold tripleCharges sourceA2184 sourceB2184 sourceC2184 difference raw30043; decide +kernel
    rw [ha]
    exact (canonical30043 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2184 + difference 3 1) (sourceB2184 + difference 1 3) sourceC2184) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2805) := by
    have ha : (tripleCharges (sourceA2184 + difference 3 1) (sourceB2184 + difference 1 3) sourceC2184) = raw30044 := by
      apply Matrix.ext; unfold tripleCharges sourceA2184 sourceB2184 sourceC2184 difference raw30044; decide +kernel
    rw [ha]
    exact (canonical30044 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2184 + difference 4 1) (sourceB2184 + difference 1 4) sourceC2184) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2301) := by
    have ha : (tripleCharges (sourceA2184 + difference 4 1) (sourceB2184 + difference 1 4) sourceC2184) = raw30045 := by
      apply Matrix.ext; unfold tripleCharges sourceA2184 sourceB2184 sourceC2184 difference raw30045; decide +kernel
    rw [ha]
    exact (canonical30045 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2184 + difference 5 1) (sourceB2184 + difference 1 5) sourceC2184) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2301) := by
    have ha : (tripleCharges (sourceA2184 + difference 5 1) (sourceB2184 + difference 1 5) sourceC2184) = raw30046 := by
      apply Matrix.ext; unfold tripleCharges sourceA2184 sourceB2184 sourceC2184 difference raw30046; decide +kernel
    rw [ha]
    exact (canonical30046 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2184 + sourceB2184) sourceC2184) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA2184 + sourceB2184) sourceC2184) = raw30047 := by
      apply Matrix.ext; unfold doubleCharges sourceA2184 sourceB2184 sourceC2184 raw30047; decide +kernel
    rw [ha]
    exact (canonical30047 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2184 sourceB2184 sourceC2184
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2184, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2185 : Charge := ![1, 2, 0, 1, -2, -2]
def sourceB2185 : Charge := ![2, -1, 0, -1, 0, 0]
def sourceC2185 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceForm2185 : Integer.Sparse Master := [(Sum.inr 2307, 2), (Sum.inr 3332, 1), (Sum.inr 3361, 1), (Sum.inr 3439, 1), (Sum.inr 3630, 1), (Sum.inr 4082, -1)]

theorem sourceEq2185 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2185 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2185 + difference 0 0) (sourceB2185 + difference 0 0) sourceC2185) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3630) := by
    have ha : (tripleCharges (sourceA2185 + difference 0 0) (sourceB2185 + difference 0 0) sourceC2185) = raw29354 := by
      apply Matrix.ext; unfold tripleCharges sourceA2185 sourceB2185 sourceC2185 difference raw29354; decide +kernel
    rw [ha]
    exact (canonical29354 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2185 + difference 0 1) (sourceB2185 + difference 1 0) sourceC2185) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3439) := by
    have ha : (tripleCharges (sourceA2185 + difference 0 1) (sourceB2185 + difference 1 0) sourceC2185) = raw29860 := by
      apply Matrix.ext; unfold tripleCharges sourceA2185 sourceB2185 sourceC2185 difference raw29860; decide +kernel
    rw [ha]
    exact (canonical29860 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2185 + difference 0 2) (sourceB2185 + difference 2 0) sourceC2185) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3332) := by
    have ha : (tripleCharges (sourceA2185 + difference 0 2) (sourceB2185 + difference 2 0) sourceC2185) = raw30048 := by
      apply Matrix.ext; unfold tripleCharges sourceA2185 sourceB2185 sourceC2185 difference raw30048; decide +kernel
    rw [ha]
    exact (canonical30048 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2185 + difference 0 3) (sourceB2185 + difference 3 0) sourceC2185) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3361) := by
    have ha : (tripleCharges (sourceA2185 + difference 0 3) (sourceB2185 + difference 3 0) sourceC2185) = raw30049 := by
      apply Matrix.ext; unfold tripleCharges sourceA2185 sourceB2185 sourceC2185 difference raw30049; decide +kernel
    rw [ha]
    exact (canonical30049 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2185 + difference 0 4) (sourceB2185 + difference 4 0) sourceC2185) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2307) := by
    have ha : (tripleCharges (sourceA2185 + difference 0 4) (sourceB2185 + difference 4 0) sourceC2185) = raw30050 := by
      apply Matrix.ext; unfold tripleCharges sourceA2185 sourceB2185 sourceC2185 difference raw30050; decide +kernel
    rw [ha]
    exact (canonical30050 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2185 + difference 0 5) (sourceB2185 + difference 5 0) sourceC2185) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2307) := by
    have ha : (tripleCharges (sourceA2185 + difference 0 5) (sourceB2185 + difference 5 0) sourceC2185) = raw30051 := by
      apply Matrix.ext; unfold tripleCharges sourceA2185 sourceB2185 sourceC2185 difference raw30051; decide +kernel
    rw [ha]
    exact (canonical30051 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2185 + sourceB2185) sourceC2185) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2185 + sourceB2185) sourceC2185) = raw29319 := by
      apply Matrix.ext; unfold doubleCharges sourceA2185 sourceB2185 sourceC2185 raw29319; decide +kernel
    rw [ha]
    exact (canonical29319 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2185 sourceB2185 sourceC2185
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2185, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2186 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2186 : Charge := ![2, -2, 0, 0, 0, 0]
def sourceC2186 : Charge := ![1, 3, 0, 0, -2, -2]
def sourceForm2186 : Integer.Sparse Master := [(Sum.inr 2315, 2), (Sum.inr 2792, 2), (Sum.inr 2843, 1), (Sum.inr 3361, 1), (Sum.inr 4082, -1)]

theorem sourceEq2186 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2186 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2186 + difference 0 1) (sourceB2186 + difference 1 0) sourceC2186) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3361) := by
    have ha : (tripleCharges (sourceA2186 + difference 0 1) (sourceB2186 + difference 1 0) sourceC2186) = raw30052 := by
      apply Matrix.ext; unfold tripleCharges sourceA2186 sourceB2186 sourceC2186 difference raw30052; decide +kernel
    rw [ha]
    exact (canonical30052 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2186 + difference 1 1) (sourceB2186 + difference 1 1) sourceC2186) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2843) := by
    have ha : (tripleCharges (sourceA2186 + difference 1 1) (sourceB2186 + difference 1 1) sourceC2186) = raw30053 := by
      apply Matrix.ext; unfold tripleCharges sourceA2186 sourceB2186 sourceC2186 difference raw30053; decide +kernel
    rw [ha]
    exact (canonical30053 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2186 + difference 2 1) (sourceB2186 + difference 1 2) sourceC2186) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2792) := by
    have ha : (tripleCharges (sourceA2186 + difference 2 1) (sourceB2186 + difference 1 2) sourceC2186) = raw30054 := by
      apply Matrix.ext; unfold tripleCharges sourceA2186 sourceB2186 sourceC2186 difference raw30054; decide +kernel
    rw [ha]
    exact (canonical30054 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2186 + difference 3 1) (sourceB2186 + difference 1 3) sourceC2186) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2792) := by
    have ha : (tripleCharges (sourceA2186 + difference 3 1) (sourceB2186 + difference 1 3) sourceC2186) = raw30055 := by
      apply Matrix.ext; unfold tripleCharges sourceA2186 sourceB2186 sourceC2186 difference raw30055; decide +kernel
    rw [ha]
    exact (canonical30055 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2186 + difference 4 1) (sourceB2186 + difference 1 4) sourceC2186) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2315) := by
    have ha : (tripleCharges (sourceA2186 + difference 4 1) (sourceB2186 + difference 1 4) sourceC2186) = raw30056 := by
      apply Matrix.ext; unfold tripleCharges sourceA2186 sourceB2186 sourceC2186 difference raw30056; decide +kernel
    rw [ha]
    exact (canonical30056 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2186 + difference 5 1) (sourceB2186 + difference 1 5) sourceC2186) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2315) := by
    have ha : (tripleCharges (sourceA2186 + difference 5 1) (sourceB2186 + difference 1 5) sourceC2186) = raw30057 := by
      apply Matrix.ext; unfold tripleCharges sourceA2186 sourceB2186 sourceC2186 difference raw30057; decide +kernel
    rw [ha]
    exact (canonical30057 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2186 + sourceB2186) sourceC2186) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2186 + sourceB2186) sourceC2186) = raw30058 := by
      apply Matrix.ext; unfold doubleCharges sourceA2186 sourceB2186 sourceC2186 raw30058; decide +kernel
    rw [ha]
    exact (canonical30058 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2186 sourceB2186 sourceC2186
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2186, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2187 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2187 : Charge := ![1, 2, 0, -2, 0, -1]
def sourceC2187 : Charge := ![2, -1, 0, 2, -2, -1]
def sourceForm2187 : Integer.Sparse Master := [(Sum.inr 2608, 1), (Sum.inr 3042, 1), (Sum.inr 3695, 1), (Sum.inr 3702, 1), (Sum.inr 3811, 1), (Sum.inr 3868, 1), (Sum.inr 4088, -1)]

theorem sourceEq2187 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2187 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2187 + difference 0 0) (sourceB2187 + difference 0 0) sourceC2187) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2608) := by
    have ha : (tripleCharges (sourceA2187 + difference 0 0) (sourceB2187 + difference 0 0) sourceC2187) = raw22458 := by
      apply Matrix.ext; unfold tripleCharges sourceA2187 sourceB2187 sourceC2187 difference raw22458; decide +kernel
    rw [ha]
    exact (canonical22458 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2187 + difference 0 1) (sourceB2187 + difference 1 0) sourceC2187) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3042) := by
    have ha : (tripleCharges (sourceA2187 + difference 0 1) (sourceB2187 + difference 1 0) sourceC2187) = raw30059 := by
      apply Matrix.ext; unfold tripleCharges sourceA2187 sourceB2187 sourceC2187 difference raw30059; decide +kernel
    rw [ha]
    exact (canonical30059 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2187 + difference 0 2) (sourceB2187 + difference 2 0) sourceC2187) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3695) := by
    have ha : (tripleCharges (sourceA2187 + difference 0 2) (sourceB2187 + difference 2 0) sourceC2187) = raw30060 := by
      apply Matrix.ext; unfold tripleCharges sourceA2187 sourceB2187 sourceC2187 difference raw30060; decide +kernel
    rw [ha]
    exact (canonical30060 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2187 + difference 0 3) (sourceB2187 + difference 3 0) sourceC2187) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3702) := by
    have ha : (tripleCharges (sourceA2187 + difference 0 3) (sourceB2187 + difference 3 0) sourceC2187) = raw30061 := by
      apply Matrix.ext; unfold tripleCharges sourceA2187 sourceB2187 sourceC2187 difference raw30061; decide +kernel
    rw [ha]
    exact (canonical30061 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2187 + difference 0 4) (sourceB2187 + difference 4 0) sourceC2187) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3868) := by
    have ha : (tripleCharges (sourceA2187 + difference 0 4) (sourceB2187 + difference 4 0) sourceC2187) = raw30062 := by
      apply Matrix.ext; unfold tripleCharges sourceA2187 sourceB2187 sourceC2187 difference raw30062; decide +kernel
    rw [ha]
    exact (canonical30062 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2187 + difference 0 5) (sourceB2187 + difference 5 0) sourceC2187) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3811) := by
    have ha : (tripleCharges (sourceA2187 + difference 0 5) (sourceB2187 + difference 5 0) sourceC2187) = raw30063 := by
      apply Matrix.ext; unfold tripleCharges sourceA2187 sourceB2187 sourceC2187 difference raw30063; decide +kernel
    rw [ha]
    exact (canonical30063 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2187 + sourceB2187) sourceC2187) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA2187 + sourceB2187) sourceC2187) = raw22463 := by
      apply Matrix.ext; unfold doubleCharges sourceA2187 sourceB2187 sourceC2187 raw22463; decide +kernel
    rw [ha]
    exact (canonical22463 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2187 sourceB2187 sourceC2187
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2187, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2188 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2188 : Charge := ![1, 2, -1, -1, 0, -1]
def sourceC2188 : Charge := ![2, -1, 1, 1, -2, -1]
def sourceForm2188 : Integer.Sparse Master := [(Sum.inr 2609, 1), (Sum.inr 3041, 1), (Sum.inr 3687, 2), (Sum.inr 3799, 1), (Sum.inr 3869, 1), (Sum.inr 4090, -1)]

theorem sourceEq2188 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2188 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2188 + difference 0 0) (sourceB2188 + difference 0 0) sourceC2188) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2609) := by
    have ha : (tripleCharges (sourceA2188 + difference 0 0) (sourceB2188 + difference 0 0) sourceC2188) = raw22465 := by
      apply Matrix.ext; unfold tripleCharges sourceA2188 sourceB2188 sourceC2188 difference raw22465; decide +kernel
    rw [ha]
    exact (canonical22465 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2188 + difference 0 1) (sourceB2188 + difference 1 0) sourceC2188) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3041) := by
    have ha : (tripleCharges (sourceA2188 + difference 0 1) (sourceB2188 + difference 1 0) sourceC2188) = raw30064 := by
      apply Matrix.ext; unfold tripleCharges sourceA2188 sourceB2188 sourceC2188 difference raw30064; decide +kernel
    rw [ha]
    exact (canonical30064 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2188 + difference 0 2) (sourceB2188 + difference 2 0) sourceC2188) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3687) := by
    have ha : (tripleCharges (sourceA2188 + difference 0 2) (sourceB2188 + difference 2 0) sourceC2188) = raw30065 := by
      apply Matrix.ext; unfold tripleCharges sourceA2188 sourceB2188 sourceC2188 difference raw30065; decide +kernel
    rw [ha]
    exact (canonical30065 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2188 + difference 0 3) (sourceB2188 + difference 3 0) sourceC2188) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3687) := by
    have ha : (tripleCharges (sourceA2188 + difference 0 3) (sourceB2188 + difference 3 0) sourceC2188) = raw30066 := by
      apply Matrix.ext; unfold tripleCharges sourceA2188 sourceB2188 sourceC2188 difference raw30066; decide +kernel
    rw [ha]
    exact (canonical30066 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2188 + difference 0 4) (sourceB2188 + difference 4 0) sourceC2188) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3869) := by
    have ha : (tripleCharges (sourceA2188 + difference 0 4) (sourceB2188 + difference 4 0) sourceC2188) = raw30067 := by
      apply Matrix.ext; unfold tripleCharges sourceA2188 sourceB2188 sourceC2188 difference raw30067; decide +kernel
    rw [ha]
    exact (canonical30067 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2188 + difference 0 5) (sourceB2188 + difference 5 0) sourceC2188) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3799) := by
    have ha : (tripleCharges (sourceA2188 + difference 0 5) (sourceB2188 + difference 5 0) sourceC2188) = raw30068 := by
      apply Matrix.ext; unfold tripleCharges sourceA2188 sourceB2188 sourceC2188 difference raw30068; decide +kernel
    rw [ha]
    exact (canonical30068 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2188 + sourceB2188) sourceC2188) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (doubleCharges (sourceA2188 + sourceB2188) sourceC2188) = raw22470 := by
      apply Matrix.ext; unfold doubleCharges sourceA2188 sourceB2188 sourceC2188 raw22470; decide +kernel
    rw [ha]
    exact (canonical22470 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2188 sourceB2188 sourceC2188
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2188, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2189 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2189 : Charge := ![1, 1, 1, -2, 0, -1]
def sourceC2189 : Charge := ![2, 0, -1, 2, -2, -1]
def sourceForm2189 : Integer.Sparse Master := [(Sum.inr 2533, 1), (Sum.inr 3679, 1), (Sum.inr 3681, 1), (Sum.inr 3695, 1), (Sum.inr 3795, 1), (Sum.inr 3832, 1), (Sum.inr 4088, -1)]

theorem sourceEq2189 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2189 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2189 + difference 0 0) (sourceB2189 + difference 0 0) sourceC2189) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2533) := by
    have ha : (tripleCharges (sourceA2189 + difference 0 0) (sourceB2189 + difference 0 0) sourceC2189) = raw30069 := by
      apply Matrix.ext; unfold tripleCharges sourceA2189 sourceB2189 sourceC2189 difference raw30069; decide +kernel
    rw [ha]
    exact (canonical30069 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2189 + difference 0 1) (sourceB2189 + difference 1 0) sourceC2189) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3679) := by
    have ha : (tripleCharges (sourceA2189 + difference 0 1) (sourceB2189 + difference 1 0) sourceC2189) = raw30070 := by
      apply Matrix.ext; unfold tripleCharges sourceA2189 sourceB2189 sourceC2189 difference raw30070; decide +kernel
    rw [ha]
    exact (canonical30070 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2189 + difference 0 2) (sourceB2189 + difference 2 0) sourceC2189) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3695) := by
    have ha : (tripleCharges (sourceA2189 + difference 0 2) (sourceB2189 + difference 2 0) sourceC2189) = raw30071 := by
      apply Matrix.ext; unfold tripleCharges sourceA2189 sourceB2189 sourceC2189 difference raw30071; decide +kernel
    rw [ha]
    exact (canonical30071 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2189 + difference 0 3) (sourceB2189 + difference 3 0) sourceC2189) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3681) := by
    have ha : (tripleCharges (sourceA2189 + difference 0 3) (sourceB2189 + difference 3 0) sourceC2189) = raw30072 := by
      apply Matrix.ext; unfold tripleCharges sourceA2189 sourceB2189 sourceC2189 difference raw30072; decide +kernel
    rw [ha]
    exact (canonical30072 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2189 + difference 0 4) (sourceB2189 + difference 4 0) sourceC2189) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3832) := by
    have ha : (tripleCharges (sourceA2189 + difference 0 4) (sourceB2189 + difference 4 0) sourceC2189) = raw30073 := by
      apply Matrix.ext; unfold tripleCharges sourceA2189 sourceB2189 sourceC2189 difference raw30073; decide +kernel
    rw [ha]
    exact (canonical30073 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2189 + difference 0 5) (sourceB2189 + difference 5 0) sourceC2189) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3795) := by
    have ha : (tripleCharges (sourceA2189 + difference 0 5) (sourceB2189 + difference 5 0) sourceC2189) = raw30074 := by
      apply Matrix.ext; unfold tripleCharges sourceA2189 sourceB2189 sourceC2189 difference raw30074; decide +kernel
    rw [ha]
    exact (canonical30074 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2189 + sourceB2189) sourceC2189) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA2189 + sourceB2189) sourceC2189) = raw30075 := by
      apply Matrix.ext; unfold doubleCharges sourceA2189 sourceB2189 sourceC2189 raw30075; decide +kernel
    rw [ha]
    exact (canonical30075 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2189 sourceB2189 sourceC2189
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2189, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2190 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2190 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC2190 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceForm2190 : Integer.Sparse Master := [(Sum.inr 4533, 1), (Sum.inr 4534, 1), (Sum.inr 4535, 1), (Sum.inr 4556, 1), (Sum.inr 4612, 1), (Sum.inr 4929, 1), (Sum.inr 4934, 1), (Sum.inr 4943, 1), (Sum.inr 4955, 1), (Sum.inr 4956, 1), (Sum.inr 4959, 1), (Sum.inr 4966, 1), (Sum.inr 4972, 1), (Sum.inr 5036, 1), (Sum.inr 5075, 1), (Sum.inr 5111, 1), (Sum.inr 5112, 1), (Sum.inr 5134, 1), (Sum.inr 5135, 1), (Sum.inr 5139, 1), (Sum.inr 5141, 1), (Sum.inr 5163, 1), (Sum.inr 5164, 1), (Sum.inr 5274, 1), (Sum.inr 5275, 1), (Sum.inr 5351, 1), (Sum.inr 5355, 1), (Sum.inr 5367, 1), (Sum.inr 5409, 1), (Sum.inr 5428, 1)]

theorem sourceEq2190 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2190 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2190 + difference 0 1) (sourceB2190 + difference 1 0) sourceC2190) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5355) := by
    have ha : (tripleCharges (sourceA2190 + difference 0 1) (sourceB2190 + difference 1 0) sourceC2190) = raw30076 := by
      apply Matrix.ext; unfold tripleCharges sourceA2190 sourceB2190 sourceC2190 difference raw30076; decide +kernel
    rw [ha]
    exact (canonical30076 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2190 + difference 0 2) (sourceB2190 + difference 2 0) sourceC2190) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5351) := by
    have ha : (tripleCharges (sourceA2190 + difference 0 2) (sourceB2190 + difference 2 0) sourceC2190) = raw30077 := by
      apply Matrix.ext; unfold tripleCharges sourceA2190 sourceB2190 sourceC2190 difference raw30077; decide +kernel
    rw [ha]
    exact (canonical30077 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2190 + difference 0 3) (sourceB2190 + difference 3 0) sourceC2190) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5367) := by
    have ha : (tripleCharges (sourceA2190 + difference 0 3) (sourceB2190 + difference 3 0) sourceC2190) = raw30078 := by
      apply Matrix.ext; unfold tripleCharges sourceA2190 sourceB2190 sourceC2190 difference raw30078; decide +kernel
    rw [ha]
    exact (canonical30078 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2190 + difference 0 4) (sourceB2190 + difference 4 0) sourceC2190) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5428) := by
    have ha : (tripleCharges (sourceA2190 + difference 0 4) (sourceB2190 + difference 4 0) sourceC2190) = raw10342 := by
      apply Matrix.ext; unfold tripleCharges sourceA2190 sourceB2190 sourceC2190 difference raw10342; decide +kernel
    rw [ha]
    exact (canonical10342 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2190 + difference 0 5) (sourceB2190 + difference 5 0) sourceC2190) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5409) := by
    have ha : (tripleCharges (sourceA2190 + difference 0 5) (sourceB2190 + difference 5 0) sourceC2190) = raw30079 := by
      apply Matrix.ext; unfold tripleCharges sourceA2190 sourceB2190 sourceC2190 difference raw30079; decide +kernel
    rw [ha]
    exact (canonical30079 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2190 + difference 1 0) (sourceB2190 + difference 0 1) sourceC2190) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA2190 + difference 1 0) (sourceB2190 + difference 0 1) sourceC2190) = raw10362 := by
      apply Matrix.ext; unfold tripleCharges sourceA2190 sourceB2190 sourceC2190 difference raw10362; decide +kernel
    rw [ha]
    exact (canonical10362 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2190 + difference 1 2) (sourceB2190 + difference 2 1) sourceC2190) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA2190 + difference 1 2) (sourceB2190 + difference 2 1) sourceC2190) = raw10364 := by
      apply Matrix.ext; unfold tripleCharges sourceA2190 sourceB2190 sourceC2190 difference raw10364; decide +kernel
    rw [ha]
    exact (canonical10364 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2190 + difference 1 3) (sourceB2190 + difference 3 1) sourceC2190) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5111) := by
    have ha : (tripleCharges (sourceA2190 + difference 1 3) (sourceB2190 + difference 3 1) sourceC2190) = raw10365 := by
      apply Matrix.ext; unfold tripleCharges sourceA2190 sourceB2190 sourceC2190 difference raw10365; decide +kernel
    rw [ha]
    exact (canonical10365 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2190 + difference 1 4) (sourceB2190 + difference 4 1) sourceC2190) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5275) := by
    have ha : (tripleCharges (sourceA2190 + difference 1 4) (sourceB2190 + difference 4 1) sourceC2190) = raw22655 := by
      apply Matrix.ext; unfold tripleCharges sourceA2190 sourceB2190 sourceC2190 difference raw22655; decide +kernel
    rw [ha]
    exact (canonical22655 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2190 + difference 1 5) (sourceB2190 + difference 5 1) sourceC2190) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5274) := by
    have ha : (tripleCharges (sourceA2190 + difference 1 5) (sourceB2190 + difference 5 1) sourceC2190) = raw10366 := by
      apply Matrix.ext; unfold tripleCharges sourceA2190 sourceB2190 sourceC2190 difference raw10366; decide +kernel
    rw [ha]
    exact (canonical10366 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2190 + difference 2 0) (sourceB2190 + difference 0 2) sourceC2190) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4533) := by
    have ha : (tripleCharges (sourceA2190 + difference 2 0) (sourceB2190 + difference 0 2) sourceC2190) = raw22661 := by
      apply Matrix.ext; unfold tripleCharges sourceA2190 sourceB2190 sourceC2190 difference raw22661; decide +kernel
    rw [ha]
    exact (canonical22661 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2190 + difference 2 1) (sourceB2190 + difference 1 2) sourceC2190) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4955) := by
    have ha : (tripleCharges (sourceA2190 + difference 2 1) (sourceB2190 + difference 1 2) sourceC2190) = raw30080 := by
      apply Matrix.ext; unfold tripleCharges sourceA2190 sourceB2190 sourceC2190 difference raw30080; decide +kernel
    rw [ha]
    exact (canonical30080 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2190 + difference 2 3) (sourceB2190 + difference 3 2) sourceC2190) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5036) := by
    have ha : (tripleCharges (sourceA2190 + difference 2 3) (sourceB2190 + difference 3 2) sourceC2190) = raw30081 := by
      apply Matrix.ext; unfold tripleCharges sourceA2190 sourceB2190 sourceC2190 difference raw30081; decide +kernel
    rw [ha]
    exact (canonical30081 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2190 + difference 2 4) (sourceB2190 + difference 4 2) sourceC2190) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5135) := by
    have ha : (tripleCharges (sourceA2190 + difference 2 4) (sourceB2190 + difference 4 2) sourceC2190) = raw10353 := by
      apply Matrix.ext; unfold tripleCharges sourceA2190 sourceB2190 sourceC2190 difference raw10353; decide +kernel
    rw [ha]
    exact (canonical10353 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2190 + difference 2 5) (sourceB2190 + difference 5 2) sourceC2190) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5134) := by
    have ha : (tripleCharges (sourceA2190 + difference 2 5) (sourceB2190 + difference 5 2) sourceC2190) = raw30082 := by
      apply Matrix.ext; unfold tripleCharges sourceA2190 sourceB2190 sourceC2190 difference raw30082; decide +kernel
    rw [ha]
    exact (canonical30082 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2190 + difference 3 0) (sourceB2190 + difference 0 3) sourceC2190) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4556) := by
    have ha : (tripleCharges (sourceA2190 + difference 3 0) (sourceB2190 + difference 0 3) sourceC2190) = raw22665 := by
      apply Matrix.ext; unfold tripleCharges sourceA2190 sourceB2190 sourceC2190 difference raw22665; decide +kernel
    rw [ha]
    exact (canonical22665 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2190 + difference 3 1) (sourceB2190 + difference 1 3) sourceC2190) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4966) := by
    have ha : (tripleCharges (sourceA2190 + difference 3 1) (sourceB2190 + difference 1 3) sourceC2190) = raw30083 := by
      apply Matrix.ext; unfold tripleCharges sourceA2190 sourceB2190 sourceC2190 difference raw30083; decide +kernel
    rw [ha]
    exact (canonical30083 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2190 + difference 3 2) (sourceB2190 + difference 2 3) sourceC2190) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5112) := by
    have ha : (tripleCharges (sourceA2190 + difference 3 2) (sourceB2190 + difference 2 3) sourceC2190) = raw30084 := by
      apply Matrix.ext; unfold tripleCharges sourceA2190 sourceB2190 sourceC2190 difference raw30084; decide +kernel
    rw [ha]
    exact (canonical30084 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2190 + difference 3 4) (sourceB2190 + difference 4 3) sourceC2190) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5164) := by
    have ha : (tripleCharges (sourceA2190 + difference 3 4) (sourceB2190 + difference 4 3) sourceC2190) = raw10358 := by
      apply Matrix.ext; unfold tripleCharges sourceA2190 sourceB2190 sourceC2190 difference raw10358; decide +kernel
    rw [ha]
    exact (canonical10358 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2190 + difference 3 5) (sourceB2190 + difference 5 3) sourceC2190) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5163) := by
    have ha : (tripleCharges (sourceA2190 + difference 3 5) (sourceB2190 + difference 5 3) sourceC2190) = raw30085 := by
      apply Matrix.ext; unfold tripleCharges sourceA2190 sourceB2190 sourceC2190 difference raw30085; decide +kernel
    rw [ha]
    exact (canonical30085 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2190 + difference 4 0) (sourceB2190 + difference 0 4) sourceC2190) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4535) := by
    have ha : (tripleCharges (sourceA2190 + difference 4 0) (sourceB2190 + difference 0 4) sourceC2190) = raw22669 := by
      apply Matrix.ext; unfold tripleCharges sourceA2190 sourceB2190 sourceC2190 difference raw22669; decide +kernel
    rw [ha]
    exact (canonical22669 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2190 + difference 4 1) (sourceB2190 + difference 1 4) sourceC2190) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4934) := by
    have ha : (tripleCharges (sourceA2190 + difference 4 1) (sourceB2190 + difference 1 4) sourceC2190) = raw30086 := by
      apply Matrix.ext; unfold tripleCharges sourceA2190 sourceB2190 sourceC2190 difference raw30086; decide +kernel
    rw [ha]
    exact (canonical30086 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2190 + difference 4 2) (sourceB2190 + difference 2 4) sourceC2190) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4929) := by
    have ha : (tripleCharges (sourceA2190 + difference 4 2) (sourceB2190 + difference 2 4) sourceC2190) = raw30087 := by
      apply Matrix.ext; unfold tripleCharges sourceA2190 sourceB2190 sourceC2190 difference raw30087; decide +kernel
    rw [ha]
    exact (canonical30087 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2190 + difference 4 3) (sourceB2190 + difference 3 4) sourceC2190) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4943) := by
    have ha : (tripleCharges (sourceA2190 + difference 4 3) (sourceB2190 + difference 3 4) sourceC2190) = raw30088 := by
      apply Matrix.ext; unfold tripleCharges sourceA2190 sourceB2190 sourceC2190 difference raw30088; decide +kernel
    rw [ha]
    exact (canonical30088 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2190 + difference 4 5) (sourceB2190 + difference 5 4) sourceC2190) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA2190 + difference 4 5) (sourceB2190 + difference 5 4) sourceC2190) = raw30089 := by
      apply Matrix.ext; unfold tripleCharges sourceA2190 sourceB2190 sourceC2190 difference raw30089; decide +kernel
    rw [ha]
    exact (canonical30089 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2190 + difference 5 0) (sourceB2190 + difference 0 5) sourceC2190) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4534) := by
    have ha : (tripleCharges (sourceA2190 + difference 5 0) (sourceB2190 + difference 0 5) sourceC2190) = raw22674 := by
      apply Matrix.ext; unfold tripleCharges sourceA2190 sourceB2190 sourceC2190 difference raw22674; decide +kernel
    rw [ha]
    exact (canonical22674 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2190 + difference 5 1) (sourceB2190 + difference 1 5) sourceC2190) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4959) := by
    have ha : (tripleCharges (sourceA2190 + difference 5 1) (sourceB2190 + difference 1 5) sourceC2190) = raw30090 := by
      apply Matrix.ext; unfold tripleCharges sourceA2190 sourceB2190 sourceC2190 difference raw30090; decide +kernel
    rw [ha]
    exact (canonical30090 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2190 + difference 5 2) (sourceB2190 + difference 2 5) sourceC2190) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4956) := by
    have ha : (tripleCharges (sourceA2190 + difference 5 2) (sourceB2190 + difference 2 5) sourceC2190) = raw30091 := by
      apply Matrix.ext; unfold tripleCharges sourceA2190 sourceB2190 sourceC2190 difference raw30091; decide +kernel
    rw [ha]
    exact (canonical30091 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2190 + difference 5 3) (sourceB2190 + difference 3 5) sourceC2190) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4972) := by
    have ha : (tripleCharges (sourceA2190 + difference 5 3) (sourceB2190 + difference 3 5) sourceC2190) = raw30092 := by
      apply Matrix.ext; unfold tripleCharges sourceA2190 sourceB2190 sourceC2190 difference raw30092; decide +kernel
    rw [ha]
    exact (canonical30092 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2190 + difference 5 4) (sourceB2190 + difference 4 5) sourceC2190) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5139) := by
    have ha : (tripleCharges (sourceA2190 + difference 5 4) (sourceB2190 + difference 4 5) sourceC2190) = raw10368 := by
      apply Matrix.ext; unfold tripleCharges sourceA2190 sourceB2190 sourceC2190 difference raw10368; decide +kernel
    rw [ha]
    exact (canonical10368 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2190 sourceB2190 sourceC2190
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2190, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2191 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2191 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC2191 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceForm2191 : Integer.Sparse Master := [(Sum.inr 1117, 1), (Sum.inr 1119, 1), (Sum.inr 1120, 1), (Sum.inr 1141, 1), (Sum.inr 1274, 1), (Sum.inr 2349, 1), (Sum.inr 2352, 1), (Sum.inr 2358, 1), (Sum.inr 2618, 1), (Sum.inr 2801, 1), (Sum.inr 2802, 1), (Sum.inr 2819, 1), (Sum.inr 2823, 1), (Sum.inr 2828, 1), (Sum.inr 2898, 1), (Sum.inr 2903, 1), (Sum.inr 2934, 1), (Sum.inr 2937, 1), (Sum.inr 2939, 1), (Sum.inr 2943, 1), (Sum.inr 2955, 1), (Sum.inr 2961, 1), (Sum.inr 3006, 1), (Sum.inr 3110, 1), (Sum.inr 3112, 1), (Sum.inr 3728, 1), (Sum.inr 3937, 1), (Sum.inr 3941, 1), (Sum.inr 4003, 1), (Sum.inr 4035, 1)]

theorem sourceEq2191 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2191 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2191 + difference 0 1) (sourceB2191 + difference 1 0) sourceC2191) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3728) := by
    have ha : (tripleCharges (sourceA2191 + difference 0 1) (sourceB2191 + difference 1 0) sourceC2191) = raw30093 := by
      apply Matrix.ext; unfold tripleCharges sourceA2191 sourceB2191 sourceC2191 difference raw30093; decide +kernel
    rw [ha]
    exact (canonical30093 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2191 + difference 0 2) (sourceB2191 + difference 2 0) sourceC2191) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3937) := by
    have ha : (tripleCharges (sourceA2191 + difference 0 2) (sourceB2191 + difference 2 0) sourceC2191) = raw30094 := by
      apply Matrix.ext; unfold tripleCharges sourceA2191 sourceB2191 sourceC2191 difference raw30094; decide +kernel
    rw [ha]
    exact (canonical30094 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2191 + difference 0 3) (sourceB2191 + difference 3 0) sourceC2191) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3941) := by
    have ha : (tripleCharges (sourceA2191 + difference 0 3) (sourceB2191 + difference 3 0) sourceC2191) = raw30095 := by
      apply Matrix.ext; unfold tripleCharges sourceA2191 sourceB2191 sourceC2191 difference raw30095; decide +kernel
    rw [ha]
    exact (canonical30095 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2191 + difference 0 4) (sourceB2191 + difference 4 0) sourceC2191) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4003) := by
    have ha : (tripleCharges (sourceA2191 + difference 0 4) (sourceB2191 + difference 4 0) sourceC2191) = raw10372 := by
      apply Matrix.ext; unfold tripleCharges sourceA2191 sourceB2191 sourceC2191 difference raw10372; decide +kernel
    rw [ha]
    exact (canonical10372 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2191 + difference 0 5) (sourceB2191 + difference 5 0) sourceC2191) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4035) := by
    have ha : (tripleCharges (sourceA2191 + difference 0 5) (sourceB2191 + difference 5 0) sourceC2191) = raw30096 := by
      apply Matrix.ext; unfold tripleCharges sourceA2191 sourceB2191 sourceC2191 difference raw30096; decide +kernel
    rw [ha]
    exact (canonical30096 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2191 + difference 1 0) (sourceB2191 + difference 0 1) sourceC2191) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1274) := by
    have ha : (tripleCharges (sourceA2191 + difference 1 0) (sourceB2191 + difference 0 1) sourceC2191) = raw10392 := by
      apply Matrix.ext; unfold tripleCharges sourceA2191 sourceB2191 sourceC2191 difference raw10392; decide +kernel
    rw [ha]
    exact (canonical10392 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2191 + difference 1 2) (sourceB2191 + difference 2 1) sourceC2191) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2943) := by
    have ha : (tripleCharges (sourceA2191 + difference 1 2) (sourceB2191 + difference 2 1) sourceC2191) = raw10394 := by
      apply Matrix.ext; unfold tripleCharges sourceA2191 sourceB2191 sourceC2191 difference raw10394; decide +kernel
    rw [ha]
    exact (canonical10394 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2191 + difference 1 3) (sourceB2191 + difference 3 1) sourceC2191) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3006) := by
    have ha : (tripleCharges (sourceA2191 + difference 1 3) (sourceB2191 + difference 3 1) sourceC2191) = raw10395 := by
      apply Matrix.ext; unfold tripleCharges sourceA2191 sourceB2191 sourceC2191 difference raw10395; decide +kernel
    rw [ha]
    exact (canonical10395 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2191 + difference 1 4) (sourceB2191 + difference 4 1) sourceC2191) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3110) := by
    have ha : (tripleCharges (sourceA2191 + difference 1 4) (sourceB2191 + difference 4 1) sourceC2191) = raw22677 := by
      apply Matrix.ext; unfold tripleCharges sourceA2191 sourceB2191 sourceC2191 difference raw22677; decide +kernel
    rw [ha]
    exact (canonical22677 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2191 + difference 1 5) (sourceB2191 + difference 5 1) sourceC2191) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3112) := by
    have ha : (tripleCharges (sourceA2191 + difference 1 5) (sourceB2191 + difference 5 1) sourceC2191) = raw10396 := by
      apply Matrix.ext; unfold tripleCharges sourceA2191 sourceB2191 sourceC2191 difference raw10396; decide +kernel
    rw [ha]
    exact (canonical10396 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2191 + difference 2 0) (sourceB2191 + difference 0 2) sourceC2191) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1117) := by
    have ha : (tripleCharges (sourceA2191 + difference 2 0) (sourceB2191 + difference 0 2) sourceC2191) = raw22683 := by
      apply Matrix.ext; unfold tripleCharges sourceA2191 sourceB2191 sourceC2191 difference raw22683; decide +kernel
    rw [ha]
    exact (canonical22683 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2191 + difference 2 1) (sourceB2191 + difference 1 2) sourceC2191) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2801) := by
    have ha : (tripleCharges (sourceA2191 + difference 2 1) (sourceB2191 + difference 1 2) sourceC2191) = raw30097 := by
      apply Matrix.ext; unfold tripleCharges sourceA2191 sourceB2191 sourceC2191 difference raw30097; decide +kernel
    rw [ha]
    exact (canonical30097 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2191 + difference 2 3) (sourceB2191 + difference 3 2) sourceC2191) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2903) := by
    have ha : (tripleCharges (sourceA2191 + difference 2 3) (sourceB2191 + difference 3 2) sourceC2191) = raw30098 := by
      apply Matrix.ext; unfold tripleCharges sourceA2191 sourceB2191 sourceC2191 difference raw30098; decide +kernel
    rw [ha]
    exact (canonical30098 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2191 + difference 2 4) (sourceB2191 + difference 4 2) sourceC2191) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2934) := by
    have ha : (tripleCharges (sourceA2191 + difference 2 4) (sourceB2191 + difference 4 2) sourceC2191) = raw10383 := by
      apply Matrix.ext; unfold tripleCharges sourceA2191 sourceB2191 sourceC2191 difference raw10383; decide +kernel
    rw [ha]
    exact (canonical10383 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2191 + difference 2 5) (sourceB2191 + difference 5 2) sourceC2191) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2937) := by
    have ha : (tripleCharges (sourceA2191 + difference 2 5) (sourceB2191 + difference 5 2) sourceC2191) = raw30099 := by
      apply Matrix.ext; unfold tripleCharges sourceA2191 sourceB2191 sourceC2191 difference raw30099; decide +kernel
    rw [ha]
    exact (canonical30099 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2191 + difference 3 0) (sourceB2191 + difference 0 3) sourceC2191) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1141) := by
    have ha : (tripleCharges (sourceA2191 + difference 3 0) (sourceB2191 + difference 0 3) sourceC2191) = raw22687 := by
      apply Matrix.ext; unfold tripleCharges sourceA2191 sourceB2191 sourceC2191 difference raw22687; decide +kernel
    rw [ha]
    exact (canonical22687 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2191 + difference 3 1) (sourceB2191 + difference 1 3) sourceC2191) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2819) := by
    have ha : (tripleCharges (sourceA2191 + difference 3 1) (sourceB2191 + difference 1 3) sourceC2191) = raw30100 := by
      apply Matrix.ext; unfold tripleCharges sourceA2191 sourceB2191 sourceC2191 difference raw30100; decide +kernel
    rw [ha]
    exact (canonical30100 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2191 + difference 3 2) (sourceB2191 + difference 2 3) sourceC2191) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2898) := by
    have ha : (tripleCharges (sourceA2191 + difference 3 2) (sourceB2191 + difference 2 3) sourceC2191) = raw30101 := by
      apply Matrix.ext; unfold tripleCharges sourceA2191 sourceB2191 sourceC2191 difference raw30101; decide +kernel
    rw [ha]
    exact (canonical30101 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2191 + difference 3 4) (sourceB2191 + difference 4 3) sourceC2191) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2955) := by
    have ha : (tripleCharges (sourceA2191 + difference 3 4) (sourceB2191 + difference 4 3) sourceC2191) = raw10388 := by
      apply Matrix.ext; unfold tripleCharges sourceA2191 sourceB2191 sourceC2191 difference raw10388; decide +kernel
    rw [ha]
    exact (canonical10388 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2191 + difference 3 5) (sourceB2191 + difference 5 3) sourceC2191) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2961) := by
    have ha : (tripleCharges (sourceA2191 + difference 3 5) (sourceB2191 + difference 5 3) sourceC2191) = raw30102 := by
      apply Matrix.ext; unfold tripleCharges sourceA2191 sourceB2191 sourceC2191 difference raw30102; decide +kernel
    rw [ha]
    exact (canonical30102 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2191 + difference 4 0) (sourceB2191 + difference 0 4) sourceC2191) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1120) := by
    have ha : (tripleCharges (sourceA2191 + difference 4 0) (sourceB2191 + difference 0 4) sourceC2191) = raw22691 := by
      apply Matrix.ext; unfold tripleCharges sourceA2191 sourceB2191 sourceC2191 difference raw22691; decide +kernel
    rw [ha]
    exact (canonical22691 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2191 + difference 4 1) (sourceB2191 + difference 1 4) sourceC2191) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2802) := by
    have ha : (tripleCharges (sourceA2191 + difference 4 1) (sourceB2191 + difference 1 4) sourceC2191) = raw30103 := by
      apply Matrix.ext; unfold tripleCharges sourceA2191 sourceB2191 sourceC2191 difference raw30103; decide +kernel
    rw [ha]
    exact (canonical30103 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2191 + difference 4 2) (sourceB2191 + difference 2 4) sourceC2191) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2823) := by
    have ha : (tripleCharges (sourceA2191 + difference 4 2) (sourceB2191 + difference 2 4) sourceC2191) = raw30104 := by
      apply Matrix.ext; unfold tripleCharges sourceA2191 sourceB2191 sourceC2191 difference raw30104; decide +kernel
    rw [ha]
    exact (canonical30104 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2191 + difference 4 3) (sourceB2191 + difference 3 4) sourceC2191) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2828) := by
    have ha : (tripleCharges (sourceA2191 + difference 4 3) (sourceB2191 + difference 3 4) sourceC2191) = raw30105 := by
      apply Matrix.ext; unfold tripleCharges sourceA2191 sourceB2191 sourceC2191 difference raw30105; decide +kernel
    rw [ha]
    exact (canonical30105 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2191 + difference 4 5) (sourceB2191 + difference 5 4) sourceC2191) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2939) := by
    have ha : (tripleCharges (sourceA2191 + difference 4 5) (sourceB2191 + difference 5 4) sourceC2191) = raw30106 := by
      apply Matrix.ext; unfold tripleCharges sourceA2191 sourceB2191 sourceC2191 difference raw30106; decide +kernel
    rw [ha]
    exact (canonical30106 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2191 + difference 5 0) (sourceB2191 + difference 0 5) sourceC2191) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1119) := by
    have ha : (tripleCharges (sourceA2191 + difference 5 0) (sourceB2191 + difference 0 5) sourceC2191) = raw22696 := by
      apply Matrix.ext; unfold tripleCharges sourceA2191 sourceB2191 sourceC2191 difference raw22696; decide +kernel
    rw [ha]
    exact (canonical22696 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2191 + difference 5 1) (sourceB2191 + difference 1 5) sourceC2191) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2352) := by
    have ha : (tripleCharges (sourceA2191 + difference 5 1) (sourceB2191 + difference 1 5) sourceC2191) = raw30107 := by
      apply Matrix.ext; unfold tripleCharges sourceA2191 sourceB2191 sourceC2191 difference raw30107; decide +kernel
    rw [ha]
    exact (canonical30107 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2191 + difference 5 2) (sourceB2191 + difference 2 5) sourceC2191) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2349) := by
    have ha : (tripleCharges (sourceA2191 + difference 5 2) (sourceB2191 + difference 2 5) sourceC2191) = raw30108 := by
      apply Matrix.ext; unfold tripleCharges sourceA2191 sourceB2191 sourceC2191 difference raw30108; decide +kernel
    rw [ha]
    exact (canonical30108 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2191 + difference 5 3) (sourceB2191 + difference 3 5) sourceC2191) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2358) := by
    have ha : (tripleCharges (sourceA2191 + difference 5 3) (sourceB2191 + difference 3 5) sourceC2191) = raw30109 := by
      apply Matrix.ext; unfold tripleCharges sourceA2191 sourceB2191 sourceC2191 difference raw30109; decide +kernel
    rw [ha]
    exact (canonical30109 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2191 + difference 5 4) (sourceB2191 + difference 4 5) sourceC2191) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2618) := by
    have ha : (tripleCharges (sourceA2191 + difference 5 4) (sourceB2191 + difference 4 5) sourceC2191) = raw10398 := by
      apply Matrix.ext; unfold tripleCharges sourceA2191 sourceB2191 sourceC2191 difference raw10398; decide +kernel
    rw [ha]
    exact (canonical10398 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2191 sourceB2191 sourceC2191
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2191, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2192 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2192 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC2192 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceForm2192 : Integer.Sparse Master := [(Sum.inr 3267, 1), (Sum.inr 3268, 1), (Sum.inr 3271, 1), (Sum.inr 3272, 1), (Sum.inr 3301, 1), (Sum.inr 3403, 1), (Sum.inr 3411, 1), (Sum.inr 3415, 1), (Sum.inr 3450, 1), (Sum.inr 3457, 1), (Sum.inr 3468, 1), (Sum.inr 3485, 1), (Sum.inr 3508, 1), (Sum.inr 3510, 1), (Sum.inr 3512, 1), (Sum.inr 3514, 1), (Sum.inr 3515, 1), (Sum.inr 3522, 1), (Sum.inr 3523, 1), (Sum.inr 3547, 1), (Sum.inr 3548, 1), (Sum.inr 3555, 1), (Sum.inr 3556, 1), (Sum.inr 3564, 1), (Sum.inr 3565, 1), (Sum.inr 3757, 1), (Sum.inr 3766, 1), (Sum.inr 3770, 1), (Sum.inr 3807, 1), (Sum.inr 3845, 1)]

theorem sourceEq2192 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2192 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2192 + difference 0 1) (sourceB2192 + difference 1 0) sourceC2192) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3770) := by
    have ha : (tripleCharges (sourceA2192 + difference 0 1) (sourceB2192 + difference 1 0) sourceC2192) = raw30110 := by
      apply Matrix.ext; unfold tripleCharges sourceA2192 sourceB2192 sourceC2192 difference raw30110; decide +kernel
    rw [ha]
    exact (canonical30110 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2192 + difference 0 2) (sourceB2192 + difference 2 0) sourceC2192) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3757) := by
    have ha : (tripleCharges (sourceA2192 + difference 0 2) (sourceB2192 + difference 2 0) sourceC2192) = raw30111 := by
      apply Matrix.ext; unfold tripleCharges sourceA2192 sourceB2192 sourceC2192 difference raw30111; decide +kernel
    rw [ha]
    exact (canonical30111 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2192 + difference 0 3) (sourceB2192 + difference 3 0) sourceC2192) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3766) := by
    have ha : (tripleCharges (sourceA2192 + difference 0 3) (sourceB2192 + difference 3 0) sourceC2192) = raw30112 := by
      apply Matrix.ext; unfold tripleCharges sourceA2192 sourceB2192 sourceC2192 difference raw30112; decide +kernel
    rw [ha]
    exact (canonical30112 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2192 + difference 0 4) (sourceB2192 + difference 4 0) sourceC2192) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3845) := by
    have ha : (tripleCharges (sourceA2192 + difference 0 4) (sourceB2192 + difference 4 0) sourceC2192) = raw10402 := by
      apply Matrix.ext; unfold tripleCharges sourceA2192 sourceB2192 sourceC2192 difference raw10402; decide +kernel
    rw [ha]
    exact (canonical10402 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2192 + difference 0 5) (sourceB2192 + difference 5 0) sourceC2192) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3807) := by
    have ha : (tripleCharges (sourceA2192 + difference 0 5) (sourceB2192 + difference 5 0) sourceC2192) = raw30113 := by
      apply Matrix.ext; unfold tripleCharges sourceA2192 sourceB2192 sourceC2192 difference raw30113; decide +kernel
    rw [ha]
    exact (canonical30113 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2192 + difference 1 0) (sourceB2192 + difference 0 1) sourceC2192) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3301) := by
    have ha : (tripleCharges (sourceA2192 + difference 1 0) (sourceB2192 + difference 0 1) sourceC2192) = raw10422 := by
      apply Matrix.ext; unfold tripleCharges sourceA2192 sourceB2192 sourceC2192 difference raw10422; decide +kernel
    rw [ha]
    exact (canonical10422 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2192 + difference 1 2) (sourceB2192 + difference 2 1) sourceC2192) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3522) := by
    have ha : (tripleCharges (sourceA2192 + difference 1 2) (sourceB2192 + difference 2 1) sourceC2192) = raw10424 := by
      apply Matrix.ext; unfold tripleCharges sourceA2192 sourceB2192 sourceC2192 difference raw10424; decide +kernel
    rw [ha]
    exact (canonical10424 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2192 + difference 1 3) (sourceB2192 + difference 3 1) sourceC2192) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3485) := by
    have ha : (tripleCharges (sourceA2192 + difference 1 3) (sourceB2192 + difference 3 1) sourceC2192) = raw10425 := by
      apply Matrix.ext; unfold tripleCharges sourceA2192 sourceB2192 sourceC2192 difference raw10425; decide +kernel
    rw [ha]
    exact (canonical10425 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2192 + difference 1 4) (sourceB2192 + difference 4 1) sourceC2192) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3548) := by
    have ha : (tripleCharges (sourceA2192 + difference 1 4) (sourceB2192 + difference 4 1) sourceC2192) = raw22699 := by
      apply Matrix.ext; unfold tripleCharges sourceA2192 sourceB2192 sourceC2192 difference raw22699; decide +kernel
    rw [ha]
    exact (canonical22699 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2192 + difference 1 5) (sourceB2192 + difference 5 1) sourceC2192) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3547) := by
    have ha : (tripleCharges (sourceA2192 + difference 1 5) (sourceB2192 + difference 5 1) sourceC2192) = raw10426 := by
      apply Matrix.ext; unfold tripleCharges sourceA2192 sourceB2192 sourceC2192 difference raw10426; decide +kernel
    rw [ha]
    exact (canonical10426 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2192 + difference 2 0) (sourceB2192 + difference 0 2) sourceC2192) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3267) := by
    have ha : (tripleCharges (sourceA2192 + difference 2 0) (sourceB2192 + difference 0 2) sourceC2192) = raw22705 := by
      apply Matrix.ext; unfold tripleCharges sourceA2192 sourceB2192 sourceC2192 difference raw22705; decide +kernel
    rw [ha]
    exact (canonical22705 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2192 + difference 2 1) (sourceB2192 + difference 1 2) sourceC2192) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3508) := by
    have ha : (tripleCharges (sourceA2192 + difference 2 1) (sourceB2192 + difference 1 2) sourceC2192) = raw30114 := by
      apply Matrix.ext; unfold tripleCharges sourceA2192 sourceB2192 sourceC2192 difference raw30114; decide +kernel
    rw [ha]
    exact (canonical30114 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2192 + difference 2 3) (sourceB2192 + difference 3 2) sourceC2192) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3450) := by
    have ha : (tripleCharges (sourceA2192 + difference 2 3) (sourceB2192 + difference 3 2) sourceC2192) = raw30115 := by
      apply Matrix.ext; unfold tripleCharges sourceA2192 sourceB2192 sourceC2192 difference raw30115; decide +kernel
    rw [ha]
    exact (canonical30115 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2192 + difference 2 4) (sourceB2192 + difference 4 2) sourceC2192) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3515) := by
    have ha : (tripleCharges (sourceA2192 + difference 2 4) (sourceB2192 + difference 4 2) sourceC2192) = raw10413 := by
      apply Matrix.ext; unfold tripleCharges sourceA2192 sourceB2192 sourceC2192 difference raw10413; decide +kernel
    rw [ha]
    exact (canonical10413 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2192 + difference 2 5) (sourceB2192 + difference 5 2) sourceC2192) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3514) := by
    have ha : (tripleCharges (sourceA2192 + difference 2 5) (sourceB2192 + difference 5 2) sourceC2192) = raw30116 := by
      apply Matrix.ext; unfold tripleCharges sourceA2192 sourceB2192 sourceC2192 difference raw30116; decide +kernel
    rw [ha]
    exact (canonical30116 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2192 + difference 3 0) (sourceB2192 + difference 0 3) sourceC2192) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3271) := by
    have ha : (tripleCharges (sourceA2192 + difference 3 0) (sourceB2192 + difference 0 3) sourceC2192) = raw22709 := by
      apply Matrix.ext; unfold tripleCharges sourceA2192 sourceB2192 sourceC2192 difference raw22709; decide +kernel
    rw [ha]
    exact (canonical22709 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2192 + difference 3 1) (sourceB2192 + difference 1 3) sourceC2192) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3555) := by
    have ha : (tripleCharges (sourceA2192 + difference 3 1) (sourceB2192 + difference 1 3) sourceC2192) = raw30117 := by
      apply Matrix.ext; unfold tripleCharges sourceA2192 sourceB2192 sourceC2192 difference raw30117; decide +kernel
    rw [ha]
    exact (canonical30117 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2192 + difference 3 2) (sourceB2192 + difference 2 3) sourceC2192) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3556) := by
    have ha : (tripleCharges (sourceA2192 + difference 3 2) (sourceB2192 + difference 2 3) sourceC2192) = raw30118 := by
      apply Matrix.ext; unfold tripleCharges sourceA2192 sourceB2192 sourceC2192 difference raw30118; decide +kernel
    rw [ha]
    exact (canonical30118 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2192 + difference 3 4) (sourceB2192 + difference 4 3) sourceC2192) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3565) := by
    have ha : (tripleCharges (sourceA2192 + difference 3 4) (sourceB2192 + difference 4 3) sourceC2192) = raw10418 := by
      apply Matrix.ext; unfold tripleCharges sourceA2192 sourceB2192 sourceC2192 difference raw10418; decide +kernel
    rw [ha]
    exact (canonical10418 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2192 + difference 3 5) (sourceB2192 + difference 5 3) sourceC2192) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3564) := by
    have ha : (tripleCharges (sourceA2192 + difference 3 5) (sourceB2192 + difference 5 3) sourceC2192) = raw30119 := by
      apply Matrix.ext; unfold tripleCharges sourceA2192 sourceB2192 sourceC2192 difference raw30119; decide +kernel
    rw [ha]
    exact (canonical30119 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2192 + difference 4 0) (sourceB2192 + difference 0 4) sourceC2192) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3272) := by
    have ha : (tripleCharges (sourceA2192 + difference 4 0) (sourceB2192 + difference 0 4) sourceC2192) = raw22713 := by
      apply Matrix.ext; unfold tripleCharges sourceA2192 sourceB2192 sourceC2192 difference raw22713; decide +kernel
    rw [ha]
    exact (canonical22713 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2192 + difference 4 1) (sourceB2192 + difference 1 4) sourceC2192) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3415) := by
    have ha : (tripleCharges (sourceA2192 + difference 4 1) (sourceB2192 + difference 1 4) sourceC2192) = raw30120 := by
      apply Matrix.ext; unfold tripleCharges sourceA2192 sourceB2192 sourceC2192 difference raw30120; decide +kernel
    rw [ha]
    exact (canonical30120 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2192 + difference 4 2) (sourceB2192 + difference 2 4) sourceC2192) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3403) := by
    have ha : (tripleCharges (sourceA2192 + difference 4 2) (sourceB2192 + difference 2 4) sourceC2192) = raw30121 := by
      apply Matrix.ext; unfold tripleCharges sourceA2192 sourceB2192 sourceC2192 difference raw30121; decide +kernel
    rw [ha]
    exact (canonical30121 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2192 + difference 4 3) (sourceB2192 + difference 3 4) sourceC2192) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3411) := by
    have ha : (tripleCharges (sourceA2192 + difference 4 3) (sourceB2192 + difference 3 4) sourceC2192) = raw30122 := by
      apply Matrix.ext; unfold tripleCharges sourceA2192 sourceB2192 sourceC2192 difference raw30122; decide +kernel
    rw [ha]
    exact (canonical30122 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2192 + difference 4 5) (sourceB2192 + difference 5 4) sourceC2192) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3468) := by
    have ha : (tripleCharges (sourceA2192 + difference 4 5) (sourceB2192 + difference 5 4) sourceC2192) = raw30123 := by
      apply Matrix.ext; unfold tripleCharges sourceA2192 sourceB2192 sourceC2192 difference raw30123; decide +kernel
    rw [ha]
    exact (canonical30123 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2192 + difference 5 0) (sourceB2192 + difference 0 5) sourceC2192) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3268) := by
    have ha : (tripleCharges (sourceA2192 + difference 5 0) (sourceB2192 + difference 0 5) sourceC2192) = raw22718 := by
      apply Matrix.ext; unfold tripleCharges sourceA2192 sourceB2192 sourceC2192 difference raw22718; decide +kernel
    rw [ha]
    exact (canonical22718 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2192 + difference 5 1) (sourceB2192 + difference 1 5) sourceC2192) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3512) := by
    have ha : (tripleCharges (sourceA2192 + difference 5 1) (sourceB2192 + difference 1 5) sourceC2192) = raw30124 := by
      apply Matrix.ext; unfold tripleCharges sourceA2192 sourceB2192 sourceC2192 difference raw30124; decide +kernel
    rw [ha]
    exact (canonical30124 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2192 + difference 5 2) (sourceB2192 + difference 2 5) sourceC2192) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3510) := by
    have ha : (tripleCharges (sourceA2192 + difference 5 2) (sourceB2192 + difference 2 5) sourceC2192) = raw30125 := by
      apply Matrix.ext; unfold tripleCharges sourceA2192 sourceB2192 sourceC2192 difference raw30125; decide +kernel
    rw [ha]
    exact (canonical30125 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2192 + difference 5 3) (sourceB2192 + difference 3 5) sourceC2192) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3457) := by
    have ha : (tripleCharges (sourceA2192 + difference 5 3) (sourceB2192 + difference 3 5) sourceC2192) = raw30126 := by
      apply Matrix.ext; unfold tripleCharges sourceA2192 sourceB2192 sourceC2192 difference raw30126; decide +kernel
    rw [ha]
    exact (canonical30126 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2192 + difference 5 4) (sourceB2192 + difference 4 5) sourceC2192) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3523) := by
    have ha : (tripleCharges (sourceA2192 + difference 5 4) (sourceB2192 + difference 4 5) sourceC2192) = raw10428 := by
      apply Matrix.ext; unfold tripleCharges sourceA2192 sourceB2192 sourceC2192 difference raw10428; decide +kernel
    rw [ha]
    exact (canonical10428 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2192 sourceB2192 sourceC2192
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2192, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2193 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2193 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC2193 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceForm2193 : Integer.Sparse Master := [(Sum.inr 2325, 1), (Sum.inr 2348, 1), (Sum.inr 2352, 1), (Sum.inr 2356, 1), (Sum.inr 2561, 1), (Sum.inr 3693, 1), (Sum.inr 4092, -1)]

theorem sourceEq2193 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2193 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2193 + difference 0 1) (sourceB2193 + difference 1 0) sourceC2193) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3693) := by
    have ha : (tripleCharges (sourceA2193 + difference 0 1) (sourceB2193 + difference 1 0) sourceC2193) = raw30127 := by
      apply Matrix.ext; unfold tripleCharges sourceA2193 sourceB2193 sourceC2193 difference raw30127; decide +kernel
    rw [ha]
    exact (canonical30127 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2193 + difference 1 1) (sourceB2193 + difference 1 1) sourceC2193) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2561) := by
    have ha : (tripleCharges (sourceA2193 + difference 1 1) (sourceB2193 + difference 1 1) sourceC2193) = raw10441 := by
      apply Matrix.ext; unfold tripleCharges sourceA2193 sourceB2193 sourceC2193 difference raw10441; decide +kernel
    rw [ha]
    exact (canonical10441 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2193 + difference 2 1) (sourceB2193 + difference 1 2) sourceC2193) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2348) := by
    have ha : (tripleCharges (sourceA2193 + difference 2 1) (sourceB2193 + difference 1 2) sourceC2193) = raw30128 := by
      apply Matrix.ext; unfold tripleCharges sourceA2193 sourceB2193 sourceC2193 difference raw30128; decide +kernel
    rw [ha]
    exact (canonical30128 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2193 + difference 3 1) (sourceB2193 + difference 1 3) sourceC2193) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2356) := by
    have ha : (tripleCharges (sourceA2193 + difference 3 1) (sourceB2193 + difference 1 3) sourceC2193) = raw30129 := by
      apply Matrix.ext; unfold tripleCharges sourceA2193 sourceB2193 sourceC2193 difference raw30129; decide +kernel
    rw [ha]
    exact (canonical30129 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2193 + difference 4 1) (sourceB2193 + difference 1 4) sourceC2193) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2325) := by
    have ha : (tripleCharges (sourceA2193 + difference 4 1) (sourceB2193 + difference 1 4) sourceC2193) = raw30130 := by
      apply Matrix.ext; unfold tripleCharges sourceA2193 sourceB2193 sourceC2193 difference raw30130; decide +kernel
    rw [ha]
    exact (canonical30130 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2193 + difference 5 1) (sourceB2193 + difference 1 5) sourceC2193) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2352) := by
    have ha : (tripleCharges (sourceA2193 + difference 5 1) (sourceB2193 + difference 1 5) sourceC2193) = raw30131 := by
      apply Matrix.ext; unfold tripleCharges sourceA2193 sourceB2193 sourceC2193 difference raw30131; decide +kernel
    rw [ha]
    exact (canonical30131 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2193 + sourceB2193) sourceC2193) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2193 + sourceB2193) sourceC2193) = raw10438 := by
      apply Matrix.ext; unfold doubleCharges sourceA2193 sourceB2193 sourceC2193 raw10438; decide +kernel
    rw [ha]
    exact (canonical10438 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2193 sourceB2193 sourceC2193
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2193, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2194 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2194 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC2194 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceForm2194 : Integer.Sparse Master := [(Sum.inr 1149, 1), (Sum.inr 2348, 1), (Sum.inr 2428, 1), (Sum.inr 2553, 1), (Sum.inr 2554, 1), (Sum.inr 2561, 1), (Sum.inr 4092, -1)]

theorem sourceEq2194 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2194 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2194 + difference 2 0) (sourceB2194 + difference 0 2) sourceC2194) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1149) := by
    have ha : (tripleCharges (sourceA2194 + difference 2 0) (sourceB2194 + difference 0 2) sourceC2194) = raw22730 := by
      apply Matrix.ext; unfold tripleCharges sourceA2194 sourceB2194 sourceC2194 difference raw22730; decide +kernel
    rw [ha]
    exact (canonical22730 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2194 + difference 2 1) (sourceB2194 + difference 1 2) sourceC2194) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2348) := by
    have ha : (tripleCharges (sourceA2194 + difference 2 1) (sourceB2194 + difference 1 2) sourceC2194) = raw30128 := by
      apply Matrix.ext; unfold tripleCharges sourceA2194 sourceB2194 sourceC2194 difference raw30128; decide +kernel
    rw [ha]
    exact (canonical30128 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2194 + difference 2 2) (sourceB2194 + difference 2 2) sourceC2194) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2561) := by
    have ha : (tripleCharges (sourceA2194 + difference 2 2) (sourceB2194 + difference 2 2) sourceC2194) = raw10441 := by
      apply Matrix.ext; unfold tripleCharges sourceA2194 sourceB2194 sourceC2194 difference raw10441; decide +kernel
    rw [ha]
    exact (canonical10441 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2194 + difference 2 3) (sourceB2194 + difference 3 2) sourceC2194) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2428) := by
    have ha : (tripleCharges (sourceA2194 + difference 2 3) (sourceB2194 + difference 3 2) sourceC2194) = raw30132 := by
      apply Matrix.ext; unfold tripleCharges sourceA2194 sourceB2194 sourceC2194 difference raw30132; decide +kernel
    rw [ha]
    exact (canonical30132 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2194 + difference 2 4) (sourceB2194 + difference 4 2) sourceC2194) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2554) := by
    have ha : (tripleCharges (sourceA2194 + difference 2 4) (sourceB2194 + difference 4 2) sourceC2194) = raw10439 := by
      apply Matrix.ext; unfold tripleCharges sourceA2194 sourceB2194 sourceC2194 difference raw10439; decide +kernel
    rw [ha]
    exact (canonical10439 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2194 + difference 2 5) (sourceB2194 + difference 5 2) sourceC2194) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2553) := by
    have ha : (tripleCharges (sourceA2194 + difference 2 5) (sourceB2194 + difference 5 2) sourceC2194) = raw30133 := by
      apply Matrix.ext; unfold tripleCharges sourceA2194 sourceB2194 sourceC2194 difference raw30133; decide +kernel
    rw [ha]
    exact (canonical30133 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2194 + sourceB2194) sourceC2194) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2194 + sourceB2194) sourceC2194) = raw10438 := by
      apply Matrix.ext; unfold doubleCharges sourceA2194 sourceB2194 sourceC2194 raw10438; decide +kernel
    rw [ha]
    exact (canonical10438 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2194 sourceB2194 sourceC2194
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2194, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2195 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2195 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC2195 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceForm2195 : Integer.Sparse Master := [(Sum.inr 2319, 1), (Sum.inr 2524, 1), (Sum.inr 2525, 1), (Sum.inr 2561, 2), (Sum.inr 3689, 1), (Sum.inr 4092, -1)]

theorem sourceEq2195 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2195 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2195 + difference 0 2) (sourceB2195 + difference 2 0) sourceC2195) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3689) := by
    have ha : (tripleCharges (sourceA2195 + difference 0 2) (sourceB2195 + difference 2 0) sourceC2195) = raw30134 := by
      apply Matrix.ext; unfold tripleCharges sourceA2195 sourceB2195 sourceC2195 difference raw30134; decide +kernel
    rw [ha]
    exact (canonical30134 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2195 + difference 1 2) (sourceB2195 + difference 2 1) sourceC2195) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2561) := by
    have ha : (tripleCharges (sourceA2195 + difference 1 2) (sourceB2195 + difference 2 1) sourceC2195) = raw10448 := by
      apply Matrix.ext; unfold tripleCharges sourceA2195 sourceB2195 sourceC2195 difference raw10448; decide +kernel
    rw [ha]
    exact (canonical10448 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2195 + difference 2 2) (sourceB2195 + difference 2 2) sourceC2195) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2561) := by
    have ha : (tripleCharges (sourceA2195 + difference 2 2) (sourceB2195 + difference 2 2) sourceC2195) = raw10441 := by
      apply Matrix.ext; unfold tripleCharges sourceA2195 sourceB2195 sourceC2195 difference raw10441; decide +kernel
    rw [ha]
    exact (canonical10441 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2195 + difference 3 2) (sourceB2195 + difference 2 3) sourceC2195) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2525) := by
    have ha : (tripleCharges (sourceA2195 + difference 3 2) (sourceB2195 + difference 2 3) sourceC2195) = raw30135 := by
      apply Matrix.ext; unfold tripleCharges sourceA2195 sourceB2195 sourceC2195 difference raw30135; decide +kernel
    rw [ha]
    exact (canonical30135 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2195 + difference 4 2) (sourceB2195 + difference 2 4) sourceC2195) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2319) := by
    have ha : (tripleCharges (sourceA2195 + difference 4 2) (sourceB2195 + difference 2 4) sourceC2195) = raw30136 := by
      apply Matrix.ext; unfold tripleCharges sourceA2195 sourceB2195 sourceC2195 difference raw30136; decide +kernel
    rw [ha]
    exact (canonical30136 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2195 + difference 5 2) (sourceB2195 + difference 2 5) sourceC2195) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2524) := by
    have ha : (tripleCharges (sourceA2195 + difference 5 2) (sourceB2195 + difference 2 5) sourceC2195) = raw30137 := by
      apply Matrix.ext; unfold tripleCharges sourceA2195 sourceB2195 sourceC2195 difference raw30137; decide +kernel
    rw [ha]
    exact (canonical30137 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2195 + sourceB2195) sourceC2195) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2195 + sourceB2195) sourceC2195) = raw10438 := by
      apply Matrix.ext; unfold doubleCharges sourceA2195 sourceB2195 sourceC2195 raw10438; decide +kernel
    rw [ha]
    exact (canonical10438 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2195 sourceB2195 sourceC2195
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2195, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2196 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2196 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC2196 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceForm2196 : Integer.Sparse Master := [(Sum.inr 1160, 1), (Sum.inr 2356, 1), (Sum.inr 2525, 1), (Sum.inr 2561, 1), (Sum.inr 2590, 1), (Sum.inr 2591, 1), (Sum.inr 4092, -1)]

theorem sourceEq2196 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2196 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2196 + difference 3 0) (sourceB2196 + difference 0 3) sourceC2196) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1160) := by
    have ha : (tripleCharges (sourceA2196 + difference 3 0) (sourceB2196 + difference 0 3) sourceC2196) = raw22731 := by
      apply Matrix.ext; unfold tripleCharges sourceA2196 sourceB2196 sourceC2196 difference raw22731; decide +kernel
    rw [ha]
    exact (canonical22731 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2196 + difference 3 1) (sourceB2196 + difference 1 3) sourceC2196) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2356) := by
    have ha : (tripleCharges (sourceA2196 + difference 3 1) (sourceB2196 + difference 1 3) sourceC2196) = raw30129 := by
      apply Matrix.ext; unfold tripleCharges sourceA2196 sourceB2196 sourceC2196 difference raw30129; decide +kernel
    rw [ha]
    exact (canonical30129 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2196 + difference 3 2) (sourceB2196 + difference 2 3) sourceC2196) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2525) := by
    have ha : (tripleCharges (sourceA2196 + difference 3 2) (sourceB2196 + difference 2 3) sourceC2196) = raw30135 := by
      apply Matrix.ext; unfold tripleCharges sourceA2196 sourceB2196 sourceC2196 difference raw30135; decide +kernel
    rw [ha]
    exact (canonical30135 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2196 + difference 3 3) (sourceB2196 + difference 3 3) sourceC2196) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2561) := by
    have ha : (tripleCharges (sourceA2196 + difference 3 3) (sourceB2196 + difference 3 3) sourceC2196) = raw10441 := by
      apply Matrix.ext; unfold tripleCharges sourceA2196 sourceB2196 sourceC2196 difference raw10441; decide +kernel
    rw [ha]
    exact (canonical10441 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2196 + difference 3 4) (sourceB2196 + difference 4 3) sourceC2196) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2591) := by
    have ha : (tripleCharges (sourceA2196 + difference 3 4) (sourceB2196 + difference 4 3) sourceC2196) = raw10440 := by
      apply Matrix.ext; unfold tripleCharges sourceA2196 sourceB2196 sourceC2196 difference raw10440; decide +kernel
    rw [ha]
    exact (canonical10440 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2196 + difference 3 5) (sourceB2196 + difference 5 3) sourceC2196) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2590) := by
    have ha : (tripleCharges (sourceA2196 + difference 3 5) (sourceB2196 + difference 5 3) sourceC2196) = raw30138 := by
      apply Matrix.ext; unfold tripleCharges sourceA2196 sourceB2196 sourceC2196 difference raw30138; decide +kernel
    rw [ha]
    exact (canonical30138 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2196 + sourceB2196) sourceC2196) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2196 + sourceB2196) sourceC2196) = raw10438 := by
      apply Matrix.ext; unfold doubleCharges sourceA2196 sourceB2196 sourceC2196 raw10438; decide +kernel
    rw [ha]
    exact (canonical10438 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2196 sourceB2196 sourceC2196
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2196, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2197 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2197 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceC2197 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceForm2197 : Integer.Sparse Master := [(Sum.inr 4323, 1), (Sum.inr 4324, 1), (Sum.inr 4325, 1), (Sum.inr 4349, 1), (Sum.inr 4404, 1), (Sum.inr 4631, 1), (Sum.inr 4637, 1), (Sum.inr 4644, 1), (Sum.inr 4804, 1), (Sum.inr 4902, 1), (Sum.inr 4907, 1), (Sum.inr 4913, 1), (Sum.inr 4928, 1), (Sum.inr 4946, 1), (Sum.inr 4987, 1), (Sum.inr 5003, 1), (Sum.inr 5036, 1), (Sum.inr 5050, 1), (Sum.inr 5075, 1), (Sum.inr 5134, 1), (Sum.inr 5137, 1), (Sum.inr 5168, 1), (Sum.inr 5169, 1), (Sum.inr 5258, 1), (Sum.inr 5259, 1), (Sum.inr 5352, 1), (Sum.inr 5356, 1), (Sum.inr 5368, 1), (Sum.inr 5434, 1), (Sum.inr 5483, 1)]

theorem sourceEq2197 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2197 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2197 + difference 0 1) (sourceB2197 + difference 1 0) sourceC2197) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5356) := by
    have ha : (tripleCharges (sourceA2197 + difference 0 1) (sourceB2197 + difference 1 0) sourceC2197) = raw17096 := by
      apply Matrix.ext; unfold tripleCharges sourceA2197 sourceB2197 sourceC2197 difference raw17096; decide +kernel
    rw [ha]
    exact (canonical17096 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2197 + difference 0 2) (sourceB2197 + difference 2 0) sourceC2197) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5352) := by
    have ha : (tripleCharges (sourceA2197 + difference 0 2) (sourceB2197 + difference 2 0) sourceC2197) = raw17097 := by
      apply Matrix.ext; unfold tripleCharges sourceA2197 sourceB2197 sourceC2197 difference raw17097; decide +kernel
    rw [ha]
    exact (canonical17097 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2197 + difference 0 3) (sourceB2197 + difference 3 0) sourceC2197) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5368) := by
    have ha : (tripleCharges (sourceA2197 + difference 0 3) (sourceB2197 + difference 3 0) sourceC2197) = raw17098 := by
      apply Matrix.ext; unfold tripleCharges sourceA2197 sourceB2197 sourceC2197 difference raw17098; decide +kernel
    rw [ha]
    exact (canonical17098 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2197 + difference 0 4) (sourceB2197 + difference 4 0) sourceC2197) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA2197 + difference 0 4) (sourceB2197 + difference 4 0) sourceC2197) = raw3145 := by
      apply Matrix.ext; unfold tripleCharges sourceA2197 sourceB2197 sourceC2197 difference raw3145; decide +kernel
    rw [ha]
    exact (canonical3145 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2197 + difference 0 5) (sourceB2197 + difference 5 0) sourceC2197) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA2197 + difference 0 5) (sourceB2197 + difference 5 0) sourceC2197) = raw3140 := by
      apply Matrix.ext; unfold tripleCharges sourceA2197 sourceB2197 sourceC2197 difference raw3140; decide +kernel
    rw [ha]
    exact (canonical3140 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2197 + difference 1 0) (sourceB2197 + difference 0 1) sourceC2197) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4404) := by
    have ha : (tripleCharges (sourceA2197 + difference 1 0) (sourceB2197 + difference 0 1) sourceC2197) = raw9860 := by
      apply Matrix.ext; unfold tripleCharges sourceA2197 sourceB2197 sourceC2197 difference raw9860; decide +kernel
    rw [ha]
    exact (canonical9860 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2197 + difference 1 2) (sourceB2197 + difference 2 1) sourceC2197) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5050) := by
    have ha : (tripleCharges (sourceA2197 + difference 1 2) (sourceB2197 + difference 2 1) sourceC2197) = raw9862 := by
      apply Matrix.ext; unfold tripleCharges sourceA2197 sourceB2197 sourceC2197 difference raw9862; decide +kernel
    rw [ha]
    exact (canonical9862 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2197 + difference 1 3) (sourceB2197 + difference 3 1) sourceC2197) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5003) := by
    have ha : (tripleCharges (sourceA2197 + difference 1 3) (sourceB2197 + difference 3 1) sourceC2197) = raw9863 := by
      apply Matrix.ext; unfold tripleCharges sourceA2197 sourceB2197 sourceC2197 difference raw9863; decide +kernel
    rw [ha]
    exact (canonical9863 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2197 + difference 1 4) (sourceB2197 + difference 4 1) sourceC2197) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA2197 + difference 1 4) (sourceB2197 + difference 4 1) sourceC2197) = raw3144 := by
      apply Matrix.ext; unfold tripleCharges sourceA2197 sourceB2197 sourceC2197 difference raw3144; decide +kernel
    rw [ha]
    exact (canonical3144 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2197 + difference 1 5) (sourceB2197 + difference 5 1) sourceC2197) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA2197 + difference 1 5) (sourceB2197 + difference 5 1) sourceC2197) = raw3139 := by
      apply Matrix.ext; unfold tripleCharges sourceA2197 sourceB2197 sourceC2197 difference raw3139; decide +kernel
    rw [ha]
    exact (canonical3139 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2197 + difference 2 0) (sourceB2197 + difference 0 2) sourceC2197) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4323) := by
    have ha : (tripleCharges (sourceA2197 + difference 2 0) (sourceB2197 + difference 0 2) sourceC2197) = raw30139 := by
      apply Matrix.ext; unfold tripleCharges sourceA2197 sourceB2197 sourceC2197 difference raw30139; decide +kernel
    rw [ha]
    exact (canonical30139 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2197 + difference 2 1) (sourceB2197 + difference 1 2) sourceC2197) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4928) := by
    have ha : (tripleCharges (sourceA2197 + difference 2 1) (sourceB2197 + difference 1 2) sourceC2197) = raw30140 := by
      apply Matrix.ext; unfold tripleCharges sourceA2197 sourceB2197 sourceC2197 difference raw30140; decide +kernel
    rw [ha]
    exact (canonical30140 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2197 + difference 2 3) (sourceB2197 + difference 3 2) sourceC2197) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4987) := by
    have ha : (tripleCharges (sourceA2197 + difference 2 3) (sourceB2197 + difference 3 2) sourceC2197) = raw30141 := by
      apply Matrix.ext; unfold tripleCharges sourceA2197 sourceB2197 sourceC2197 difference raw30141; decide +kernel
    rw [ha]
    exact (canonical30141 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2197 + difference 2 4) (sourceB2197 + difference 4 2) sourceC2197) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5137) := by
    have ha : (tripleCharges (sourceA2197 + difference 2 4) (sourceB2197 + difference 4 2) sourceC2197) = raw9853 := by
      apply Matrix.ext; unfold tripleCharges sourceA2197 sourceB2197 sourceC2197 difference raw9853; decide +kernel
    rw [ha]
    exact (canonical9853 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2197 + difference 2 5) (sourceB2197 + difference 5 2) sourceC2197) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5134) := by
    have ha : (tripleCharges (sourceA2197 + difference 2 5) (sourceB2197 + difference 5 2) sourceC2197) = raw30142 := by
      apply Matrix.ext; unfold tripleCharges sourceA2197 sourceB2197 sourceC2197 difference raw30142; decide +kernel
    rw [ha]
    exact (canonical30142 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2197 + difference 3 0) (sourceB2197 + difference 0 3) sourceC2197) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4349) := by
    have ha : (tripleCharges (sourceA2197 + difference 3 0) (sourceB2197 + difference 0 3) sourceC2197) = raw30143 := by
      apply Matrix.ext; unfold tripleCharges sourceA2197 sourceB2197 sourceC2197 difference raw30143; decide +kernel
    rw [ha]
    exact (canonical30143 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2197 + difference 3 1) (sourceB2197 + difference 1 3) sourceC2197) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4946) := by
    have ha : (tripleCharges (sourceA2197 + difference 3 1) (sourceB2197 + difference 1 3) sourceC2197) = raw30144 := by
      apply Matrix.ext; unfold tripleCharges sourceA2197 sourceB2197 sourceC2197 difference raw30144; decide +kernel
    rw [ha]
    exact (canonical30144 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2197 + difference 3 2) (sourceB2197 + difference 2 3) sourceC2197) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5036) := by
    have ha : (tripleCharges (sourceA2197 + difference 3 2) (sourceB2197 + difference 2 3) sourceC2197) = raw30145 := by
      apply Matrix.ext; unfold tripleCharges sourceA2197 sourceB2197 sourceC2197 difference raw30145; decide +kernel
    rw [ha]
    exact (canonical30145 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2197 + difference 3 4) (sourceB2197 + difference 4 3) sourceC2197) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA2197 + difference 3 4) (sourceB2197 + difference 4 3) sourceC2197) = raw9857 := by
      apply Matrix.ext; unfold tripleCharges sourceA2197 sourceB2197 sourceC2197 difference raw9857; decide +kernel
    rw [ha]
    exact (canonical9857 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2197 + difference 3 5) (sourceB2197 + difference 5 3) sourceC2197) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5168) := by
    have ha : (tripleCharges (sourceA2197 + difference 3 5) (sourceB2197 + difference 5 3) sourceC2197) = raw30146 := by
      apply Matrix.ext; unfold tripleCharges sourceA2197 sourceB2197 sourceC2197 difference raw30146; decide +kernel
    rw [ha]
    exact (canonical30146 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2197 + difference 4 0) (sourceB2197 + difference 0 4) sourceC2197) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4324) := by
    have ha : (tripleCharges (sourceA2197 + difference 4 0) (sourceB2197 + difference 0 4) sourceC2197) = raw30147 := by
      apply Matrix.ext; unfold tripleCharges sourceA2197 sourceB2197 sourceC2197 difference raw30147; decide +kernel
    rw [ha]
    exact (canonical30147 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2197 + difference 4 1) (sourceB2197 + difference 1 4) sourceC2197) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4637) := by
    have ha : (tripleCharges (sourceA2197 + difference 4 1) (sourceB2197 + difference 1 4) sourceC2197) = raw30148 := by
      apply Matrix.ext; unfold tripleCharges sourceA2197 sourceB2197 sourceC2197 difference raw30148; decide +kernel
    rw [ha]
    exact (canonical30148 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2197 + difference 4 2) (sourceB2197 + difference 2 4) sourceC2197) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4631) := by
    have ha : (tripleCharges (sourceA2197 + difference 4 2) (sourceB2197 + difference 2 4) sourceC2197) = raw30149 := by
      apply Matrix.ext; unfold tripleCharges sourceA2197 sourceB2197 sourceC2197 difference raw30149; decide +kernel
    rw [ha]
    exact (canonical30149 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2197 + difference 4 3) (sourceB2197 + difference 3 4) sourceC2197) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4644) := by
    have ha : (tripleCharges (sourceA2197 + difference 4 3) (sourceB2197 + difference 3 4) sourceC2197) = raw30150 := by
      apply Matrix.ext; unfold tripleCharges sourceA2197 sourceB2197 sourceC2197 difference raw30150; decide +kernel
    rw [ha]
    exact (canonical30150 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2197 + difference 4 5) (sourceB2197 + difference 5 4) sourceC2197) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA2197 + difference 4 5) (sourceB2197 + difference 5 4) sourceC2197) = raw30151 := by
      apply Matrix.ext; unfold tripleCharges sourceA2197 sourceB2197 sourceC2197 difference raw30151; decide +kernel
    rw [ha]
    exact (canonical30151 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2197 + difference 5 0) (sourceB2197 + difference 0 5) sourceC2197) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4325) := by
    have ha : (tripleCharges (sourceA2197 + difference 5 0) (sourceB2197 + difference 0 5) sourceC2197) = raw28772 := by
      apply Matrix.ext; unfold tripleCharges sourceA2197 sourceB2197 sourceC2197 difference raw28772; decide +kernel
    rw [ha]
    exact (canonical28772 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2197 + difference 5 1) (sourceB2197 + difference 1 5) sourceC2197) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4907) := by
    have ha : (tripleCharges (sourceA2197 + difference 5 1) (sourceB2197 + difference 1 5) sourceC2197) = raw28773 := by
      apply Matrix.ext; unfold tripleCharges sourceA2197 sourceB2197 sourceC2197 difference raw28773; decide +kernel
    rw [ha]
    exact (canonical28773 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2197 + difference 5 2) (sourceB2197 + difference 2 5) sourceC2197) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4902) := by
    have ha : (tripleCharges (sourceA2197 + difference 5 2) (sourceB2197 + difference 2 5) sourceC2197) = raw28774 := by
      apply Matrix.ext; unfold tripleCharges sourceA2197 sourceB2197 sourceC2197 difference raw28774; decide +kernel
    rw [ha]
    exact (canonical28774 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2197 + difference 5 3) (sourceB2197 + difference 3 5) sourceC2197) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4913) := by
    have ha : (tripleCharges (sourceA2197 + difference 5 3) (sourceB2197 + difference 3 5) sourceC2197) = raw28775 := by
      apply Matrix.ext; unfold tripleCharges sourceA2197 sourceB2197 sourceC2197 difference raw28775; decide +kernel
    rw [ha]
    exact (canonical28775 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2197 + difference 5 4) (sourceB2197 + difference 4 5) sourceC2197) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA2197 + difference 5 4) (sourceB2197 + difference 4 5) sourceC2197) = raw9865 := by
      apply Matrix.ext; unfold tripleCharges sourceA2197 sourceB2197 sourceC2197 difference raw9865; decide +kernel
    rw [ha]
    exact (canonical9865 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2197 sourceB2197 sourceC2197
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2197, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2198 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2198 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceC2198 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceForm2198 : Integer.Sparse Master := [(Sum.inr 901, 1), (Sum.inr 902, 1), (Sum.inr 903, 1), (Sum.inr 927, 1), (Sum.inr 985, 1), (Sum.inr 1760, 1), (Sum.inr 1766, 1), (Sum.inr 1773, 1), (Sum.inr 2022, 1), (Sum.inr 2295, 1), (Sum.inr 2300, 1), (Sum.inr 2306, 1), (Sum.inr 2318, 1), (Sum.inr 2337, 1), (Sum.inr 2372, 1), (Sum.inr 2388, 1), (Sum.inr 2428, 1), (Sum.inr 2452, 1), (Sum.inr 2482, 1), (Sum.inr 2553, 1), (Sum.inr 2556, 1), (Sum.inr 2594, 1), (Sum.inr 2595, 1), (Sum.inr 2722, 1), (Sum.inr 2723, 1), (Sum.inr 3690, 1), (Sum.inr 3694, 1), (Sum.inr 3705, 1), (Sum.inr 3852, 1), (Sum.inr 3981, 1)]

theorem sourceEq2198 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2198 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2198 + difference 0 1) (sourceB2198 + difference 1 0) sourceC2198) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3694) := by
    have ha : (tripleCharges (sourceA2198 + difference 0 1) (sourceB2198 + difference 1 0) sourceC2198) = raw17113 := by
      apply Matrix.ext; unfold tripleCharges sourceA2198 sourceB2198 sourceC2198 difference raw17113; decide +kernel
    rw [ha]
    exact (canonical17113 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2198 + difference 0 2) (sourceB2198 + difference 2 0) sourceC2198) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3690) := by
    have ha : (tripleCharges (sourceA2198 + difference 0 2) (sourceB2198 + difference 2 0) sourceC2198) = raw17114 := by
      apply Matrix.ext; unfold tripleCharges sourceA2198 sourceB2198 sourceC2198 difference raw17114; decide +kernel
    rw [ha]
    exact (canonical17114 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2198 + difference 0 3) (sourceB2198 + difference 3 0) sourceC2198) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3705) := by
    have ha : (tripleCharges (sourceA2198 + difference 0 3) (sourceB2198 + difference 3 0) sourceC2198) = raw17115 := by
      apply Matrix.ext; unfold tripleCharges sourceA2198 sourceB2198 sourceC2198 difference raw17115; decide +kernel
    rw [ha]
    exact (canonical17115 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2198 + difference 0 4) (sourceB2198 + difference 4 0) sourceC2198) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3981) := by
    have ha : (tripleCharges (sourceA2198 + difference 0 4) (sourceB2198 + difference 4 0) sourceC2198) = raw3175 := by
      apply Matrix.ext; unfold tripleCharges sourceA2198 sourceB2198 sourceC2198 difference raw3175; decide +kernel
    rw [ha]
    exact (canonical3175 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2198 + difference 0 5) (sourceB2198 + difference 5 0) sourceC2198) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3852) := by
    have ha : (tripleCharges (sourceA2198 + difference 0 5) (sourceB2198 + difference 5 0) sourceC2198) = raw3170 := by
      apply Matrix.ext; unfold tripleCharges sourceA2198 sourceB2198 sourceC2198 difference raw3170; decide +kernel
    rw [ha]
    exact (canonical3170 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2198 + difference 1 0) (sourceB2198 + difference 0 1) sourceC2198) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 985) := by
    have ha : (tripleCharges (sourceA2198 + difference 1 0) (sourceB2198 + difference 0 1) sourceC2198) = raw9882 := by
      apply Matrix.ext; unfold tripleCharges sourceA2198 sourceB2198 sourceC2198 difference raw9882; decide +kernel
    rw [ha]
    exact (canonical9882 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2198 + difference 1 2) (sourceB2198 + difference 2 1) sourceC2198) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2452) := by
    have ha : (tripleCharges (sourceA2198 + difference 1 2) (sourceB2198 + difference 2 1) sourceC2198) = raw9884 := by
      apply Matrix.ext; unfold tripleCharges sourceA2198 sourceB2198 sourceC2198 difference raw9884; decide +kernel
    rw [ha]
    exact (canonical9884 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2198 + difference 1 3) (sourceB2198 + difference 3 1) sourceC2198) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2388) := by
    have ha : (tripleCharges (sourceA2198 + difference 1 3) (sourceB2198 + difference 3 1) sourceC2198) = raw9885 := by
      apply Matrix.ext; unfold tripleCharges sourceA2198 sourceB2198 sourceC2198 difference raw9885; decide +kernel
    rw [ha]
    exact (canonical9885 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2198 + difference 1 4) (sourceB2198 + difference 4 1) sourceC2198) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA2198 + difference 1 4) (sourceB2198 + difference 4 1) sourceC2198) = raw3174 := by
      apply Matrix.ext; unfold tripleCharges sourceA2198 sourceB2198 sourceC2198 difference raw3174; decide +kernel
    rw [ha]
    exact (canonical3174 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2198 + difference 1 5) (sourceB2198 + difference 5 1) sourceC2198) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA2198 + difference 1 5) (sourceB2198 + difference 5 1) sourceC2198) = raw3169 := by
      apply Matrix.ext; unfold tripleCharges sourceA2198 sourceB2198 sourceC2198 difference raw3169; decide +kernel
    rw [ha]
    exact (canonical3169 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2198 + difference 2 0) (sourceB2198 + difference 0 2) sourceC2198) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 901) := by
    have ha : (tripleCharges (sourceA2198 + difference 2 0) (sourceB2198 + difference 0 2) sourceC2198) = raw30152 := by
      apply Matrix.ext; unfold tripleCharges sourceA2198 sourceB2198 sourceC2198 difference raw30152; decide +kernel
    rw [ha]
    exact (canonical30152 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2198 + difference 2 1) (sourceB2198 + difference 1 2) sourceC2198) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2318) := by
    have ha : (tripleCharges (sourceA2198 + difference 2 1) (sourceB2198 + difference 1 2) sourceC2198) = raw30153 := by
      apply Matrix.ext; unfold tripleCharges sourceA2198 sourceB2198 sourceC2198 difference raw30153; decide +kernel
    rw [ha]
    exact (canonical30153 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2198 + difference 2 3) (sourceB2198 + difference 3 2) sourceC2198) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2372) := by
    have ha : (tripleCharges (sourceA2198 + difference 2 3) (sourceB2198 + difference 3 2) sourceC2198) = raw30154 := by
      apply Matrix.ext; unfold tripleCharges sourceA2198 sourceB2198 sourceC2198 difference raw30154; decide +kernel
    rw [ha]
    exact (canonical30154 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2198 + difference 2 4) (sourceB2198 + difference 4 2) sourceC2198) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2556) := by
    have ha : (tripleCharges (sourceA2198 + difference 2 4) (sourceB2198 + difference 4 2) sourceC2198) = raw9875 := by
      apply Matrix.ext; unfold tripleCharges sourceA2198 sourceB2198 sourceC2198 difference raw9875; decide +kernel
    rw [ha]
    exact (canonical9875 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2198 + difference 2 5) (sourceB2198 + difference 5 2) sourceC2198) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2553) := by
    have ha : (tripleCharges (sourceA2198 + difference 2 5) (sourceB2198 + difference 5 2) sourceC2198) = raw30155 := by
      apply Matrix.ext; unfold tripleCharges sourceA2198 sourceB2198 sourceC2198 difference raw30155; decide +kernel
    rw [ha]
    exact (canonical30155 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2198 + difference 3 0) (sourceB2198 + difference 0 3) sourceC2198) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 927) := by
    have ha : (tripleCharges (sourceA2198 + difference 3 0) (sourceB2198 + difference 0 3) sourceC2198) = raw30156 := by
      apply Matrix.ext; unfold tripleCharges sourceA2198 sourceB2198 sourceC2198 difference raw30156; decide +kernel
    rw [ha]
    exact (canonical30156 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2198 + difference 3 1) (sourceB2198 + difference 1 3) sourceC2198) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2337) := by
    have ha : (tripleCharges (sourceA2198 + difference 3 1) (sourceB2198 + difference 1 3) sourceC2198) = raw30157 := by
      apply Matrix.ext; unfold tripleCharges sourceA2198 sourceB2198 sourceC2198 difference raw30157; decide +kernel
    rw [ha]
    exact (canonical30157 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2198 + difference 3 2) (sourceB2198 + difference 2 3) sourceC2198) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2428) := by
    have ha : (tripleCharges (sourceA2198 + difference 3 2) (sourceB2198 + difference 2 3) sourceC2198) = raw30158 := by
      apply Matrix.ext; unfold tripleCharges sourceA2198 sourceB2198 sourceC2198 difference raw30158; decide +kernel
    rw [ha]
    exact (canonical30158 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2198 + difference 3 4) (sourceB2198 + difference 4 3) sourceC2198) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2595) := by
    have ha : (tripleCharges (sourceA2198 + difference 3 4) (sourceB2198 + difference 4 3) sourceC2198) = raw9879 := by
      apply Matrix.ext; unfold tripleCharges sourceA2198 sourceB2198 sourceC2198 difference raw9879; decide +kernel
    rw [ha]
    exact (canonical9879 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2198 + difference 3 5) (sourceB2198 + difference 5 3) sourceC2198) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2594) := by
    have ha : (tripleCharges (sourceA2198 + difference 3 5) (sourceB2198 + difference 5 3) sourceC2198) = raw30159 := by
      apply Matrix.ext; unfold tripleCharges sourceA2198 sourceB2198 sourceC2198 difference raw30159; decide +kernel
    rw [ha]
    exact (canonical30159 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2198 + difference 4 0) (sourceB2198 + difference 0 4) sourceC2198) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 902) := by
    have ha : (tripleCharges (sourceA2198 + difference 4 0) (sourceB2198 + difference 0 4) sourceC2198) = raw30160 := by
      apply Matrix.ext; unfold tripleCharges sourceA2198 sourceB2198 sourceC2198 difference raw30160; decide +kernel
    rw [ha]
    exact (canonical30160 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2198 + difference 4 1) (sourceB2198 + difference 1 4) sourceC2198) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1766) := by
    have ha : (tripleCharges (sourceA2198 + difference 4 1) (sourceB2198 + difference 1 4) sourceC2198) = raw30161 := by
      apply Matrix.ext; unfold tripleCharges sourceA2198 sourceB2198 sourceC2198 difference raw30161; decide +kernel
    rw [ha]
    exact (canonical30161 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2198 + difference 4 2) (sourceB2198 + difference 2 4) sourceC2198) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1760) := by
    have ha : (tripleCharges (sourceA2198 + difference 4 2) (sourceB2198 + difference 2 4) sourceC2198) = raw30162 := by
      apply Matrix.ext; unfold tripleCharges sourceA2198 sourceB2198 sourceC2198 difference raw30162; decide +kernel
    rw [ha]
    exact (canonical30162 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2198 + difference 4 3) (sourceB2198 + difference 3 4) sourceC2198) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1773) := by
    have ha : (tripleCharges (sourceA2198 + difference 4 3) (sourceB2198 + difference 3 4) sourceC2198) = raw30163 := by
      apply Matrix.ext; unfold tripleCharges sourceA2198 sourceB2198 sourceC2198 difference raw30163; decide +kernel
    rw [ha]
    exact (canonical30163 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2198 + difference 4 5) (sourceB2198 + difference 5 4) sourceC2198) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2022) := by
    have ha : (tripleCharges (sourceA2198 + difference 4 5) (sourceB2198 + difference 5 4) sourceC2198) = raw30164 := by
      apply Matrix.ext; unfold tripleCharges sourceA2198 sourceB2198 sourceC2198 difference raw30164; decide +kernel
    rw [ha]
    exact (canonical30164 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2198 + difference 5 0) (sourceB2198 + difference 0 5) sourceC2198) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 903) := by
    have ha : (tripleCharges (sourceA2198 + difference 5 0) (sourceB2198 + difference 0 5) sourceC2198) = raw28789 := by
      apply Matrix.ext; unfold tripleCharges sourceA2198 sourceB2198 sourceC2198 difference raw28789; decide +kernel
    rw [ha]
    exact (canonical28789 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2198 + difference 5 1) (sourceB2198 + difference 1 5) sourceC2198) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2300) := by
    have ha : (tripleCharges (sourceA2198 + difference 5 1) (sourceB2198 + difference 1 5) sourceC2198) = raw28790 := by
      apply Matrix.ext; unfold tripleCharges sourceA2198 sourceB2198 sourceC2198 difference raw28790; decide +kernel
    rw [ha]
    exact (canonical28790 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2198 + difference 5 2) (sourceB2198 + difference 2 5) sourceC2198) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2295) := by
    have ha : (tripleCharges (sourceA2198 + difference 5 2) (sourceB2198 + difference 2 5) sourceC2198) = raw28791 := by
      apply Matrix.ext; unfold tripleCharges sourceA2198 sourceB2198 sourceC2198 difference raw28791; decide +kernel
    rw [ha]
    exact (canonical28791 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2198 + difference 5 3) (sourceB2198 + difference 3 5) sourceC2198) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2306) := by
    have ha : (tripleCharges (sourceA2198 + difference 5 3) (sourceB2198 + difference 3 5) sourceC2198) = raw28792 := by
      apply Matrix.ext; unfold tripleCharges sourceA2198 sourceB2198 sourceC2198 difference raw28792; decide +kernel
    rw [ha]
    exact (canonical28792 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2198 + difference 5 4) (sourceB2198 + difference 4 5) sourceC2198) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2482) := by
    have ha : (tripleCharges (sourceA2198 + difference 5 4) (sourceB2198 + difference 4 5) sourceC2198) = raw9887 := by
      apply Matrix.ext; unfold tripleCharges sourceA2198 sourceB2198 sourceC2198 difference raw9887; decide +kernel
    rw [ha]
    exact (canonical9887 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2198 sourceB2198 sourceC2198
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2198, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2199 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceB2199 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceC2199 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceForm2199 : Integer.Sparse Master := [(Sum.inr 4782, 1), (Sum.inr 4788, 1), (Sum.inr 4790, 1), (Sum.inr 4828, 1), (Sum.inr 4846, 1), (Sum.inr 4995, 1), (Sum.inr 5002, 1), (Sum.inr 5014, 1), (Sum.inr 5050, 1), (Sum.inr 5063, 1), (Sum.inr 5067, 1), (Sum.inr 5080, 1), (Sum.inr 5081, 1), (Sum.inr 5090, 1), (Sum.inr 5111, 1), (Sum.inr 5121, 1), (Sum.inr 5125, 1), (Sum.inr 5126, 1), (Sum.inr 5129, 1), (Sum.inr 5130, 1), (Sum.inr 5140, 1), (Sum.inr 5141, 2), (Sum.inr 5152, 1), (Sum.inr 5176, 1), (Sum.inr 5177, 1), (Sum.inr 5180, 1), (Sum.inr 5181, 1), (Sum.inr 5188, 1), (Sum.inr 5189, 1)]

theorem sourceEq2199 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2199 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2199 + difference 0 1) (sourceB2199 + difference 1 0) sourceC2199) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5152) := by
    have ha : (tripleCharges (sourceA2199 + difference 0 1) (sourceB2199 + difference 1 0) sourceC2199) = raw30165 := by
      apply Matrix.ext; unfold tripleCharges sourceA2199 sourceB2199 sourceC2199 difference raw30165; decide +kernel
    rw [ha]
    exact (canonical30165 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2199 + difference 0 2) (sourceB2199 + difference 2 0) sourceC2199) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5067) := by
    have ha : (tripleCharges (sourceA2199 + difference 0 2) (sourceB2199 + difference 2 0) sourceC2199) = raw30166 := by
      apply Matrix.ext; unfold tripleCharges sourceA2199 sourceB2199 sourceC2199 difference raw30166; decide +kernel
    rw [ha]
    exact (canonical30166 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2199 + difference 0 3) (sourceB2199 + difference 3 0) sourceC2199) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5090) := by
    have ha : (tripleCharges (sourceA2199 + difference 0 3) (sourceB2199 + difference 3 0) sourceC2199) = raw30167 := by
      apply Matrix.ext; unfold tripleCharges sourceA2199 sourceB2199 sourceC2199 difference raw30167; decide +kernel
    rw [ha]
    exact (canonical30167 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2199 + difference 0 4) (sourceB2199 + difference 4 0) sourceC2199) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5081) := by
    have ha : (tripleCharges (sourceA2199 + difference 0 4) (sourceB2199 + difference 4 0) sourceC2199) = raw29676 := by
      apply Matrix.ext; unfold tripleCharges sourceA2199 sourceB2199 sourceC2199 difference raw29676; decide +kernel
    rw [ha]
    exact (canonical29676 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2199 + difference 0 5) (sourceB2199 + difference 5 0) sourceC2199) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5080) := by
    have ha : (tripleCharges (sourceA2199 + difference 0 5) (sourceB2199 + difference 5 0) sourceC2199) = raw30168 := by
      apply Matrix.ext; unfold tripleCharges sourceA2199 sourceB2199 sourceC2199 difference raw30168; decide +kernel
    rw [ha]
    exact (canonical30168 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2199 + difference 1 0) (sourceB2199 + difference 0 1) sourceC2199) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4828) := by
    have ha : (tripleCharges (sourceA2199 + difference 1 0) (sourceB2199 + difference 0 1) sourceC2199) = raw30169 := by
      apply Matrix.ext; unfold tripleCharges sourceA2199 sourceB2199 sourceC2199 difference raw30169; decide +kernel
    rw [ha]
    exact (canonical30169 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2199 + difference 1 2) (sourceB2199 + difference 2 1) sourceC2199) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5181) := by
    have ha : (tripleCharges (sourceA2199 + difference 1 2) (sourceB2199 + difference 2 1) sourceC2199) = raw30170 := by
      apply Matrix.ext; unfold tripleCharges sourceA2199 sourceB2199 sourceC2199 difference raw30170; decide +kernel
    rw [ha]
    exact (canonical30170 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2199 + difference 1 3) (sourceB2199 + difference 3 1) sourceC2199) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5180) := by
    have ha : (tripleCharges (sourceA2199 + difference 1 3) (sourceB2199 + difference 3 1) sourceC2199) = raw30171 := by
      apply Matrix.ext; unfold tripleCharges sourceA2199 sourceB2199 sourceC2199 difference raw30171; decide +kernel
    rw [ha]
    exact (canonical30171 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2199 + difference 1 4) (sourceB2199 + difference 4 1) sourceC2199) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5189) := by
    have ha : (tripleCharges (sourceA2199 + difference 1 4) (sourceB2199 + difference 4 1) sourceC2199) = raw29680 := by
      apply Matrix.ext; unfold tripleCharges sourceA2199 sourceB2199 sourceC2199 difference raw29680; decide +kernel
    rw [ha]
    exact (canonical29680 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2199 + difference 1 5) (sourceB2199 + difference 5 1) sourceC2199) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5188) := by
    have ha : (tripleCharges (sourceA2199 + difference 1 5) (sourceB2199 + difference 5 1) sourceC2199) = raw30172 := by
      apply Matrix.ext; unfold tripleCharges sourceA2199 sourceB2199 sourceC2199 difference raw30172; decide +kernel
    rw [ha]
    exact (canonical30172 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2199 + difference 2 0) (sourceB2199 + difference 0 2) sourceC2199) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4782) := by
    have ha : (tripleCharges (sourceA2199 + difference 2 0) (sourceB2199 + difference 0 2) sourceC2199) = raw30173 := by
      apply Matrix.ext; unfold tripleCharges sourceA2199 sourceB2199 sourceC2199 difference raw30173; decide +kernel
    rw [ha]
    exact (canonical30173 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2199 + difference 2 1) (sourceB2199 + difference 1 2) sourceC2199) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5050) := by
    have ha : (tripleCharges (sourceA2199 + difference 2 1) (sourceB2199 + difference 1 2) sourceC2199) = raw30174 := by
      apply Matrix.ext; unfold tripleCharges sourceA2199 sourceB2199 sourceC2199 difference raw30174; decide +kernel
    rw [ha]
    exact (canonical30174 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2199 + difference 2 3) (sourceB2199 + difference 3 2) sourceC2199) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5121) := by
    have ha : (tripleCharges (sourceA2199 + difference 2 3) (sourceB2199 + difference 3 2) sourceC2199) = raw30175 := by
      apply Matrix.ext; unfold tripleCharges sourceA2199 sourceB2199 sourceC2199 difference raw30175; decide +kernel
    rw [ha]
    exact (canonical30175 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2199 + difference 2 4) (sourceB2199 + difference 4 2) sourceC2199) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5130) := by
    have ha : (tripleCharges (sourceA2199 + difference 2 4) (sourceB2199 + difference 4 2) sourceC2199) = raw29684 := by
      apply Matrix.ext; unfold tripleCharges sourceA2199 sourceB2199 sourceC2199 difference raw29684; decide +kernel
    rw [ha]
    exact (canonical29684 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2199 + difference 2 5) (sourceB2199 + difference 5 2) sourceC2199) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5129) := by
    have ha : (tripleCharges (sourceA2199 + difference 2 5) (sourceB2199 + difference 5 2) sourceC2199) = raw30176 := by
      apply Matrix.ext; unfold tripleCharges sourceA2199 sourceB2199 sourceC2199 difference raw30176; decide +kernel
    rw [ha]
    exact (canonical30176 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2199 + difference 3 0) (sourceB2199 + difference 0 3) sourceC2199) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4846) := by
    have ha : (tripleCharges (sourceA2199 + difference 3 0) (sourceB2199 + difference 0 3) sourceC2199) = raw29690 := by
      apply Matrix.ext; unfold tripleCharges sourceA2199 sourceB2199 sourceC2199 difference raw29690; decide +kernel
    rw [ha]
    exact (canonical29690 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2199 + difference 3 1) (sourceB2199 + difference 1 3) sourceC2199) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5111) := by
    have ha : (tripleCharges (sourceA2199 + difference 3 1) (sourceB2199 + difference 1 3) sourceC2199) = raw29691 := by
      apply Matrix.ext; unfold tripleCharges sourceA2199 sourceB2199 sourceC2199 difference raw29691; decide +kernel
    rw [ha]
    exact (canonical29691 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2199 + difference 3 2) (sourceB2199 + difference 2 3) sourceC2199) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA2199 + difference 3 2) (sourceB2199 + difference 2 3) sourceC2199) = raw29692 := by
      apply Matrix.ext; unfold tripleCharges sourceA2199 sourceB2199 sourceC2199 difference raw29692; decide +kernel
    rw [ha]
    exact (canonical29692 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2199 + difference 3 4) (sourceB2199 + difference 4 3) sourceC2199) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5177) := by
    have ha : (tripleCharges (sourceA2199 + difference 3 4) (sourceB2199 + difference 4 3) sourceC2199) = raw29586 := by
      apply Matrix.ext; unfold tripleCharges sourceA2199 sourceB2199 sourceC2199 difference raw29586; decide +kernel
    rw [ha]
    exact (canonical29586 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2199 + difference 3 5) (sourceB2199 + difference 5 3) sourceC2199) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5176) := by
    have ha : (tripleCharges (sourceA2199 + difference 3 5) (sourceB2199 + difference 5 3) sourceC2199) = raw29694 := by
      apply Matrix.ext; unfold tripleCharges sourceA2199 sourceB2199 sourceC2199 difference raw29694; decide +kernel
    rw [ha]
    exact (canonical29694 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2199 + difference 4 0) (sourceB2199 + difference 0 4) sourceC2199) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4788) := by
    have ha : (tripleCharges (sourceA2199 + difference 4 0) (sourceB2199 + difference 0 4) sourceC2199) = raw30177 := by
      apply Matrix.ext; unfold tripleCharges sourceA2199 sourceB2199 sourceC2199 difference raw30177; decide +kernel
    rw [ha]
    exact (canonical30177 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2199 + difference 4 1) (sourceB2199 + difference 1 4) sourceC2199) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5014) := by
    have ha : (tripleCharges (sourceA2199 + difference 4 1) (sourceB2199 + difference 1 4) sourceC2199) = raw30178 := by
      apply Matrix.ext; unfold tripleCharges sourceA2199 sourceB2199 sourceC2199 difference raw30178; decide +kernel
    rw [ha]
    exact (canonical30178 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2199 + difference 4 2) (sourceB2199 + difference 2 4) sourceC2199) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4995) := by
    have ha : (tripleCharges (sourceA2199 + difference 4 2) (sourceB2199 + difference 2 4) sourceC2199) = raw30179 := by
      apply Matrix.ext; unfold tripleCharges sourceA2199 sourceB2199 sourceC2199 difference raw30179; decide +kernel
    rw [ha]
    exact (canonical30179 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2199 + difference 4 3) (sourceB2199 + difference 3 4) sourceC2199) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5002) := by
    have ha : (tripleCharges (sourceA2199 + difference 4 3) (sourceB2199 + difference 3 4) sourceC2199) = raw30180 := by
      apply Matrix.ext; unfold tripleCharges sourceA2199 sourceB2199 sourceC2199 difference raw30180; decide +kernel
    rw [ha]
    exact (canonical30180 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2199 + difference 4 5) (sourceB2199 + difference 5 4) sourceC2199) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5140) := by
    have ha : (tripleCharges (sourceA2199 + difference 4 5) (sourceB2199 + difference 5 4) sourceC2199) = raw30181 := by
      apply Matrix.ext; unfold tripleCharges sourceA2199 sourceB2199 sourceC2199 difference raw30181; decide +kernel
    rw [ha]
    exact (canonical30181 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2199 + difference 5 0) (sourceB2199 + difference 0 5) sourceC2199) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4790) := by
    have ha : (tripleCharges (sourceA2199 + difference 5 0) (sourceB2199 + difference 0 5) sourceC2199) = raw30182 := by
      apply Matrix.ext; unfold tripleCharges sourceA2199 sourceB2199 sourceC2199 difference raw30182; decide +kernel
    rw [ha]
    exact (canonical30182 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2199 + difference 5 1) (sourceB2199 + difference 1 5) sourceC2199) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5063) := by
    have ha : (tripleCharges (sourceA2199 + difference 5 1) (sourceB2199 + difference 1 5) sourceC2199) = raw30183 := by
      apply Matrix.ext; unfold tripleCharges sourceA2199 sourceB2199 sourceC2199 difference raw30183; decide +kernel
    rw [ha]
    exact (canonical30183 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2199 + difference 5 2) (sourceB2199 + difference 2 5) sourceC2199) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5126) := by
    have ha : (tripleCharges (sourceA2199 + difference 5 2) (sourceB2199 + difference 2 5) sourceC2199) = raw30184 := by
      apply Matrix.ext; unfold tripleCharges sourceA2199 sourceB2199 sourceC2199 difference raw30184; decide +kernel
    rw [ha]
    exact (canonical30184 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2199 + difference 5 3) (sourceB2199 + difference 3 5) sourceC2199) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5125) := by
    have ha : (tripleCharges (sourceA2199 + difference 5 3) (sourceB2199 + difference 3 5) sourceC2199) = raw30185 := by
      apply Matrix.ext; unfold tripleCharges sourceA2199 sourceB2199 sourceC2199 difference raw30185; decide +kernel
    rw [ha]
    exact (canonical30185 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2199 + difference 5 4) (sourceB2199 + difference 4 5) sourceC2199) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA2199 + difference 5 4) (sourceB2199 + difference 4 5) sourceC2199) = raw29585 := by
      apply Matrix.ext; unfold tripleCharges sourceA2199 sourceB2199 sourceC2199 difference raw29585; decide +kernel
    rw [ha]
    exact (canonical29585 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2199 sourceB2199 sourceC2199
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2199, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2200 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2200 : Charge := ![1, 1, 0, -2, 0, 0]
def sourceC2200 : Charge := ![2, 0, 0, 2, -2, -2]
def sourceForm2200 : Integer.Sparse Master := [(Sum.inr 2539, 1), (Sum.inr 3656, 1), (Sum.inr 3660, 1), (Sum.inr 3664, 1), (Sum.inr 3770, 2), (Sum.inr 4089, -1)]

theorem sourceEq2200 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2200 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2200 + difference 0 0) (sourceB2200 + difference 0 0) sourceC2200) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2539) := by
    have ha : (tripleCharges (sourceA2200 + difference 0 0) (sourceB2200 + difference 0 0) sourceC2200) = raw22850 := by
      apply Matrix.ext; unfold tripleCharges sourceA2200 sourceB2200 sourceC2200 difference raw22850; decide +kernel
    rw [ha]
    exact (canonical22850 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2200 + difference 0 1) (sourceB2200 + difference 1 0) sourceC2200) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3660) := by
    have ha : (tripleCharges (sourceA2200 + difference 0 1) (sourceB2200 + difference 1 0) sourceC2200) = raw30186 := by
      apply Matrix.ext; unfold tripleCharges sourceA2200 sourceB2200 sourceC2200 difference raw30186; decide +kernel
    rw [ha]
    exact (canonical30186 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2200 + difference 0 2) (sourceB2200 + difference 2 0) sourceC2200) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3656) := by
    have ha : (tripleCharges (sourceA2200 + difference 0 2) (sourceB2200 + difference 2 0) sourceC2200) = raw30187 := by
      apply Matrix.ext; unfold tripleCharges sourceA2200 sourceB2200 sourceC2200 difference raw30187; decide +kernel
    rw [ha]
    exact (canonical30187 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2200 + difference 0 3) (sourceB2200 + difference 3 0) sourceC2200) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3664) := by
    have ha : (tripleCharges (sourceA2200 + difference 0 3) (sourceB2200 + difference 3 0) sourceC2200) = raw30188 := by
      apply Matrix.ext; unfold tripleCharges sourceA2200 sourceB2200 sourceC2200 difference raw30188; decide +kernel
    rw [ha]
    exact (canonical30188 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2200 + difference 0 4) (sourceB2200 + difference 4 0) sourceC2200) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3770) := by
    have ha : (tripleCharges (sourceA2200 + difference 0 4) (sourceB2200 + difference 4 0) sourceC2200) = raw28965 := by
      apply Matrix.ext; unfold tripleCharges sourceA2200 sourceB2200 sourceC2200 difference raw28965; decide +kernel
    rw [ha]
    exact (canonical28965 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2200 + difference 0 5) (sourceB2200 + difference 5 0) sourceC2200) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3770) := by
    have ha : (tripleCharges (sourceA2200 + difference 0 5) (sourceB2200 + difference 5 0) sourceC2200) = raw30189 := by
      apply Matrix.ext; unfold tripleCharges sourceA2200 sourceB2200 sourceC2200 difference raw30189; decide +kernel
    rw [ha]
    exact (canonical30189 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2200 + sourceB2200) sourceC2200) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4089) := by
    have ha : (doubleCharges (sourceA2200 + sourceB2200) sourceC2200) = raw21008 := by
      apply Matrix.ext; unfold doubleCharges sourceA2200 sourceB2200 sourceC2200 raw21008; decide +kernel
    rw [ha]
    exact (canonical21008 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2200 sourceB2200 sourceC2200
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2200, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2201 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2201 : Charge := ![1, 1, 0, -2, 0, 0]
def sourceC2201 : Charge := ![2, 0, 0, 2, -2, -2]
def sourceForm2201 : Integer.Sparse Master := [(Sum.inr 2306, 2), (Sum.inr 2370, 1), (Sum.inr 2411, 1), (Sum.inr 2539, 1), (Sum.inr 3664, 1), (Sum.inr 4089, -1)]

theorem sourceEq2201 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2201 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2201 + difference 0 3) (sourceB2201 + difference 3 0) sourceC2201) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3664) := by
    have ha : (tripleCharges (sourceA2201 + difference 0 3) (sourceB2201 + difference 3 0) sourceC2201) = raw30188 := by
      apply Matrix.ext; unfold tripleCharges sourceA2201 sourceB2201 sourceC2201 difference raw30188; decide +kernel
    rw [ha]
    exact (canonical30188 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2201 + difference 1 3) (sourceB2201 + difference 3 1) sourceC2201) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2411) := by
    have ha : (tripleCharges (sourceA2201 + difference 1 3) (sourceB2201 + difference 3 1) sourceC2201) = raw22852 := by
      apply Matrix.ext; unfold tripleCharges sourceA2201 sourceB2201 sourceC2201 difference raw22852; decide +kernel
    rw [ha]
    exact (canonical22852 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2201 + difference 2 3) (sourceB2201 + difference 3 2) sourceC2201) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2370) := by
    have ha : (tripleCharges (sourceA2201 + difference 2 3) (sourceB2201 + difference 3 2) sourceC2201) = raw30190 := by
      apply Matrix.ext; unfold tripleCharges sourceA2201 sourceB2201 sourceC2201 difference raw30190; decide +kernel
    rw [ha]
    exact (canonical30190 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2201 + difference 3 3) (sourceB2201 + difference 3 3) sourceC2201) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2539) := by
    have ha : (tripleCharges (sourceA2201 + difference 3 3) (sourceB2201 + difference 3 3) sourceC2201) = raw22850 := by
      apply Matrix.ext; unfold tripleCharges sourceA2201 sourceB2201 sourceC2201 difference raw22850; decide +kernel
    rw [ha]
    exact (canonical22850 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2201 + difference 4 3) (sourceB2201 + difference 3 4) sourceC2201) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2306) := by
    have ha : (tripleCharges (sourceA2201 + difference 4 3) (sourceB2201 + difference 3 4) sourceC2201) = raw30191 := by
      apply Matrix.ext; unfold tripleCharges sourceA2201 sourceB2201 sourceC2201 difference raw30191; decide +kernel
    rw [ha]
    exact (canonical30191 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2201 + difference 5 3) (sourceB2201 + difference 3 5) sourceC2201) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2306) := by
    have ha : (tripleCharges (sourceA2201 + difference 5 3) (sourceB2201 + difference 3 5) sourceC2201) = raw30192 := by
      apply Matrix.ext; unfold tripleCharges sourceA2201 sourceB2201 sourceC2201 difference raw30192; decide +kernel
    rw [ha]
    exact (canonical30192 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2201 + sourceB2201) sourceC2201) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4089) := by
    have ha : (doubleCharges (sourceA2201 + sourceB2201) sourceC2201) = raw21008 := by
      apply Matrix.ext; unfold doubleCharges sourceA2201 sourceB2201 sourceC2201 raw21008; decide +kernel
    rw [ha]
    exact (canonical21008 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2201 sourceB2201 sourceC2201
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2201, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2202 : Charge := ![1, 1, 0, -2, 0, 0]
def sourceB2202 : Charge := ![2, 0, 0, 2, -2, -2]
def sourceC2202 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceForm2202 : Integer.Sparse Master := [(Sum.inr 1785, 1), (Sum.inr 1788, 2), (Sum.inr 1800, 1), (Sum.inr 2007, 1), (Sum.inr 3372, 1), (Sum.inr 4082, -1)]

theorem sourceEq2202 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2202 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2202 + difference 0 0) (sourceB2202 + difference 0 0) sourceC2202) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3372) := by
    have ha : (tripleCharges (sourceA2202 + difference 0 0) (sourceB2202 + difference 0 0) sourceC2202) = raw30193 := by
      apply Matrix.ext; unfold tripleCharges sourceA2202 sourceB2202 sourceC2202 difference raw30193; decide +kernel
    rw [ha]
    exact (canonical30193 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2202 + difference 1 0) (sourceB2202 + difference 0 1) sourceC2202) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1800) := by
    have ha : (tripleCharges (sourceA2202 + difference 1 0) (sourceB2202 + difference 0 1) sourceC2202) = raw30194 := by
      apply Matrix.ext; unfold tripleCharges sourceA2202 sourceB2202 sourceC2202 difference raw30194; decide +kernel
    rw [ha]
    exact (canonical30194 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2202 + difference 2 0) (sourceB2202 + difference 0 2) sourceC2202) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1785) := by
    have ha : (tripleCharges (sourceA2202 + difference 2 0) (sourceB2202 + difference 0 2) sourceC2202) = raw30195 := by
      apply Matrix.ext; unfold tripleCharges sourceA2202 sourceB2202 sourceC2202 difference raw30195; decide +kernel
    rw [ha]
    exact (canonical30195 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2202 + difference 3 0) (sourceB2202 + difference 0 3) sourceC2202) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2007) := by
    have ha : (tripleCharges (sourceA2202 + difference 3 0) (sourceB2202 + difference 0 3) sourceC2202) = raw30196 := by
      apply Matrix.ext; unfold tripleCharges sourceA2202 sourceB2202 sourceC2202 difference raw30196; decide +kernel
    rw [ha]
    exact (canonical30196 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2202 + difference 4 0) (sourceB2202 + difference 0 4) sourceC2202) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1788) := by
    have ha : (tripleCharges (sourceA2202 + difference 4 0) (sourceB2202 + difference 0 4) sourceC2202) = raw30197 := by
      apply Matrix.ext; unfold tripleCharges sourceA2202 sourceB2202 sourceC2202 difference raw30197; decide +kernel
    rw [ha]
    exact (canonical30197 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2202 + difference 5 0) (sourceB2202 + difference 0 5) sourceC2202) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1788) := by
    have ha : (tripleCharges (sourceA2202 + difference 5 0) (sourceB2202 + difference 0 5) sourceC2202) = raw30198 := by
      apply Matrix.ext; unfold tripleCharges sourceA2202 sourceB2202 sourceC2202 difference raw30198; decide +kernel
    rw [ha]
    exact (canonical30198 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2202 + sourceB2202) sourceC2202) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2202 + sourceB2202) sourceC2202) = raw29319 := by
      apply Matrix.ext; unfold doubleCharges sourceA2202 sourceB2202 sourceC2202 raw29319; decide +kernel
    rw [ha]
    exact (canonical29319 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2202 sourceB2202 sourceC2202
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2202, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2203 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2203 : Charge := ![1, 1, -1, -1, 0, 0]
def sourceC2203 : Charge := ![2, 0, 1, 1, -2, -2]
def sourceForm2203 : Integer.Sparse Master := [(Sum.inr 2541, 1), (Sum.inr 3646, 1), (Sum.inr 3650, 2), (Sum.inr 3757, 2), (Sum.inr 4088, -1)]

theorem sourceEq2203 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2203 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2203 + difference 0 0) (sourceB2203 + difference 0 0) sourceC2203) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2541) := by
    have ha : (tripleCharges (sourceA2203 + difference 0 0) (sourceB2203 + difference 0 0) sourceC2203) = raw22871 := by
      apply Matrix.ext; unfold tripleCharges sourceA2203 sourceB2203 sourceC2203 difference raw22871; decide +kernel
    rw [ha]
    exact (canonical22871 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2203 + difference 0 1) (sourceB2203 + difference 1 0) sourceC2203) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3646) := by
    have ha : (tripleCharges (sourceA2203 + difference 0 1) (sourceB2203 + difference 1 0) sourceC2203) = raw30199 := by
      apply Matrix.ext; unfold tripleCharges sourceA2203 sourceB2203 sourceC2203 difference raw30199; decide +kernel
    rw [ha]
    exact (canonical30199 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2203 + difference 0 2) (sourceB2203 + difference 2 0) sourceC2203) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3650) := by
    have ha : (tripleCharges (sourceA2203 + difference 0 2) (sourceB2203 + difference 2 0) sourceC2203) = raw30200 := by
      apply Matrix.ext; unfold tripleCharges sourceA2203 sourceB2203 sourceC2203 difference raw30200; decide +kernel
    rw [ha]
    exact (canonical30200 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2203 + difference 0 3) (sourceB2203 + difference 3 0) sourceC2203) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3650) := by
    have ha : (tripleCharges (sourceA2203 + difference 0 3) (sourceB2203 + difference 3 0) sourceC2203) = raw30201 := by
      apply Matrix.ext; unfold tripleCharges sourceA2203 sourceB2203 sourceC2203 difference raw30201; decide +kernel
    rw [ha]
    exact (canonical30201 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2203 + difference 0 4) (sourceB2203 + difference 4 0) sourceC2203) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3757) := by
    have ha : (tripleCharges (sourceA2203 + difference 0 4) (sourceB2203 + difference 4 0) sourceC2203) = raw28989 := by
      apply Matrix.ext; unfold tripleCharges sourceA2203 sourceB2203 sourceC2203 difference raw28989; decide +kernel
    rw [ha]
    exact (canonical28989 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2203 + difference 0 5) (sourceB2203 + difference 5 0) sourceC2203) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3757) := by
    have ha : (tripleCharges (sourceA2203 + difference 0 5) (sourceB2203 + difference 5 0) sourceC2203) = raw30202 := by
      apply Matrix.ext; unfold tripleCharges sourceA2203 sourceB2203 sourceC2203 difference raw30202; decide +kernel
    rw [ha]
    exact (canonical30202 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2203 + sourceB2203) sourceC2203) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA2203 + sourceB2203) sourceC2203) = raw21046 := by
      apply Matrix.ext; unfold doubleCharges sourceA2203 sourceB2203 sourceC2203 raw21046; decide +kernel
    rw [ha]
    exact (canonical21046 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2203 sourceB2203 sourceC2203
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2203, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2204 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2204 : Charge := ![1, 1, -1, -1, 0, 0]
def sourceC2204 : Charge := ![2, 0, 1, 1, -2, -2]
def sourceForm2204 : Integer.Sparse Master := [(Sum.inr 2295, 2), (Sum.inr 2424, 1), (Sum.inr 2468, 1), (Sum.inr 2541, 1), (Sum.inr 3650, 1), (Sum.inr 4088, -1)]

theorem sourceEq2204 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2204 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2204 + difference 0 2) (sourceB2204 + difference 2 0) sourceC2204) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3650) := by
    have ha : (tripleCharges (sourceA2204 + difference 0 2) (sourceB2204 + difference 2 0) sourceC2204) = raw30200 := by
      apply Matrix.ext; unfold tripleCharges sourceA2204 sourceB2204 sourceC2204 difference raw30200; decide +kernel
    rw [ha]
    exact (canonical30200 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2204 + difference 1 2) (sourceB2204 + difference 2 1) sourceC2204) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2468) := by
    have ha : (tripleCharges (sourceA2204 + difference 1 2) (sourceB2204 + difference 2 1) sourceC2204) = raw22872 := by
      apply Matrix.ext; unfold tripleCharges sourceA2204 sourceB2204 sourceC2204 difference raw22872; decide +kernel
    rw [ha]
    exact (canonical22872 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2204 + difference 2 2) (sourceB2204 + difference 2 2) sourceC2204) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2541) := by
    have ha : (tripleCharges (sourceA2204 + difference 2 2) (sourceB2204 + difference 2 2) sourceC2204) = raw22871 := by
      apply Matrix.ext; unfold tripleCharges sourceA2204 sourceB2204 sourceC2204 difference raw22871; decide +kernel
    rw [ha]
    exact (canonical22871 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2204 + difference 3 2) (sourceB2204 + difference 2 3) sourceC2204) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2424) := by
    have ha : (tripleCharges (sourceA2204 + difference 3 2) (sourceB2204 + difference 2 3) sourceC2204) = raw30203 := by
      apply Matrix.ext; unfold tripleCharges sourceA2204 sourceB2204 sourceC2204 difference raw30203; decide +kernel
    rw [ha]
    exact (canonical30203 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2204 + difference 4 2) (sourceB2204 + difference 2 4) sourceC2204) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2295) := by
    have ha : (tripleCharges (sourceA2204 + difference 4 2) (sourceB2204 + difference 2 4) sourceC2204) = raw30204 := by
      apply Matrix.ext; unfold tripleCharges sourceA2204 sourceB2204 sourceC2204 difference raw30204; decide +kernel
    rw [ha]
    exact (canonical30204 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2204 + difference 5 2) (sourceB2204 + difference 2 5) sourceC2204) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2295) := by
    have ha : (tripleCharges (sourceA2204 + difference 5 2) (sourceB2204 + difference 2 5) sourceC2204) = raw30205 := by
      apply Matrix.ext; unfold tripleCharges sourceA2204 sourceB2204 sourceC2204 difference raw30205; decide +kernel
    rw [ha]
    exact (canonical30205 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2204 + sourceB2204) sourceC2204) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA2204 + sourceB2204) sourceC2204) = raw21046 := by
      apply Matrix.ext; unfold doubleCharges sourceA2204 sourceB2204 sourceC2204 raw21046; decide +kernel
    rw [ha]
    exact (canonical21046 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2204 sourceB2204 sourceC2204
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2204, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2205 : Charge := ![1, 1, -1, -1, 0, 0]
def sourceB2205 : Charge := ![2, 0, 1, 1, -2, -2]
def sourceC2205 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceForm2205 : Integer.Sparse Master := [(Sum.inr 1954, 2), (Sum.inr 1958, 1), (Sum.inr 2007, 2), (Sum.inr 3487, 1), (Sum.inr 4082, -1)]

theorem sourceEq2205 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2205 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2205 + difference 0 0) (sourceB2205 + difference 0 0) sourceC2205) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3487) := by
    have ha : (tripleCharges (sourceA2205 + difference 0 0) (sourceB2205 + difference 0 0) sourceC2205) = raw30206 := by
      apply Matrix.ext; unfold tripleCharges sourceA2205 sourceB2205 sourceC2205 difference raw30206; decide +kernel
    rw [ha]
    exact (canonical30206 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2205 + difference 1 0) (sourceB2205 + difference 0 1) sourceC2205) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1958) := by
    have ha : (tripleCharges (sourceA2205 + difference 1 0) (sourceB2205 + difference 0 1) sourceC2205) = raw30207 := by
      apply Matrix.ext; unfold tripleCharges sourceA2205 sourceB2205 sourceC2205 difference raw30207; decide +kernel
    rw [ha]
    exact (canonical30207 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2205 + difference 2 0) (sourceB2205 + difference 0 2) sourceC2205) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2007) := by
    have ha : (tripleCharges (sourceA2205 + difference 2 0) (sourceB2205 + difference 0 2) sourceC2205) = raw30196 := by
      apply Matrix.ext; unfold tripleCharges sourceA2205 sourceB2205 sourceC2205 difference raw30196; decide +kernel
    rw [ha]
    exact (canonical30196 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2205 + difference 3 0) (sourceB2205 + difference 0 3) sourceC2205) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2007) := by
    have ha : (tripleCharges (sourceA2205 + difference 3 0) (sourceB2205 + difference 0 3) sourceC2205) = raw30208 := by
      apply Matrix.ext; unfold tripleCharges sourceA2205 sourceB2205 sourceC2205 difference raw30208; decide +kernel
    rw [ha]
    exact (canonical30208 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2205 + difference 4 0) (sourceB2205 + difference 0 4) sourceC2205) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1954) := by
    have ha : (tripleCharges (sourceA2205 + difference 4 0) (sourceB2205 + difference 0 4) sourceC2205) = raw30209 := by
      apply Matrix.ext; unfold tripleCharges sourceA2205 sourceB2205 sourceC2205 difference raw30209; decide +kernel
    rw [ha]
    exact (canonical30209 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2205 + difference 5 0) (sourceB2205 + difference 0 5) sourceC2205) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1954) := by
    have ha : (tripleCharges (sourceA2205 + difference 5 0) (sourceB2205 + difference 0 5) sourceC2205) = raw30210 := by
      apply Matrix.ext; unfold tripleCharges sourceA2205 sourceB2205 sourceC2205 difference raw30210; decide +kernel
    rw [ha]
    exact (canonical30210 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2205 + sourceB2205) sourceC2205) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2205 + sourceB2205) sourceC2205) = raw29319 := by
      apply Matrix.ext; unfold doubleCharges sourceA2205 sourceB2205 sourceC2205 raw29319; decide +kernel
    rw [ha]
    exact (canonical29319 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2205 sourceB2205 sourceC2205
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2205, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2206 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2206 : Charge := ![1, 0, 2, 0, 0, -3]
def sourceC2206 : Charge := ![2, 1, -2, 0, -2, 1]
def sourceForm2206 : Integer.Sparse Master := [(Sum.inr 2498, 1), (Sum.inr 2667, 1), (Sum.inr 3018, 1), (Sum.inr 3025, 1), (Sum.inr 3042, 1), (Sum.inr 3811, 1), (Sum.inr 4088, -1)]

theorem sourceEq2206 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2206 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2206 + difference 0 0) (sourceB2206 + difference 0 0) sourceC2206) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2498) := by
    have ha : (tripleCharges (sourceA2206 + difference 0 0) (sourceB2206 + difference 0 0) sourceC2206) = raw30211 := by
      apply Matrix.ext; unfold tripleCharges sourceA2206 sourceB2206 sourceC2206 difference raw30211; decide +kernel
    rw [ha]
    exact (canonical30211 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2206 + difference 0 1) (sourceB2206 + difference 1 0) sourceC2206) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3042) := by
    have ha : (tripleCharges (sourceA2206 + difference 0 1) (sourceB2206 + difference 1 0) sourceC2206) = raw30212 := by
      apply Matrix.ext; unfold tripleCharges sourceA2206 sourceB2206 sourceC2206 difference raw30212; decide +kernel
    rw [ha]
    exact (canonical30212 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2206 + difference 0 2) (sourceB2206 + difference 2 0) sourceC2206) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2667) := by
    have ha : (tripleCharges (sourceA2206 + difference 0 2) (sourceB2206 + difference 2 0) sourceC2206) = raw30213 := by
      apply Matrix.ext; unfold tripleCharges sourceA2206 sourceB2206 sourceC2206 difference raw30213; decide +kernel
    rw [ha]
    exact (canonical30213 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2206 + difference 0 3) (sourceB2206 + difference 3 0) sourceC2206) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3018) := by
    have ha : (tripleCharges (sourceA2206 + difference 0 3) (sourceB2206 + difference 3 0) sourceC2206) = raw30214 := by
      apply Matrix.ext; unfold tripleCharges sourceA2206 sourceB2206 sourceC2206 difference raw30214; decide +kernel
    rw [ha]
    exact (canonical30214 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2206 + difference 0 4) (sourceB2206 + difference 4 0) sourceC2206) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3025) := by
    have ha : (tripleCharges (sourceA2206 + difference 0 4) (sourceB2206 + difference 4 0) sourceC2206) = raw30215 := by
      apply Matrix.ext; unfold tripleCharges sourceA2206 sourceB2206 sourceC2206 difference raw30215; decide +kernel
    rw [ha]
    exact (canonical30215 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2206 + difference 0 5) (sourceB2206 + difference 5 0) sourceC2206) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3811) := by
    have ha : (tripleCharges (sourceA2206 + difference 0 5) (sourceB2206 + difference 5 0) sourceC2206) = raw30216 := by
      apply Matrix.ext; unfold tripleCharges sourceA2206 sourceB2206 sourceC2206 difference raw30216; decide +kernel
    rw [ha]
    exact (canonical30216 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2206 + sourceB2206) sourceC2206) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA2206 + sourceB2206) sourceC2206) = raw30217 := by
      apply Matrix.ext; unfold doubleCharges sourceA2206 sourceB2206 sourceC2206 raw30217; decide +kernel
    rw [ha]
    exact (canonical30217 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2206 sourceB2206 sourceC2206
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2206, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2207 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2207 : Charge := ![1, 0, 2, -1, -1, -1]
def sourceC2207 : Charge := ![2, 1, -2, 1, -1, -1]
def sourceForm2207 : Integer.Sparse Master := [(Sum.inr 2456, 1), (Sum.inr 2756, 1), (Sum.inr 3680, 1), (Sum.inr 3776, 1), (Sum.inr 3796, 2), (Sum.inr 4090, -1)]

theorem sourceEq2207 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2207 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2207 + difference 0 0) (sourceB2207 + difference 0 0) sourceC2207) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2456) := by
    have ha : (tripleCharges (sourceA2207 + difference 0 0) (sourceB2207 + difference 0 0) sourceC2207) = raw30218 := by
      apply Matrix.ext; unfold tripleCharges sourceA2207 sourceB2207 sourceC2207 difference raw30218; decide +kernel
    rw [ha]
    exact (canonical30218 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2207 + difference 0 1) (sourceB2207 + difference 1 0) sourceC2207) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3680) := by
    have ha : (tripleCharges (sourceA2207 + difference 0 1) (sourceB2207 + difference 1 0) sourceC2207) = raw30219 := by
      apply Matrix.ext; unfold tripleCharges sourceA2207 sourceB2207 sourceC2207 difference raw30219; decide +kernel
    rw [ha]
    exact (canonical30219 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2207 + difference 0 2) (sourceB2207 + difference 2 0) sourceC2207) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2756) := by
    have ha : (tripleCharges (sourceA2207 + difference 0 2) (sourceB2207 + difference 2 0) sourceC2207) = raw30220 := by
      apply Matrix.ext; unfold tripleCharges sourceA2207 sourceB2207 sourceC2207 difference raw30220; decide +kernel
    rw [ha]
    exact (canonical30220 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2207 + difference 0 3) (sourceB2207 + difference 3 0) sourceC2207) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3776) := by
    have ha : (tripleCharges (sourceA2207 + difference 0 3) (sourceB2207 + difference 3 0) sourceC2207) = raw30221 := by
      apply Matrix.ext; unfold tripleCharges sourceA2207 sourceB2207 sourceC2207 difference raw30221; decide +kernel
    rw [ha]
    exact (canonical30221 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2207 + difference 0 4) (sourceB2207 + difference 4 0) sourceC2207) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3796) := by
    have ha : (tripleCharges (sourceA2207 + difference 0 4) (sourceB2207 + difference 4 0) sourceC2207) = raw30222 := by
      apply Matrix.ext; unfold tripleCharges sourceA2207 sourceB2207 sourceC2207 difference raw30222; decide +kernel
    rw [ha]
    exact (canonical30222 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2207 + difference 0 5) (sourceB2207 + difference 5 0) sourceC2207) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3796) := by
    have ha : (tripleCharges (sourceA2207 + difference 0 5) (sourceB2207 + difference 5 0) sourceC2207) = raw30223 := by
      apply Matrix.ext; unfold tripleCharges sourceA2207 sourceB2207 sourceC2207 difference raw30223; decide +kernel
    rw [ha]
    exact (canonical30223 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2207 + sourceB2207) sourceC2207) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (doubleCharges (sourceA2207 + sourceB2207) sourceC2207) = raw30224 := by
      apply Matrix.ext; unfold doubleCharges sourceA2207 sourceB2207 sourceC2207 raw30224; decide +kernel
    rw [ha]
    exact (canonical30224 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2207 sourceB2207 sourceC2207
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2207, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
