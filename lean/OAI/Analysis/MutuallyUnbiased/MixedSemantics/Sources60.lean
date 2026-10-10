import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical94
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical116
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical135
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical138
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical143
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical152
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical154
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical158
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical159
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical160
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical167
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical168
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical175
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical176
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical181
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical189
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical191
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical193
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical197
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical213
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical214
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical215
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical216

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA1920 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1920 : Charge := ![1, 0, 1, 1, -1, -2]
def sourceC1920 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceForm1920 : Integer.Sparse Master := [(Sum.inr 1112, 1), (Sum.inr 2320, 1), (Sum.inr 2437, 1), (Sum.inr 2470, 1), (Sum.inr 2480, 1), (Sum.inr 2485, 1), (Sum.inr 4091, -1)]

theorem sourceEq1920 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1920 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1920 + difference 2 0) (sourceB1920 + difference 0 2) sourceC1920) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1112) := by
    have ha : (tripleCharges (sourceA1920 + difference 2 0) (sourceB1920 + difference 0 2) sourceC1920) = raw27447 := by
      apply Matrix.ext; unfold tripleCharges sourceA1920 sourceB1920 sourceC1920 difference raw27447; decide +kernel
    rw [ha]
    exact (canonical27447 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1920 + difference 2 1) (sourceB1920 + difference 1 2) sourceC1920) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2320) := by
    have ha : (tripleCharges (sourceA1920 + difference 2 1) (sourceB1920 + difference 1 2) sourceC1920) = raw27448 := by
      apply Matrix.ext; unfold tripleCharges sourceA1920 sourceB1920 sourceC1920 difference raw27448; decide +kernel
    rw [ha]
    exact (canonical27448 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1920 + difference 2 2) (sourceB1920 + difference 2 2) sourceC1920) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2470) := by
    have ha : (tripleCharges (sourceA1920 + difference 2 2) (sourceB1920 + difference 2 2) sourceC1920) = raw7212 := by
      apply Matrix.ext; unfold tripleCharges sourceA1920 sourceB1920 sourceC1920 difference raw7212; decide +kernel
    rw [ha]
    exact (canonical7212 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1920 + difference 2 3) (sourceB1920 + difference 3 2) sourceC1920) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2437) := by
    have ha : (tripleCharges (sourceA1920 + difference 2 3) (sourceB1920 + difference 3 2) sourceC1920) = raw27449 := by
      apply Matrix.ext; unfold tripleCharges sourceA1920 sourceB1920 sourceC1920 difference raw27449; decide +kernel
    rw [ha]
    exact (canonical27449 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1920 + difference 2 4) (sourceB1920 + difference 4 2) sourceC1920) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2485) := by
    have ha : (tripleCharges (sourceA1920 + difference 2 4) (sourceB1920 + difference 4 2) sourceC1920) = raw27450 := by
      apply Matrix.ext; unfold tripleCharges sourceA1920 sourceB1920 sourceC1920 difference raw27450; decide +kernel
    rw [ha]
    exact (canonical27450 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1920 + difference 2 5) (sourceB1920 + difference 5 2) sourceC1920) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2480) := by
    have ha : (tripleCharges (sourceA1920 + difference 2 5) (sourceB1920 + difference 5 2) sourceC1920) = raw7209 := by
      apply Matrix.ext; unfold tripleCharges sourceA1920 sourceB1920 sourceC1920 difference raw7209; decide +kernel
    rw [ha]
    exact (canonical7209 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1920 + sourceB1920) sourceC1920) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1920 + sourceB1920) sourceC1920) = raw7199 := by
      apply Matrix.ext; unfold doubleCharges sourceA1920 sourceB1920 sourceC1920 raw7199; decide +kernel
    rw [ha]
    exact (canonical7199 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1920 sourceB1920 sourceC1920
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1920, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1921 : Charge := ![1, 0, 1, 1, -1, -2]
def sourceB1921 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceC1921 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceForm1921 : Integer.Sparse Master := [(Sum.inr 1907, 1), (Sum.inr 3339, 1), (Sum.inr 3443, 1), (Sum.inr 3466, 1), (Sum.inr 3468, 2), (Sum.inr 4081, -1)]

theorem sourceEq1921 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1921 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1921 + difference 0 0) (sourceB1921 + difference 0 0) sourceC1921) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3466) := by
    have ha : (tripleCharges (sourceA1921 + difference 0 0) (sourceB1921 + difference 0 0) sourceC1921) = raw27378 := by
      apply Matrix.ext; unfold tripleCharges sourceA1921 sourceB1921 sourceC1921 difference raw27378; decide +kernel
    rw [ha]
    exact (canonical27378 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1921 + difference 0 1) (sourceB1921 + difference 1 0) sourceC1921) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3443) := by
    have ha : (tripleCharges (sourceA1921 + difference 0 1) (sourceB1921 + difference 1 0) sourceC1921) = raw27451 := by
      apply Matrix.ext; unfold tripleCharges sourceA1921 sourceB1921 sourceC1921 difference raw27451; decide +kernel
    rw [ha]
    exact (canonical27451 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1921 + difference 0 2) (sourceB1921 + difference 2 0) sourceC1921) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3468) := by
    have ha : (tripleCharges (sourceA1921 + difference 0 2) (sourceB1921 + difference 2 0) sourceC1921) = raw27442 := by
      apply Matrix.ext; unfold tripleCharges sourceA1921 sourceB1921 sourceC1921 difference raw27442; decide +kernel
    rw [ha]
    exact (canonical27442 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1921 + difference 0 3) (sourceB1921 + difference 3 0) sourceC1921) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3468) := by
    have ha : (tripleCharges (sourceA1921 + difference 0 3) (sourceB1921 + difference 3 0) sourceC1921) = raw27452 := by
      apply Matrix.ext; unfold tripleCharges sourceA1921 sourceB1921 sourceC1921 difference raw27452; decide +kernel
    rw [ha]
    exact (canonical27452 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1921 + difference 0 4) (sourceB1921 + difference 4 0) sourceC1921) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3339) := by
    have ha : (tripleCharges (sourceA1921 + difference 0 4) (sourceB1921 + difference 4 0) sourceC1921) = raw27453 := by
      apply Matrix.ext; unfold tripleCharges sourceA1921 sourceB1921 sourceC1921 difference raw27453; decide +kernel
    rw [ha]
    exact (canonical27453 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1921 + difference 0 5) (sourceB1921 + difference 5 0) sourceC1921) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1907) := by
    have ha : (tripleCharges (sourceA1921 + difference 0 5) (sourceB1921 + difference 5 0) sourceC1921) = raw27454 := by
      apply Matrix.ext; unfold tripleCharges sourceA1921 sourceB1921 sourceC1921 difference raw27454; decide +kernel
    rw [ha]
    exact (canonical27454 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1921 + sourceB1921) sourceC1921) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1921 + sourceB1921) sourceC1921) = raw27319 := by
      apply Matrix.ext; unfold doubleCharges sourceA1921 sourceB1921 sourceC1921 raw27319; decide +kernel
    rw [ha]
    exact (canonical27319 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1921 sourceB1921 sourceC1921
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1921, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1922 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1922 : Charge := ![2, 1, -1, -2, 0, 0]
def sourceC1922 : Charge := ![1, 0, 1, 2, -1, -3]
def sourceForm1922 : Integer.Sparse Master := [(Sum.inr 1902, 1), (Sum.inr 1904, 1), (Sum.inr 1909, 1), (Sum.inr 1922, 1), (Sum.inr 2195, 1), (Sum.inr 3463, 1), (Sum.inr 4080, -1)]

theorem sourceEq1922 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1922 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1922 + difference 0 0) (sourceB1922 + difference 0 0) sourceC1922) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1902) := by
    have ha : (tripleCharges (sourceA1922 + difference 0 0) (sourceB1922 + difference 0 0) sourceC1922) = raw20231 := by
      apply Matrix.ext; unfold tripleCharges sourceA1922 sourceB1922 sourceC1922 difference raw20231; decide +kernel
    rw [ha]
    exact (canonical20231 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1922 + difference 0 1) (sourceB1922 + difference 1 0) sourceC1922) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1904) := by
    have ha : (tripleCharges (sourceA1922 + difference 0 1) (sourceB1922 + difference 1 0) sourceC1922) = raw27455 := by
      apply Matrix.ext; unfold tripleCharges sourceA1922 sourceB1922 sourceC1922 difference raw27455; decide +kernel
    rw [ha]
    exact (canonical27455 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1922 + difference 0 2) (sourceB1922 + difference 2 0) sourceC1922) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1922) := by
    have ha : (tripleCharges (sourceA1922 + difference 0 2) (sourceB1922 + difference 2 0) sourceC1922) = raw27456 := by
      apply Matrix.ext; unfold tripleCharges sourceA1922 sourceB1922 sourceC1922 difference raw27456; decide +kernel
    rw [ha]
    exact (canonical27456 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1922 + difference 0 3) (sourceB1922 + difference 3 0) sourceC1922) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1909) := by
    have ha : (tripleCharges (sourceA1922 + difference 0 3) (sourceB1922 + difference 3 0) sourceC1922) = raw27457 := by
      apply Matrix.ext; unfold tripleCharges sourceA1922 sourceB1922 sourceC1922 difference raw27457; decide +kernel
    rw [ha]
    exact (canonical27457 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1922 + difference 0 4) (sourceB1922 + difference 4 0) sourceC1922) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2195) := by
    have ha : (tripleCharges (sourceA1922 + difference 0 4) (sourceB1922 + difference 4 0) sourceC1922) = raw27458 := by
      apply Matrix.ext; unfold tripleCharges sourceA1922 sourceB1922 sourceC1922 difference raw27458; decide +kernel
    rw [ha]
    exact (canonical27458 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1922 + difference 0 5) (sourceB1922 + difference 5 0) sourceC1922) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3463) := by
    have ha : (tripleCharges (sourceA1922 + difference 0 5) (sourceB1922 + difference 5 0) sourceC1922) = raw27459 := by
      apply Matrix.ext; unfold tripleCharges sourceA1922 sourceB1922 sourceC1922 difference raw27459; decide +kernel
    rw [ha]
    exact (canonical27459 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1922 + sourceB1922) sourceC1922) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1922 + sourceB1922) sourceC1922) = raw20236 := by
      apply Matrix.ext; unfold doubleCharges sourceA1922 sourceB1922 sourceC1922 raw20236; decide +kernel
    rw [ha]
    exact (canonical20236 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1922 sourceB1922 sourceC1922
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1922, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1923 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1923 : Charge := ![1, 1, -1, 0, 1, -2]
def sourceC1923 : Charge := ![2, 0, 1, 0, -2, -1]
def sourceForm1923 : Integer.Sparse Master := [(Sum.inr 1317, 1), (Sum.inr 2426, 1), (Sum.inr 2434, 1), (Sum.inr 2519, 1), (Sum.inr 2558, 1), (Sum.inr 2881, 1), (Sum.inr 4092, -1)]

theorem sourceEq1923 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1923 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1923 + difference 0 2) (sourceB1923 + difference 2 0) sourceC1923) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2881) := by
    have ha : (tripleCharges (sourceA1923 + difference 0 2) (sourceB1923 + difference 2 0) sourceC1923) = raw27460 := by
      apply Matrix.ext; unfold tripleCharges sourceA1923 sourceB1923 sourceC1923 difference raw27460; decide +kernel
    rw [ha]
    exact (canonical27460 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1923 + difference 1 2) (sourceB1923 + difference 2 1) sourceC1923) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2519) := by
    have ha : (tripleCharges (sourceA1923 + difference 1 2) (sourceB1923 + difference 2 1) sourceC1923) = raw27461 := by
      apply Matrix.ext; unfold tripleCharges sourceA1923 sourceB1923 sourceC1923 difference raw27461; decide +kernel
    rw [ha]
    exact (canonical27461 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1923 + difference 2 2) (sourceB1923 + difference 2 2) sourceC1923) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2558) := by
    have ha : (tripleCharges (sourceA1923 + difference 2 2) (sourceB1923 + difference 2 2) sourceC1923) = raw27462 := by
      apply Matrix.ext; unfold tripleCharges sourceA1923 sourceB1923 sourceC1923 difference raw27462; decide +kernel
    rw [ha]
    exact (canonical27462 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1923 + difference 3 2) (sourceB1923 + difference 2 3) sourceC1923) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2426) := by
    have ha : (tripleCharges (sourceA1923 + difference 3 2) (sourceB1923 + difference 2 3) sourceC1923) = raw27463 := by
      apply Matrix.ext; unfold tripleCharges sourceA1923 sourceB1923 sourceC1923 difference raw27463; decide +kernel
    rw [ha]
    exact (canonical27463 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1923 + difference 4 2) (sourceB1923 + difference 2 4) sourceC1923) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2434) := by
    have ha : (tripleCharges (sourceA1923 + difference 4 2) (sourceB1923 + difference 2 4) sourceC1923) = raw27464 := by
      apply Matrix.ext; unfold tripleCharges sourceA1923 sourceB1923 sourceC1923 difference raw27464; decide +kernel
    rw [ha]
    exact (canonical27464 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1923 + difference 5 2) (sourceB1923 + difference 2 5) sourceC1923) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1317) := by
    have ha : (tripleCharges (sourceA1923 + difference 5 2) (sourceB1923 + difference 2 5) sourceC1923) = raw27465 := by
      apply Matrix.ext; unfold tripleCharges sourceA1923 sourceB1923 sourceC1923 difference raw27465; decide +kernel
    rw [ha]
    exact (canonical27465 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1923 + sourceB1923) sourceC1923) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1923 + sourceB1923) sourceC1923) = raw27466 := by
      apply Matrix.ext; unfold doubleCharges sourceA1923 sourceB1923 sourceC1923 raw27466; decide +kernel
    rw [ha]
    exact (canonical27466 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1923 sourceB1923 sourceC1923
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1923, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1924 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1924 : Charge := ![1, 1, -1, 0, 1, -2]
def sourceC1924 : Charge := ![2, 0, 1, 0, -2, -1]
def sourceForm1924 : Integer.Sparse Master := [(Sum.inr 1155, 1), (Sum.inr 2352, 1), (Sum.inr 2434, 1), (Sum.inr 2524, 1), (Sum.inr 2558, 1), (Sum.inr 2561, 1), (Sum.inr 4092, -1)]

theorem sourceEq1924 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1924 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1924 + difference 4 0) (sourceB1924 + difference 0 4) sourceC1924) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1155) := by
    have ha : (tripleCharges (sourceA1924 + difference 4 0) (sourceB1924 + difference 0 4) sourceC1924) = raw27467 := by
      apply Matrix.ext; unfold tripleCharges sourceA1924 sourceB1924 sourceC1924 difference raw27467; decide +kernel
    rw [ha]
    exact (canonical27467 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1924 + difference 4 1) (sourceB1924 + difference 1 4) sourceC1924) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2352) := by
    have ha : (tripleCharges (sourceA1924 + difference 4 1) (sourceB1924 + difference 1 4) sourceC1924) = raw27468 := by
      apply Matrix.ext; unfold tripleCharges sourceA1924 sourceB1924 sourceC1924 difference raw27468; decide +kernel
    rw [ha]
    exact (canonical27468 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1924 + difference 4 2) (sourceB1924 + difference 2 4) sourceC1924) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2434) := by
    have ha : (tripleCharges (sourceA1924 + difference 4 2) (sourceB1924 + difference 2 4) sourceC1924) = raw27464 := by
      apply Matrix.ext; unfold tripleCharges sourceA1924 sourceB1924 sourceC1924 difference raw27464; decide +kernel
    rw [ha]
    exact (canonical27464 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1924 + difference 4 3) (sourceB1924 + difference 3 4) sourceC1924) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2524) := by
    have ha : (tripleCharges (sourceA1924 + difference 4 3) (sourceB1924 + difference 3 4) sourceC1924) = raw27469 := by
      apply Matrix.ext; unfold tripleCharges sourceA1924 sourceB1924 sourceC1924 difference raw27469; decide +kernel
    rw [ha]
    exact (canonical27469 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1924 + difference 4 4) (sourceB1924 + difference 4 4) sourceC1924) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2558) := by
    have ha : (tripleCharges (sourceA1924 + difference 4 4) (sourceB1924 + difference 4 4) sourceC1924) = raw27462 := by
      apply Matrix.ext; unfold tripleCharges sourceA1924 sourceB1924 sourceC1924 difference raw27462; decide +kernel
    rw [ha]
    exact (canonical27462 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1924 + difference 4 5) (sourceB1924 + difference 5 4) sourceC1924) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2561) := by
    have ha : (tripleCharges (sourceA1924 + difference 4 5) (sourceB1924 + difference 5 4) sourceC1924) = raw27470 := by
      apply Matrix.ext; unfold tripleCharges sourceA1924 sourceB1924 sourceC1924 difference raw27470; decide +kernel
    rw [ha]
    exact (canonical27470 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1924 + sourceB1924) sourceC1924) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1924 + sourceB1924) sourceC1924) = raw27466 := by
      apply Matrix.ext; unfold doubleCharges sourceA1924 sourceB1924 sourceC1924 raw27466; decide +kernel
    rw [ha]
    exact (canonical27466 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1924 sourceB1924 sourceC1924
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1924, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1925 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1925 : Charge := ![2, 0, 1, 0, -2, -1]
def sourceC1925 : Charge := ![1, 1, -1, 0, 1, -2]
def sourceForm1925 : Integer.Sparse Master := [(Sum.inr 1337, 1), (Sum.inr 2437, 1), (Sum.inr 2442, 1), (Sum.inr 2485, 1), (Sum.inr 2618, 1), (Sum.inr 2954, 1), (Sum.inr 4091, -1)]

theorem sourceEq1925 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1925 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1925 + difference 2 0) (sourceB1925 + difference 0 2) sourceC1925) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1337) := by
    have ha : (tripleCharges (sourceA1925 + difference 2 0) (sourceB1925 + difference 0 2) sourceC1925) = raw27471 := by
      apply Matrix.ext; unfold tripleCharges sourceA1925 sourceB1925 sourceC1925 difference raw27471; decide +kernel
    rw [ha]
    exact (canonical27471 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1925 + difference 2 1) (sourceB1925 + difference 1 2) sourceC1925) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2442) := by
    have ha : (tripleCharges (sourceA1925 + difference 2 1) (sourceB1925 + difference 1 2) sourceC1925) = raw27472 := by
      apply Matrix.ext; unfold tripleCharges sourceA1925 sourceB1925 sourceC1925 difference raw27472; decide +kernel
    rw [ha]
    exact (canonical27472 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1925 + difference 2 2) (sourceB1925 + difference 2 2) sourceC1925) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2618) := by
    have ha : (tripleCharges (sourceA1925 + difference 2 2) (sourceB1925 + difference 2 2) sourceC1925) = raw27473 := by
      apply Matrix.ext; unfold tripleCharges sourceA1925 sourceB1925 sourceC1925 difference raw27473; decide +kernel
    rw [ha]
    exact (canonical27473 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1925 + difference 2 3) (sourceB1925 + difference 3 2) sourceC1925) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2437) := by
    have ha : (tripleCharges (sourceA1925 + difference 2 3) (sourceB1925 + difference 3 2) sourceC1925) = raw27474 := by
      apply Matrix.ext; unfold tripleCharges sourceA1925 sourceB1925 sourceC1925 difference raw27474; decide +kernel
    rw [ha]
    exact (canonical27474 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1925 + difference 2 4) (sourceB1925 + difference 4 2) sourceC1925) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2485) := by
    have ha : (tripleCharges (sourceA1925 + difference 2 4) (sourceB1925 + difference 4 2) sourceC1925) = raw27475 := by
      apply Matrix.ext; unfold tripleCharges sourceA1925 sourceB1925 sourceC1925 difference raw27475; decide +kernel
    rw [ha]
    exact (canonical27475 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1925 + difference 2 5) (sourceB1925 + difference 5 2) sourceC1925) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2954) := by
    have ha : (tripleCharges (sourceA1925 + difference 2 5) (sourceB1925 + difference 5 2) sourceC1925) = raw27476 := by
      apply Matrix.ext; unfold tripleCharges sourceA1925 sourceB1925 sourceC1925 difference raw27476; decide +kernel
    rw [ha]
    exact (canonical27476 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1925 + sourceB1925) sourceC1925) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1925 + sourceB1925) sourceC1925) = raw17313 := by
      apply Matrix.ext; unfold doubleCharges sourceA1925 sourceB1925 sourceC1925 raw17313; decide +kernel
    rw [ha]
    exact (canonical17313 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1925 sourceB1925 sourceC1925
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1925, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1926 : Charge := ![1, 1, -1, 0, 1, -2]
def sourceB1926 : Charge := ![2, 0, 1, 0, -2, -1]
def sourceC1926 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceForm1926 : Integer.Sparse Master := [(Sum.inr 2047, 1), (Sum.inr 3385, 1), (Sum.inr 3443, 1), (Sum.inr 3468, 1), (Sum.inr 3523, 1), (Sum.inr 3530, 1), (Sum.inr 4081, -1)]

theorem sourceEq1926 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1926 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1926 + difference 0 0) (sourceB1926 + difference 0 0) sourceC1926) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3523) := by
    have ha : (tripleCharges (sourceA1926 + difference 0 0) (sourceB1926 + difference 0 0) sourceC1926) = raw27477 := by
      apply Matrix.ext; unfold tripleCharges sourceA1926 sourceB1926 sourceC1926 difference raw27477; decide +kernel
    rw [ha]
    exact (canonical27477 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1926 + difference 0 1) (sourceB1926 + difference 1 0) sourceC1926) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3530) := by
    have ha : (tripleCharges (sourceA1926 + difference 0 1) (sourceB1926 + difference 1 0) sourceC1926) = raw27478 := by
      apply Matrix.ext; unfold tripleCharges sourceA1926 sourceB1926 sourceC1926 difference raw27478; decide +kernel
    rw [ha]
    exact (canonical27478 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1926 + difference 0 2) (sourceB1926 + difference 2 0) sourceC1926) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3385) := by
    have ha : (tripleCharges (sourceA1926 + difference 0 2) (sourceB1926 + difference 2 0) sourceC1926) = raw27479 := by
      apply Matrix.ext; unfold tripleCharges sourceA1926 sourceB1926 sourceC1926 difference raw27479; decide +kernel
    rw [ha]
    exact (canonical27479 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1926 + difference 0 3) (sourceB1926 + difference 3 0) sourceC1926) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3443) := by
    have ha : (tripleCharges (sourceA1926 + difference 0 3) (sourceB1926 + difference 3 0) sourceC1926) = raw27480 := by
      apply Matrix.ext; unfold tripleCharges sourceA1926 sourceB1926 sourceC1926 difference raw27480; decide +kernel
    rw [ha]
    exact (canonical27480 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1926 + difference 0 4) (sourceB1926 + difference 4 0) sourceC1926) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3468) := by
    have ha : (tripleCharges (sourceA1926 + difference 0 4) (sourceB1926 + difference 4 0) sourceC1926) = raw27481 := by
      apply Matrix.ext; unfold tripleCharges sourceA1926 sourceB1926 sourceC1926 difference raw27481; decide +kernel
    rw [ha]
    exact (canonical27481 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1926 + difference 0 5) (sourceB1926 + difference 5 0) sourceC1926) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2047) := by
    have ha : (tripleCharges (sourceA1926 + difference 0 5) (sourceB1926 + difference 5 0) sourceC1926) = raw27482 := by
      apply Matrix.ext; unfold tripleCharges sourceA1926 sourceB1926 sourceC1926 difference raw27482; decide +kernel
    rw [ha]
    exact (canonical27482 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1926 + sourceB1926) sourceC1926) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1926 + sourceB1926) sourceC1926) = raw27319 := by
      apply Matrix.ext; unfold doubleCharges sourceA1926 sourceB1926 sourceC1926 raw27319; decide +kernel
    rw [ha]
    exact (canonical27319 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1926 sourceB1926 sourceC1926
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1926, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1927 : Charge := ![1, 1, -1, 0, 1, -2]
def sourceB1927 : Charge := ![2, 0, 1, 0, -2, -1]
def sourceC1927 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceForm1927 : Integer.Sparse Master := [(Sum.inr 1998, 1), (Sum.inr 2004, 1), (Sum.inr 2006, 1), (Sum.inr 2049, 1), (Sum.inr 2230, 1), (Sum.inr 3523, 1), (Sum.inr 4081, -1)]

theorem sourceEq1927 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1927 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1927 + difference 0 0) (sourceB1927 + difference 0 0) sourceC1927) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3523) := by
    have ha : (tripleCharges (sourceA1927 + difference 0 0) (sourceB1927 + difference 0 0) sourceC1927) = raw27477 := by
      apply Matrix.ext; unfold tripleCharges sourceA1927 sourceB1927 sourceC1927 difference raw27477; decide +kernel
    rw [ha]
    exact (canonical27477 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1927 + difference 1 0) (sourceB1927 + difference 0 1) sourceC1927) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2049) := by
    have ha : (tripleCharges (sourceA1927 + difference 1 0) (sourceB1927 + difference 0 1) sourceC1927) = raw27483 := by
      apply Matrix.ext; unfold tripleCharges sourceA1927 sourceB1927 sourceC1927 difference raw27483; decide +kernel
    rw [ha]
    exact (canonical27483 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1927 + difference 2 0) (sourceB1927 + difference 0 2) sourceC1927) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2230) := by
    have ha : (tripleCharges (sourceA1927 + difference 2 0) (sourceB1927 + difference 0 2) sourceC1927) = raw27318 := by
      apply Matrix.ext; unfold tripleCharges sourceA1927 sourceB1927 sourceC1927 difference raw27318; decide +kernel
    rw [ha]
    exact (canonical27318 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1927 + difference 3 0) (sourceB1927 + difference 0 3) sourceC1927) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1998) := by
    have ha : (tripleCharges (sourceA1927 + difference 3 0) (sourceB1927 + difference 0 3) sourceC1927) = raw27484 := by
      apply Matrix.ext; unfold tripleCharges sourceA1927 sourceB1927 sourceC1927 difference raw27484; decide +kernel
    rw [ha]
    exact (canonical27484 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1927 + difference 4 0) (sourceB1927 + difference 0 4) sourceC1927) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2004) := by
    have ha : (tripleCharges (sourceA1927 + difference 4 0) (sourceB1927 + difference 0 4) sourceC1927) = raw27485 := by
      apply Matrix.ext; unfold tripleCharges sourceA1927 sourceB1927 sourceC1927 difference raw27485; decide +kernel
    rw [ha]
    exact (canonical27485 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1927 + difference 5 0) (sourceB1927 + difference 0 5) sourceC1927) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2006) := by
    have ha : (tripleCharges (sourceA1927 + difference 5 0) (sourceB1927 + difference 0 5) sourceC1927) = raw27486 := by
      apply Matrix.ext; unfold tripleCharges sourceA1927 sourceB1927 sourceC1927 difference raw27486; decide +kernel
    rw [ha]
    exact (canonical27486 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1927 + sourceB1927) sourceC1927) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1927 + sourceB1927) sourceC1927) = raw27319 := by
      apply Matrix.ext; unfold doubleCharges sourceA1927 sourceB1927 sourceC1927 raw27319; decide +kernel
    rw [ha]
    exact (canonical27319 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1927 sourceB1927 sourceC1927
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1927, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1928 : Charge := ![1, 1, -1, 0, 1, -2]
def sourceB1928 : Charge := ![2, 0, 1, 0, -2, -1]
def sourceC1928 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceForm1928 : Integer.Sparse Master := [(Sum.inr 2837, 1), (Sum.inr 3353, 1), (Sum.inr 3434, 1), (Sum.inr 3486, 1), (Sum.inr 3523, 1), (Sum.inr 3530, 1), (Sum.inr 4081, -1)]

theorem sourceEq1928 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1928 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1928 + difference 0 1) (sourceB1928 + difference 1 0) sourceC1928) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3530) := by
    have ha : (tripleCharges (sourceA1928 + difference 0 1) (sourceB1928 + difference 1 0) sourceC1928) = raw27478 := by
      apply Matrix.ext; unfold tripleCharges sourceA1928 sourceB1928 sourceC1928 difference raw27478; decide +kernel
    rw [ha]
    exact (canonical27478 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1928 + difference 1 1) (sourceB1928 + difference 1 1) sourceC1928) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3523) := by
    have ha : (tripleCharges (sourceA1928 + difference 1 1) (sourceB1928 + difference 1 1) sourceC1928) = raw27477 := by
      apply Matrix.ext; unfold tripleCharges sourceA1928 sourceB1928 sourceC1928 difference raw27477; decide +kernel
    rw [ha]
    exact (canonical27477 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1928 + difference 2 1) (sourceB1928 + difference 1 2) sourceC1928) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3486) := by
    have ha : (tripleCharges (sourceA1928 + difference 2 1) (sourceB1928 + difference 1 2) sourceC1928) = raw27487 := by
      apply Matrix.ext; unfold tripleCharges sourceA1928 sourceB1928 sourceC1928 difference raw27487; decide +kernel
    rw [ha]
    exact (canonical27487 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1928 + difference 3 1) (sourceB1928 + difference 1 3) sourceC1928) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3434) := by
    have ha : (tripleCharges (sourceA1928 + difference 3 1) (sourceB1928 + difference 1 3) sourceC1928) = raw27488 := by
      apply Matrix.ext; unfold tripleCharges sourceA1928 sourceB1928 sourceC1928 difference raw27488; decide +kernel
    rw [ha]
    exact (canonical27488 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1928 + difference 4 1) (sourceB1928 + difference 1 4) sourceC1928) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2837) := by
    have ha : (tripleCharges (sourceA1928 + difference 4 1) (sourceB1928 + difference 1 4) sourceC1928) = raw27489 := by
      apply Matrix.ext; unfold tripleCharges sourceA1928 sourceB1928 sourceC1928 difference raw27489; decide +kernel
    rw [ha]
    exact (canonical27489 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1928 + difference 5 1) (sourceB1928 + difference 1 5) sourceC1928) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3353) := by
    have ha : (tripleCharges (sourceA1928 + difference 5 1) (sourceB1928 + difference 1 5) sourceC1928) = raw27490 := by
      apply Matrix.ext; unfold tripleCharges sourceA1928 sourceB1928 sourceC1928 difference raw27490; decide +kernel
    rw [ha]
    exact (canonical27490 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1928 + sourceB1928) sourceC1928) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1928 + sourceB1928) sourceC1928) = raw27319 := by
      apply Matrix.ext; unfold doubleCharges sourceA1928 sourceB1928 sourceC1928 raw27319; decide +kernel
    rw [ha]
    exact (canonical27319 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1928 sourceB1928 sourceC1928
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1928, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1929 : Charge := ![1, 1, -1, 0, 1, -2]
def sourceB1929 : Charge := ![2, 0, 1, 0, -2, -1]
def sourceC1929 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceForm1929 : Integer.Sparse Master := [(Sum.inr 3468, 2), (Sum.inr 3519, 1), (Sum.inr 3523, 2), (Sum.inr 3615, 1), (Sum.inr 4081, -1)]

theorem sourceEq1929 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1929 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1929 + difference 0 4) (sourceB1929 + difference 4 0) sourceC1929) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3468) := by
    have ha : (tripleCharges (sourceA1929 + difference 0 4) (sourceB1929 + difference 4 0) sourceC1929) = raw27481 := by
      apply Matrix.ext; unfold tripleCharges sourceA1929 sourceB1929 sourceC1929 difference raw27481; decide +kernel
    rw [ha]
    exact (canonical27481 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1929 + difference 1 4) (sourceB1929 + difference 4 1) sourceC1929) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3523) := by
    have ha : (tripleCharges (sourceA1929 + difference 1 4) (sourceB1929 + difference 4 1) sourceC1929) = raw27491 := by
      apply Matrix.ext; unfold tripleCharges sourceA1929 sourceB1929 sourceC1929 difference raw27491; decide +kernel
    rw [ha]
    exact (canonical27491 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1929 + difference 2 4) (sourceB1929 + difference 4 2) sourceC1929) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3615) := by
    have ha : (tripleCharges (sourceA1929 + difference 2 4) (sourceB1929 + difference 4 2) sourceC1929) = raw27492 := by
      apply Matrix.ext; unfold tripleCharges sourceA1929 sourceB1929 sourceC1929 difference raw27492; decide +kernel
    rw [ha]
    exact (canonical27492 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1929 + difference 3 4) (sourceB1929 + difference 4 3) sourceC1929) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3519) := by
    have ha : (tripleCharges (sourceA1929 + difference 3 4) (sourceB1929 + difference 4 3) sourceC1929) = raw27493 := by
      apply Matrix.ext; unfold tripleCharges sourceA1929 sourceB1929 sourceC1929 difference raw27493; decide +kernel
    rw [ha]
    exact (canonical27493 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1929 + difference 4 4) (sourceB1929 + difference 4 4) sourceC1929) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3523) := by
    have ha : (tripleCharges (sourceA1929 + difference 4 4) (sourceB1929 + difference 4 4) sourceC1929) = raw27477 := by
      apply Matrix.ext; unfold tripleCharges sourceA1929 sourceB1929 sourceC1929 difference raw27477; decide +kernel
    rw [ha]
    exact (canonical27477 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1929 + difference 5 4) (sourceB1929 + difference 4 5) sourceC1929) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3468) := by
    have ha : (tripleCharges (sourceA1929 + difference 5 4) (sourceB1929 + difference 4 5) sourceC1929) = raw27494 := by
      apply Matrix.ext; unfold tripleCharges sourceA1929 sourceB1929 sourceC1929 difference raw27494; decide +kernel
    rw [ha]
    exact (canonical27494 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1929 + sourceB1929) sourceC1929) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1929 + sourceB1929) sourceC1929) = raw27319 := by
      apply Matrix.ext; unfold doubleCharges sourceA1929 sourceB1929 sourceC1929 raw27319; decide +kernel
    rw [ha]
    exact (canonical27319 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1929 sourceB1929 sourceC1929
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1929, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1930 : Charge := ![1, 1, -1, 0, 1, -2]
def sourceB1930 : Charge := ![2, 0, 1, 0, -2, -1]
def sourceC1930 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceForm1930 : Integer.Sparse Master := [(Sum.inr 2006, 1), (Sum.inr 3339, 1), (Sum.inr 3343, 1), (Sum.inr 3353, 1), (Sum.inr 3468, 1), (Sum.inr 3523, 1), (Sum.inr 4081, -1)]

theorem sourceEq1930 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1930 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1930 + difference 5 0) (sourceB1930 + difference 0 5) sourceC1930) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2006) := by
    have ha : (tripleCharges (sourceA1930 + difference 5 0) (sourceB1930 + difference 0 5) sourceC1930) = raw27486 := by
      apply Matrix.ext; unfold tripleCharges sourceA1930 sourceB1930 sourceC1930 difference raw27486; decide +kernel
    rw [ha]
    exact (canonical27486 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1930 + difference 5 1) (sourceB1930 + difference 1 5) sourceC1930) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3353) := by
    have ha : (tripleCharges (sourceA1930 + difference 5 1) (sourceB1930 + difference 1 5) sourceC1930) = raw27490 := by
      apply Matrix.ext; unfold tripleCharges sourceA1930 sourceB1930 sourceC1930 difference raw27490; decide +kernel
    rw [ha]
    exact (canonical27490 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1930 + difference 5 2) (sourceB1930 + difference 2 5) sourceC1930) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3343) := by
    have ha : (tripleCharges (sourceA1930 + difference 5 2) (sourceB1930 + difference 2 5) sourceC1930) = raw27495 := by
      apply Matrix.ext; unfold tripleCharges sourceA1930 sourceB1930 sourceC1930 difference raw27495; decide +kernel
    rw [ha]
    exact (canonical27495 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1930 + difference 5 3) (sourceB1930 + difference 3 5) sourceC1930) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3339) := by
    have ha : (tripleCharges (sourceA1930 + difference 5 3) (sourceB1930 + difference 3 5) sourceC1930) = raw27496 := by
      apply Matrix.ext; unfold tripleCharges sourceA1930 sourceB1930 sourceC1930 difference raw27496; decide +kernel
    rw [ha]
    exact (canonical27496 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1930 + difference 5 4) (sourceB1930 + difference 4 5) sourceC1930) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3468) := by
    have ha : (tripleCharges (sourceA1930 + difference 5 4) (sourceB1930 + difference 4 5) sourceC1930) = raw27494 := by
      apply Matrix.ext; unfold tripleCharges sourceA1930 sourceB1930 sourceC1930 difference raw27494; decide +kernel
    rw [ha]
    exact (canonical27494 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1930 + difference 5 5) (sourceB1930 + difference 5 5) sourceC1930) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3523) := by
    have ha : (tripleCharges (sourceA1930 + difference 5 5) (sourceB1930 + difference 5 5) sourceC1930) = raw27477 := by
      apply Matrix.ext; unfold tripleCharges sourceA1930 sourceB1930 sourceC1930 difference raw27477; decide +kernel
    rw [ha]
    exact (canonical27477 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1930 + sourceB1930) sourceC1930) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1930 + sourceB1930) sourceC1930) = raw27319 := by
      apply Matrix.ext; unfold doubleCharges sourceA1930 sourceB1930 sourceC1930 raw27319; decide +kernel
    rw [ha]
    exact (canonical27319 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1930 sourceB1930 sourceC1930
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1930, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1931 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1931 : Charge := ![2, 0, 1, 0, -3, 0]
def sourceC1931 : Charge := ![1, 1, -1, 0, 2, -3]
def sourceForm1931 : Integer.Sparse Master := [(Sum.inr 2118, 1), (Sum.inr 2121, 1), (Sum.inr 2123, 1), (Sum.inr 2129, 1), (Sum.inr 2216, 1), (Sum.inr 2735, 1), (Sum.inr 4080, -1)]

theorem sourceEq1931 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1931 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1931 + difference 0 0) (sourceB1931 + difference 0 0) sourceC1931) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2121) := by
    have ha : (tripleCharges (sourceA1931 + difference 0 0) (sourceB1931 + difference 0 0) sourceC1931) = raw27497 := by
      apply Matrix.ext; unfold tripleCharges sourceA1931 sourceB1931 sourceC1931 difference raw27497; decide +kernel
    rw [ha]
    exact (canonical27497 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1931 + difference 0 1) (sourceB1931 + difference 1 0) sourceC1931) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2123) := by
    have ha : (tripleCharges (sourceA1931 + difference 0 1) (sourceB1931 + difference 1 0) sourceC1931) = raw27498 := by
      apply Matrix.ext; unfold tripleCharges sourceA1931 sourceB1931 sourceC1931 difference raw27498; decide +kernel
    rw [ha]
    exact (canonical27498 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1931 + difference 0 2) (sourceB1931 + difference 2 0) sourceC1931) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2129) := by
    have ha : (tripleCharges (sourceA1931 + difference 0 2) (sourceB1931 + difference 2 0) sourceC1931) = raw27499 := by
      apply Matrix.ext; unfold tripleCharges sourceA1931 sourceB1931 sourceC1931 difference raw27499; decide +kernel
    rw [ha]
    exact (canonical27499 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1931 + difference 0 3) (sourceB1931 + difference 3 0) sourceC1931) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2118) := by
    have ha : (tripleCharges (sourceA1931 + difference 0 3) (sourceB1931 + difference 3 0) sourceC1931) = raw27500 := by
      apply Matrix.ext; unfold tripleCharges sourceA1931 sourceB1931 sourceC1931 difference raw27500; decide +kernel
    rw [ha]
    exact (canonical27500 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1931 + difference 0 4) (sourceB1931 + difference 4 0) sourceC1931) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2216) := by
    have ha : (tripleCharges (sourceA1931 + difference 0 4) (sourceB1931 + difference 4 0) sourceC1931) = raw27501 := by
      apply Matrix.ext; unfold tripleCharges sourceA1931 sourceB1931 sourceC1931 difference raw27501; decide +kernel
    rw [ha]
    exact (canonical27501 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1931 + difference 0 5) (sourceB1931 + difference 5 0) sourceC1931) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2735) := by
    have ha : (tripleCharges (sourceA1931 + difference 0 5) (sourceB1931 + difference 5 0) sourceC1931) = raw27502 := by
      apply Matrix.ext; unfold tripleCharges sourceA1931 sourceB1931 sourceC1931 difference raw27502; decide +kernel
    rw [ha]
    exact (canonical27502 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1931 + sourceB1931) sourceC1931) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1931 + sourceB1931) sourceC1931) = raw27503 := by
      apply Matrix.ext; unfold doubleCharges sourceA1931 sourceB1931 sourceC1931 raw27503; decide +kernel
    rw [ha]
    exact (canonical27503 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1931 sourceB1931 sourceC1931
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1931, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1932 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1932 : Charge := ![1, 1, -1, 1, -1, -1]
def sourceC1932 : Charge := ![2, 0, 1, -1, 0, -2]
def sourceForm1932 : Integer.Sparse Master := [(Sum.inr 1148, 1), (Sum.inr 2347, 1), (Sum.inr 2425, 1), (Sum.inr 2482, 1), (Sum.inr 2542, 1), (Sum.inr 2553, 1), (Sum.inr 4092, -1)]

theorem sourceEq1932 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1932 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1932 + difference 0 2) (sourceB1932 + difference 2 0) sourceC1932) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2553) := by
    have ha : (tripleCharges (sourceA1932 + difference 0 2) (sourceB1932 + difference 2 0) sourceC1932) = raw27504 := by
      apply Matrix.ext; unfold tripleCharges sourceA1932 sourceB1932 sourceC1932 difference raw27504; decide +kernel
    rw [ha]
    exact (canonical27504 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1932 + difference 1 2) (sourceB1932 + difference 2 1) sourceC1932) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2482) := by
    have ha : (tripleCharges (sourceA1932 + difference 1 2) (sourceB1932 + difference 2 1) sourceC1932) = raw27505 := by
      apply Matrix.ext; unfold tripleCharges sourceA1932 sourceB1932 sourceC1932 difference raw27505; decide +kernel
    rw [ha]
    exact (canonical27505 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1932 + difference 2 2) (sourceB1932 + difference 2 2) sourceC1932) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2542) := by
    have ha : (tripleCharges (sourceA1932 + difference 2 2) (sourceB1932 + difference 2 2) sourceC1932) = raw27506 := by
      apply Matrix.ext; unfold tripleCharges sourceA1932 sourceB1932 sourceC1932 difference raw27506; decide +kernel
    rw [ha]
    exact (canonical27506 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1932 + difference 3 2) (sourceB1932 + difference 2 3) sourceC1932) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2425) := by
    have ha : (tripleCharges (sourceA1932 + difference 3 2) (sourceB1932 + difference 2 3) sourceC1932) = raw27507 := by
      apply Matrix.ext; unfold tripleCharges sourceA1932 sourceB1932 sourceC1932 difference raw27507; decide +kernel
    rw [ha]
    exact (canonical27507 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1932 + difference 4 2) (sourceB1932 + difference 2 4) sourceC1932) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2347) := by
    have ha : (tripleCharges (sourceA1932 + difference 4 2) (sourceB1932 + difference 2 4) sourceC1932) = raw27508 := by
      apply Matrix.ext; unfold tripleCharges sourceA1932 sourceB1932 sourceC1932 difference raw27508; decide +kernel
    rw [ha]
    exact (canonical27508 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1932 + difference 5 2) (sourceB1932 + difference 2 5) sourceC1932) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1148) := by
    have ha : (tripleCharges (sourceA1932 + difference 5 2) (sourceB1932 + difference 2 5) sourceC1932) = raw27509 := by
      apply Matrix.ext; unfold tripleCharges sourceA1932 sourceB1932 sourceC1932 difference raw27509; decide +kernel
    rw [ha]
    exact (canonical27509 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1932 + sourceB1932) sourceC1932) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1932 + sourceB1932) sourceC1932) = raw24746 := by
      apply Matrix.ext; unfold doubleCharges sourceA1932 sourceB1932 sourceC1932 raw24746; decide +kernel
    rw [ha]
    exact (canonical24746 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1932 sourceB1932 sourceC1932
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1932, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1933 : Charge := ![1, 1, -1, 1, -1, -1]
def sourceB1933 : Charge := ![2, 0, 1, -1, 0, -2]
def sourceC1933 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceForm1933 : Integer.Sparse Master := [(Sum.inr 3432, 1), (Sum.inr 3434, 1), (Sum.inr 3437, 1), (Sum.inr 3481, 1), (Sum.inr 3513, 1), (Sum.inr 3519, 1), (Sum.inr 4081, -1)]

theorem sourceEq1933 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1933 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1933 + difference 0 0) (sourceB1933 + difference 0 0) sourceC1933) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3513) := by
    have ha : (tripleCharges (sourceA1933 + difference 0 0) (sourceB1933 + difference 0 0) sourceC1933) = raw27510 := by
      apply Matrix.ext; unfold tripleCharges sourceA1933 sourceB1933 sourceC1933 difference raw27510; decide +kernel
    rw [ha]
    exact (canonical27510 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1933 + difference 0 1) (sourceB1933 + difference 1 0) sourceC1933) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3519) := by
    have ha : (tripleCharges (sourceA1933 + difference 0 1) (sourceB1933 + difference 1 0) sourceC1933) = raw27511 := by
      apply Matrix.ext; unfold tripleCharges sourceA1933 sourceB1933 sourceC1933 difference raw27511; decide +kernel
    rw [ha]
    exact (canonical27511 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1933 + difference 0 2) (sourceB1933 + difference 2 0) sourceC1933) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3437) := by
    have ha : (tripleCharges (sourceA1933 + difference 0 2) (sourceB1933 + difference 2 0) sourceC1933) = raw27512 := by
      apply Matrix.ext; unfold tripleCharges sourceA1933 sourceB1933 sourceC1933 difference raw27512; decide +kernel
    rw [ha]
    exact (canonical27512 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1933 + difference 0 3) (sourceB1933 + difference 3 0) sourceC1933) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3481) := by
    have ha : (tripleCharges (sourceA1933 + difference 0 3) (sourceB1933 + difference 3 0) sourceC1933) = raw27513 := by
      apply Matrix.ext; unfold tripleCharges sourceA1933 sourceB1933 sourceC1933 difference raw27513; decide +kernel
    rw [ha]
    exact (canonical27513 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1933 + difference 0 4) (sourceB1933 + difference 4 0) sourceC1933) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3434) := by
    have ha : (tripleCharges (sourceA1933 + difference 0 4) (sourceB1933 + difference 4 0) sourceC1933) = raw27514 := by
      apply Matrix.ext; unfold tripleCharges sourceA1933 sourceB1933 sourceC1933 difference raw27514; decide +kernel
    rw [ha]
    exact (canonical27514 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1933 + difference 0 5) (sourceB1933 + difference 5 0) sourceC1933) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3432) := by
    have ha : (tripleCharges (sourceA1933 + difference 0 5) (sourceB1933 + difference 5 0) sourceC1933) = raw27515 := by
      apply Matrix.ext; unfold tripleCharges sourceA1933 sourceB1933 sourceC1933 difference raw27515; decide +kernel
    rw [ha]
    exact (canonical27515 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1933 + sourceB1933) sourceC1933) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1933 + sourceB1933) sourceC1933) = raw27319 := by
      apply Matrix.ext; unfold doubleCharges sourceA1933 sourceB1933 sourceC1933 raw27319; decide +kernel
    rw [ha]
    exact (canonical27319 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1933 sourceB1933 sourceC1933
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1933, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1934 : Charge := ![1, 1, -1, 1, -1, -1]
def sourceB1934 : Charge := ![2, 0, 1, -1, 0, -2]
def sourceC1934 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceForm1934 : Integer.Sparse Master := [(Sum.inr 1986, 1), (Sum.inr 1989, 1), (Sum.inr 1996, 1), (Sum.inr 2015, 1), (Sum.inr 2203, 1), (Sum.inr 3513, 1), (Sum.inr 4081, -1)]

theorem sourceEq1934 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1934 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1934 + difference 0 0) (sourceB1934 + difference 0 0) sourceC1934) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3513) := by
    have ha : (tripleCharges (sourceA1934 + difference 0 0) (sourceB1934 + difference 0 0) sourceC1934) = raw27510 := by
      apply Matrix.ext; unfold tripleCharges sourceA1934 sourceB1934 sourceC1934 difference raw27510; decide +kernel
    rw [ha]
    exact (canonical27510 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1934 + difference 1 0) (sourceB1934 + difference 0 1) sourceC1934) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2015) := by
    have ha : (tripleCharges (sourceA1934 + difference 1 0) (sourceB1934 + difference 0 1) sourceC1934) = raw27516 := by
      apply Matrix.ext; unfold tripleCharges sourceA1934 sourceB1934 sourceC1934 difference raw27516; decide +kernel
    rw [ha]
    exact (canonical27516 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1934 + difference 2 0) (sourceB1934 + difference 0 2) sourceC1934) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2203) := by
    have ha : (tripleCharges (sourceA1934 + difference 2 0) (sourceB1934 + difference 0 2) sourceC1934) = raw27368 := by
      apply Matrix.ext; unfold tripleCharges sourceA1934 sourceB1934 sourceC1934 difference raw27368; decide +kernel
    rw [ha]
    exact (canonical27368 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1934 + difference 3 0) (sourceB1934 + difference 0 3) sourceC1934) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1989) := by
    have ha : (tripleCharges (sourceA1934 + difference 3 0) (sourceB1934 + difference 0 3) sourceC1934) = raw27517 := by
      apply Matrix.ext; unfold tripleCharges sourceA1934 sourceB1934 sourceC1934 difference raw27517; decide +kernel
    rw [ha]
    exact (canonical27517 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1934 + difference 4 0) (sourceB1934 + difference 0 4) sourceC1934) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1996) := by
    have ha : (tripleCharges (sourceA1934 + difference 4 0) (sourceB1934 + difference 0 4) sourceC1934) = raw27518 := by
      apply Matrix.ext; unfold tripleCharges sourceA1934 sourceB1934 sourceC1934 difference raw27518; decide +kernel
    rw [ha]
    exact (canonical27518 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1934 + difference 5 0) (sourceB1934 + difference 0 5) sourceC1934) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1986) := by
    have ha : (tripleCharges (sourceA1934 + difference 5 0) (sourceB1934 + difference 0 5) sourceC1934) = raw27519 := by
      apply Matrix.ext; unfold tripleCharges sourceA1934 sourceB1934 sourceC1934 difference raw27519; decide +kernel
    rw [ha]
    exact (canonical27519 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1934 + sourceB1934) sourceC1934) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1934 + sourceB1934) sourceC1934) = raw27319 := by
      apply Matrix.ext; unfold doubleCharges sourceA1934 sourceB1934 sourceC1934 raw27319; decide +kernel
    rw [ha]
    exact (canonical27319 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1934 sourceB1934 sourceC1934
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1934, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1935 : Charge := ![1, 1, -1, 1, -1, -1]
def sourceB1935 : Charge := ![2, 0, 1, -1, 0, -2]
def sourceC1935 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceForm1935 : Integer.Sparse Master := [(Sum.inr 1996, 1), (Sum.inr 3368, 1), (Sum.inr 3432, 1), (Sum.inr 3468, 1), (Sum.inr 3513, 1), (Sum.inr 3519, 1), (Sum.inr 4081, -1)]

theorem sourceEq1935 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1935 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1935 + difference 0 1) (sourceB1935 + difference 1 0) sourceC1935) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3519) := by
    have ha : (tripleCharges (sourceA1935 + difference 0 1) (sourceB1935 + difference 1 0) sourceC1935) = raw27511 := by
      apply Matrix.ext; unfold tripleCharges sourceA1935 sourceB1935 sourceC1935 difference raw27511; decide +kernel
    rw [ha]
    exact (canonical27511 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1935 + difference 1 1) (sourceB1935 + difference 1 1) sourceC1935) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3513) := by
    have ha : (tripleCharges (sourceA1935 + difference 1 1) (sourceB1935 + difference 1 1) sourceC1935) = raw27510 := by
      apply Matrix.ext; unfold tripleCharges sourceA1935 sourceB1935 sourceC1935 difference raw27510; decide +kernel
    rw [ha]
    exact (canonical27510 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1935 + difference 2 1) (sourceB1935 + difference 1 2) sourceC1935) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3468) := by
    have ha : (tripleCharges (sourceA1935 + difference 2 1) (sourceB1935 + difference 1 2) sourceC1935) = raw27446 := by
      apply Matrix.ext; unfold tripleCharges sourceA1935 sourceB1935 sourceC1935 difference raw27446; decide +kernel
    rw [ha]
    exact (canonical27446 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1935 + difference 3 1) (sourceB1935 + difference 1 3) sourceC1935) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3368) := by
    have ha : (tripleCharges (sourceA1935 + difference 3 1) (sourceB1935 + difference 1 3) sourceC1935) = raw27520 := by
      apply Matrix.ext; unfold tripleCharges sourceA1935 sourceB1935 sourceC1935 difference raw27520; decide +kernel
    rw [ha]
    exact (canonical27520 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1935 + difference 4 1) (sourceB1935 + difference 1 4) sourceC1935) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3432) := by
    have ha : (tripleCharges (sourceA1935 + difference 4 1) (sourceB1935 + difference 1 4) sourceC1935) = raw27521 := by
      apply Matrix.ext; unfold tripleCharges sourceA1935 sourceB1935 sourceC1935 difference raw27521; decide +kernel
    rw [ha]
    exact (canonical27521 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1935 + difference 5 1) (sourceB1935 + difference 1 5) sourceC1935) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1996) := by
    have ha : (tripleCharges (sourceA1935 + difference 5 1) (sourceB1935 + difference 1 5) sourceC1935) = raw27522 := by
      apply Matrix.ext; unfold tripleCharges sourceA1935 sourceB1935 sourceC1935 difference raw27522; decide +kernel
    rw [ha]
    exact (canonical27522 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1935 + sourceB1935) sourceC1935) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1935 + sourceB1935) sourceC1935) = raw27319 := by
      apply Matrix.ext; unfold doubleCharges sourceA1935 sourceB1935 sourceC1935 raw27319; decide +kernel
    rw [ha]
    exact (canonical27319 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1935 sourceB1935 sourceC1935
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1935, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1936 : Charge := ![1, 1, -1, 1, -1, -1]
def sourceB1936 : Charge := ![2, 0, 1, -1, 0, -2]
def sourceC1936 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceForm1936 : Integer.Sparse Master := [(Sum.inr 2203, 1), (Sum.inr 3468, 1), (Sum.inr 3481, 1), (Sum.inr 3513, 1), (Sum.inr 3530, 1), (Sum.inr 3608, 1), (Sum.inr 4081, -1)]

theorem sourceEq1936 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1936 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1936 + difference 2 0) (sourceB1936 + difference 0 2) sourceC1936) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2203) := by
    have ha : (tripleCharges (sourceA1936 + difference 2 0) (sourceB1936 + difference 0 2) sourceC1936) = raw27368 := by
      apply Matrix.ext; unfold tripleCharges sourceA1936 sourceB1936 sourceC1936 difference raw27368; decide +kernel
    rw [ha]
    exact (canonical27368 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1936 + difference 2 1) (sourceB1936 + difference 1 2) sourceC1936) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3468) := by
    have ha : (tripleCharges (sourceA1936 + difference 2 1) (sourceB1936 + difference 1 2) sourceC1936) = raw27446 := by
      apply Matrix.ext; unfold tripleCharges sourceA1936 sourceB1936 sourceC1936 difference raw27446; decide +kernel
    rw [ha]
    exact (canonical27446 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1936 + difference 2 2) (sourceB1936 + difference 2 2) sourceC1936) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3513) := by
    have ha : (tripleCharges (sourceA1936 + difference 2 2) (sourceB1936 + difference 2 2) sourceC1936) = raw27510 := by
      apply Matrix.ext; unfold tripleCharges sourceA1936 sourceB1936 sourceC1936 difference raw27510; decide +kernel
    rw [ha]
    exact (canonical27510 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1936 + difference 2 3) (sourceB1936 + difference 3 2) sourceC1936) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3608) := by
    have ha : (tripleCharges (sourceA1936 + difference 2 3) (sourceB1936 + difference 3 2) sourceC1936) = raw27523 := by
      apply Matrix.ext; unfold tripleCharges sourceA1936 sourceB1936 sourceC1936 difference raw27523; decide +kernel
    rw [ha]
    exact (canonical27523 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1936 + difference 2 4) (sourceB1936 + difference 4 2) sourceC1936) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3530) := by
    have ha : (tripleCharges (sourceA1936 + difference 2 4) (sourceB1936 + difference 4 2) sourceC1936) = raw27524 := by
      apply Matrix.ext; unfold tripleCharges sourceA1936 sourceB1936 sourceC1936 difference raw27524; decide +kernel
    rw [ha]
    exact (canonical27524 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1936 + difference 2 5) (sourceB1936 + difference 5 2) sourceC1936) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3481) := by
    have ha : (tripleCharges (sourceA1936 + difference 2 5) (sourceB1936 + difference 5 2) sourceC1936) = raw27359 := by
      apply Matrix.ext; unfold tripleCharges sourceA1936 sourceB1936 sourceC1936 difference raw27359; decide +kernel
    rw [ha]
    exact (canonical27359 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1936 + sourceB1936) sourceC1936) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1936 + sourceB1936) sourceC1936) = raw27319 := by
      apply Matrix.ext; unfold doubleCharges sourceA1936 sourceB1936 sourceC1936 raw27319; decide +kernel
    rw [ha]
    exact (canonical27319 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1936 sourceB1936 sourceC1936
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1936, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1937 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1937 : Charge := ![1, 1, -1, 1, 0, -2]
def sourceC1937 : Charge := ![2, 0, 1, -1, -1, -1]
def sourceForm1937 : Integer.Sparse Master := [(Sum.inr 1327, 1), (Sum.inr 2422, 1), (Sum.inr 2429, 1), (Sum.inr 2485, 1), (Sum.inr 2543, 1), (Sum.inr 2924, 1), (Sum.inr 4091, -1)]

theorem sourceEq1937 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1937 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1937 + difference 0 2) (sourceB1937 + difference 2 0) sourceC1937) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2924) := by
    have ha : (tripleCharges (sourceA1937 + difference 0 2) (sourceB1937 + difference 2 0) sourceC1937) = raw27525 := by
      apply Matrix.ext; unfold tripleCharges sourceA1937 sourceB1937 sourceC1937 difference raw27525; decide +kernel
    rw [ha]
    exact (canonical27525 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1937 + difference 1 2) (sourceB1937 + difference 2 1) sourceC1937) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2485) := by
    have ha : (tripleCharges (sourceA1937 + difference 1 2) (sourceB1937 + difference 2 1) sourceC1937) = raw27526 := by
      apply Matrix.ext; unfold tripleCharges sourceA1937 sourceB1937 sourceC1937 difference raw27526; decide +kernel
    rw [ha]
    exact (canonical27526 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1937 + difference 2 2) (sourceB1937 + difference 2 2) sourceC1937) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2543) := by
    have ha : (tripleCharges (sourceA1937 + difference 2 2) (sourceB1937 + difference 2 2) sourceC1937) = raw27527 := by
      apply Matrix.ext; unfold tripleCharges sourceA1937 sourceB1937 sourceC1937 difference raw27527; decide +kernel
    rw [ha]
    exact (canonical27527 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1937 + difference 3 2) (sourceB1937 + difference 2 3) sourceC1937) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2429) := by
    have ha : (tripleCharges (sourceA1937 + difference 3 2) (sourceB1937 + difference 2 3) sourceC1937) = raw27528 := by
      apply Matrix.ext; unfold tripleCharges sourceA1937 sourceB1937 sourceC1937 difference raw27528; decide +kernel
    rw [ha]
    exact (canonical27528 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1937 + difference 4 2) (sourceB1937 + difference 2 4) sourceC1937) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2422) := by
    have ha : (tripleCharges (sourceA1937 + difference 4 2) (sourceB1937 + difference 2 4) sourceC1937) = raw27529 := by
      apply Matrix.ext; unfold tripleCharges sourceA1937 sourceB1937 sourceC1937 difference raw27529; decide +kernel
    rw [ha]
    exact (canonical27529 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1937 + difference 5 2) (sourceB1937 + difference 2 5) sourceC1937) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1327) := by
    have ha : (tripleCharges (sourceA1937 + difference 5 2) (sourceB1937 + difference 2 5) sourceC1937) = raw27530 := by
      apply Matrix.ext; unfold tripleCharges sourceA1937 sourceB1937 sourceC1937 difference raw27530; decide +kernel
    rw [ha]
    exact (canonical27530 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1937 + sourceB1937) sourceC1937) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1937 + sourceB1937) sourceC1937) = raw24552 := by
      apply Matrix.ext; unfold doubleCharges sourceA1937 sourceB1937 sourceC1937 raw24552; decide +kernel
    rw [ha]
    exact (canonical24552 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1937 sourceB1937 sourceC1937
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1937, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1938 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1938 : Charge := ![1, 1, -1, 1, 0, -2]
def sourceC1938 : Charge := ![2, 0, 1, -1, -1, -1]
def sourceForm1938 : Integer.Sparse Master := [(Sum.inr 1150, 1), (Sum.inr 2349, 1), (Sum.inr 2429, 1), (Sum.inr 2543, 2), (Sum.inr 2556, 1), (Sum.inr 4091, -1)]

theorem sourceEq1938 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1938 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1938 + difference 3 0) (sourceB1938 + difference 0 3) sourceC1938) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1150) := by
    have ha : (tripleCharges (sourceA1938 + difference 3 0) (sourceB1938 + difference 0 3) sourceC1938) = raw24557 := by
      apply Matrix.ext; unfold tripleCharges sourceA1938 sourceB1938 sourceC1938 difference raw24557; decide +kernel
    rw [ha]
    exact (canonical24557 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1938 + difference 3 1) (sourceB1938 + difference 1 3) sourceC1938) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2349) := by
    have ha : (tripleCharges (sourceA1938 + difference 3 1) (sourceB1938 + difference 1 3) sourceC1938) = raw27531 := by
      apply Matrix.ext; unfold tripleCharges sourceA1938 sourceB1938 sourceC1938 difference raw27531; decide +kernel
    rw [ha]
    exact (canonical27531 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1938 + difference 3 2) (sourceB1938 + difference 2 3) sourceC1938) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2429) := by
    have ha : (tripleCharges (sourceA1938 + difference 3 2) (sourceB1938 + difference 2 3) sourceC1938) = raw27528 := by
      apply Matrix.ext; unfold tripleCharges sourceA1938 sourceB1938 sourceC1938 difference raw27528; decide +kernel
    rw [ha]
    exact (canonical27528 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1938 + difference 3 3) (sourceB1938 + difference 3 3) sourceC1938) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2543) := by
    have ha : (tripleCharges (sourceA1938 + difference 3 3) (sourceB1938 + difference 3 3) sourceC1938) = raw27527 := by
      apply Matrix.ext; unfold tripleCharges sourceA1938 sourceB1938 sourceC1938 difference raw27527; decide +kernel
    rw [ha]
    exact (canonical27527 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1938 + difference 3 4) (sourceB1938 + difference 4 3) sourceC1938) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2543) := by
    have ha : (tripleCharges (sourceA1938 + difference 3 4) (sourceB1938 + difference 4 3) sourceC1938) = raw27532 := by
      apply Matrix.ext; unfold tripleCharges sourceA1938 sourceB1938 sourceC1938 difference raw27532; decide +kernel
    rw [ha]
    exact (canonical27532 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1938 + difference 3 5) (sourceB1938 + difference 5 3) sourceC1938) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2556) := by
    have ha : (tripleCharges (sourceA1938 + difference 3 5) (sourceB1938 + difference 5 3) sourceC1938) = raw24553 := by
      apply Matrix.ext; unfold tripleCharges sourceA1938 sourceB1938 sourceC1938 difference raw24553; decide +kernel
    rw [ha]
    exact (canonical24553 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1938 + sourceB1938) sourceC1938) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1938 + sourceB1938) sourceC1938) = raw24552 := by
      apply Matrix.ext; unfold doubleCharges sourceA1938 sourceB1938 sourceC1938 raw24552; decide +kernel
    rw [ha]
    exact (canonical24552 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1938 sourceB1938 sourceC1938
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1938, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1939 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1939 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceC1939 : Charge := ![1, 1, -1, 1, 1, -3]
def sourceForm1939 : Integer.Sparse Master := [(Sum.inr 2071, 1), (Sum.inr 2073, 1), (Sum.inr 2077, 1), (Sum.inr 2086, 1), (Sum.inr 2191, 1), (Sum.inr 3558, 1), (Sum.inr 4079, -1)]

theorem sourceEq1939 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1939 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1939 + difference 0 0) (sourceB1939 + difference 0 0) sourceC1939) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2071) := by
    have ha : (tripleCharges (sourceA1939 + difference 0 0) (sourceB1939 + difference 0 0) sourceC1939) = raw27533 := by
      apply Matrix.ext; unfold tripleCharges sourceA1939 sourceB1939 sourceC1939 difference raw27533; decide +kernel
    rw [ha]
    exact (canonical27533 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1939 + difference 0 1) (sourceB1939 + difference 1 0) sourceC1939) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2073) := by
    have ha : (tripleCharges (sourceA1939 + difference 0 1) (sourceB1939 + difference 1 0) sourceC1939) = raw27534 := by
      apply Matrix.ext; unfold tripleCharges sourceA1939 sourceB1939 sourceC1939 difference raw27534; decide +kernel
    rw [ha]
    exact (canonical27534 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1939 + difference 0 2) (sourceB1939 + difference 2 0) sourceC1939) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2086) := by
    have ha : (tripleCharges (sourceA1939 + difference 0 2) (sourceB1939 + difference 2 0) sourceC1939) = raw27535 := by
      apply Matrix.ext; unfold tripleCharges sourceA1939 sourceB1939 sourceC1939 difference raw27535; decide +kernel
    rw [ha]
    exact (canonical27535 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1939 + difference 0 3) (sourceB1939 + difference 3 0) sourceC1939) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2077) := by
    have ha : (tripleCharges (sourceA1939 + difference 0 3) (sourceB1939 + difference 3 0) sourceC1939) = raw27536 := by
      apply Matrix.ext; unfold tripleCharges sourceA1939 sourceB1939 sourceC1939 difference raw27536; decide +kernel
    rw [ha]
    exact (canonical27536 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1939 + difference 0 4) (sourceB1939 + difference 4 0) sourceC1939) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2191) := by
    have ha : (tripleCharges (sourceA1939 + difference 0 4) (sourceB1939 + difference 4 0) sourceC1939) = raw27537 := by
      apply Matrix.ext; unfold tripleCharges sourceA1939 sourceB1939 sourceC1939 difference raw27537; decide +kernel
    rw [ha]
    exact (canonical27537 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1939 + difference 0 5) (sourceB1939 + difference 5 0) sourceC1939) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3558) := by
    have ha : (tripleCharges (sourceA1939 + difference 0 5) (sourceB1939 + difference 5 0) sourceC1939) = raw27538 := by
      apply Matrix.ext; unfold tripleCharges sourceA1939 sourceB1939 sourceC1939 difference raw27538; decide +kernel
    rw [ha]
    exact (canonical27538 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1939 + sourceB1939) sourceC1939) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4079) := by
    have ha : (doubleCharges (sourceA1939 + sourceB1939) sourceC1939) = raw27539 := by
      apply Matrix.ext; unfold doubleCharges sourceA1939 sourceB1939 sourceC1939 raw27539; decide +kernel
    rw [ha]
    exact (canonical27539 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1939 sourceB1939 sourceC1939
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1939, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1940 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1940 : Charge := ![2, 0, 1, -2, 0, -1]
def sourceC1940 : Charge := ![1, 1, -1, 2, -1, -2]
def sourceForm1940 : Integer.Sparse Master := [(Sum.inr 2454, 1), (Sum.inr 2456, 1), (Sum.inr 2462, 1), (Sum.inr 2491, 1), (Sum.inr 2698, 1), (Sum.inr 3796, 1), (Sum.inr 4090, -1)]

theorem sourceEq1940 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1940 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1940 + difference 0 0) (sourceB1940 + difference 0 0) sourceC1940) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2454) := by
    have ha : (tripleCharges (sourceA1940 + difference 0 0) (sourceB1940 + difference 0 0) sourceC1940) = raw27540 := by
      apply Matrix.ext; unfold tripleCharges sourceA1940 sourceB1940 sourceC1940 difference raw27540; decide +kernel
    rw [ha]
    exact (canonical27540 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1940 + difference 0 1) (sourceB1940 + difference 1 0) sourceC1940) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2456) := by
    have ha : (tripleCharges (sourceA1940 + difference 0 1) (sourceB1940 + difference 1 0) sourceC1940) = raw27541 := by
      apply Matrix.ext; unfold tripleCharges sourceA1940 sourceB1940 sourceC1940 difference raw27541; decide +kernel
    rw [ha]
    exact (canonical27541 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1940 + difference 0 2) (sourceB1940 + difference 2 0) sourceC1940) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2491) := by
    have ha : (tripleCharges (sourceA1940 + difference 0 2) (sourceB1940 + difference 2 0) sourceC1940) = raw27542 := by
      apply Matrix.ext; unfold tripleCharges sourceA1940 sourceB1940 sourceC1940 difference raw27542; decide +kernel
    rw [ha]
    exact (canonical27542 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1940 + difference 0 3) (sourceB1940 + difference 3 0) sourceC1940) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2462) := by
    have ha : (tripleCharges (sourceA1940 + difference 0 3) (sourceB1940 + difference 3 0) sourceC1940) = raw27543 := by
      apply Matrix.ext; unfold tripleCharges sourceA1940 sourceB1940 sourceC1940 difference raw27543; decide +kernel
    rw [ha]
    exact (canonical27543 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1940 + difference 0 4) (sourceB1940 + difference 4 0) sourceC1940) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2698) := by
    have ha : (tripleCharges (sourceA1940 + difference 0 4) (sourceB1940 + difference 4 0) sourceC1940) = raw27544 := by
      apply Matrix.ext; unfold tripleCharges sourceA1940 sourceB1940 sourceC1940 difference raw27544; decide +kernel
    rw [ha]
    exact (canonical27544 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1940 + difference 0 5) (sourceB1940 + difference 5 0) sourceC1940) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3796) := by
    have ha : (tripleCharges (sourceA1940 + difference 0 5) (sourceB1940 + difference 5 0) sourceC1940) = raw27545 := by
      apply Matrix.ext; unfold tripleCharges sourceA1940 sourceB1940 sourceC1940 difference raw27545; decide +kernel
    rw [ha]
    exact (canonical27545 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1940 + sourceB1940) sourceC1940) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (doubleCharges (sourceA1940 + sourceB1940) sourceC1940) = raw27546 := by
      apply Matrix.ext; unfold doubleCharges sourceA1940 sourceB1940 sourceC1940 raw27546; decide +kernel
    rw [ha]
    exact (canonical27546 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1940 sourceB1940 sourceC1940
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1940, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1941 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1941 : Charge := ![2, 0, 1, -2, 0, -1]
def sourceC1941 : Charge := ![1, 1, -1, 2, -1, -2]
def sourceForm1941 : Integer.Sparse Master := [(Sum.inr 2454, 1), (Sum.inr 2715, 1), (Sum.inr 2905, 1), (Sum.inr 2908, 1), (Sum.inr 3016, 1), (Sum.inr 3796, 1), (Sum.inr 4090, -1)]

theorem sourceEq1941 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1941 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1941 + difference 0 5) (sourceB1941 + difference 5 0) sourceC1941) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3796) := by
    have ha : (tripleCharges (sourceA1941 + difference 0 5) (sourceB1941 + difference 5 0) sourceC1941) = raw27545 := by
      apply Matrix.ext; unfold tripleCharges sourceA1941 sourceB1941 sourceC1941 difference raw27545; decide +kernel
    rw [ha]
    exact (canonical27545 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1941 + difference 1 5) (sourceB1941 + difference 5 1) sourceC1941) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3016) := by
    have ha : (tripleCharges (sourceA1941 + difference 1 5) (sourceB1941 + difference 5 1) sourceC1941) = raw27547 := by
      apply Matrix.ext; unfold tripleCharges sourceA1941 sourceB1941 sourceC1941 difference raw27547; decide +kernel
    rw [ha]
    exact (canonical27547 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1941 + difference 2 5) (sourceB1941 + difference 5 2) sourceC1941) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2908) := by
    have ha : (tripleCharges (sourceA1941 + difference 2 5) (sourceB1941 + difference 5 2) sourceC1941) = raw27548 := by
      apply Matrix.ext; unfold tripleCharges sourceA1941 sourceB1941 sourceC1941 difference raw27548; decide +kernel
    rw [ha]
    exact (canonical27548 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1941 + difference 3 5) (sourceB1941 + difference 5 3) sourceC1941) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2715) := by
    have ha : (tripleCharges (sourceA1941 + difference 3 5) (sourceB1941 + difference 5 3) sourceC1941) = raw27549 := by
      apply Matrix.ext; unfold tripleCharges sourceA1941 sourceB1941 sourceC1941 difference raw27549; decide +kernel
    rw [ha]
    exact (canonical27549 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1941 + difference 4 5) (sourceB1941 + difference 5 4) sourceC1941) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2905) := by
    have ha : (tripleCharges (sourceA1941 + difference 4 5) (sourceB1941 + difference 5 4) sourceC1941) = raw27550 := by
      apply Matrix.ext; unfold tripleCharges sourceA1941 sourceB1941 sourceC1941 difference raw27550; decide +kernel
    rw [ha]
    exact (canonical27550 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1941 + difference 5 5) (sourceB1941 + difference 5 5) sourceC1941) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2454) := by
    have ha : (tripleCharges (sourceA1941 + difference 5 5) (sourceB1941 + difference 5 5) sourceC1941) = raw27540 := by
      apply Matrix.ext; unfold tripleCharges sourceA1941 sourceB1941 sourceC1941 difference raw27540; decide +kernel
    rw [ha]
    exact (canonical27540 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1941 + sourceB1941) sourceC1941) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (doubleCharges (sourceA1941 + sourceB1941) sourceC1941) = raw27546 := by
      apply Matrix.ext; unfold doubleCharges sourceA1941 sourceB1941 sourceC1941 raw27546; decide +kernel
    rw [ha]
    exact (canonical27546 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1941 sourceB1941 sourceC1941
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1941, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1942 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1942 : Charge := ![2, 0, 1, -2, -1, 0]
def sourceC1942 : Charge := ![1, 1, -1, 2, 0, -3]
def sourceForm1942 : Integer.Sparse Master := [(Sum.inr 1992, 1), (Sum.inr 1994, 1), (Sum.inr 2000, 1), (Sum.inr 2031, 1), (Sum.inr 2216, 1), (Sum.inr 3517, 1), (Sum.inr 4080, -1)]

theorem sourceEq1942 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1942 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1942 + difference 0 0) (sourceB1942 + difference 0 0) sourceC1942) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1992) := by
    have ha : (tripleCharges (sourceA1942 + difference 0 0) (sourceB1942 + difference 0 0) sourceC1942) = raw27551 := by
      apply Matrix.ext; unfold tripleCharges sourceA1942 sourceB1942 sourceC1942 difference raw27551; decide +kernel
    rw [ha]
    exact (canonical27551 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1942 + difference 0 1) (sourceB1942 + difference 1 0) sourceC1942) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1994) := by
    have ha : (tripleCharges (sourceA1942 + difference 0 1) (sourceB1942 + difference 1 0) sourceC1942) = raw27552 := by
      apply Matrix.ext; unfold tripleCharges sourceA1942 sourceB1942 sourceC1942 difference raw27552; decide +kernel
    rw [ha]
    exact (canonical27552 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1942 + difference 0 2) (sourceB1942 + difference 2 0) sourceC1942) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2031) := by
    have ha : (tripleCharges (sourceA1942 + difference 0 2) (sourceB1942 + difference 2 0) sourceC1942) = raw27553 := by
      apply Matrix.ext; unfold tripleCharges sourceA1942 sourceB1942 sourceC1942 difference raw27553; decide +kernel
    rw [ha]
    exact (canonical27553 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1942 + difference 0 3) (sourceB1942 + difference 3 0) sourceC1942) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2000) := by
    have ha : (tripleCharges (sourceA1942 + difference 0 3) (sourceB1942 + difference 3 0) sourceC1942) = raw27554 := by
      apply Matrix.ext; unfold tripleCharges sourceA1942 sourceB1942 sourceC1942 difference raw27554; decide +kernel
    rw [ha]
    exact (canonical27554 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1942 + difference 0 4) (sourceB1942 + difference 4 0) sourceC1942) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2216) := by
    have ha : (tripleCharges (sourceA1942 + difference 0 4) (sourceB1942 + difference 4 0) sourceC1942) = raw27555 := by
      apply Matrix.ext; unfold tripleCharges sourceA1942 sourceB1942 sourceC1942 difference raw27555; decide +kernel
    rw [ha]
    exact (canonical27555 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1942 + difference 0 5) (sourceB1942 + difference 5 0) sourceC1942) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3517) := by
    have ha : (tripleCharges (sourceA1942 + difference 0 5) (sourceB1942 + difference 5 0) sourceC1942) = raw27556 := by
      apply Matrix.ext; unfold tripleCharges sourceA1942 sourceB1942 sourceC1942 difference raw27556; decide +kernel
    rw [ha]
    exact (canonical27556 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1942 + sourceB1942) sourceC1942) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1942 + sourceB1942) sourceC1942) = raw27557 := by
      apply Matrix.ext; unfold doubleCharges sourceA1942 sourceB1942 sourceC1942 raw27557; decide +kernel
    rw [ha]
    exact (canonical27557 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1942 sourceB1942 sourceC1942
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1942, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1943 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1943 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1943 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceForm1943 : Integer.Sparse Master := [(Sum.inr 4551, 4), (Sum.inr 4555, 1), (Sum.inr 4559, 2), (Sum.inr 4625, 2), (Sum.inr 4970, 4), (Sum.inr 4979, 1), (Sum.inr 5113, 2), (Sum.inr 5168, 4), (Sum.inr 5171, 4), (Sum.inr 5176, 2), (Sum.inr 5308, 2), (Sum.inr 5312, 1), (Sum.inr 5441, 1)]

theorem sourceEq1943 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1943 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1943 + difference 0 1) (sourceB1943 + difference 1 0) sourceC1943) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5176) := by
    have ha : (tripleCharges (sourceA1943 + difference 0 1) (sourceB1943 + difference 1 0) sourceC1943) = raw18310 := by
      apply Matrix.ext; unfold tripleCharges sourceA1943 sourceB1943 sourceC1943 difference raw18310; decide +kernel
    rw [ha]
    exact (canonical18310 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1943 + difference 0 2) (sourceB1943 + difference 2 0) sourceC1943) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5168) := by
    have ha : (tripleCharges (sourceA1943 + difference 0 2) (sourceB1943 + difference 2 0) sourceC1943) = raw18311 := by
      apply Matrix.ext; unfold tripleCharges sourceA1943 sourceB1943 sourceC1943 difference raw18311; decide +kernel
    rw [ha]
    exact (canonical18311 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1943 + difference 0 3) (sourceB1943 + difference 3 0) sourceC1943) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5168) := by
    have ha : (tripleCharges (sourceA1943 + difference 0 3) (sourceB1943 + difference 3 0) sourceC1943) = raw18312 := by
      apply Matrix.ext; unfold tripleCharges sourceA1943 sourceB1943 sourceC1943 difference raw18312; decide +kernel
    rw [ha]
    exact (canonical18312 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1943 + difference 0 4) (sourceB1943 + difference 4 0) sourceC1943) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5308) := by
    have ha : (tripleCharges (sourceA1943 + difference 0 4) (sourceB1943 + difference 4 0) sourceC1943) = raw5058 := by
      apply Matrix.ext; unfold tripleCharges sourceA1943 sourceB1943 sourceC1943 difference raw5058; decide +kernel
    rw [ha]
    exact (canonical5058 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1943 + difference 0 5) (sourceB1943 + difference 5 0) sourceC1943) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5441) := by
    have ha : (tripleCharges (sourceA1943 + difference 0 5) (sourceB1943 + difference 5 0) sourceC1943) = raw10216 := by
      apply Matrix.ext; unfold tripleCharges sourceA1943 sourceB1943 sourceC1943 difference raw10216; decide +kernel
    rw [ha]
    exact (canonical10216 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1943 + difference 1 0) (sourceB1943 + difference 0 1) sourceC1943) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4625) := by
    have ha : (tripleCharges (sourceA1943 + difference 1 0) (sourceB1943 + difference 0 1) sourceC1943) = raw5078 := by
      apply Matrix.ext; unfold tripleCharges sourceA1943 sourceB1943 sourceC1943 difference raw5078; decide +kernel
    rw [ha]
    exact (canonical5078 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1943 + difference 1 2) (sourceB1943 + difference 2 1) sourceC1943) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5171) := by
    have ha : (tripleCharges (sourceA1943 + difference 1 2) (sourceB1943 + difference 2 1) sourceC1943) = raw5080 := by
      apply Matrix.ext; unfold tripleCharges sourceA1943 sourceB1943 sourceC1943 difference raw5080; decide +kernel
    rw [ha]
    exact (canonical5080 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1943 + difference 1 3) (sourceB1943 + difference 3 1) sourceC1943) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5171) := by
    have ha : (tripleCharges (sourceA1943 + difference 1 3) (sourceB1943 + difference 3 1) sourceC1943) = raw5081 := by
      apply Matrix.ext; unfold tripleCharges sourceA1943 sourceB1943 sourceC1943 difference raw5081; decide +kernel
    rw [ha]
    exact (canonical5081 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1943 + difference 1 4) (sourceB1943 + difference 4 1) sourceC1943) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5312) := by
    have ha : (tripleCharges (sourceA1943 + difference 1 4) (sourceB1943 + difference 4 1) sourceC1943) = raw10237 := by
      apply Matrix.ext; unfold tripleCharges sourceA1943 sourceB1943 sourceC1943 difference raw10237; decide +kernel
    rw [ha]
    exact (canonical10237 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1943 + difference 1 5) (sourceB1943 + difference 5 1) sourceC1943) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5308) := by
    have ha : (tripleCharges (sourceA1943 + difference 1 5) (sourceB1943 + difference 5 1) sourceC1943) = raw5082 := by
      apply Matrix.ext; unfold tripleCharges sourceA1943 sourceB1943 sourceC1943 difference raw5082; decide +kernel
    rw [ha]
    exact (canonical5082 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1943 + difference 2 0) (sourceB1943 + difference 0 2) sourceC1943) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4551) := by
    have ha : (tripleCharges (sourceA1943 + difference 2 0) (sourceB1943 + difference 0 2) sourceC1943) = raw20355 := by
      apply Matrix.ext; unfold tripleCharges sourceA1943 sourceB1943 sourceC1943 difference raw20355; decide +kernel
    rw [ha]
    exact (canonical20355 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1943 + difference 2 1) (sourceB1943 + difference 1 2) sourceC1943) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4970) := by
    have ha : (tripleCharges (sourceA1943 + difference 2 1) (sourceB1943 + difference 1 2) sourceC1943) = raw27558 := by
      apply Matrix.ext; unfold tripleCharges sourceA1943 sourceB1943 sourceC1943 difference raw27558; decide +kernel
    rw [ha]
    exact (canonical27558 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1943 + difference 2 3) (sourceB1943 + difference 3 2) sourceC1943) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5113) := by
    have ha : (tripleCharges (sourceA1943 + difference 2 3) (sourceB1943 + difference 3 2) sourceC1943) = raw27559 := by
      apply Matrix.ext; unfold tripleCharges sourceA1943 sourceB1943 sourceC1943 difference raw27559; decide +kernel
    rw [ha]
    exact (canonical27559 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1943 + difference 2 4) (sourceB1943 + difference 4 2) sourceC1943) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5171) := by
    have ha : (tripleCharges (sourceA1943 + difference 2 4) (sourceB1943 + difference 4 2) sourceC1943) = raw5069 := by
      apply Matrix.ext; unfold tripleCharges sourceA1943 sourceB1943 sourceC1943 difference raw5069; decide +kernel
    rw [ha]
    exact (canonical5069 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1943 + difference 2 5) (sourceB1943 + difference 5 2) sourceC1943) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5168) := by
    have ha : (tripleCharges (sourceA1943 + difference 2 5) (sourceB1943 + difference 5 2) sourceC1943) = raw10225 := by
      apply Matrix.ext; unfold tripleCharges sourceA1943 sourceB1943 sourceC1943 difference raw10225; decide +kernel
    rw [ha]
    exact (canonical10225 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1943 + difference 3 0) (sourceB1943 + difference 0 3) sourceC1943) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4551) := by
    have ha : (tripleCharges (sourceA1943 + difference 3 0) (sourceB1943 + difference 0 3) sourceC1943) = raw20358 := by
      apply Matrix.ext; unfold tripleCharges sourceA1943 sourceB1943 sourceC1943 difference raw20358; decide +kernel
    rw [ha]
    exact (canonical20358 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1943 + difference 3 1) (sourceB1943 + difference 1 3) sourceC1943) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4970) := by
    have ha : (tripleCharges (sourceA1943 + difference 3 1) (sourceB1943 + difference 1 3) sourceC1943) = raw27560 := by
      apply Matrix.ext; unfold tripleCharges sourceA1943 sourceB1943 sourceC1943 difference raw27560; decide +kernel
    rw [ha]
    exact (canonical27560 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1943 + difference 3 2) (sourceB1943 + difference 2 3) sourceC1943) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5113) := by
    have ha : (tripleCharges (sourceA1943 + difference 3 2) (sourceB1943 + difference 2 3) sourceC1943) = raw27561 := by
      apply Matrix.ext; unfold tripleCharges sourceA1943 sourceB1943 sourceC1943 difference raw27561; decide +kernel
    rw [ha]
    exact (canonical27561 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1943 + difference 3 4) (sourceB1943 + difference 4 3) sourceC1943) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5171) := by
    have ha : (tripleCharges (sourceA1943 + difference 3 4) (sourceB1943 + difference 4 3) sourceC1943) = raw5074 := by
      apply Matrix.ext; unfold tripleCharges sourceA1943 sourceB1943 sourceC1943 difference raw5074; decide +kernel
    rw [ha]
    exact (canonical5074 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1943 + difference 3 5) (sourceB1943 + difference 5 3) sourceC1943) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5168) := by
    have ha : (tripleCharges (sourceA1943 + difference 3 5) (sourceB1943 + difference 5 3) sourceC1943) = raw10229 := by
      apply Matrix.ext; unfold tripleCharges sourceA1943 sourceB1943 sourceC1943 difference raw10229; decide +kernel
    rw [ha]
    exact (canonical10229 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1943 + difference 4 0) (sourceB1943 + difference 0 4) sourceC1943) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4559) := by
    have ha : (tripleCharges (sourceA1943 + difference 4 0) (sourceB1943 + difference 0 4) sourceC1943) = raw20361 := by
      apply Matrix.ext; unfold tripleCharges sourceA1943 sourceB1943 sourceC1943 difference raw20361; decide +kernel
    rw [ha]
    exact (canonical20361 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1943 + difference 4 1) (sourceB1943 + difference 1 4) sourceC1943) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4979) := by
    have ha : (tripleCharges (sourceA1943 + difference 4 1) (sourceB1943 + difference 1 4) sourceC1943) = raw27562 := by
      apply Matrix.ext; unfold tripleCharges sourceA1943 sourceB1943 sourceC1943 difference raw27562; decide +kernel
    rw [ha]
    exact (canonical27562 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1943 + difference 4 2) (sourceB1943 + difference 2 4) sourceC1943) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4970) := by
    have ha : (tripleCharges (sourceA1943 + difference 4 2) (sourceB1943 + difference 2 4) sourceC1943) = raw27563 := by
      apply Matrix.ext; unfold tripleCharges sourceA1943 sourceB1943 sourceC1943 difference raw27563; decide +kernel
    rw [ha]
    exact (canonical27563 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1943 + difference 4 3) (sourceB1943 + difference 3 4) sourceC1943) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4970) := by
    have ha : (tripleCharges (sourceA1943 + difference 4 3) (sourceB1943 + difference 3 4) sourceC1943) = raw27564 := by
      apply Matrix.ext; unfold tripleCharges sourceA1943 sourceB1943 sourceC1943 difference raw27564; decide +kernel
    rw [ha]
    exact (canonical27564 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1943 + difference 4 5) (sourceB1943 + difference 5 4) sourceC1943) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5176) := by
    have ha : (tripleCharges (sourceA1943 + difference 4 5) (sourceB1943 + difference 5 4) sourceC1943) = raw10233 := by
      apply Matrix.ext; unfold tripleCharges sourceA1943 sourceB1943 sourceC1943 difference raw10233; decide +kernel
    rw [ha]
    exact (canonical10233 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1943 + difference 5 0) (sourceB1943 + difference 0 5) sourceC1943) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4555) := by
    have ha : (tripleCharges (sourceA1943 + difference 5 0) (sourceB1943 + difference 0 5) sourceC1943) = raw19517 := by
      apply Matrix.ext; unfold tripleCharges sourceA1943 sourceB1943 sourceC1943 difference raw19517; decide +kernel
    rw [ha]
    exact (canonical19517 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1943 + difference 5 1) (sourceB1943 + difference 1 5) sourceC1943) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4559) := by
    have ha : (tripleCharges (sourceA1943 + difference 5 1) (sourceB1943 + difference 1 5) sourceC1943) = raw27565 := by
      apply Matrix.ext; unfold tripleCharges sourceA1943 sourceB1943 sourceC1943 difference raw27565; decide +kernel
    rw [ha]
    exact (canonical27565 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1943 + difference 5 2) (sourceB1943 + difference 2 5) sourceC1943) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4551) := by
    have ha : (tripleCharges (sourceA1943 + difference 5 2) (sourceB1943 + difference 2 5) sourceC1943) = raw27566 := by
      apply Matrix.ext; unfold tripleCharges sourceA1943 sourceB1943 sourceC1943 difference raw27566; decide +kernel
    rw [ha]
    exact (canonical27566 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1943 + difference 5 3) (sourceB1943 + difference 3 5) sourceC1943) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4551) := by
    have ha : (tripleCharges (sourceA1943 + difference 5 3) (sourceB1943 + difference 3 5) sourceC1943) = raw27567 := by
      apply Matrix.ext; unfold tripleCharges sourceA1943 sourceB1943 sourceC1943 difference raw27567; decide +kernel
    rw [ha]
    exact (canonical27567 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1943 + difference 5 4) (sourceB1943 + difference 4 5) sourceC1943) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4625) := by
    have ha : (tripleCharges (sourceA1943 + difference 5 4) (sourceB1943 + difference 4 5) sourceC1943) = raw5084 := by
      apply Matrix.ext; unfold tripleCharges sourceA1943 sourceB1943 sourceC1943 difference raw5084; decide +kernel
    rw [ha]
    exact (canonical5084 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1943 sourceB1943 sourceC1943
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1943, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1944 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1944 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1944 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceForm1944 : Integer.Sparse Master := [(Sum.inr 1136, 4), (Sum.inr 1140, 1), (Sum.inr 1145, 2), (Sum.inr 1307, 2), (Sum.inr 2815, 4), (Sum.inr 2820, 1), (Sum.inr 2894, 2), (Sum.inr 2963, 4), (Sum.inr 2965, 4), (Sum.inr 2968, 2), (Sum.inr 3124, 2), (Sum.inr 3126, 1), (Sum.inr 4037, 1)]

theorem sourceEq1944 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1944 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1944 + difference 0 1) (sourceB1944 + difference 1 0) sourceC1944) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2968) := by
    have ha : (tripleCharges (sourceA1944 + difference 0 1) (sourceB1944 + difference 1 0) sourceC1944) = raw27568 := by
      apply Matrix.ext; unfold tripleCharges sourceA1944 sourceB1944 sourceC1944 difference raw27568; decide +kernel
    rw [ha]
    exact (canonical27568 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1944 + difference 0 2) (sourceB1944 + difference 2 0) sourceC1944) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2963) := by
    have ha : (tripleCharges (sourceA1944 + difference 0 2) (sourceB1944 + difference 2 0) sourceC1944) = raw27569 := by
      apply Matrix.ext; unfold tripleCharges sourceA1944 sourceB1944 sourceC1944 difference raw27569; decide +kernel
    rw [ha]
    exact (canonical27569 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1944 + difference 0 3) (sourceB1944 + difference 3 0) sourceC1944) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2963) := by
    have ha : (tripleCharges (sourceA1944 + difference 0 3) (sourceB1944 + difference 3 0) sourceC1944) = raw27570 := by
      apply Matrix.ext; unfold tripleCharges sourceA1944 sourceB1944 sourceC1944 difference raw27570; decide +kernel
    rw [ha]
    exact (canonical27570 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1944 + difference 0 4) (sourceB1944 + difference 4 0) sourceC1944) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3124) := by
    have ha : (tripleCharges (sourceA1944 + difference 0 4) (sourceB1944 + difference 4 0) sourceC1944) = raw27571 := by
      apply Matrix.ext; unfold tripleCharges sourceA1944 sourceB1944 sourceC1944 difference raw27571; decide +kernel
    rw [ha]
    exact (canonical27571 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1944 + difference 0 5) (sourceB1944 + difference 5 0) sourceC1944) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4037) := by
    have ha : (tripleCharges (sourceA1944 + difference 0 5) (sourceB1944 + difference 5 0) sourceC1944) = raw27572 := by
      apply Matrix.ext; unfold tripleCharges sourceA1944 sourceB1944 sourceC1944 difference raw27572; decide +kernel
    rw [ha]
    exact (canonical27572 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1944 + difference 1 0) (sourceB1944 + difference 0 1) sourceC1944) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1307) := by
    have ha : (tripleCharges (sourceA1944 + difference 1 0) (sourceB1944 + difference 0 1) sourceC1944) = raw19549 := by
      apply Matrix.ext; unfold tripleCharges sourceA1944 sourceB1944 sourceC1944 difference raw19549; decide +kernel
    rw [ha]
    exact (canonical19549 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1944 + difference 1 2) (sourceB1944 + difference 2 1) sourceC1944) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2965) := by
    have ha : (tripleCharges (sourceA1944 + difference 1 2) (sourceB1944 + difference 2 1) sourceC1944) = raw20365 := by
      apply Matrix.ext; unfold tripleCharges sourceA1944 sourceB1944 sourceC1944 difference raw20365; decide +kernel
    rw [ha]
    exact (canonical20365 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1944 + difference 1 3) (sourceB1944 + difference 3 1) sourceC1944) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2965) := by
    have ha : (tripleCharges (sourceA1944 + difference 1 3) (sourceB1944 + difference 3 1) sourceC1944) = raw20366 := by
      apply Matrix.ext; unfold tripleCharges sourceA1944 sourceB1944 sourceC1944 difference raw20366; decide +kernel
    rw [ha]
    exact (canonical20366 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1944 + difference 1 4) (sourceB1944 + difference 4 1) sourceC1944) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3126) := by
    have ha : (tripleCharges (sourceA1944 + difference 1 4) (sourceB1944 + difference 4 1) sourceC1944) = raw19529 := by
      apply Matrix.ext; unfold tripleCharges sourceA1944 sourceB1944 sourceC1944 difference raw19529; decide +kernel
    rw [ha]
    exact (canonical19529 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1944 + difference 1 5) (sourceB1944 + difference 5 1) sourceC1944) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3124) := by
    have ha : (tripleCharges (sourceA1944 + difference 1 5) (sourceB1944 + difference 5 1) sourceC1944) = raw12129 := by
      apply Matrix.ext; unfold tripleCharges sourceA1944 sourceB1944 sourceC1944 difference raw12129; decide +kernel
    rw [ha]
    exact (canonical12129 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1944 + difference 2 0) (sourceB1944 + difference 0 2) sourceC1944) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1136) := by
    have ha : (tripleCharges (sourceA1944 + difference 2 0) (sourceB1944 + difference 0 2) sourceC1944) = raw20372 := by
      apply Matrix.ext; unfold tripleCharges sourceA1944 sourceB1944 sourceC1944 difference raw20372; decide +kernel
    rw [ha]
    exact (canonical20372 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1944 + difference 2 1) (sourceB1944 + difference 1 2) sourceC1944) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2815) := by
    have ha : (tripleCharges (sourceA1944 + difference 2 1) (sourceB1944 + difference 1 2) sourceC1944) = raw27573 := by
      apply Matrix.ext; unfold tripleCharges sourceA1944 sourceB1944 sourceC1944 difference raw27573; decide +kernel
    rw [ha]
    exact (canonical27573 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1944 + difference 2 3) (sourceB1944 + difference 3 2) sourceC1944) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2894) := by
    have ha : (tripleCharges (sourceA1944 + difference 2 3) (sourceB1944 + difference 3 2) sourceC1944) = raw27574 := by
      apply Matrix.ext; unfold tripleCharges sourceA1944 sourceB1944 sourceC1944 difference raw27574; decide +kernel
    rw [ha]
    exact (canonical27574 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1944 + difference 2 4) (sourceB1944 + difference 4 2) sourceC1944) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2965) := by
    have ha : (tripleCharges (sourceA1944 + difference 2 4) (sourceB1944 + difference 4 2) sourceC1944) = raw27575 := by
      apply Matrix.ext; unfold tripleCharges sourceA1944 sourceB1944 sourceC1944 difference raw27575; decide +kernel
    rw [ha]
    exact (canonical27575 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1944 + difference 2 5) (sourceB1944 + difference 5 2) sourceC1944) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2963) := by
    have ha : (tripleCharges (sourceA1944 + difference 2 5) (sourceB1944 + difference 5 2) sourceC1944) = raw27576 := by
      apply Matrix.ext; unfold tripleCharges sourceA1944 sourceB1944 sourceC1944 difference raw27576; decide +kernel
    rw [ha]
    exact (canonical27576 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1944 + difference 3 0) (sourceB1944 + difference 0 3) sourceC1944) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1136) := by
    have ha : (tripleCharges (sourceA1944 + difference 3 0) (sourceB1944 + difference 0 3) sourceC1944) = raw20376 := by
      apply Matrix.ext; unfold tripleCharges sourceA1944 sourceB1944 sourceC1944 difference raw20376; decide +kernel
    rw [ha]
    exact (canonical20376 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1944 + difference 3 1) (sourceB1944 + difference 1 3) sourceC1944) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2815) := by
    have ha : (tripleCharges (sourceA1944 + difference 3 1) (sourceB1944 + difference 1 3) sourceC1944) = raw27577 := by
      apply Matrix.ext; unfold tripleCharges sourceA1944 sourceB1944 sourceC1944 difference raw27577; decide +kernel
    rw [ha]
    exact (canonical27577 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1944 + difference 3 2) (sourceB1944 + difference 2 3) sourceC1944) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2894) := by
    have ha : (tripleCharges (sourceA1944 + difference 3 2) (sourceB1944 + difference 2 3) sourceC1944) = raw27578 := by
      apply Matrix.ext; unfold tripleCharges sourceA1944 sourceB1944 sourceC1944 difference raw27578; decide +kernel
    rw [ha]
    exact (canonical27578 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1944 + difference 3 4) (sourceB1944 + difference 4 3) sourceC1944) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2965) := by
    have ha : (tripleCharges (sourceA1944 + difference 3 4) (sourceB1944 + difference 4 3) sourceC1944) = raw27579 := by
      apply Matrix.ext; unfold tripleCharges sourceA1944 sourceB1944 sourceC1944 difference raw27579; decide +kernel
    rw [ha]
    exact (canonical27579 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1944 + difference 3 5) (sourceB1944 + difference 5 3) sourceC1944) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2963) := by
    have ha : (tripleCharges (sourceA1944 + difference 3 5) (sourceB1944 + difference 5 3) sourceC1944) = raw12127 := by
      apply Matrix.ext; unfold tripleCharges sourceA1944 sourceB1944 sourceC1944 difference raw12127; decide +kernel
    rw [ha]
    exact (canonical12127 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1944 + difference 4 0) (sourceB1944 + difference 0 4) sourceC1944) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1145) := by
    have ha : (tripleCharges (sourceA1944 + difference 4 0) (sourceB1944 + difference 0 4) sourceC1944) = raw20379 := by
      apply Matrix.ext; unfold tripleCharges sourceA1944 sourceB1944 sourceC1944 difference raw20379; decide +kernel
    rw [ha]
    exact (canonical20379 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1944 + difference 4 1) (sourceB1944 + difference 1 4) sourceC1944) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2820) := by
    have ha : (tripleCharges (sourceA1944 + difference 4 1) (sourceB1944 + difference 1 4) sourceC1944) = raw27580 := by
      apply Matrix.ext; unfold tripleCharges sourceA1944 sourceB1944 sourceC1944 difference raw27580; decide +kernel
    rw [ha]
    exact (canonical27580 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1944 + difference 4 2) (sourceB1944 + difference 2 4) sourceC1944) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2815) := by
    have ha : (tripleCharges (sourceA1944 + difference 4 2) (sourceB1944 + difference 2 4) sourceC1944) = raw27581 := by
      apply Matrix.ext; unfold tripleCharges sourceA1944 sourceB1944 sourceC1944 difference raw27581; decide +kernel
    rw [ha]
    exact (canonical27581 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1944 + difference 4 3) (sourceB1944 + difference 3 4) sourceC1944) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2815) := by
    have ha : (tripleCharges (sourceA1944 + difference 4 3) (sourceB1944 + difference 3 4) sourceC1944) = raw27582 := by
      apply Matrix.ext; unfold tripleCharges sourceA1944 sourceB1944 sourceC1944 difference raw27582; decide +kernel
    rw [ha]
    exact (canonical27582 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1944 + difference 4 5) (sourceB1944 + difference 5 4) sourceC1944) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2968) := by
    have ha : (tripleCharges (sourceA1944 + difference 4 5) (sourceB1944 + difference 5 4) sourceC1944) = raw22487 := by
      apply Matrix.ext; unfold tripleCharges sourceA1944 sourceB1944 sourceC1944 difference raw22487; decide +kernel
    rw [ha]
    exact (canonical22487 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1944 + difference 5 0) (sourceB1944 + difference 0 5) sourceC1944) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1140) := by
    have ha : (tripleCharges (sourceA1944 + difference 5 0) (sourceB1944 + difference 0 5) sourceC1944) = raw19546 := by
      apply Matrix.ext; unfold tripleCharges sourceA1944 sourceB1944 sourceC1944 difference raw19546; decide +kernel
    rw [ha]
    exact (canonical19546 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1944 + difference 5 1) (sourceB1944 + difference 1 5) sourceC1944) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1145) := by
    have ha : (tripleCharges (sourceA1944 + difference 5 1) (sourceB1944 + difference 1 5) sourceC1944) = raw27583 := by
      apply Matrix.ext; unfold tripleCharges sourceA1944 sourceB1944 sourceC1944 difference raw27583; decide +kernel
    rw [ha]
    exact (canonical27583 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1944 + difference 5 2) (sourceB1944 + difference 2 5) sourceC1944) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1136) := by
    have ha : (tripleCharges (sourceA1944 + difference 5 2) (sourceB1944 + difference 2 5) sourceC1944) = raw27584 := by
      apply Matrix.ext; unfold tripleCharges sourceA1944 sourceB1944 sourceC1944 difference raw27584; decide +kernel
    rw [ha]
    exact (canonical27584 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1944 + difference 5 3) (sourceB1944 + difference 3 5) sourceC1944) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1136) := by
    have ha : (tripleCharges (sourceA1944 + difference 5 3) (sourceB1944 + difference 3 5) sourceC1944) = raw27585 := by
      apply Matrix.ext; unfold tripleCharges sourceA1944 sourceB1944 sourceC1944 difference raw27585; decide +kernel
    rw [ha]
    exact (canonical27585 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1944 + difference 5 4) (sourceB1944 + difference 4 5) sourceC1944) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1307) := by
    have ha : (tripleCharges (sourceA1944 + difference 5 4) (sourceB1944 + difference 4 5) sourceC1944) = raw19525 := by
      apply Matrix.ext; unfold tripleCharges sourceA1944 sourceB1944 sourceC1944 difference raw19525; decide +kernel
    rw [ha]
    exact (canonical19525 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1944 sourceB1944 sourceC1944
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1944, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1945 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1945 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1945 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceForm1945 : Integer.Sparse Master := [(Sum.inr 4346, 4), (Sum.inr 4350, 1), (Sum.inr 4360, 2), (Sum.inr 4460, 2), (Sum.inr 4943, 4), (Sum.inr 4952, 1), (Sum.inr 5033, 2), (Sum.inr 5075, 4), (Sum.inr 5169, 4), (Sum.inr 5177, 2), (Sum.inr 5261, 1), (Sum.inr 5293, 2), (Sum.inr 5487, 1)]

theorem sourceEq1945 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1945 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1945 + difference 0 1) (sourceB1945 + difference 1 0) sourceC1945) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5177) := by
    have ha : (tripleCharges (sourceA1945 + difference 0 1) (sourceB1945 + difference 1 0) sourceC1945) = raw17680 := by
      apply Matrix.ext; unfold tripleCharges sourceA1945 sourceB1945 sourceC1945 difference raw17680; decide +kernel
    rw [ha]
    exact (canonical17680 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1945 + difference 0 2) (sourceB1945 + difference 2 0) sourceC1945) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA1945 + difference 0 2) (sourceB1945 + difference 2 0) sourceC1945) = raw17681 := by
      apply Matrix.ext; unfold tripleCharges sourceA1945 sourceB1945 sourceC1945 difference raw17681; decide +kernel
    rw [ha]
    exact (canonical17681 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1945 + difference 0 3) (sourceB1945 + difference 3 0) sourceC1945) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA1945 + difference 0 3) (sourceB1945 + difference 3 0) sourceC1945) = raw17682 := by
      apply Matrix.ext; unfold tripleCharges sourceA1945 sourceB1945 sourceC1945 difference raw17682; decide +kernel
    rw [ha]
    exact (canonical17682 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1945 + difference 0 4) (sourceB1945 + difference 4 0) sourceC1945) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA1945 + difference 0 4) (sourceB1945 + difference 4 0) sourceC1945) = raw2777 := by
      apply Matrix.ext; unfold tripleCharges sourceA1945 sourceB1945 sourceC1945 difference raw2777; decide +kernel
    rw [ha]
    exact (canonical2777 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1945 + difference 0 5) (sourceB1945 + difference 5 0) sourceC1945) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5487) := by
    have ha : (tripleCharges (sourceA1945 + difference 0 5) (sourceB1945 + difference 5 0) sourceC1945) = raw2772 := by
      apply Matrix.ext; unfold tripleCharges sourceA1945 sourceB1945 sourceC1945 difference raw2772; decide +kernel
    rw [ha]
    exact (canonical2772 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1945 + difference 1 0) (sourceB1945 + difference 0 1) sourceC1945) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4460) := by
    have ha : (tripleCharges (sourceA1945 + difference 1 0) (sourceB1945 + difference 0 1) sourceC1945) = raw4935 := by
      apply Matrix.ext; unfold tripleCharges sourceA1945 sourceB1945 sourceC1945 difference raw4935; decide +kernel
    rw [ha]
    exact (canonical4935 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1945 + difference 1 2) (sourceB1945 + difference 2 1) sourceC1945) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA1945 + difference 1 2) (sourceB1945 + difference 2 1) sourceC1945) = raw4937 := by
      apply Matrix.ext; unfold tripleCharges sourceA1945 sourceB1945 sourceC1945 difference raw4937; decide +kernel
    rw [ha]
    exact (canonical4937 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1945 + difference 1 3) (sourceB1945 + difference 3 1) sourceC1945) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA1945 + difference 1 3) (sourceB1945 + difference 3 1) sourceC1945) = raw4938 := by
      apply Matrix.ext; unfold tripleCharges sourceA1945 sourceB1945 sourceC1945 difference raw4938; decide +kernel
    rw [ha]
    exact (canonical4938 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1945 + difference 1 4) (sourceB1945 + difference 4 1) sourceC1945) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5261) := by
    have ha : (tripleCharges (sourceA1945 + difference 1 4) (sourceB1945 + difference 4 1) sourceC1945) = raw2776 := by
      apply Matrix.ext; unfold tripleCharges sourceA1945 sourceB1945 sourceC1945 difference raw2776; decide +kernel
    rw [ha]
    exact (canonical2776 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1945 + difference 1 5) (sourceB1945 + difference 5 1) sourceC1945) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA1945 + difference 1 5) (sourceB1945 + difference 5 1) sourceC1945) = raw2771 := by
      apply Matrix.ext; unfold tripleCharges sourceA1945 sourceB1945 sourceC1945 difference raw2771; decide +kernel
    rw [ha]
    exact (canonical2771 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1945 + difference 2 0) (sourceB1945 + difference 0 2) sourceC1945) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4346) := by
    have ha : (tripleCharges (sourceA1945 + difference 2 0) (sourceB1945 + difference 0 2) sourceC1945) = raw21483 := by
      apply Matrix.ext; unfold tripleCharges sourceA1945 sourceB1945 sourceC1945 difference raw21483; decide +kernel
    rw [ha]
    exact (canonical21483 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1945 + difference 2 1) (sourceB1945 + difference 1 2) sourceC1945) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4943) := by
    have ha : (tripleCharges (sourceA1945 + difference 2 1) (sourceB1945 + difference 1 2) sourceC1945) = raw27586 := by
      apply Matrix.ext; unfold tripleCharges sourceA1945 sourceB1945 sourceC1945 difference raw27586; decide +kernel
    rw [ha]
    exact (canonical27586 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1945 + difference 2 3) (sourceB1945 + difference 3 2) sourceC1945) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5033) := by
    have ha : (tripleCharges (sourceA1945 + difference 2 3) (sourceB1945 + difference 3 2) sourceC1945) = raw27587 := by
      apply Matrix.ext; unfold tripleCharges sourceA1945 sourceB1945 sourceC1945 difference raw27587; decide +kernel
    rw [ha]
    exact (canonical27587 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1945 + difference 2 4) (sourceB1945 + difference 4 2) sourceC1945) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA1945 + difference 2 4) (sourceB1945 + difference 4 2) sourceC1945) = raw4928 := by
      apply Matrix.ext; unfold tripleCharges sourceA1945 sourceB1945 sourceC1945 difference raw4928; decide +kernel
    rw [ha]
    exact (canonical4928 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1945 + difference 2 5) (sourceB1945 + difference 5 2) sourceC1945) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA1945 + difference 2 5) (sourceB1945 + difference 5 2) sourceC1945) = raw17667 := by
      apply Matrix.ext; unfold tripleCharges sourceA1945 sourceB1945 sourceC1945 difference raw17667; decide +kernel
    rw [ha]
    exact (canonical17667 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1945 + difference 3 0) (sourceB1945 + difference 0 3) sourceC1945) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4346) := by
    have ha : (tripleCharges (sourceA1945 + difference 3 0) (sourceB1945 + difference 0 3) sourceC1945) = raw21487 := by
      apply Matrix.ext; unfold tripleCharges sourceA1945 sourceB1945 sourceC1945 difference raw21487; decide +kernel
    rw [ha]
    exact (canonical21487 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1945 + difference 3 1) (sourceB1945 + difference 1 3) sourceC1945) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4943) := by
    have ha : (tripleCharges (sourceA1945 + difference 3 1) (sourceB1945 + difference 1 3) sourceC1945) = raw27588 := by
      apply Matrix.ext; unfold tripleCharges sourceA1945 sourceB1945 sourceC1945 difference raw27588; decide +kernel
    rw [ha]
    exact (canonical27588 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1945 + difference 3 2) (sourceB1945 + difference 2 3) sourceC1945) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5033) := by
    have ha : (tripleCharges (sourceA1945 + difference 3 2) (sourceB1945 + difference 2 3) sourceC1945) = raw27589 := by
      apply Matrix.ext; unfold tripleCharges sourceA1945 sourceB1945 sourceC1945 difference raw27589; decide +kernel
    rw [ha]
    exact (canonical27589 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1945 + difference 3 4) (sourceB1945 + difference 4 3) sourceC1945) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA1945 + difference 3 4) (sourceB1945 + difference 4 3) sourceC1945) = raw4932 := by
      apply Matrix.ext; unfold tripleCharges sourceA1945 sourceB1945 sourceC1945 difference raw4932; decide +kernel
    rw [ha]
    exact (canonical4932 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1945 + difference 3 5) (sourceB1945 + difference 5 3) sourceC1945) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA1945 + difference 3 5) (sourceB1945 + difference 5 3) sourceC1945) = raw17671 := by
      apply Matrix.ext; unfold tripleCharges sourceA1945 sourceB1945 sourceC1945 difference raw17671; decide +kernel
    rw [ha]
    exact (canonical17671 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1945 + difference 4 0) (sourceB1945 + difference 0 4) sourceC1945) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4360) := by
    have ha : (tripleCharges (sourceA1945 + difference 4 0) (sourceB1945 + difference 0 4) sourceC1945) = raw21491 := by
      apply Matrix.ext; unfold tripleCharges sourceA1945 sourceB1945 sourceC1945 difference raw21491; decide +kernel
    rw [ha]
    exact (canonical21491 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1945 + difference 4 1) (sourceB1945 + difference 1 4) sourceC1945) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4952) := by
    have ha : (tripleCharges (sourceA1945 + difference 4 1) (sourceB1945 + difference 1 4) sourceC1945) = raw27590 := by
      apply Matrix.ext; unfold tripleCharges sourceA1945 sourceB1945 sourceC1945 difference raw27590; decide +kernel
    rw [ha]
    exact (canonical27590 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1945 + difference 4 2) (sourceB1945 + difference 2 4) sourceC1945) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4943) := by
    have ha : (tripleCharges (sourceA1945 + difference 4 2) (sourceB1945 + difference 2 4) sourceC1945) = raw27591 := by
      apply Matrix.ext; unfold tripleCharges sourceA1945 sourceB1945 sourceC1945 difference raw27591; decide +kernel
    rw [ha]
    exact (canonical27591 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1945 + difference 4 3) (sourceB1945 + difference 3 4) sourceC1945) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4943) := by
    have ha : (tripleCharges (sourceA1945 + difference 4 3) (sourceB1945 + difference 3 4) sourceC1945) = raw27592 := by
      apply Matrix.ext; unfold tripleCharges sourceA1945 sourceB1945 sourceC1945 difference raw27592; decide +kernel
    rw [ha]
    exact (canonical27592 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1945 + difference 4 5) (sourceB1945 + difference 5 4) sourceC1945) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5177) := by
    have ha : (tripleCharges (sourceA1945 + difference 4 5) (sourceB1945 + difference 5 4) sourceC1945) = raw17675 := by
      apply Matrix.ext; unfold tripleCharges sourceA1945 sourceB1945 sourceC1945 difference raw17675; decide +kernel
    rw [ha]
    exact (canonical17675 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1945 + difference 5 0) (sourceB1945 + difference 0 5) sourceC1945) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4350) := by
    have ha : (tripleCharges (sourceA1945 + difference 5 0) (sourceB1945 + difference 0 5) sourceC1945) = raw21496 := by
      apply Matrix.ext; unfold tripleCharges sourceA1945 sourceB1945 sourceC1945 difference raw21496; decide +kernel
    rw [ha]
    exact (canonical21496 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1945 + difference 5 1) (sourceB1945 + difference 1 5) sourceC1945) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4360) := by
    have ha : (tripleCharges (sourceA1945 + difference 5 1) (sourceB1945 + difference 1 5) sourceC1945) = raw27593 := by
      apply Matrix.ext; unfold tripleCharges sourceA1945 sourceB1945 sourceC1945 difference raw27593; decide +kernel
    rw [ha]
    exact (canonical27593 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1945 + difference 5 2) (sourceB1945 + difference 2 5) sourceC1945) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4346) := by
    have ha : (tripleCharges (sourceA1945 + difference 5 2) (sourceB1945 + difference 2 5) sourceC1945) = raw27594 := by
      apply Matrix.ext; unfold tripleCharges sourceA1945 sourceB1945 sourceC1945 difference raw27594; decide +kernel
    rw [ha]
    exact (canonical27594 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1945 + difference 5 3) (sourceB1945 + difference 3 5) sourceC1945) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4346) := by
    have ha : (tripleCharges (sourceA1945 + difference 5 3) (sourceB1945 + difference 3 5) sourceC1945) = raw27595 := by
      apply Matrix.ext; unfold tripleCharges sourceA1945 sourceB1945 sourceC1945 difference raw27595; decide +kernel
    rw [ha]
    exact (canonical27595 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1945 + difference 5 4) (sourceB1945 + difference 4 5) sourceC1945) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4460) := by
    have ha : (tripleCharges (sourceA1945 + difference 5 4) (sourceB1945 + difference 4 5) sourceC1945) = raw4940 := by
      apply Matrix.ext; unfold tripleCharges sourceA1945 sourceB1945 sourceC1945 difference raw4940; decide +kernel
    rw [ha]
    exact (canonical4940 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1945 sourceB1945 sourceC1945
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1945, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1946 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1946 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1946 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceForm1946 : Integer.Sparse Master := [(Sum.inr 924, 4), (Sum.inr 928, 1), (Sum.inr 938, 2), (Sum.inr 1043, 2), (Sum.inr 2334, 4), (Sum.inr 2344, 1), (Sum.inr 2425, 2), (Sum.inr 2482, 4), (Sum.inr 2595, 4), (Sum.inr 2605, 2), (Sum.inr 2726, 1), (Sum.inr 2767, 2), (Sum.inr 4000, 1)]

theorem sourceEq1946 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1946 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1946 + difference 0 1) (sourceB1946 + difference 1 0) sourceC1946) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2605) := by
    have ha : (tripleCharges (sourceA1946 + difference 0 1) (sourceB1946 + difference 1 0) sourceC1946) = raw27596 := by
      apply Matrix.ext; unfold tripleCharges sourceA1946 sourceB1946 sourceC1946 difference raw27596; decide +kernel
    rw [ha]
    exact (canonical27596 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1946 + difference 0 2) (sourceB1946 + difference 2 0) sourceC1946) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2595) := by
    have ha : (tripleCharges (sourceA1946 + difference 0 2) (sourceB1946 + difference 2 0) sourceC1946) = raw27597 := by
      apply Matrix.ext; unfold tripleCharges sourceA1946 sourceB1946 sourceC1946 difference raw27597; decide +kernel
    rw [ha]
    exact (canonical27597 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1946 + difference 0 3) (sourceB1946 + difference 3 0) sourceC1946) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2595) := by
    have ha : (tripleCharges (sourceA1946 + difference 0 3) (sourceB1946 + difference 3 0) sourceC1946) = raw27598 := by
      apply Matrix.ext; unfold tripleCharges sourceA1946 sourceB1946 sourceC1946 difference raw27598; decide +kernel
    rw [ha]
    exact (canonical27598 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1946 + difference 0 4) (sourceB1946 + difference 4 0) sourceC1946) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2767) := by
    have ha : (tripleCharges (sourceA1946 + difference 0 4) (sourceB1946 + difference 4 0) sourceC1946) = raw2807 := by
      apply Matrix.ext; unfold tripleCharges sourceA1946 sourceB1946 sourceC1946 difference raw2807; decide +kernel
    rw [ha]
    exact (canonical2807 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1946 + difference 0 5) (sourceB1946 + difference 5 0) sourceC1946) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4000) := by
    have ha : (tripleCharges (sourceA1946 + difference 0 5) (sourceB1946 + difference 5 0) sourceC1946) = raw2802 := by
      apply Matrix.ext; unfold tripleCharges sourceA1946 sourceB1946 sourceC1946 difference raw2802; decide +kernel
    rw [ha]
    exact (canonical2802 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1946 + difference 1 0) (sourceB1946 + difference 0 1) sourceC1946) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1043) := by
    have ha : (tripleCharges (sourceA1946 + difference 1 0) (sourceB1946 + difference 0 1) sourceC1946) = raw4957 := by
      apply Matrix.ext; unfold tripleCharges sourceA1946 sourceB1946 sourceC1946 difference raw4957; decide +kernel
    rw [ha]
    exact (canonical4957 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1946 + difference 1 2) (sourceB1946 + difference 2 1) sourceC1946) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2482) := by
    have ha : (tripleCharges (sourceA1946 + difference 1 2) (sourceB1946 + difference 2 1) sourceC1946) = raw4959 := by
      apply Matrix.ext; unfold tripleCharges sourceA1946 sourceB1946 sourceC1946 difference raw4959; decide +kernel
    rw [ha]
    exact (canonical4959 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1946 + difference 1 3) (sourceB1946 + difference 3 1) sourceC1946) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2482) := by
    have ha : (tripleCharges (sourceA1946 + difference 1 3) (sourceB1946 + difference 3 1) sourceC1946) = raw4960 := by
      apply Matrix.ext; unfold tripleCharges sourceA1946 sourceB1946 sourceC1946 difference raw4960; decide +kernel
    rw [ha]
    exact (canonical4960 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1946 + difference 1 4) (sourceB1946 + difference 4 1) sourceC1946) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2726) := by
    have ha : (tripleCharges (sourceA1946 + difference 1 4) (sourceB1946 + difference 4 1) sourceC1946) = raw2806 := by
      apply Matrix.ext; unfold tripleCharges sourceA1946 sourceB1946 sourceC1946 difference raw2806; decide +kernel
    rw [ha]
    exact (canonical2806 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1946 + difference 1 5) (sourceB1946 + difference 5 1) sourceC1946) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2767) := by
    have ha : (tripleCharges (sourceA1946 + difference 1 5) (sourceB1946 + difference 5 1) sourceC1946) = raw2801 := by
      apply Matrix.ext; unfold tripleCharges sourceA1946 sourceB1946 sourceC1946 difference raw2801; decide +kernel
    rw [ha]
    exact (canonical2801 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1946 + difference 2 0) (sourceB1946 + difference 0 2) sourceC1946) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 924) := by
    have ha : (tripleCharges (sourceA1946 + difference 2 0) (sourceB1946 + difference 0 2) sourceC1946) = raw21504 := by
      apply Matrix.ext; unfold tripleCharges sourceA1946 sourceB1946 sourceC1946 difference raw21504; decide +kernel
    rw [ha]
    exact (canonical21504 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1946 + difference 2 1) (sourceB1946 + difference 1 2) sourceC1946) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2334) := by
    have ha : (tripleCharges (sourceA1946 + difference 2 1) (sourceB1946 + difference 1 2) sourceC1946) = raw27599 := by
      apply Matrix.ext; unfold tripleCharges sourceA1946 sourceB1946 sourceC1946 difference raw27599; decide +kernel
    rw [ha]
    exact (canonical27599 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1946 + difference 2 3) (sourceB1946 + difference 3 2) sourceC1946) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2425) := by
    have ha : (tripleCharges (sourceA1946 + difference 2 3) (sourceB1946 + difference 3 2) sourceC1946) = raw27600 := by
      apply Matrix.ext; unfold tripleCharges sourceA1946 sourceB1946 sourceC1946 difference raw27600; decide +kernel
    rw [ha]
    exact (canonical27600 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1946 + difference 2 4) (sourceB1946 + difference 4 2) sourceC1946) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2482) := by
    have ha : (tripleCharges (sourceA1946 + difference 2 4) (sourceB1946 + difference 4 2) sourceC1946) = raw4950 := by
      apply Matrix.ext; unfold tripleCharges sourceA1946 sourceB1946 sourceC1946 difference raw4950; decide +kernel
    rw [ha]
    exact (canonical4950 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1946 + difference 2 5) (sourceB1946 + difference 5 2) sourceC1946) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2595) := by
    have ha : (tripleCharges (sourceA1946 + difference 2 5) (sourceB1946 + difference 5 2) sourceC1946) = raw27601 := by
      apply Matrix.ext; unfold tripleCharges sourceA1946 sourceB1946 sourceC1946 difference raw27601; decide +kernel
    rw [ha]
    exact (canonical27601 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1946 + difference 3 0) (sourceB1946 + difference 0 3) sourceC1946) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 924) := by
    have ha : (tripleCharges (sourceA1946 + difference 3 0) (sourceB1946 + difference 0 3) sourceC1946) = raw21508 := by
      apply Matrix.ext; unfold tripleCharges sourceA1946 sourceB1946 sourceC1946 difference raw21508; decide +kernel
    rw [ha]
    exact (canonical21508 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1946 + difference 3 1) (sourceB1946 + difference 1 3) sourceC1946) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2334) := by
    have ha : (tripleCharges (sourceA1946 + difference 3 1) (sourceB1946 + difference 1 3) sourceC1946) = raw27602 := by
      apply Matrix.ext; unfold tripleCharges sourceA1946 sourceB1946 sourceC1946 difference raw27602; decide +kernel
    rw [ha]
    exact (canonical27602 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1946 + difference 3 2) (sourceB1946 + difference 2 3) sourceC1946) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2425) := by
    have ha : (tripleCharges (sourceA1946 + difference 3 2) (sourceB1946 + difference 2 3) sourceC1946) = raw27603 := by
      apply Matrix.ext; unfold tripleCharges sourceA1946 sourceB1946 sourceC1946 difference raw27603; decide +kernel
    rw [ha]
    exact (canonical27603 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1946 + difference 3 4) (sourceB1946 + difference 4 3) sourceC1946) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2482) := by
    have ha : (tripleCharges (sourceA1946 + difference 3 4) (sourceB1946 + difference 4 3) sourceC1946) = raw4954 := by
      apply Matrix.ext; unfold tripleCharges sourceA1946 sourceB1946 sourceC1946 difference raw4954; decide +kernel
    rw [ha]
    exact (canonical4954 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1946 + difference 3 5) (sourceB1946 + difference 5 3) sourceC1946) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2595) := by
    have ha : (tripleCharges (sourceA1946 + difference 3 5) (sourceB1946 + difference 5 3) sourceC1946) = raw25256 := by
      apply Matrix.ext; unfold tripleCharges sourceA1946 sourceB1946 sourceC1946 difference raw25256; decide +kernel
    rw [ha]
    exact (canonical25256 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1946 + difference 4 0) (sourceB1946 + difference 0 4) sourceC1946) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 938) := by
    have ha : (tripleCharges (sourceA1946 + difference 4 0) (sourceB1946 + difference 0 4) sourceC1946) = raw21512 := by
      apply Matrix.ext; unfold tripleCharges sourceA1946 sourceB1946 sourceC1946 difference raw21512; decide +kernel
    rw [ha]
    exact (canonical21512 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1946 + difference 4 1) (sourceB1946 + difference 1 4) sourceC1946) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2344) := by
    have ha : (tripleCharges (sourceA1946 + difference 4 1) (sourceB1946 + difference 1 4) sourceC1946) = raw27604 := by
      apply Matrix.ext; unfold tripleCharges sourceA1946 sourceB1946 sourceC1946 difference raw27604; decide +kernel
    rw [ha]
    exact (canonical27604 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1946 + difference 4 2) (sourceB1946 + difference 2 4) sourceC1946) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2334) := by
    have ha : (tripleCharges (sourceA1946 + difference 4 2) (sourceB1946 + difference 2 4) sourceC1946) = raw27605 := by
      apply Matrix.ext; unfold tripleCharges sourceA1946 sourceB1946 sourceC1946 difference raw27605; decide +kernel
    rw [ha]
    exact (canonical27605 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1946 + difference 4 3) (sourceB1946 + difference 3 4) sourceC1946) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2334) := by
    have ha : (tripleCharges (sourceA1946 + difference 4 3) (sourceB1946 + difference 3 4) sourceC1946) = raw27606 := by
      apply Matrix.ext; unfold tripleCharges sourceA1946 sourceB1946 sourceC1946 difference raw27606; decide +kernel
    rw [ha]
    exact (canonical27606 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1946 + difference 4 5) (sourceB1946 + difference 5 4) sourceC1946) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2605) := by
    have ha : (tripleCharges (sourceA1946 + difference 4 5) (sourceB1946 + difference 5 4) sourceC1946) = raw23239 := by
      apply Matrix.ext; unfold tripleCharges sourceA1946 sourceB1946 sourceC1946 difference raw23239; decide +kernel
    rw [ha]
    exact (canonical23239 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1946 + difference 5 0) (sourceB1946 + difference 0 5) sourceC1946) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 928) := by
    have ha : (tripleCharges (sourceA1946 + difference 5 0) (sourceB1946 + difference 0 5) sourceC1946) = raw21517 := by
      apply Matrix.ext; unfold tripleCharges sourceA1946 sourceB1946 sourceC1946 difference raw21517; decide +kernel
    rw [ha]
    exact (canonical21517 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1946 + difference 5 1) (sourceB1946 + difference 1 5) sourceC1946) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 938) := by
    have ha : (tripleCharges (sourceA1946 + difference 5 1) (sourceB1946 + difference 1 5) sourceC1946) = raw27607 := by
      apply Matrix.ext; unfold tripleCharges sourceA1946 sourceB1946 sourceC1946 difference raw27607; decide +kernel
    rw [ha]
    exact (canonical27607 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1946 + difference 5 2) (sourceB1946 + difference 2 5) sourceC1946) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 924) := by
    have ha : (tripleCharges (sourceA1946 + difference 5 2) (sourceB1946 + difference 2 5) sourceC1946) = raw27608 := by
      apply Matrix.ext; unfold tripleCharges sourceA1946 sourceB1946 sourceC1946 difference raw27608; decide +kernel
    rw [ha]
    exact (canonical27608 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1946 + difference 5 3) (sourceB1946 + difference 3 5) sourceC1946) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 924) := by
    have ha : (tripleCharges (sourceA1946 + difference 5 3) (sourceB1946 + difference 3 5) sourceC1946) = raw27609 := by
      apply Matrix.ext; unfold tripleCharges sourceA1946 sourceB1946 sourceC1946 difference raw27609; decide +kernel
    rw [ha]
    exact (canonical27609 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1946 + difference 5 4) (sourceB1946 + difference 4 5) sourceC1946) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1043) := by
    have ha : (tripleCharges (sourceA1946 + difference 5 4) (sourceB1946 + difference 4 5) sourceC1946) = raw4962 := by
      apply Matrix.ext; unfold tripleCharges sourceA1946 sourceB1946 sourceC1946 difference raw4962; decide +kernel
    rw [ha]
    exact (canonical4962 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1946 sourceB1946 sourceC1946
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1946, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1947 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1947 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC1947 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceForm1947 : Integer.Sparse Master := [(Sum.inr 4352, 2), (Sum.inr 4356, 1), (Sum.inr 4361, 1), (Sum.inr 4463, 1), (Sum.inr 4546, 2), (Sum.inr 4558, 1), (Sum.inr 4625, 1), (Sum.inr 4948, 2), (Sum.inr 4953, 1), (Sum.inr 4972, 2), (Sum.inr 5037, 2), (Sum.inr 5078, 2), (Sum.inr 5169, 2), (Sum.inr 5172, 2), (Sum.inr 5174, 2), (Sum.inr 5176, 1), (Sum.inr 5177, 1), (Sum.inr 5294, 1), (Sum.inr 5296, 1), (Sum.inr 5309, 1), (Sum.inr 5442, 1)]

theorem sourceEq1947 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1947 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1947 + difference 0 1) (sourceB1947 + difference 1 0) sourceC1947) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5176) := by
    have ha : (tripleCharges (sourceA1947 + difference 0 1) (sourceB1947 + difference 1 0) sourceC1947) = raw27610 := by
      apply Matrix.ext; unfold tripleCharges sourceA1947 sourceB1947 sourceC1947 difference raw27610; decide +kernel
    rw [ha]
    exact (canonical27610 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1947 + difference 0 2) (sourceB1947 + difference 2 0) sourceC1947) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5172) := by
    have ha : (tripleCharges (sourceA1947 + difference 0 2) (sourceB1947 + difference 2 0) sourceC1947) = raw27611 := by
      apply Matrix.ext; unfold tripleCharges sourceA1947 sourceB1947 sourceC1947 difference raw27611; decide +kernel
    rw [ha]
    exact (canonical27611 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1947 + difference 0 3) (sourceB1947 + difference 3 0) sourceC1947) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5172) := by
    have ha : (tripleCharges (sourceA1947 + difference 0 3) (sourceB1947 + difference 3 0) sourceC1947) = raw27612 := by
      apply Matrix.ext; unfold tripleCharges sourceA1947 sourceB1947 sourceC1947 difference raw27612; decide +kernel
    rw [ha]
    exact (canonical27612 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1947 + difference 0 4) (sourceB1947 + difference 4 0) sourceC1947) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA1947 + difference 0 4) (sourceB1947 + difference 4 0) sourceC1947) = raw4282 := by
      apply Matrix.ext; unfold tripleCharges sourceA1947 sourceB1947 sourceC1947 difference raw4282; decide +kernel
    rw [ha]
    exact (canonical4282 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1947 + difference 0 5) (sourceB1947 + difference 5 0) sourceC1947) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5442) := by
    have ha : (tripleCharges (sourceA1947 + difference 0 5) (sourceB1947 + difference 5 0) sourceC1947) = raw10194 := by
      apply Matrix.ext; unfold tripleCharges sourceA1947 sourceB1947 sourceC1947 difference raw10194; decide +kernel
    rw [ha]
    exact (canonical10194 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1947 + difference 1 0) (sourceB1947 + difference 0 1) sourceC1947) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4625) := by
    have ha : (tripleCharges (sourceA1947 + difference 1 0) (sourceB1947 + difference 0 1) sourceC1947) = raw4302 := by
      apply Matrix.ext; unfold tripleCharges sourceA1947 sourceB1947 sourceC1947 difference raw4302; decide +kernel
    rw [ha]
    exact (canonical4302 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1947 + difference 1 2) (sourceB1947 + difference 2 1) sourceC1947) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5174) := by
    have ha : (tripleCharges (sourceA1947 + difference 1 2) (sourceB1947 + difference 2 1) sourceC1947) = raw4304 := by
      apply Matrix.ext; unfold tripleCharges sourceA1947 sourceB1947 sourceC1947 difference raw4304; decide +kernel
    rw [ha]
    exact (canonical4304 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1947 + difference 1 3) (sourceB1947 + difference 3 1) sourceC1947) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5174) := by
    have ha : (tripleCharges (sourceA1947 + difference 1 3) (sourceB1947 + difference 3 1) sourceC1947) = raw4305 := by
      apply Matrix.ext; unfold tripleCharges sourceA1947 sourceB1947 sourceC1947 difference raw4305; decide +kernel
    rw [ha]
    exact (canonical4305 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1947 + difference 1 4) (sourceB1947 + difference 4 1) sourceC1947) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5296) := by
    have ha : (tripleCharges (sourceA1947 + difference 1 4) (sourceB1947 + difference 4 1) sourceC1947) = raw10215 := by
      apply Matrix.ext; unfold tripleCharges sourceA1947 sourceB1947 sourceC1947 difference raw10215; decide +kernel
    rw [ha]
    exact (canonical10215 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1947 + difference 1 5) (sourceB1947 + difference 5 1) sourceC1947) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5309) := by
    have ha : (tripleCharges (sourceA1947 + difference 1 5) (sourceB1947 + difference 5 1) sourceC1947) = raw4306 := by
      apply Matrix.ext; unfold tripleCharges sourceA1947 sourceB1947 sourceC1947 difference raw4306; decide +kernel
    rw [ha]
    exact (canonical4306 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1947 + difference 2 0) (sourceB1947 + difference 0 2) sourceC1947) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4546) := by
    have ha : (tripleCharges (sourceA1947 + difference 2 0) (sourceB1947 + difference 0 2) sourceC1947) = raw20388 := by
      apply Matrix.ext; unfold tripleCharges sourceA1947 sourceB1947 sourceC1947 difference raw20388; decide +kernel
    rw [ha]
    exact (canonical20388 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1947 + difference 2 1) (sourceB1947 + difference 1 2) sourceC1947) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4972) := by
    have ha : (tripleCharges (sourceA1947 + difference 2 1) (sourceB1947 + difference 1 2) sourceC1947) = raw27613 := by
      apply Matrix.ext; unfold tripleCharges sourceA1947 sourceB1947 sourceC1947 difference raw27613; decide +kernel
    rw [ha]
    exact (canonical27613 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1947 + difference 2 3) (sourceB1947 + difference 3 2) sourceC1947) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5037) := by
    have ha : (tripleCharges (sourceA1947 + difference 2 3) (sourceB1947 + difference 3 2) sourceC1947) = raw27614 := by
      apply Matrix.ext; unfold tripleCharges sourceA1947 sourceB1947 sourceC1947 difference raw27614; decide +kernel
    rw [ha]
    exact (canonical27614 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1947 + difference 2 4) (sourceB1947 + difference 4 2) sourceC1947) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5078) := by
    have ha : (tripleCharges (sourceA1947 + difference 2 4) (sourceB1947 + difference 4 2) sourceC1947) = raw4293 := by
      apply Matrix.ext; unfold tripleCharges sourceA1947 sourceB1947 sourceC1947 difference raw4293; decide +kernel
    rw [ha]
    exact (canonical4293 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1947 + difference 2 5) (sourceB1947 + difference 5 2) sourceC1947) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA1947 + difference 2 5) (sourceB1947 + difference 5 2) sourceC1947) = raw10203 := by
      apply Matrix.ext; unfold tripleCharges sourceA1947 sourceB1947 sourceC1947 difference raw10203; decide +kernel
    rw [ha]
    exact (canonical10203 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1947 + difference 3 0) (sourceB1947 + difference 0 3) sourceC1947) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4546) := by
    have ha : (tripleCharges (sourceA1947 + difference 3 0) (sourceB1947 + difference 0 3) sourceC1947) = raw20391 := by
      apply Matrix.ext; unfold tripleCharges sourceA1947 sourceB1947 sourceC1947 difference raw20391; decide +kernel
    rw [ha]
    exact (canonical20391 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1947 + difference 3 1) (sourceB1947 + difference 1 3) sourceC1947) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4972) := by
    have ha : (tripleCharges (sourceA1947 + difference 3 1) (sourceB1947 + difference 1 3) sourceC1947) = raw27615 := by
      apply Matrix.ext; unfold tripleCharges sourceA1947 sourceB1947 sourceC1947 difference raw27615; decide +kernel
    rw [ha]
    exact (canonical27615 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1947 + difference 3 2) (sourceB1947 + difference 2 3) sourceC1947) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5037) := by
    have ha : (tripleCharges (sourceA1947 + difference 3 2) (sourceB1947 + difference 2 3) sourceC1947) = raw27616 := by
      apply Matrix.ext; unfold tripleCharges sourceA1947 sourceB1947 sourceC1947 difference raw27616; decide +kernel
    rw [ha]
    exact (canonical27616 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1947 + difference 3 4) (sourceB1947 + difference 4 3) sourceC1947) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5078) := by
    have ha : (tripleCharges (sourceA1947 + difference 3 4) (sourceB1947 + difference 4 3) sourceC1947) = raw4298 := by
      apply Matrix.ext; unfold tripleCharges sourceA1947 sourceB1947 sourceC1947 difference raw4298; decide +kernel
    rw [ha]
    exact (canonical4298 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1947 + difference 3 5) (sourceB1947 + difference 5 3) sourceC1947) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA1947 + difference 3 5) (sourceB1947 + difference 5 3) sourceC1947) = raw10207 := by
      apply Matrix.ext; unfold tripleCharges sourceA1947 sourceB1947 sourceC1947 difference raw10207; decide +kernel
    rw [ha]
    exact (canonical10207 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1947 + difference 4 0) (sourceB1947 + difference 0 4) sourceC1947) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4558) := by
    have ha : (tripleCharges (sourceA1947 + difference 4 0) (sourceB1947 + difference 0 4) sourceC1947) = raw20394 := by
      apply Matrix.ext; unfold tripleCharges sourceA1947 sourceB1947 sourceC1947 difference raw20394; decide +kernel
    rw [ha]
    exact (canonical20394 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1947 + difference 4 1) (sourceB1947 + difference 1 4) sourceC1947) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4953) := by
    have ha : (tripleCharges (sourceA1947 + difference 4 1) (sourceB1947 + difference 1 4) sourceC1947) = raw27617 := by
      apply Matrix.ext; unfold tripleCharges sourceA1947 sourceB1947 sourceC1947 difference raw27617; decide +kernel
    rw [ha]
    exact (canonical27617 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1947 + difference 4 2) (sourceB1947 + difference 2 4) sourceC1947) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4948) := by
    have ha : (tripleCharges (sourceA1947 + difference 4 2) (sourceB1947 + difference 2 4) sourceC1947) = raw27618 := by
      apply Matrix.ext; unfold tripleCharges sourceA1947 sourceB1947 sourceC1947 difference raw27618; decide +kernel
    rw [ha]
    exact (canonical27618 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1947 + difference 4 3) (sourceB1947 + difference 3 4) sourceC1947) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4948) := by
    have ha : (tripleCharges (sourceA1947 + difference 4 3) (sourceB1947 + difference 3 4) sourceC1947) = raw27619 := by
      apply Matrix.ext; unfold tripleCharges sourceA1947 sourceB1947 sourceC1947 difference raw27619; decide +kernel
    rw [ha]
    exact (canonical27619 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1947 + difference 4 5) (sourceB1947 + difference 5 4) sourceC1947) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5177) := by
    have ha : (tripleCharges (sourceA1947 + difference 4 5) (sourceB1947 + difference 5 4) sourceC1947) = raw10211 := by
      apply Matrix.ext; unfold tripleCharges sourceA1947 sourceB1947 sourceC1947 difference raw10211; decide +kernel
    rw [ha]
    exact (canonical10211 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1947 + difference 5 0) (sourceB1947 + difference 0 5) sourceC1947) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4356) := by
    have ha : (tripleCharges (sourceA1947 + difference 5 0) (sourceB1947 + difference 0 5) sourceC1947) = raw19720 := by
      apply Matrix.ext; unfold tripleCharges sourceA1947 sourceB1947 sourceC1947 difference raw19720; decide +kernel
    rw [ha]
    exact (canonical19720 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1947 + difference 5 1) (sourceB1947 + difference 1 5) sourceC1947) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4361) := by
    have ha : (tripleCharges (sourceA1947 + difference 5 1) (sourceB1947 + difference 1 5) sourceC1947) = raw27620 := by
      apply Matrix.ext; unfold tripleCharges sourceA1947 sourceB1947 sourceC1947 difference raw27620; decide +kernel
    rw [ha]
    exact (canonical27620 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1947 + difference 5 2) (sourceB1947 + difference 2 5) sourceC1947) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4352) := by
    have ha : (tripleCharges (sourceA1947 + difference 5 2) (sourceB1947 + difference 2 5) sourceC1947) = raw27621 := by
      apply Matrix.ext; unfold tripleCharges sourceA1947 sourceB1947 sourceC1947 difference raw27621; decide +kernel
    rw [ha]
    exact (canonical27621 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1947 + difference 5 3) (sourceB1947 + difference 3 5) sourceC1947) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4352) := by
    have ha : (tripleCharges (sourceA1947 + difference 5 3) (sourceB1947 + difference 3 5) sourceC1947) = raw27622 := by
      apply Matrix.ext; unfold tripleCharges sourceA1947 sourceB1947 sourceC1947 difference raw27622; decide +kernel
    rw [ha]
    exact (canonical27622 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1947 + difference 5 4) (sourceB1947 + difference 4 5) sourceC1947) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4463) := by
    have ha : (tripleCharges (sourceA1947 + difference 5 4) (sourceB1947 + difference 4 5) sourceC1947) = raw4308 := by
      apply Matrix.ext; unfold tripleCharges sourceA1947 sourceB1947 sourceC1947 difference raw4308; decide +kernel
    rw [ha]
    exact (canonical4308 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1947 sourceB1947 sourceC1947
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1947, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1948 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1948 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC1948 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceForm1948 : Integer.Sparse Master := [(Sum.inr 930, 2), (Sum.inr 934, 1), (Sum.inr 939, 1), (Sum.inr 1046, 1), (Sum.inr 1131, 2), (Sum.inr 1144, 1), (Sum.inr 1304, 1), (Sum.inr 2339, 2), (Sum.inr 2345, 1), (Sum.inr 2429, 2), (Sum.inr 2434, 2), (Sum.inr 2485, 2), (Sum.inr 2599, 2), (Sum.inr 2601, 2), (Sum.inr 2604, 1), (Sum.inr 2768, 1), (Sum.inr 2770, 1), (Sum.inr 2960, 2), (Sum.inr 2969, 1), (Sum.inr 3123, 1), (Sum.inr 4001, 1)]

theorem sourceEq1948 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1948 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1948 + difference 0 1) (sourceB1948 + difference 1 0) sourceC1948) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2604) := by
    have ha : (tripleCharges (sourceA1948 + difference 0 1) (sourceB1948 + difference 1 0) sourceC1948) = raw27623 := by
      apply Matrix.ext; unfold tripleCharges sourceA1948 sourceB1948 sourceC1948 difference raw27623; decide +kernel
    rw [ha]
    exact (canonical27623 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1948 + difference 0 2) (sourceB1948 + difference 2 0) sourceC1948) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2599) := by
    have ha : (tripleCharges (sourceA1948 + difference 0 2) (sourceB1948 + difference 2 0) sourceC1948) = raw27624 := by
      apply Matrix.ext; unfold tripleCharges sourceA1948 sourceB1948 sourceC1948 difference raw27624; decide +kernel
    rw [ha]
    exact (canonical27624 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1948 + difference 0 3) (sourceB1948 + difference 3 0) sourceC1948) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2599) := by
    have ha : (tripleCharges (sourceA1948 + difference 0 3) (sourceB1948 + difference 3 0) sourceC1948) = raw27625 := by
      apply Matrix.ext; unfold tripleCharges sourceA1948 sourceB1948 sourceC1948 difference raw27625; decide +kernel
    rw [ha]
    exact (canonical27625 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1948 + difference 0 4) (sourceB1948 + difference 4 0) sourceC1948) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2768) := by
    have ha : (tripleCharges (sourceA1948 + difference 0 4) (sourceB1948 + difference 4 0) sourceC1948) = raw4312 := by
      apply Matrix.ext; unfold tripleCharges sourceA1948 sourceB1948 sourceC1948 difference raw4312; decide +kernel
    rw [ha]
    exact (canonical4312 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1948 + difference 0 5) (sourceB1948 + difference 5 0) sourceC1948) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4001) := by
    have ha : (tripleCharges (sourceA1948 + difference 0 5) (sourceB1948 + difference 5 0) sourceC1948) = raw27626 := by
      apply Matrix.ext; unfold tripleCharges sourceA1948 sourceB1948 sourceC1948 difference raw27626; decide +kernel
    rw [ha]
    exact (canonical27626 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1948 + difference 1 0) (sourceB1948 + difference 0 1) sourceC1948) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1304) := by
    have ha : (tripleCharges (sourceA1948 + difference 1 0) (sourceB1948 + difference 0 1) sourceC1948) = raw4332 := by
      apply Matrix.ext; unfold tripleCharges sourceA1948 sourceB1948 sourceC1948 difference raw4332; decide +kernel
    rw [ha]
    exact (canonical4332 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1948 + difference 1 2) (sourceB1948 + difference 2 1) sourceC1948) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2601) := by
    have ha : (tripleCharges (sourceA1948 + difference 1 2) (sourceB1948 + difference 2 1) sourceC1948) = raw4334 := by
      apply Matrix.ext; unfold tripleCharges sourceA1948 sourceB1948 sourceC1948 difference raw4334; decide +kernel
    rw [ha]
    exact (canonical4334 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1948 + difference 1 3) (sourceB1948 + difference 3 1) sourceC1948) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2601) := by
    have ha : (tripleCharges (sourceA1948 + difference 1 3) (sourceB1948 + difference 3 1) sourceC1948) = raw4335 := by
      apply Matrix.ext; unfold tripleCharges sourceA1948 sourceB1948 sourceC1948 difference raw4335; decide +kernel
    rw [ha]
    exact (canonical4335 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1948 + difference 1 4) (sourceB1948 + difference 4 1) sourceC1948) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2770) := by
    have ha : (tripleCharges (sourceA1948 + difference 1 4) (sourceB1948 + difference 4 1) sourceC1948) = raw19728 := by
      apply Matrix.ext; unfold tripleCharges sourceA1948 sourceB1948 sourceC1948 difference raw19728; decide +kernel
    rw [ha]
    exact (canonical19728 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1948 + difference 1 5) (sourceB1948 + difference 5 1) sourceC1948) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3123) := by
    have ha : (tripleCharges (sourceA1948 + difference 1 5) (sourceB1948 + difference 5 1) sourceC1948) = raw4336 := by
      apply Matrix.ext; unfold tripleCharges sourceA1948 sourceB1948 sourceC1948 difference raw4336; decide +kernel
    rw [ha]
    exact (canonical4336 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1948 + difference 2 0) (sourceB1948 + difference 0 2) sourceC1948) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1131) := by
    have ha : (tripleCharges (sourceA1948 + difference 2 0) (sourceB1948 + difference 0 2) sourceC1948) = raw20402 := by
      apply Matrix.ext; unfold tripleCharges sourceA1948 sourceB1948 sourceC1948 difference raw20402; decide +kernel
    rw [ha]
    exact (canonical20402 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1948 + difference 2 1) (sourceB1948 + difference 1 2) sourceC1948) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2434) := by
    have ha : (tripleCharges (sourceA1948 + difference 2 1) (sourceB1948 + difference 1 2) sourceC1948) = raw27627 := by
      apply Matrix.ext; unfold tripleCharges sourceA1948 sourceB1948 sourceC1948 difference raw27627; decide +kernel
    rw [ha]
    exact (canonical27627 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1948 + difference 2 3) (sourceB1948 + difference 3 2) sourceC1948) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2429) := by
    have ha : (tripleCharges (sourceA1948 + difference 2 3) (sourceB1948 + difference 3 2) sourceC1948) = raw27628 := by
      apply Matrix.ext; unfold tripleCharges sourceA1948 sourceB1948 sourceC1948 difference raw27628; decide +kernel
    rw [ha]
    exact (canonical27628 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1948 + difference 2 4) (sourceB1948 + difference 4 2) sourceC1948) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2485) := by
    have ha : (tripleCharges (sourceA1948 + difference 2 4) (sourceB1948 + difference 4 2) sourceC1948) = raw4323 := by
      apply Matrix.ext; unfold tripleCharges sourceA1948 sourceB1948 sourceC1948 difference raw4323; decide +kernel
    rw [ha]
    exact (canonical4323 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1948 + difference 2 5) (sourceB1948 + difference 5 2) sourceC1948) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2960) := by
    have ha : (tripleCharges (sourceA1948 + difference 2 5) (sourceB1948 + difference 5 2) sourceC1948) = raw27629 := by
      apply Matrix.ext; unfold tripleCharges sourceA1948 sourceB1948 sourceC1948 difference raw27629; decide +kernel
    rw [ha]
    exact (canonical27629 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1948 + difference 3 0) (sourceB1948 + difference 0 3) sourceC1948) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1131) := by
    have ha : (tripleCharges (sourceA1948 + difference 3 0) (sourceB1948 + difference 0 3) sourceC1948) = raw20406 := by
      apply Matrix.ext; unfold tripleCharges sourceA1948 sourceB1948 sourceC1948 difference raw20406; decide +kernel
    rw [ha]
    exact (canonical20406 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1948 + difference 3 1) (sourceB1948 + difference 1 3) sourceC1948) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2434) := by
    have ha : (tripleCharges (sourceA1948 + difference 3 1) (sourceB1948 + difference 1 3) sourceC1948) = raw27630 := by
      apply Matrix.ext; unfold tripleCharges sourceA1948 sourceB1948 sourceC1948 difference raw27630; decide +kernel
    rw [ha]
    exact (canonical27630 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1948 + difference 3 2) (sourceB1948 + difference 2 3) sourceC1948) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2429) := by
    have ha : (tripleCharges (sourceA1948 + difference 3 2) (sourceB1948 + difference 2 3) sourceC1948) = raw27631 := by
      apply Matrix.ext; unfold tripleCharges sourceA1948 sourceB1948 sourceC1948 difference raw27631; decide +kernel
    rw [ha]
    exact (canonical27631 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1948 + difference 3 4) (sourceB1948 + difference 4 3) sourceC1948) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2485) := by
    have ha : (tripleCharges (sourceA1948 + difference 3 4) (sourceB1948 + difference 4 3) sourceC1948) = raw4328 := by
      apply Matrix.ext; unfold tripleCharges sourceA1948 sourceB1948 sourceC1948 difference raw4328; decide +kernel
    rw [ha]
    exact (canonical4328 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1948 + difference 3 5) (sourceB1948 + difference 5 3) sourceC1948) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2960) := by
    have ha : (tripleCharges (sourceA1948 + difference 3 5) (sourceB1948 + difference 5 3) sourceC1948) = raw24232 := by
      apply Matrix.ext; unfold tripleCharges sourceA1948 sourceB1948 sourceC1948 difference raw24232; decide +kernel
    rw [ha]
    exact (canonical24232 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1948 + difference 4 0) (sourceB1948 + difference 0 4) sourceC1948) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1144) := by
    have ha : (tripleCharges (sourceA1948 + difference 4 0) (sourceB1948 + difference 0 4) sourceC1948) = raw20410 := by
      apply Matrix.ext; unfold tripleCharges sourceA1948 sourceB1948 sourceC1948 difference raw20410; decide +kernel
    rw [ha]
    exact (canonical20410 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1948 + difference 4 1) (sourceB1948 + difference 1 4) sourceC1948) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2345) := by
    have ha : (tripleCharges (sourceA1948 + difference 4 1) (sourceB1948 + difference 1 4) sourceC1948) = raw27632 := by
      apply Matrix.ext; unfold tripleCharges sourceA1948 sourceB1948 sourceC1948 difference raw27632; decide +kernel
    rw [ha]
    exact (canonical27632 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1948 + difference 4 2) (sourceB1948 + difference 2 4) sourceC1948) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2339) := by
    have ha : (tripleCharges (sourceA1948 + difference 4 2) (sourceB1948 + difference 2 4) sourceC1948) = raw27633 := by
      apply Matrix.ext; unfold tripleCharges sourceA1948 sourceB1948 sourceC1948 difference raw27633; decide +kernel
    rw [ha]
    exact (canonical27633 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1948 + difference 4 3) (sourceB1948 + difference 3 4) sourceC1948) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2339) := by
    have ha : (tripleCharges (sourceA1948 + difference 4 3) (sourceB1948 + difference 3 4) sourceC1948) = raw27634 := by
      apply Matrix.ext; unfold tripleCharges sourceA1948 sourceB1948 sourceC1948 difference raw27634; decide +kernel
    rw [ha]
    exact (canonical27634 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1948 + difference 4 5) (sourceB1948 + difference 5 4) sourceC1948) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2969) := by
    have ha : (tripleCharges (sourceA1948 + difference 4 5) (sourceB1948 + difference 5 4) sourceC1948) = raw22586 := by
      apply Matrix.ext; unfold tripleCharges sourceA1948 sourceB1948 sourceC1948 difference raw22586; decide +kernel
    rw [ha]
    exact (canonical22586 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1948 + difference 5 0) (sourceB1948 + difference 0 5) sourceC1948) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 934) := by
    have ha : (tripleCharges (sourceA1948 + difference 5 0) (sourceB1948 + difference 0 5) sourceC1948) = raw19742 := by
      apply Matrix.ext; unfold tripleCharges sourceA1948 sourceB1948 sourceC1948 difference raw19742; decide +kernel
    rw [ha]
    exact (canonical19742 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1948 + difference 5 1) (sourceB1948 + difference 1 5) sourceC1948) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 939) := by
    have ha : (tripleCharges (sourceA1948 + difference 5 1) (sourceB1948 + difference 1 5) sourceC1948) = raw27635 := by
      apply Matrix.ext; unfold tripleCharges sourceA1948 sourceB1948 sourceC1948 difference raw27635; decide +kernel
    rw [ha]
    exact (canonical27635 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1948 + difference 5 2) (sourceB1948 + difference 2 5) sourceC1948) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 930) := by
    have ha : (tripleCharges (sourceA1948 + difference 5 2) (sourceB1948 + difference 2 5) sourceC1948) = raw27636 := by
      apply Matrix.ext; unfold tripleCharges sourceA1948 sourceB1948 sourceC1948 difference raw27636; decide +kernel
    rw [ha]
    exact (canonical27636 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1948 + difference 5 3) (sourceB1948 + difference 3 5) sourceC1948) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 930) := by
    have ha : (tripleCharges (sourceA1948 + difference 5 3) (sourceB1948 + difference 3 5) sourceC1948) = raw27637 := by
      apply Matrix.ext; unfold tripleCharges sourceA1948 sourceB1948 sourceC1948 difference raw27637; decide +kernel
    rw [ha]
    exact (canonical27637 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1948 + difference 5 4) (sourceB1948 + difference 4 5) sourceC1948) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1046) := by
    have ha : (tripleCharges (sourceA1948 + difference 5 4) (sourceB1948 + difference 4 5) sourceC1948) = raw4338 := by
      apply Matrix.ext; unfold tripleCharges sourceA1948 sourceB1948 sourceC1948 difference raw4338; decide +kernel
    rw [ha]
    exact (canonical4338 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1948 sourceB1948 sourceC1948
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1948, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1949 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceB1949 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC1949 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceForm1949 : Integer.Sparse Master := [(Sum.inr 4807, 4), (Sum.inr 4841, 2), (Sum.inr 4843, 2), (Sum.inr 4871, 2), (Sum.inr 5075, 4), (Sum.inr 5078, 4), (Sum.inr 5107, 2), (Sum.inr 5109, 2), (Sum.inr 5128, 2), (Sum.inr 5139, 4), (Sum.inr 5171, 2)]

theorem sourceEq1949 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1949 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1949 + difference 0 1) (sourceB1949 + difference 1 0) sourceC1949) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5171) := by
    have ha : (tripleCharges (sourceA1949 + difference 0 1) (sourceB1949 + difference 1 0) sourceC1949) = raw27638 := by
      apply Matrix.ext; unfold tripleCharges sourceA1949 sourceB1949 sourceC1949 difference raw27638; decide +kernel
    rw [ha]
    exact (canonical27638 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1949 + difference 0 2) (sourceB1949 + difference 2 0) sourceC1949) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA1949 + difference 0 2) (sourceB1949 + difference 2 0) sourceC1949) = raw27639 := by
      apply Matrix.ext; unfold tripleCharges sourceA1949 sourceB1949 sourceC1949 difference raw27639; decide +kernel
    rw [ha]
    exact (canonical27639 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1949 + difference 0 3) (sourceB1949 + difference 3 0) sourceC1949) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA1949 + difference 0 3) (sourceB1949 + difference 3 0) sourceC1949) = raw27640 := by
      apply Matrix.ext; unfold tripleCharges sourceA1949 sourceB1949 sourceC1949 difference raw27640; decide +kernel
    rw [ha]
    exact (canonical27640 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1949 + difference 0 4) (sourceB1949 + difference 4 0) sourceC1949) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5107) := by
    have ha : (tripleCharges (sourceA1949 + difference 0 4) (sourceB1949 + difference 4 0) sourceC1949) = raw27641 := by
      apply Matrix.ext; unfold tripleCharges sourceA1949 sourceB1949 sourceC1949 difference raw27641; decide +kernel
    rw [ha]
    exact (canonical27641 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1949 + difference 0 5) (sourceB1949 + difference 5 0) sourceC1949) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4841) := by
    have ha : (tripleCharges (sourceA1949 + difference 0 5) (sourceB1949 + difference 5 0) sourceC1949) = raw27642 := by
      apply Matrix.ext; unfold tripleCharges sourceA1949 sourceB1949 sourceC1949 difference raw27642; decide +kernel
    rw [ha]
    exact (canonical27642 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1949 + difference 1 0) (sourceB1949 + difference 0 1) sourceC1949) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4871) := by
    have ha : (tripleCharges (sourceA1949 + difference 1 0) (sourceB1949 + difference 0 1) sourceC1949) = raw27643 := by
      apply Matrix.ext; unfold tripleCharges sourceA1949 sourceB1949 sourceC1949 difference raw27643; decide +kernel
    rw [ha]
    exact (canonical27643 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1949 + difference 1 2) (sourceB1949 + difference 2 1) sourceC1949) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5139) := by
    have ha : (tripleCharges (sourceA1949 + difference 1 2) (sourceB1949 + difference 2 1) sourceC1949) = raw27644 := by
      apply Matrix.ext; unfold tripleCharges sourceA1949 sourceB1949 sourceC1949 difference raw27644; decide +kernel
    rw [ha]
    exact (canonical27644 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1949 + difference 1 3) (sourceB1949 + difference 3 1) sourceC1949) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5139) := by
    have ha : (tripleCharges (sourceA1949 + difference 1 3) (sourceB1949 + difference 3 1) sourceC1949) = raw27645 := by
      apply Matrix.ext; unfold tripleCharges sourceA1949 sourceB1949 sourceC1949 difference raw27645; decide +kernel
    rw [ha]
    exact (canonical27645 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1949 + difference 1 4) (sourceB1949 + difference 4 1) sourceC1949) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5109) := by
    have ha : (tripleCharges (sourceA1949 + difference 1 4) (sourceB1949 + difference 4 1) sourceC1949) = raw27646 := by
      apply Matrix.ext; unfold tripleCharges sourceA1949 sourceB1949 sourceC1949 difference raw27646; decide +kernel
    rw [ha]
    exact (canonical27646 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1949 + difference 1 5) (sourceB1949 + difference 5 1) sourceC1949) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4843) := by
    have ha : (tripleCharges (sourceA1949 + difference 1 5) (sourceB1949 + difference 5 1) sourceC1949) = raw27647 := by
      apply Matrix.ext; unfold tripleCharges sourceA1949 sourceB1949 sourceC1949 difference raw27647; decide +kernel
    rw [ha]
    exact (canonical27647 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1949 + difference 2 0) (sourceB1949 + difference 0 2) sourceC1949) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA1949 + difference 2 0) (sourceB1949 + difference 0 2) sourceC1949) = raw27648 := by
      apply Matrix.ext; unfold tripleCharges sourceA1949 sourceB1949 sourceC1949 difference raw27648; decide +kernel
    rw [ha]
    exact (canonical27648 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1949 + difference 2 1) (sourceB1949 + difference 1 2) sourceC1949) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5078) := by
    have ha : (tripleCharges (sourceA1949 + difference 2 1) (sourceB1949 + difference 1 2) sourceC1949) = raw27649 := by
      apply Matrix.ext; unfold tripleCharges sourceA1949 sourceB1949 sourceC1949 difference raw27649; decide +kernel
    rw [ha]
    exact (canonical27649 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1949 + difference 2 3) (sourceB1949 + difference 3 2) sourceC1949) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5128) := by
    have ha : (tripleCharges (sourceA1949 + difference 2 3) (sourceB1949 + difference 3 2) sourceC1949) = raw27650 := by
      apply Matrix.ext; unfold tripleCharges sourceA1949 sourceB1949 sourceC1949 difference raw27650; decide +kernel
    rw [ha]
    exact (canonical27650 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1949 + difference 2 4) (sourceB1949 + difference 4 2) sourceC1949) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5078) := by
    have ha : (tripleCharges (sourceA1949 + difference 2 4) (sourceB1949 + difference 4 2) sourceC1949) = raw27651 := by
      apply Matrix.ext; unfold tripleCharges sourceA1949 sourceB1949 sourceC1949 difference raw27651; decide +kernel
    rw [ha]
    exact (canonical27651 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1949 + difference 2 5) (sourceB1949 + difference 5 2) sourceC1949) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA1949 + difference 2 5) (sourceB1949 + difference 5 2) sourceC1949) = raw27652 := by
      apply Matrix.ext; unfold tripleCharges sourceA1949 sourceB1949 sourceC1949 difference raw27652; decide +kernel
    rw [ha]
    exact (canonical27652 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1949 + difference 3 0) (sourceB1949 + difference 0 3) sourceC1949) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA1949 + difference 3 0) (sourceB1949 + difference 0 3) sourceC1949) = raw27653 := by
      apply Matrix.ext; unfold tripleCharges sourceA1949 sourceB1949 sourceC1949 difference raw27653; decide +kernel
    rw [ha]
    exact (canonical27653 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1949 + difference 3 1) (sourceB1949 + difference 1 3) sourceC1949) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5078) := by
    have ha : (tripleCharges (sourceA1949 + difference 3 1) (sourceB1949 + difference 1 3) sourceC1949) = raw27654 := by
      apply Matrix.ext; unfold tripleCharges sourceA1949 sourceB1949 sourceC1949 difference raw27654; decide +kernel
    rw [ha]
    exact (canonical27654 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1949 + difference 3 2) (sourceB1949 + difference 2 3) sourceC1949) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5128) := by
    have ha : (tripleCharges (sourceA1949 + difference 3 2) (sourceB1949 + difference 2 3) sourceC1949) = raw27655 := by
      apply Matrix.ext; unfold tripleCharges sourceA1949 sourceB1949 sourceC1949 difference raw27655; decide +kernel
    rw [ha]
    exact (canonical27655 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1949 + difference 3 4) (sourceB1949 + difference 4 3) sourceC1949) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5078) := by
    have ha : (tripleCharges (sourceA1949 + difference 3 4) (sourceB1949 + difference 4 3) sourceC1949) = raw27656 := by
      apply Matrix.ext; unfold tripleCharges sourceA1949 sourceB1949 sourceC1949 difference raw27656; decide +kernel
    rw [ha]
    exact (canonical27656 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1949 + difference 3 5) (sourceB1949 + difference 5 3) sourceC1949) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA1949 + difference 3 5) (sourceB1949 + difference 5 3) sourceC1949) = raw27657 := by
      apply Matrix.ext; unfold tripleCharges sourceA1949 sourceB1949 sourceC1949 difference raw27657; decide +kernel
    rw [ha]
    exact (canonical27657 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1949 + difference 4 0) (sourceB1949 + difference 0 4) sourceC1949) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4843) := by
    have ha : (tripleCharges (sourceA1949 + difference 4 0) (sourceB1949 + difference 0 4) sourceC1949) = raw27658 := by
      apply Matrix.ext; unfold tripleCharges sourceA1949 sourceB1949 sourceC1949 difference raw27658; decide +kernel
    rw [ha]
    exact (canonical27658 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1949 + difference 4 1) (sourceB1949 + difference 1 4) sourceC1949) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5109) := by
    have ha : (tripleCharges (sourceA1949 + difference 4 1) (sourceB1949 + difference 1 4) sourceC1949) = raw27659 := by
      apply Matrix.ext; unfold tripleCharges sourceA1949 sourceB1949 sourceC1949 difference raw27659; decide +kernel
    rw [ha]
    exact (canonical27659 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1949 + difference 4 2) (sourceB1949 + difference 2 4) sourceC1949) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5139) := by
    have ha : (tripleCharges (sourceA1949 + difference 4 2) (sourceB1949 + difference 2 4) sourceC1949) = raw27660 := by
      apply Matrix.ext; unfold tripleCharges sourceA1949 sourceB1949 sourceC1949 difference raw27660; decide +kernel
    rw [ha]
    exact (canonical27660 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1949 + difference 4 3) (sourceB1949 + difference 3 4) sourceC1949) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5139) := by
    have ha : (tripleCharges (sourceA1949 + difference 4 3) (sourceB1949 + difference 3 4) sourceC1949) = raw27661 := by
      apply Matrix.ext; unfold tripleCharges sourceA1949 sourceB1949 sourceC1949 difference raw27661; decide +kernel
    rw [ha]
    exact (canonical27661 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1949 + difference 4 5) (sourceB1949 + difference 5 4) sourceC1949) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4871) := by
    have ha : (tripleCharges (sourceA1949 + difference 4 5) (sourceB1949 + difference 5 4) sourceC1949) = raw27662 := by
      apply Matrix.ext; unfold tripleCharges sourceA1949 sourceB1949 sourceC1949 difference raw27662; decide +kernel
    rw [ha]
    exact (canonical27662 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1949 + difference 5 0) (sourceB1949 + difference 0 5) sourceC1949) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4841) := by
    have ha : (tripleCharges (sourceA1949 + difference 5 0) (sourceB1949 + difference 0 5) sourceC1949) = raw27663 := by
      apply Matrix.ext; unfold tripleCharges sourceA1949 sourceB1949 sourceC1949 difference raw27663; decide +kernel
    rw [ha]
    exact (canonical27663 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1949 + difference 5 1) (sourceB1949 + difference 1 5) sourceC1949) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5107) := by
    have ha : (tripleCharges (sourceA1949 + difference 5 1) (sourceB1949 + difference 1 5) sourceC1949) = raw27664 := by
      apply Matrix.ext; unfold tripleCharges sourceA1949 sourceB1949 sourceC1949 difference raw27664; decide +kernel
    rw [ha]
    exact (canonical27664 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1949 + difference 5 2) (sourceB1949 + difference 2 5) sourceC1949) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA1949 + difference 5 2) (sourceB1949 + difference 2 5) sourceC1949) = raw27665 := by
      apply Matrix.ext; unfold tripleCharges sourceA1949 sourceB1949 sourceC1949 difference raw27665; decide +kernel
    rw [ha]
    exact (canonical27665 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1949 + difference 5 3) (sourceB1949 + difference 3 5) sourceC1949) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA1949 + difference 5 3) (sourceB1949 + difference 3 5) sourceC1949) = raw27666 := by
      apply Matrix.ext; unfold tripleCharges sourceA1949 sourceB1949 sourceC1949 difference raw27666; decide +kernel
    rw [ha]
    exact (canonical27666 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1949 + difference 5 4) (sourceB1949 + difference 4 5) sourceC1949) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5171) := by
    have ha : (tripleCharges (sourceA1949 + difference 5 4) (sourceB1949 + difference 4 5) sourceC1949) = raw27667 := by
      apply Matrix.ext; unfold tripleCharges sourceA1949 sourceB1949 sourceC1949 difference raw27667; decide +kernel
    rw [ha]
    exact (canonical27667 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1949 sourceB1949 sourceC1949
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1949, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1950 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1950 : Charge := ![1, 1, 0, 0, 1, -3]
def sourceC1950 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceForm1950 : Integer.Sparse Master := [(Sum.inr 4237, 2), (Sum.inr 4240, 1), (Sum.inr 4243, 1), (Sum.inr 4276, 1), (Sum.inr 4538, 2), (Sum.inr 4557, 1), (Sum.inr 4621, 1), (Sum.inr 4686, 2), (Sum.inr 4693, 1), (Sum.inr 4723, 2), (Sum.inr 4727, 2), (Sum.inr 4747, 2), (Sum.inr 4869, 2), (Sum.inr 4871, 2), (Sum.inr 4874, 1), (Sum.inr 4898, 1), (Sum.inr 4899, 1), (Sum.inr 5170, 2), (Sum.inr 5176, 1), (Sum.inr 5310, 1), (Sum.inr 5443, 1)]

theorem sourceEq1950 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1950 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1950 + difference 0 1) (sourceB1950 + difference 1 0) sourceC1950) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4874) := by
    have ha : (tripleCharges (sourceA1950 + difference 0 1) (sourceB1950 + difference 1 0) sourceC1950) = raw14890 := by
      apply Matrix.ext; unfold tripleCharges sourceA1950 sourceB1950 sourceC1950 difference raw14890; decide +kernel
    rw [ha]
    exact (canonical14890 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1950 + difference 0 2) (sourceB1950 + difference 2 0) sourceC1950) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4869) := by
    have ha : (tripleCharges (sourceA1950 + difference 0 2) (sourceB1950 + difference 2 0) sourceC1950) = raw14891 := by
      apply Matrix.ext; unfold tripleCharges sourceA1950 sourceB1950 sourceC1950 difference raw14891; decide +kernel
    rw [ha]
    exact (canonical14891 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1950 + difference 0 3) (sourceB1950 + difference 3 0) sourceC1950) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4869) := by
    have ha : (tripleCharges (sourceA1950 + difference 0 3) (sourceB1950 + difference 3 0) sourceC1950) = raw14892 := by
      apply Matrix.ext; unfold tripleCharges sourceA1950 sourceB1950 sourceC1950 difference raw14892; decide +kernel
    rw [ha]
    exact (canonical14892 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1950 + difference 0 4) (sourceB1950 + difference 4 0) sourceC1950) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4898) := by
    have ha : (tripleCharges (sourceA1950 + difference 0 4) (sourceB1950 + difference 4 0) sourceC1950) = raw2657 := by
      apply Matrix.ext; unfold tripleCharges sourceA1950 sourceB1950 sourceC1950 difference raw2657; decide +kernel
    rw [ha]
    exact (canonical2657 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1950 + difference 0 5) (sourceB1950 + difference 5 0) sourceC1950) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA1950 + difference 0 5) (sourceB1950 + difference 5 0) sourceC1950) = raw2652 := by
      apply Matrix.ext; unfold tripleCharges sourceA1950 sourceB1950 sourceC1950 difference raw2652; decide +kernel
    rw [ha]
    exact (canonical2652 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1950 + difference 1 0) (sourceB1950 + difference 0 1) sourceC1950) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4621) := by
    have ha : (tripleCharges (sourceA1950 + difference 1 0) (sourceB1950 + difference 0 1) sourceC1950) = raw4392 := by
      apply Matrix.ext; unfold tripleCharges sourceA1950 sourceB1950 sourceC1950 difference raw4392; decide +kernel
    rw [ha]
    exact (canonical4392 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1950 + difference 1 2) (sourceB1950 + difference 2 1) sourceC1950) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4871) := by
    have ha : (tripleCharges (sourceA1950 + difference 1 2) (sourceB1950 + difference 2 1) sourceC1950) = raw4394 := by
      apply Matrix.ext; unfold tripleCharges sourceA1950 sourceB1950 sourceC1950 difference raw4394; decide +kernel
    rw [ha]
    exact (canonical4394 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1950 + difference 1 3) (sourceB1950 + difference 3 1) sourceC1950) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4871) := by
    have ha : (tripleCharges (sourceA1950 + difference 1 3) (sourceB1950 + difference 3 1) sourceC1950) = raw4395 := by
      apply Matrix.ext; unfold tripleCharges sourceA1950 sourceB1950 sourceC1950 difference raw4395; decide +kernel
    rw [ha]
    exact (canonical4395 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1950 + difference 1 4) (sourceB1950 + difference 4 1) sourceC1950) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4899) := by
    have ha : (tripleCharges (sourceA1950 + difference 1 4) (sourceB1950 + difference 4 1) sourceC1950) = raw2656 := by
      apply Matrix.ext; unfold tripleCharges sourceA1950 sourceB1950 sourceC1950 difference raw2656; decide +kernel
    rw [ha]
    exact (canonical2656 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1950 + difference 1 5) (sourceB1950 + difference 5 1) sourceC1950) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5310) := by
    have ha : (tripleCharges (sourceA1950 + difference 1 5) (sourceB1950 + difference 5 1) sourceC1950) = raw2651 := by
      apply Matrix.ext; unfold tripleCharges sourceA1950 sourceB1950 sourceC1950 difference raw2651; decide +kernel
    rw [ha]
    exact (canonical2651 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1950 + difference 2 0) (sourceB1950 + difference 0 2) sourceC1950) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4538) := by
    have ha : (tripleCharges (sourceA1950 + difference 2 0) (sourceB1950 + difference 0 2) sourceC1950) = raw20538 := by
      apply Matrix.ext; unfold tripleCharges sourceA1950 sourceB1950 sourceC1950 difference raw20538; decide +kernel
    rw [ha]
    exact (canonical20538 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1950 + difference 2 1) (sourceB1950 + difference 1 2) sourceC1950) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4727) := by
    have ha : (tripleCharges (sourceA1950 + difference 2 1) (sourceB1950 + difference 1 2) sourceC1950) = raw27668 := by
      apply Matrix.ext; unfold tripleCharges sourceA1950 sourceB1950 sourceC1950 difference raw27668; decide +kernel
    rw [ha]
    exact (canonical27668 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1950 + difference 2 3) (sourceB1950 + difference 3 2) sourceC1950) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4723) := by
    have ha : (tripleCharges (sourceA1950 + difference 2 3) (sourceB1950 + difference 3 2) sourceC1950) = raw27669 := by
      apply Matrix.ext; unfold tripleCharges sourceA1950 sourceB1950 sourceC1950 difference raw27669; decide +kernel
    rw [ha]
    exact (canonical27669 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1950 + difference 2 4) (sourceB1950 + difference 4 2) sourceC1950) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4747) := by
    have ha : (tripleCharges (sourceA1950 + difference 2 4) (sourceB1950 + difference 4 2) sourceC1950) = raw4385 := by
      apply Matrix.ext; unfold tripleCharges sourceA1950 sourceB1950 sourceC1950 difference raw4385; decide +kernel
    rw [ha]
    exact (canonical4385 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1950 + difference 2 5) (sourceB1950 + difference 5 2) sourceC1950) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5170) := by
    have ha : (tripleCharges (sourceA1950 + difference 2 5) (sourceB1950 + difference 5 2) sourceC1950) = raw7563 := by
      apply Matrix.ext; unfold tripleCharges sourceA1950 sourceB1950 sourceC1950 difference raw7563; decide +kernel
    rw [ha]
    exact (canonical7563 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1950 + difference 3 0) (sourceB1950 + difference 0 3) sourceC1950) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4538) := by
    have ha : (tripleCharges (sourceA1950 + difference 3 0) (sourceB1950 + difference 0 3) sourceC1950) = raw20541 := by
      apply Matrix.ext; unfold tripleCharges sourceA1950 sourceB1950 sourceC1950 difference raw20541; decide +kernel
    rw [ha]
    exact (canonical20541 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1950 + difference 3 1) (sourceB1950 + difference 1 3) sourceC1950) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4727) := by
    have ha : (tripleCharges (sourceA1950 + difference 3 1) (sourceB1950 + difference 1 3) sourceC1950) = raw27670 := by
      apply Matrix.ext; unfold tripleCharges sourceA1950 sourceB1950 sourceC1950 difference raw27670; decide +kernel
    rw [ha]
    exact (canonical27670 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1950 + difference 3 2) (sourceB1950 + difference 2 3) sourceC1950) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4723) := by
    have ha : (tripleCharges (sourceA1950 + difference 3 2) (sourceB1950 + difference 2 3) sourceC1950) = raw27671 := by
      apply Matrix.ext; unfold tripleCharges sourceA1950 sourceB1950 sourceC1950 difference raw27671; decide +kernel
    rw [ha]
    exact (canonical27671 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1950 + difference 3 4) (sourceB1950 + difference 4 3) sourceC1950) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4747) := by
    have ha : (tripleCharges (sourceA1950 + difference 3 4) (sourceB1950 + difference 4 3) sourceC1950) = raw4389 := by
      apply Matrix.ext; unfold tripleCharges sourceA1950 sourceB1950 sourceC1950 difference raw4389; decide +kernel
    rw [ha]
    exact (canonical4389 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1950 + difference 3 5) (sourceB1950 + difference 5 3) sourceC1950) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5170) := by
    have ha : (tripleCharges (sourceA1950 + difference 3 5) (sourceB1950 + difference 5 3) sourceC1950) = raw7567 := by
      apply Matrix.ext; unfold tripleCharges sourceA1950 sourceB1950 sourceC1950 difference raw7567; decide +kernel
    rw [ha]
    exact (canonical7567 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1950 + difference 4 0) (sourceB1950 + difference 0 4) sourceC1950) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4557) := by
    have ha : (tripleCharges (sourceA1950 + difference 4 0) (sourceB1950 + difference 0 4) sourceC1950) = raw20544 := by
      apply Matrix.ext; unfold tripleCharges sourceA1950 sourceB1950 sourceC1950 difference raw20544; decide +kernel
    rw [ha]
    exact (canonical20544 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1950 + difference 4 1) (sourceB1950 + difference 1 4) sourceC1950) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4693) := by
    have ha : (tripleCharges (sourceA1950 + difference 4 1) (sourceB1950 + difference 1 4) sourceC1950) = raw27672 := by
      apply Matrix.ext; unfold tripleCharges sourceA1950 sourceB1950 sourceC1950 difference raw27672; decide +kernel
    rw [ha]
    exact (canonical27672 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1950 + difference 4 2) (sourceB1950 + difference 2 4) sourceC1950) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4686) := by
    have ha : (tripleCharges (sourceA1950 + difference 4 2) (sourceB1950 + difference 2 4) sourceC1950) = raw27673 := by
      apply Matrix.ext; unfold tripleCharges sourceA1950 sourceB1950 sourceC1950 difference raw27673; decide +kernel
    rw [ha]
    exact (canonical27673 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1950 + difference 4 3) (sourceB1950 + difference 3 4) sourceC1950) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4686) := by
    have ha : (tripleCharges (sourceA1950 + difference 4 3) (sourceB1950 + difference 3 4) sourceC1950) = raw27674 := by
      apply Matrix.ext; unfold tripleCharges sourceA1950 sourceB1950 sourceC1950 difference raw27674; decide +kernel
    rw [ha]
    exact (canonical27674 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1950 + difference 4 5) (sourceB1950 + difference 5 4) sourceC1950) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5176) := by
    have ha : (tripleCharges (sourceA1950 + difference 4 5) (sourceB1950 + difference 5 4) sourceC1950) = raw7571 := by
      apply Matrix.ext; unfold tripleCharges sourceA1950 sourceB1950 sourceC1950 difference raw7571; decide +kernel
    rw [ha]
    exact (canonical7571 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1950 + difference 5 0) (sourceB1950 + difference 0 5) sourceC1950) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4240) := by
    have ha : (tripleCharges (sourceA1950 + difference 5 0) (sourceB1950 + difference 0 5) sourceC1950) = raw20548 := by
      apply Matrix.ext; unfold tripleCharges sourceA1950 sourceB1950 sourceC1950 difference raw20548; decide +kernel
    rw [ha]
    exact (canonical20548 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1950 + difference 5 1) (sourceB1950 + difference 1 5) sourceC1950) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4243) := by
    have ha : (tripleCharges (sourceA1950 + difference 5 1) (sourceB1950 + difference 1 5) sourceC1950) = raw27675 := by
      apply Matrix.ext; unfold tripleCharges sourceA1950 sourceB1950 sourceC1950 difference raw27675; decide +kernel
    rw [ha]
    exact (canonical27675 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1950 + difference 5 2) (sourceB1950 + difference 2 5) sourceC1950) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4237) := by
    have ha : (tripleCharges (sourceA1950 + difference 5 2) (sourceB1950 + difference 2 5) sourceC1950) = raw27676 := by
      apply Matrix.ext; unfold tripleCharges sourceA1950 sourceB1950 sourceC1950 difference raw27676; decide +kernel
    rw [ha]
    exact (canonical27676 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1950 + difference 5 3) (sourceB1950 + difference 3 5) sourceC1950) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4237) := by
    have ha : (tripleCharges (sourceA1950 + difference 5 3) (sourceB1950 + difference 3 5) sourceC1950) = raw27677 := by
      apply Matrix.ext; unfold tripleCharges sourceA1950 sourceB1950 sourceC1950 difference raw27677; decide +kernel
    rw [ha]
    exact (canonical27677 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1950 + difference 5 4) (sourceB1950 + difference 4 5) sourceC1950) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4276) := by
    have ha : (tripleCharges (sourceA1950 + difference 5 4) (sourceB1950 + difference 4 5) sourceC1950) = raw4397 := by
      apply Matrix.ext; unfold tripleCharges sourceA1950 sourceB1950 sourceC1950 difference raw4397; decide +kernel
    rw [ha]
    exact (canonical4397 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1950 sourceB1950 sourceC1950
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1950, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1951 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1951 : Charge := ![1, 1, 0, 0, 1, -3]
def sourceC1951 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceForm1951 : Integer.Sparse Master := [(Sum.inr 737, 2), (Sum.inr 740, 1), (Sum.inr 743, 1), (Sum.inr 828, 1), (Sum.inr 1123, 2), (Sum.inr 1143, 1), (Sum.inr 1297, 1), (Sum.inr 1812, 2), (Sum.inr 1819, 1), (Sum.inr 1877, 2), (Sum.inr 1881, 2), (Sum.inr 1926, 2), (Sum.inr 2110, 2), (Sum.inr 2112, 2), (Sum.inr 2115, 1), (Sum.inr 2279, 1), (Sum.inr 2281, 1), (Sum.inr 2954, 2), (Sum.inr 2968, 1), (Sum.inr 3121, 1), (Sum.inr 3889, 1)]

theorem sourceEq1951 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1951 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1951 + difference 0 1) (sourceB1951 + difference 1 0) sourceC1951) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2115) := by
    have ha : (tripleCharges (sourceA1951 + difference 0 1) (sourceB1951 + difference 1 0) sourceC1951) = raw14910 := by
      apply Matrix.ext; unfold tripleCharges sourceA1951 sourceB1951 sourceC1951 difference raw14910; decide +kernel
    rw [ha]
    exact (canonical14910 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1951 + difference 0 2) (sourceB1951 + difference 2 0) sourceC1951) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2110) := by
    have ha : (tripleCharges (sourceA1951 + difference 0 2) (sourceB1951 + difference 2 0) sourceC1951) = raw14911 := by
      apply Matrix.ext; unfold tripleCharges sourceA1951 sourceB1951 sourceC1951 difference raw14911; decide +kernel
    rw [ha]
    exact (canonical14911 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1951 + difference 0 3) (sourceB1951 + difference 3 0) sourceC1951) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2110) := by
    have ha : (tripleCharges (sourceA1951 + difference 0 3) (sourceB1951 + difference 3 0) sourceC1951) = raw14912 := by
      apply Matrix.ext; unfold tripleCharges sourceA1951 sourceB1951 sourceC1951 difference raw14912; decide +kernel
    rw [ha]
    exact (canonical14912 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1951 + difference 0 4) (sourceB1951 + difference 4 0) sourceC1951) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2279) := by
    have ha : (tripleCharges (sourceA1951 + difference 0 4) (sourceB1951 + difference 4 0) sourceC1951) = raw4401 := by
      apply Matrix.ext; unfold tripleCharges sourceA1951 sourceB1951 sourceC1951 difference raw4401; decide +kernel
    rw [ha]
    exact (canonical4401 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1951 + difference 0 5) (sourceB1951 + difference 5 0) sourceC1951) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3889) := by
    have ha : (tripleCharges (sourceA1951 + difference 0 5) (sourceB1951 + difference 5 0) sourceC1951) = raw7575 := by
      apply Matrix.ext; unfold tripleCharges sourceA1951 sourceB1951 sourceC1951 difference raw7575; decide +kernel
    rw [ha]
    exact (canonical7575 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1951 + difference 1 0) (sourceB1951 + difference 0 1) sourceC1951) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1297) := by
    have ha : (tripleCharges (sourceA1951 + difference 1 0) (sourceB1951 + difference 0 1) sourceC1951) = raw4421 := by
      apply Matrix.ext; unfold tripleCharges sourceA1951 sourceB1951 sourceC1951 difference raw4421; decide +kernel
    rw [ha]
    exact (canonical4421 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1951 + difference 1 2) (sourceB1951 + difference 2 1) sourceC1951) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2112) := by
    have ha : (tripleCharges (sourceA1951 + difference 1 2) (sourceB1951 + difference 2 1) sourceC1951) = raw4423 := by
      apply Matrix.ext; unfold tripleCharges sourceA1951 sourceB1951 sourceC1951 difference raw4423; decide +kernel
    rw [ha]
    exact (canonical4423 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1951 + difference 1 3) (sourceB1951 + difference 3 1) sourceC1951) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2112) := by
    have ha : (tripleCharges (sourceA1951 + difference 1 3) (sourceB1951 + difference 3 1) sourceC1951) = raw4424 := by
      apply Matrix.ext; unfold tripleCharges sourceA1951 sourceB1951 sourceC1951 difference raw4424; decide +kernel
    rw [ha]
    exact (canonical4424 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1951 + difference 1 4) (sourceB1951 + difference 4 1) sourceC1951) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2281) := by
    have ha : (tripleCharges (sourceA1951 + difference 1 4) (sourceB1951 + difference 4 1) sourceC1951) = raw7596 := by
      apply Matrix.ext; unfold tripleCharges sourceA1951 sourceB1951 sourceC1951 difference raw7596; decide +kernel
    rw [ha]
    exact (canonical7596 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1951 + difference 1 5) (sourceB1951 + difference 5 1) sourceC1951) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3121) := by
    have ha : (tripleCharges (sourceA1951 + difference 1 5) (sourceB1951 + difference 5 1) sourceC1951) = raw4425 := by
      apply Matrix.ext; unfold tripleCharges sourceA1951 sourceB1951 sourceC1951 difference raw4425; decide +kernel
    rw [ha]
    exact (canonical4425 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1951 + difference 2 0) (sourceB1951 + difference 0 2) sourceC1951) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1123) := by
    have ha : (tripleCharges (sourceA1951 + difference 2 0) (sourceB1951 + difference 0 2) sourceC1951) = raw20555 := by
      apply Matrix.ext; unfold tripleCharges sourceA1951 sourceB1951 sourceC1951 difference raw20555; decide +kernel
    rw [ha]
    exact (canonical20555 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1951 + difference 2 1) (sourceB1951 + difference 1 2) sourceC1951) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1881) := by
    have ha : (tripleCharges (sourceA1951 + difference 2 1) (sourceB1951 + difference 1 2) sourceC1951) = raw27678 := by
      apply Matrix.ext; unfold tripleCharges sourceA1951 sourceB1951 sourceC1951 difference raw27678; decide +kernel
    rw [ha]
    exact (canonical27678 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1951 + difference 2 3) (sourceB1951 + difference 3 2) sourceC1951) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1877) := by
    have ha : (tripleCharges (sourceA1951 + difference 2 3) (sourceB1951 + difference 3 2) sourceC1951) = raw27679 := by
      apply Matrix.ext; unfold tripleCharges sourceA1951 sourceB1951 sourceC1951 difference raw27679; decide +kernel
    rw [ha]
    exact (canonical27679 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1951 + difference 2 4) (sourceB1951 + difference 4 2) sourceC1951) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1926) := by
    have ha : (tripleCharges (sourceA1951 + difference 2 4) (sourceB1951 + difference 4 2) sourceC1951) = raw4412 := by
      apply Matrix.ext; unfold tripleCharges sourceA1951 sourceB1951 sourceC1951 difference raw4412; decide +kernel
    rw [ha]
    exact (canonical4412 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1951 + difference 2 5) (sourceB1951 + difference 5 2) sourceC1951) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2954) := by
    have ha : (tripleCharges (sourceA1951 + difference 2 5) (sourceB1951 + difference 5 2) sourceC1951) = raw7584 := by
      apply Matrix.ext; unfold tripleCharges sourceA1951 sourceB1951 sourceC1951 difference raw7584; decide +kernel
    rw [ha]
    exact (canonical7584 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1951 + difference 3 0) (sourceB1951 + difference 0 3) sourceC1951) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1123) := by
    have ha : (tripleCharges (sourceA1951 + difference 3 0) (sourceB1951 + difference 0 3) sourceC1951) = raw20558 := by
      apply Matrix.ext; unfold tripleCharges sourceA1951 sourceB1951 sourceC1951 difference raw20558; decide +kernel
    rw [ha]
    exact (canonical20558 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1951 + difference 3 1) (sourceB1951 + difference 1 3) sourceC1951) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1881) := by
    have ha : (tripleCharges (sourceA1951 + difference 3 1) (sourceB1951 + difference 1 3) sourceC1951) = raw27680 := by
      apply Matrix.ext; unfold tripleCharges sourceA1951 sourceB1951 sourceC1951 difference raw27680; decide +kernel
    rw [ha]
    exact (canonical27680 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1951 + difference 3 2) (sourceB1951 + difference 2 3) sourceC1951) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1877) := by
    have ha : (tripleCharges (sourceA1951 + difference 3 2) (sourceB1951 + difference 2 3) sourceC1951) = raw27681 := by
      apply Matrix.ext; unfold tripleCharges sourceA1951 sourceB1951 sourceC1951 difference raw27681; decide +kernel
    rw [ha]
    exact (canonical27681 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1951 + difference 3 4) (sourceB1951 + difference 4 3) sourceC1951) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1926) := by
    have ha : (tripleCharges (sourceA1951 + difference 3 4) (sourceB1951 + difference 4 3) sourceC1951) = raw4417 := by
      apply Matrix.ext; unfold tripleCharges sourceA1951 sourceB1951 sourceC1951 difference raw4417; decide +kernel
    rw [ha]
    exact (canonical4417 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1951 + difference 3 5) (sourceB1951 + difference 5 3) sourceC1951) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2954) := by
    have ha : (tripleCharges (sourceA1951 + difference 3 5) (sourceB1951 + difference 5 3) sourceC1951) = raw7588 := by
      apply Matrix.ext; unfold tripleCharges sourceA1951 sourceB1951 sourceC1951 difference raw7588; decide +kernel
    rw [ha]
    exact (canonical7588 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1951 + difference 4 0) (sourceB1951 + difference 0 4) sourceC1951) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1143) := by
    have ha : (tripleCharges (sourceA1951 + difference 4 0) (sourceB1951 + difference 0 4) sourceC1951) = raw20561 := by
      apply Matrix.ext; unfold tripleCharges sourceA1951 sourceB1951 sourceC1951 difference raw20561; decide +kernel
    rw [ha]
    exact (canonical20561 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1951 + difference 4 1) (sourceB1951 + difference 1 4) sourceC1951) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1819) := by
    have ha : (tripleCharges (sourceA1951 + difference 4 1) (sourceB1951 + difference 1 4) sourceC1951) = raw27682 := by
      apply Matrix.ext; unfold tripleCharges sourceA1951 sourceB1951 sourceC1951 difference raw27682; decide +kernel
    rw [ha]
    exact (canonical27682 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1951 + difference 4 2) (sourceB1951 + difference 2 4) sourceC1951) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1812) := by
    have ha : (tripleCharges (sourceA1951 + difference 4 2) (sourceB1951 + difference 2 4) sourceC1951) = raw27683 := by
      apply Matrix.ext; unfold tripleCharges sourceA1951 sourceB1951 sourceC1951 difference raw27683; decide +kernel
    rw [ha]
    exact (canonical27683 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1951 + difference 4 3) (sourceB1951 + difference 3 4) sourceC1951) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1812) := by
    have ha : (tripleCharges (sourceA1951 + difference 4 3) (sourceB1951 + difference 3 4) sourceC1951) = raw27684 := by
      apply Matrix.ext; unfold tripleCharges sourceA1951 sourceB1951 sourceC1951 difference raw27684; decide +kernel
    rw [ha]
    exact (canonical27684 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1951 + difference 4 5) (sourceB1951 + difference 5 4) sourceC1951) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2968) := by
    have ha : (tripleCharges (sourceA1951 + difference 4 5) (sourceB1951 + difference 5 4) sourceC1951) = raw7592 := by
      apply Matrix.ext; unfold tripleCharges sourceA1951 sourceB1951 sourceC1951 difference raw7592; decide +kernel
    rw [ha]
    exact (canonical7592 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1951 + difference 5 0) (sourceB1951 + difference 0 5) sourceC1951) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 740) := by
    have ha : (tripleCharges (sourceA1951 + difference 5 0) (sourceB1951 + difference 0 5) sourceC1951) = raw20565 := by
      apply Matrix.ext; unfold tripleCharges sourceA1951 sourceB1951 sourceC1951 difference raw20565; decide +kernel
    rw [ha]
    exact (canonical20565 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1951 + difference 5 1) (sourceB1951 + difference 1 5) sourceC1951) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 743) := by
    have ha : (tripleCharges (sourceA1951 + difference 5 1) (sourceB1951 + difference 1 5) sourceC1951) = raw27685 := by
      apply Matrix.ext; unfold tripleCharges sourceA1951 sourceB1951 sourceC1951 difference raw27685; decide +kernel
    rw [ha]
    exact (canonical27685 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1951 + difference 5 2) (sourceB1951 + difference 2 5) sourceC1951) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 737) := by
    have ha : (tripleCharges (sourceA1951 + difference 5 2) (sourceB1951 + difference 2 5) sourceC1951) = raw27686 := by
      apply Matrix.ext; unfold tripleCharges sourceA1951 sourceB1951 sourceC1951 difference raw27686; decide +kernel
    rw [ha]
    exact (canonical27686 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1951 + difference 5 3) (sourceB1951 + difference 3 5) sourceC1951) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 737) := by
    have ha : (tripleCharges (sourceA1951 + difference 5 3) (sourceB1951 + difference 3 5) sourceC1951) = raw27687 := by
      apply Matrix.ext; unfold tripleCharges sourceA1951 sourceB1951 sourceC1951 difference raw27687; decide +kernel
    rw [ha]
    exact (canonical27687 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1951 + difference 5 4) (sourceB1951 + difference 4 5) sourceC1951) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 828) := by
    have ha : (tripleCharges (sourceA1951 + difference 5 4) (sourceB1951 + difference 4 5) sourceC1951) = raw4427 := by
      apply Matrix.ext; unfold tripleCharges sourceA1951 sourceB1951 sourceC1951 difference raw4427; decide +kernel
    rw [ha]
    exact (canonical4427 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1951 sourceB1951 sourceC1951
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1951, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
