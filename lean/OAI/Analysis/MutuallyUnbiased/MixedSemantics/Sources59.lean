import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical90
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical112
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical156
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical157
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical179
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical185
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical197
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical205
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical208
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical209
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical211
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical212
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical213
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical214

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA1888 : Charge := ![1, -1, 0, 0, 0, 0]
def sourceB1888 : Charge := ![3, 1, -1, -1, -1, -1]
def sourceC1888 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceForm1888 : Integer.Sparse Master := [(Sum.inr 4068, 1), (Sum.inr 4216, 4), (Sum.inr 4379, 4), (Sum.inr 4417, 12), (Sum.inr 4497, 4), (Sum.inr 4569, 1), (Sum.inr 4601, 4)]

theorem sourceEq1888 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1888 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1888 + difference 0 1) (sourceB1888 + difference 1 0) sourceC1888) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4569) := by
    have ha : (tripleCharges (sourceA1888 + difference 0 1) (sourceB1888 + difference 1 0) sourceC1888) = raw26876 := by
      apply Matrix.ext; unfold tripleCharges sourceA1888 sourceB1888 sourceC1888 difference raw26876; decide +kernel
    rw [ha]
    exact (canonical26876 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1888 + difference 0 2) (sourceB1888 + difference 2 0) sourceC1888) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4601) := by
    have ha : (tripleCharges (sourceA1888 + difference 0 2) (sourceB1888 + difference 2 0) sourceC1888) = raw26692 := by
      apply Matrix.ext; unfold tripleCharges sourceA1888 sourceB1888 sourceC1888 difference raw26692; decide +kernel
    rw [ha]
    exact (canonical26692 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1888 + difference 0 3) (sourceB1888 + difference 3 0) sourceC1888) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4601) := by
    have ha : (tripleCharges (sourceA1888 + difference 0 3) (sourceB1888 + difference 3 0) sourceC1888) = raw26688 := by
      apply Matrix.ext; unfold tripleCharges sourceA1888 sourceB1888 sourceC1888 difference raw26688; decide +kernel
    rw [ha]
    exact (canonical26688 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1888 + difference 0 4) (sourceB1888 + difference 4 0) sourceC1888) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4601) := by
    have ha : (tripleCharges (sourceA1888 + difference 0 4) (sourceB1888 + difference 4 0) sourceC1888) = raw26877 := by
      apply Matrix.ext; unfold tripleCharges sourceA1888 sourceB1888 sourceC1888 difference raw26877; decide +kernel
    rw [ha]
    exact (canonical26877 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1888 + difference 0 5) (sourceB1888 + difference 5 0) sourceC1888) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4601) := by
    have ha : (tripleCharges (sourceA1888 + difference 0 5) (sourceB1888 + difference 5 0) sourceC1888) = raw27245 := by
      apply Matrix.ext; unfold tripleCharges sourceA1888 sourceB1888 sourceC1888 difference raw27245; decide +kernel
    rw [ha]
    exact (canonical27245 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1888 + difference 1 0) (sourceB1888 + difference 0 1) sourceC1888) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (tripleCharges (sourceA1888 + difference 1 0) (sourceB1888 + difference 0 1) sourceC1888) = raw27246 := by
      apply Matrix.ext; unfold tripleCharges sourceA1888 sourceB1888 sourceC1888 difference raw27246; decide +kernel
    rw [ha]
    exact (canonical27246 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1888 + difference 1 2) (sourceB1888 + difference 2 1) sourceC1888) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4497) := by
    have ha : (tripleCharges (sourceA1888 + difference 1 2) (sourceB1888 + difference 2 1) sourceC1888) = raw26691 := by
      apply Matrix.ext; unfold tripleCharges sourceA1888 sourceB1888 sourceC1888 difference raw26691; decide +kernel
    rw [ha]
    exact (canonical26691 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1888 + difference 1 3) (sourceB1888 + difference 3 1) sourceC1888) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4497) := by
    have ha : (tripleCharges (sourceA1888 + difference 1 3) (sourceB1888 + difference 3 1) sourceC1888) = raw26687 := by
      apply Matrix.ext; unfold tripleCharges sourceA1888 sourceB1888 sourceC1888 difference raw26687; decide +kernel
    rw [ha]
    exact (canonical26687 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1888 + difference 1 4) (sourceB1888 + difference 4 1) sourceC1888) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4497) := by
    have ha : (tripleCharges (sourceA1888 + difference 1 4) (sourceB1888 + difference 4 1) sourceC1888) = raw27036 := by
      apply Matrix.ext; unfold tripleCharges sourceA1888 sourceB1888 sourceC1888 difference raw27036; decide +kernel
    rw [ha]
    exact (canonical27036 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1888 + difference 1 5) (sourceB1888 + difference 5 1) sourceC1888) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4497) := by
    have ha : (tripleCharges (sourceA1888 + difference 1 5) (sourceB1888 + difference 5 1) sourceC1888) = raw26857 := by
      apply Matrix.ext; unfold tripleCharges sourceA1888 sourceB1888 sourceC1888 difference raw26857; decide +kernel
    rw [ha]
    exact (canonical26857 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1888 + difference 2 0) (sourceB1888 + difference 0 2) sourceC1888) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4216) := by
    have ha : (tripleCharges (sourceA1888 + difference 2 0) (sourceB1888 + difference 0 2) sourceC1888) = raw27247 := by
      apply Matrix.ext; unfold tripleCharges sourceA1888 sourceB1888 sourceC1888 difference raw27247; decide +kernel
    rw [ha]
    exact (canonical27247 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1888 + difference 2 1) (sourceB1888 + difference 1 2) sourceC1888) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4379) := by
    have ha : (tripleCharges (sourceA1888 + difference 2 1) (sourceB1888 + difference 1 2) sourceC1888) = raw27248 := by
      apply Matrix.ext; unfold tripleCharges sourceA1888 sourceB1888 sourceC1888 difference raw27248; decide +kernel
    rw [ha]
    exact (canonical27248 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1888 + difference 2 3) (sourceB1888 + difference 3 2) sourceC1888) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4417) := by
    have ha : (tripleCharges (sourceA1888 + difference 2 3) (sourceB1888 + difference 3 2) sourceC1888) = raw27249 := by
      apply Matrix.ext; unfold tripleCharges sourceA1888 sourceB1888 sourceC1888 difference raw27249; decide +kernel
    rw [ha]
    exact (canonical27249 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1888 + difference 2 4) (sourceB1888 + difference 4 2) sourceC1888) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4417) := by
    have ha : (tripleCharges (sourceA1888 + difference 2 4) (sourceB1888 + difference 4 2) sourceC1888) = raw27168 := by
      apply Matrix.ext; unfold tripleCharges sourceA1888 sourceB1888 sourceC1888 difference raw27168; decide +kernel
    rw [ha]
    exact (canonical27168 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1888 + difference 2 5) (sourceB1888 + difference 5 2) sourceC1888) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4417) := by
    have ha : (tripleCharges (sourceA1888 + difference 2 5) (sourceB1888 + difference 5 2) sourceC1888) = raw26860 := by
      apply Matrix.ext; unfold tripleCharges sourceA1888 sourceB1888 sourceC1888 difference raw26860; decide +kernel
    rw [ha]
    exact (canonical26860 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1888 + difference 3 0) (sourceB1888 + difference 0 3) sourceC1888) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4216) := by
    have ha : (tripleCharges (sourceA1888 + difference 3 0) (sourceB1888 + difference 0 3) sourceC1888) = raw27250 := by
      apply Matrix.ext; unfold tripleCharges sourceA1888 sourceB1888 sourceC1888 difference raw27250; decide +kernel
    rw [ha]
    exact (canonical27250 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1888 + difference 3 1) (sourceB1888 + difference 1 3) sourceC1888) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4379) := by
    have ha : (tripleCharges (sourceA1888 + difference 3 1) (sourceB1888 + difference 1 3) sourceC1888) = raw27251 := by
      apply Matrix.ext; unfold tripleCharges sourceA1888 sourceB1888 sourceC1888 difference raw27251; decide +kernel
    rw [ha]
    exact (canonical27251 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1888 + difference 3 2) (sourceB1888 + difference 2 3) sourceC1888) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4417) := by
    have ha : (tripleCharges (sourceA1888 + difference 3 2) (sourceB1888 + difference 2 3) sourceC1888) = raw27252 := by
      apply Matrix.ext; unfold tripleCharges sourceA1888 sourceB1888 sourceC1888 difference raw27252; decide +kernel
    rw [ha]
    exact (canonical27252 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1888 + difference 3 4) (sourceB1888 + difference 4 3) sourceC1888) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4417) := by
    have ha : (tripleCharges (sourceA1888 + difference 3 4) (sourceB1888 + difference 4 3) sourceC1888) = raw27253 := by
      apply Matrix.ext; unfold tripleCharges sourceA1888 sourceB1888 sourceC1888 difference raw27253; decide +kernel
    rw [ha]
    exact (canonical27253 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1888 + difference 3 5) (sourceB1888 + difference 5 3) sourceC1888) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4417) := by
    have ha : (tripleCharges (sourceA1888 + difference 3 5) (sourceB1888 + difference 5 3) sourceC1888) = raw26865 := by
      apply Matrix.ext; unfold tripleCharges sourceA1888 sourceB1888 sourceC1888 difference raw26865; decide +kernel
    rw [ha]
    exact (canonical26865 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1888 + difference 4 0) (sourceB1888 + difference 0 4) sourceC1888) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4216) := by
    have ha : (tripleCharges (sourceA1888 + difference 4 0) (sourceB1888 + difference 0 4) sourceC1888) = raw27254 := by
      apply Matrix.ext; unfold tripleCharges sourceA1888 sourceB1888 sourceC1888 difference raw27254; decide +kernel
    rw [ha]
    exact (canonical27254 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1888 + difference 4 1) (sourceB1888 + difference 1 4) sourceC1888) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4379) := by
    have ha : (tripleCharges (sourceA1888 + difference 4 1) (sourceB1888 + difference 1 4) sourceC1888) = raw27255 := by
      apply Matrix.ext; unfold tripleCharges sourceA1888 sourceB1888 sourceC1888 difference raw27255; decide +kernel
    rw [ha]
    exact (canonical27255 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1888 + difference 4 2) (sourceB1888 + difference 2 4) sourceC1888) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4417) := by
    have ha : (tripleCharges (sourceA1888 + difference 4 2) (sourceB1888 + difference 2 4) sourceC1888) = raw27256 := by
      apply Matrix.ext; unfold tripleCharges sourceA1888 sourceB1888 sourceC1888 difference raw27256; decide +kernel
    rw [ha]
    exact (canonical27256 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1888 + difference 4 3) (sourceB1888 + difference 3 4) sourceC1888) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4417) := by
    have ha : (tripleCharges (sourceA1888 + difference 4 3) (sourceB1888 + difference 3 4) sourceC1888) = raw27257 := by
      apply Matrix.ext; unfold tripleCharges sourceA1888 sourceB1888 sourceC1888 difference raw27257; decide +kernel
    rw [ha]
    exact (canonical27257 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1888 + difference 4 5) (sourceB1888 + difference 5 4) sourceC1888) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4417) := by
    have ha : (tripleCharges (sourceA1888 + difference 4 5) (sourceB1888 + difference 5 4) sourceC1888) = raw26870 := by
      apply Matrix.ext; unfold tripleCharges sourceA1888 sourceB1888 sourceC1888 difference raw26870; decide +kernel
    rw [ha]
    exact (canonical26870 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1888 + difference 5 0) (sourceB1888 + difference 0 5) sourceC1888) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4216) := by
    have ha : (tripleCharges (sourceA1888 + difference 5 0) (sourceB1888 + difference 0 5) sourceC1888) = raw27258 := by
      apply Matrix.ext; unfold tripleCharges sourceA1888 sourceB1888 sourceC1888 difference raw27258; decide +kernel
    rw [ha]
    exact (canonical27258 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1888 + difference 5 1) (sourceB1888 + difference 1 5) sourceC1888) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4379) := by
    have ha : (tripleCharges (sourceA1888 + difference 5 1) (sourceB1888 + difference 1 5) sourceC1888) = raw27259 := by
      apply Matrix.ext; unfold tripleCharges sourceA1888 sourceB1888 sourceC1888 difference raw27259; decide +kernel
    rw [ha]
    exact (canonical27259 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1888 + difference 5 2) (sourceB1888 + difference 2 5) sourceC1888) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4417) := by
    have ha : (tripleCharges (sourceA1888 + difference 5 2) (sourceB1888 + difference 2 5) sourceC1888) = raw27260 := by
      apply Matrix.ext; unfold tripleCharges sourceA1888 sourceB1888 sourceC1888 difference raw27260; decide +kernel
    rw [ha]
    exact (canonical27260 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1888 + difference 5 3) (sourceB1888 + difference 3 5) sourceC1888) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4417) := by
    have ha : (tripleCharges (sourceA1888 + difference 5 3) (sourceB1888 + difference 3 5) sourceC1888) = raw27261 := by
      apply Matrix.ext; unfold tripleCharges sourceA1888 sourceB1888 sourceC1888 difference raw27261; decide +kernel
    rw [ha]
    exact (canonical27261 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1888 + difference 5 4) (sourceB1888 + difference 4 5) sourceC1888) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4417) := by
    have ha : (tripleCharges (sourceA1888 + difference 5 4) (sourceB1888 + difference 4 5) sourceC1888) = raw27262 := by
      apply Matrix.ext; unfold tripleCharges sourceA1888 sourceB1888 sourceC1888 difference raw27262; decide +kernel
    rw [ha]
    exact (canonical27262 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1888 sourceB1888 sourceC1888
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1888, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1889 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1889 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC1889 : Charge := ![4, -1, -1, -1, -1, 0]
def sourceForm1889 : Integer.Sparse Master := [(Sum.inr 4068, 1), (Sum.inr 4100, 3), (Sum.inr 4104, 1), (Sum.inr 4117, 1), (Sum.inr 4232, 3), (Sum.inr 4236, 1), (Sum.inr 4249, 6), (Sum.inr 4252, 3), (Sum.inr 4263, 3), (Sum.inr 4267, 3), (Sum.inr 4451, 1), (Sum.inr 4456, 3), (Sum.inr 4497, 1)]

theorem sourceEq1889 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1889 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1889 + difference 0 1) (sourceB1889 + difference 1 0) sourceC1889) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4451) := by
    have ha : (tripleCharges (sourceA1889 + difference 0 1) (sourceB1889 + difference 1 0) sourceC1889) = raw27263 := by
      apply Matrix.ext; unfold tripleCharges sourceA1889 sourceB1889 sourceC1889 difference raw27263; decide +kernel
    rw [ha]
    exact (canonical27263 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1889 + difference 0 2) (sourceB1889 + difference 2 0) sourceC1889) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4456) := by
    have ha : (tripleCharges (sourceA1889 + difference 0 2) (sourceB1889 + difference 2 0) sourceC1889) = raw27264 := by
      apply Matrix.ext; unfold tripleCharges sourceA1889 sourceB1889 sourceC1889 difference raw27264; decide +kernel
    rw [ha]
    exact (canonical27264 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1889 + difference 0 3) (sourceB1889 + difference 3 0) sourceC1889) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4456) := by
    have ha : (tripleCharges (sourceA1889 + difference 0 3) (sourceB1889 + difference 3 0) sourceC1889) = raw27265 := by
      apply Matrix.ext; unfold tripleCharges sourceA1889 sourceB1889 sourceC1889 difference raw27265; decide +kernel
    rw [ha]
    exact (canonical27265 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1889 + difference 0 4) (sourceB1889 + difference 4 0) sourceC1889) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4456) := by
    have ha : (tripleCharges (sourceA1889 + difference 0 4) (sourceB1889 + difference 4 0) sourceC1889) = raw27266 := by
      apply Matrix.ext; unfold tripleCharges sourceA1889 sourceB1889 sourceC1889 difference raw27266; decide +kernel
    rw [ha]
    exact (canonical27266 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1889 + difference 0 5) (sourceB1889 + difference 5 0) sourceC1889) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4497) := by
    have ha : (tripleCharges (sourceA1889 + difference 0 5) (sourceB1889 + difference 5 0) sourceC1889) = raw27267 := by
      apply Matrix.ext; unfold tripleCharges sourceA1889 sourceB1889 sourceC1889 difference raw27267; decide +kernel
    rw [ha]
    exact (canonical27267 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1889 + difference 1 0) (sourceB1889 + difference 0 1) sourceC1889) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4117) := by
    have ha : (tripleCharges (sourceA1889 + difference 1 0) (sourceB1889 + difference 0 1) sourceC1889) = raw27268 := by
      apply Matrix.ext; unfold tripleCharges sourceA1889 sourceB1889 sourceC1889 difference raw27268; decide +kernel
    rw [ha]
    exact (canonical27268 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1889 + difference 1 2) (sourceB1889 + difference 2 1) sourceC1889) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4263) := by
    have ha : (tripleCharges (sourceA1889 + difference 1 2) (sourceB1889 + difference 2 1) sourceC1889) = raw27269 := by
      apply Matrix.ext; unfold tripleCharges sourceA1889 sourceB1889 sourceC1889 difference raw27269; decide +kernel
    rw [ha]
    exact (canonical27269 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1889 + difference 1 3) (sourceB1889 + difference 3 1) sourceC1889) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4263) := by
    have ha : (tripleCharges (sourceA1889 + difference 1 3) (sourceB1889 + difference 3 1) sourceC1889) = raw27270 := by
      apply Matrix.ext; unfold tripleCharges sourceA1889 sourceB1889 sourceC1889 difference raw27270; decide +kernel
    rw [ha]
    exact (canonical27270 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1889 + difference 1 4) (sourceB1889 + difference 4 1) sourceC1889) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4263) := by
    have ha : (tripleCharges (sourceA1889 + difference 1 4) (sourceB1889 + difference 4 1) sourceC1889) = raw27271 := by
      apply Matrix.ext; unfold tripleCharges sourceA1889 sourceB1889 sourceC1889 difference raw27271; decide +kernel
    rw [ha]
    exact (canonical27271 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1889 + difference 1 5) (sourceB1889 + difference 5 1) sourceC1889) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (tripleCharges (sourceA1889 + difference 1 5) (sourceB1889 + difference 5 1) sourceC1889) = raw27272 := by
      apply Matrix.ext; unfold tripleCharges sourceA1889 sourceB1889 sourceC1889 difference raw27272; decide +kernel
    rw [ha]
    exact (canonical27272 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1889 + difference 2 0) (sourceB1889 + difference 0 2) sourceC1889) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4100) := by
    have ha : (tripleCharges (sourceA1889 + difference 2 0) (sourceB1889 + difference 0 2) sourceC1889) = raw27273 := by
      apply Matrix.ext; unfold tripleCharges sourceA1889 sourceB1889 sourceC1889 difference raw27273; decide +kernel
    rw [ha]
    exact (canonical27273 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1889 + difference 2 1) (sourceB1889 + difference 1 2) sourceC1889) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4232) := by
    have ha : (tripleCharges (sourceA1889 + difference 2 1) (sourceB1889 + difference 1 2) sourceC1889) = raw27274 := by
      apply Matrix.ext; unfold tripleCharges sourceA1889 sourceB1889 sourceC1889 difference raw27274; decide +kernel
    rw [ha]
    exact (canonical27274 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1889 + difference 2 3) (sourceB1889 + difference 3 2) sourceC1889) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4249) := by
    have ha : (tripleCharges (sourceA1889 + difference 2 3) (sourceB1889 + difference 3 2) sourceC1889) = raw27275 := by
      apply Matrix.ext; unfold tripleCharges sourceA1889 sourceB1889 sourceC1889 difference raw27275; decide +kernel
    rw [ha]
    exact (canonical27275 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1889 + difference 2 4) (sourceB1889 + difference 4 2) sourceC1889) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4249) := by
    have ha : (tripleCharges (sourceA1889 + difference 2 4) (sourceB1889 + difference 4 2) sourceC1889) = raw27276 := by
      apply Matrix.ext; unfold tripleCharges sourceA1889 sourceB1889 sourceC1889 difference raw27276; decide +kernel
    rw [ha]
    exact (canonical27276 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1889 + difference 2 5) (sourceB1889 + difference 5 2) sourceC1889) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4267) := by
    have ha : (tripleCharges (sourceA1889 + difference 2 5) (sourceB1889 + difference 5 2) sourceC1889) = raw27277 := by
      apply Matrix.ext; unfold tripleCharges sourceA1889 sourceB1889 sourceC1889 difference raw27277; decide +kernel
    rw [ha]
    exact (canonical27277 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1889 + difference 3 0) (sourceB1889 + difference 0 3) sourceC1889) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4100) := by
    have ha : (tripleCharges (sourceA1889 + difference 3 0) (sourceB1889 + difference 0 3) sourceC1889) = raw27278 := by
      apply Matrix.ext; unfold tripleCharges sourceA1889 sourceB1889 sourceC1889 difference raw27278; decide +kernel
    rw [ha]
    exact (canonical27278 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1889 + difference 3 1) (sourceB1889 + difference 1 3) sourceC1889) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4232) := by
    have ha : (tripleCharges (sourceA1889 + difference 3 1) (sourceB1889 + difference 1 3) sourceC1889) = raw27279 := by
      apply Matrix.ext; unfold tripleCharges sourceA1889 sourceB1889 sourceC1889 difference raw27279; decide +kernel
    rw [ha]
    exact (canonical27279 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1889 + difference 3 2) (sourceB1889 + difference 2 3) sourceC1889) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4249) := by
    have ha : (tripleCharges (sourceA1889 + difference 3 2) (sourceB1889 + difference 2 3) sourceC1889) = raw27280 := by
      apply Matrix.ext; unfold tripleCharges sourceA1889 sourceB1889 sourceC1889 difference raw27280; decide +kernel
    rw [ha]
    exact (canonical27280 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1889 + difference 3 4) (sourceB1889 + difference 4 3) sourceC1889) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4249) := by
    have ha : (tripleCharges (sourceA1889 + difference 3 4) (sourceB1889 + difference 4 3) sourceC1889) = raw27281 := by
      apply Matrix.ext; unfold tripleCharges sourceA1889 sourceB1889 sourceC1889 difference raw27281; decide +kernel
    rw [ha]
    exact (canonical27281 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1889 + difference 3 5) (sourceB1889 + difference 5 3) sourceC1889) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4267) := by
    have ha : (tripleCharges (sourceA1889 + difference 3 5) (sourceB1889 + difference 5 3) sourceC1889) = raw27282 := by
      apply Matrix.ext; unfold tripleCharges sourceA1889 sourceB1889 sourceC1889 difference raw27282; decide +kernel
    rw [ha]
    exact (canonical27282 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1889 + difference 4 0) (sourceB1889 + difference 0 4) sourceC1889) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4100) := by
    have ha : (tripleCharges (sourceA1889 + difference 4 0) (sourceB1889 + difference 0 4) sourceC1889) = raw27283 := by
      apply Matrix.ext; unfold tripleCharges sourceA1889 sourceB1889 sourceC1889 difference raw27283; decide +kernel
    rw [ha]
    exact (canonical27283 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1889 + difference 4 1) (sourceB1889 + difference 1 4) sourceC1889) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4232) := by
    have ha : (tripleCharges (sourceA1889 + difference 4 1) (sourceB1889 + difference 1 4) sourceC1889) = raw27284 := by
      apply Matrix.ext; unfold tripleCharges sourceA1889 sourceB1889 sourceC1889 difference raw27284; decide +kernel
    rw [ha]
    exact (canonical27284 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1889 + difference 4 2) (sourceB1889 + difference 2 4) sourceC1889) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4249) := by
    have ha : (tripleCharges (sourceA1889 + difference 4 2) (sourceB1889 + difference 2 4) sourceC1889) = raw27285 := by
      apply Matrix.ext; unfold tripleCharges sourceA1889 sourceB1889 sourceC1889 difference raw27285; decide +kernel
    rw [ha]
    exact (canonical27285 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1889 + difference 4 3) (sourceB1889 + difference 3 4) sourceC1889) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4249) := by
    have ha : (tripleCharges (sourceA1889 + difference 4 3) (sourceB1889 + difference 3 4) sourceC1889) = raw27286 := by
      apply Matrix.ext; unfold tripleCharges sourceA1889 sourceB1889 sourceC1889 difference raw27286; decide +kernel
    rw [ha]
    exact (canonical27286 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1889 + difference 4 5) (sourceB1889 + difference 5 4) sourceC1889) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4267) := by
    have ha : (tripleCharges (sourceA1889 + difference 4 5) (sourceB1889 + difference 5 4) sourceC1889) = raw27287 := by
      apply Matrix.ext; unfold tripleCharges sourceA1889 sourceB1889 sourceC1889 difference raw27287; decide +kernel
    rw [ha]
    exact (canonical27287 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1889 + difference 5 0) (sourceB1889 + difference 0 5) sourceC1889) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4104) := by
    have ha : (tripleCharges (sourceA1889 + difference 5 0) (sourceB1889 + difference 0 5) sourceC1889) = raw27288 := by
      apply Matrix.ext; unfold tripleCharges sourceA1889 sourceB1889 sourceC1889 difference raw27288; decide +kernel
    rw [ha]
    exact (canonical27288 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1889 + difference 5 1) (sourceB1889 + difference 1 5) sourceC1889) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4236) := by
    have ha : (tripleCharges (sourceA1889 + difference 5 1) (sourceB1889 + difference 1 5) sourceC1889) = raw27289 := by
      apply Matrix.ext; unfold tripleCharges sourceA1889 sourceB1889 sourceC1889 difference raw27289; decide +kernel
    rw [ha]
    exact (canonical27289 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1889 + difference 5 2) (sourceB1889 + difference 2 5) sourceC1889) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4252) := by
    have ha : (tripleCharges (sourceA1889 + difference 5 2) (sourceB1889 + difference 2 5) sourceC1889) = raw27290 := by
      apply Matrix.ext; unfold tripleCharges sourceA1889 sourceB1889 sourceC1889 difference raw27290; decide +kernel
    rw [ha]
    exact (canonical27290 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1889 + difference 5 3) (sourceB1889 + difference 3 5) sourceC1889) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4252) := by
    have ha : (tripleCharges (sourceA1889 + difference 5 3) (sourceB1889 + difference 3 5) sourceC1889) = raw27291 := by
      apply Matrix.ext; unfold tripleCharges sourceA1889 sourceB1889 sourceC1889 difference raw27291; decide +kernel
    rw [ha]
    exact (canonical27291 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1889 + difference 5 4) (sourceB1889 + difference 4 5) sourceC1889) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4252) := by
    have ha : (tripleCharges (sourceA1889 + difference 5 4) (sourceB1889 + difference 4 5) sourceC1889) = raw27292 := by
      apply Matrix.ext; unfold tripleCharges sourceA1889 sourceB1889 sourceC1889 difference raw27292; decide +kernel
    rw [ha]
    exact (canonical27292 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1889 sourceB1889 sourceC1889
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1889, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1890 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1890 : Charge := ![4, 0, -1, -1, -1, -1]
def sourceC1890 : Charge := ![0, 0, 0, 0, 0, 0]
def sourceForm1890 : Integer.Sparse Master := [(Sum.inr 4056, 1), (Sum.inr 4057, 4), (Sum.inr 4063, 4), (Sum.inr 4068, 4), (Sum.inr 4069, 12), (Sum.inr 4079, 1), (Sum.inr 4083, 4)]

theorem sourceEq1890 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1890 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1890 + difference 0 1) (sourceB1890 + difference 1 0) sourceC1890) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4079) := by
    have ha : (tripleCharges (sourceA1890 + difference 0 1) (sourceB1890 + difference 1 0) sourceC1890) = raw14365 := by
      apply Matrix.ext; unfold tripleCharges sourceA1890 sourceB1890 sourceC1890 difference raw14365; decide +kernel
    rw [ha]
    exact (canonical14365 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1890 + difference 0 2) (sourceB1890 + difference 2 0) sourceC1890) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (tripleCharges (sourceA1890 + difference 0 2) (sourceB1890 + difference 2 0) sourceC1890) = raw3331 := by
      apply Matrix.ext; unfold tripleCharges sourceA1890 sourceB1890 sourceC1890 difference raw3331; decide +kernel
    rw [ha]
    exact (canonical3331 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1890 + difference 0 3) (sourceB1890 + difference 3 0) sourceC1890) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (tripleCharges (sourceA1890 + difference 0 3) (sourceB1890 + difference 3 0) sourceC1890) = raw3327 := by
      apply Matrix.ext; unfold tripleCharges sourceA1890 sourceB1890 sourceC1890 difference raw3327; decide +kernel
    rw [ha]
    exact (canonical3327 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1890 + difference 0 4) (sourceB1890 + difference 4 0) sourceC1890) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (tripleCharges (sourceA1890 + difference 0 4) (sourceB1890 + difference 4 0) sourceC1890) = raw14366 := by
      apply Matrix.ext; unfold tripleCharges sourceA1890 sourceB1890 sourceC1890 difference raw14366; decide +kernel
    rw [ha]
    exact (canonical14366 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1890 + difference 0 5) (sourceB1890 + difference 5 0) sourceC1890) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (tripleCharges (sourceA1890 + difference 0 5) (sourceB1890 + difference 5 0) sourceC1890) = raw14367 := by
      apply Matrix.ext; unfold tripleCharges sourceA1890 sourceB1890 sourceC1890 difference raw14367; decide +kernel
    rw [ha]
    exact (canonical14367 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1890 + difference 1 0) (sourceB1890 + difference 0 1) sourceC1890) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4056) := by
    have ha : (tripleCharges (sourceA1890 + difference 1 0) (sourceB1890 + difference 0 1) sourceC1890) = raw27293 := by
      apply Matrix.ext; unfold tripleCharges sourceA1890 sourceB1890 sourceC1890 difference raw27293; decide +kernel
    rw [ha]
    exact (canonical27293 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1890 + difference 1 2) (sourceB1890 + difference 2 1) sourceC1890) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (tripleCharges (sourceA1890 + difference 1 2) (sourceB1890 + difference 2 1) sourceC1890) = raw14360 := by
      apply Matrix.ext; unfold tripleCharges sourceA1890 sourceB1890 sourceC1890 difference raw14360; decide +kernel
    rw [ha]
    exact (canonical14360 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1890 + difference 1 3) (sourceB1890 + difference 3 1) sourceC1890) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (tripleCharges (sourceA1890 + difference 1 3) (sourceB1890 + difference 3 1) sourceC1890) = raw27294 := by
      apply Matrix.ext; unfold tripleCharges sourceA1890 sourceB1890 sourceC1890 difference raw27294; decide +kernel
    rw [ha]
    exact (canonical27294 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1890 + difference 1 4) (sourceB1890 + difference 4 1) sourceC1890) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (tripleCharges (sourceA1890 + difference 1 4) (sourceB1890 + difference 4 1) sourceC1890) = raw27295 := by
      apply Matrix.ext; unfold tripleCharges sourceA1890 sourceB1890 sourceC1890 difference raw27295; decide +kernel
    rw [ha]
    exact (canonical27295 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1890 + difference 1 5) (sourceB1890 + difference 5 1) sourceC1890) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (tripleCharges (sourceA1890 + difference 1 5) (sourceB1890 + difference 5 1) sourceC1890) = raw27296 := by
      apply Matrix.ext; unfold tripleCharges sourceA1890 sourceB1890 sourceC1890 difference raw27296; decide +kernel
    rw [ha]
    exact (canonical27296 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1890 + difference 2 0) (sourceB1890 + difference 0 2) sourceC1890) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4057) := by
    have ha : (tripleCharges (sourceA1890 + difference 2 0) (sourceB1890 + difference 0 2) sourceC1890) = raw27297 := by
      apply Matrix.ext; unfold tripleCharges sourceA1890 sourceB1890 sourceC1890 difference raw27297; decide +kernel
    rw [ha]
    exact (canonical27297 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1890 + difference 2 1) (sourceB1890 + difference 1 2) sourceC1890) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4063) := by
    have ha : (tripleCharges (sourceA1890 + difference 2 1) (sourceB1890 + difference 1 2) sourceC1890) = raw27298 := by
      apply Matrix.ext; unfold tripleCharges sourceA1890 sourceB1890 sourceC1890 difference raw27298; decide +kernel
    rw [ha]
    exact (canonical27298 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1890 + difference 2 3) (sourceB1890 + difference 3 2) sourceC1890) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA1890 + difference 2 3) (sourceB1890 + difference 3 2) sourceC1890) = raw27299 := by
      apply Matrix.ext; unfold tripleCharges sourceA1890 sourceB1890 sourceC1890 difference raw27299; decide +kernel
    rw [ha]
    exact (canonical27299 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1890 + difference 2 4) (sourceB1890 + difference 4 2) sourceC1890) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA1890 + difference 2 4) (sourceB1890 + difference 4 2) sourceC1890) = raw27300 := by
      apply Matrix.ext; unfold tripleCharges sourceA1890 sourceB1890 sourceC1890 difference raw27300; decide +kernel
    rw [ha]
    exact (canonical27300 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1890 + difference 2 5) (sourceB1890 + difference 5 2) sourceC1890) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA1890 + difference 2 5) (sourceB1890 + difference 5 2) sourceC1890) = raw27301 := by
      apply Matrix.ext; unfold tripleCharges sourceA1890 sourceB1890 sourceC1890 difference raw27301; decide +kernel
    rw [ha]
    exact (canonical27301 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1890 + difference 3 0) (sourceB1890 + difference 0 3) sourceC1890) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4057) := by
    have ha : (tripleCharges (sourceA1890 + difference 3 0) (sourceB1890 + difference 0 3) sourceC1890) = raw27302 := by
      apply Matrix.ext; unfold tripleCharges sourceA1890 sourceB1890 sourceC1890 difference raw27302; decide +kernel
    rw [ha]
    exact (canonical27302 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1890 + difference 3 1) (sourceB1890 + difference 1 3) sourceC1890) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4063) := by
    have ha : (tripleCharges (sourceA1890 + difference 3 1) (sourceB1890 + difference 1 3) sourceC1890) = raw27303 := by
      apply Matrix.ext; unfold tripleCharges sourceA1890 sourceB1890 sourceC1890 difference raw27303; decide +kernel
    rw [ha]
    exact (canonical27303 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1890 + difference 3 2) (sourceB1890 + difference 2 3) sourceC1890) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA1890 + difference 3 2) (sourceB1890 + difference 2 3) sourceC1890) = raw14368 := by
      apply Matrix.ext; unfold tripleCharges sourceA1890 sourceB1890 sourceC1890 difference raw14368; decide +kernel
    rw [ha]
    exact (canonical14368 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1890 + difference 3 4) (sourceB1890 + difference 4 3) sourceC1890) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA1890 + difference 3 4) (sourceB1890 + difference 4 3) sourceC1890) = raw27304 := by
      apply Matrix.ext; unfold tripleCharges sourceA1890 sourceB1890 sourceC1890 difference raw27304; decide +kernel
    rw [ha]
    exact (canonical27304 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1890 + difference 3 5) (sourceB1890 + difference 5 3) sourceC1890) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA1890 + difference 3 5) (sourceB1890 + difference 5 3) sourceC1890) = raw27305 := by
      apply Matrix.ext; unfold tripleCharges sourceA1890 sourceB1890 sourceC1890 difference raw27305; decide +kernel
    rw [ha]
    exact (canonical27305 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1890 + difference 4 0) (sourceB1890 + difference 0 4) sourceC1890) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4057) := by
    have ha : (tripleCharges (sourceA1890 + difference 4 0) (sourceB1890 + difference 0 4) sourceC1890) = raw27306 := by
      apply Matrix.ext; unfold tripleCharges sourceA1890 sourceB1890 sourceC1890 difference raw27306; decide +kernel
    rw [ha]
    exact (canonical27306 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1890 + difference 4 1) (sourceB1890 + difference 1 4) sourceC1890) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4063) := by
    have ha : (tripleCharges (sourceA1890 + difference 4 1) (sourceB1890 + difference 1 4) sourceC1890) = raw27307 := by
      apply Matrix.ext; unfold tripleCharges sourceA1890 sourceB1890 sourceC1890 difference raw27307; decide +kernel
    rw [ha]
    exact (canonical27307 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1890 + difference 4 2) (sourceB1890 + difference 2 4) sourceC1890) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA1890 + difference 4 2) (sourceB1890 + difference 2 4) sourceC1890) = raw14373 := by
      apply Matrix.ext; unfold tripleCharges sourceA1890 sourceB1890 sourceC1890 difference raw14373; decide +kernel
    rw [ha]
    exact (canonical14373 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1890 + difference 4 3) (sourceB1890 + difference 3 4) sourceC1890) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA1890 + difference 4 3) (sourceB1890 + difference 3 4) sourceC1890) = raw23784 := by
      apply Matrix.ext; unfold tripleCharges sourceA1890 sourceB1890 sourceC1890 difference raw23784; decide +kernel
    rw [ha]
    exact (canonical23784 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1890 + difference 4 5) (sourceB1890 + difference 5 4) sourceC1890) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA1890 + difference 4 5) (sourceB1890 + difference 5 4) sourceC1890) = raw27308 := by
      apply Matrix.ext; unfold tripleCharges sourceA1890 sourceB1890 sourceC1890 difference raw27308; decide +kernel
    rw [ha]
    exact (canonical27308 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1890 + difference 5 0) (sourceB1890 + difference 0 5) sourceC1890) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4057) := by
    have ha : (tripleCharges (sourceA1890 + difference 5 0) (sourceB1890 + difference 0 5) sourceC1890) = raw26357 := by
      apply Matrix.ext; unfold tripleCharges sourceA1890 sourceB1890 sourceC1890 difference raw26357; decide +kernel
    rw [ha]
    exact (canonical26357 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1890 + difference 5 1) (sourceB1890 + difference 1 5) sourceC1890) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4063) := by
    have ha : (tripleCharges (sourceA1890 + difference 5 1) (sourceB1890 + difference 1 5) sourceC1890) = raw26358 := by
      apply Matrix.ext; unfold tripleCharges sourceA1890 sourceB1890 sourceC1890 difference raw26358; decide +kernel
    rw [ha]
    exact (canonical26358 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1890 + difference 5 2) (sourceB1890 + difference 2 5) sourceC1890) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA1890 + difference 5 2) (sourceB1890 + difference 2 5) sourceC1890) = raw11537 := by
      apply Matrix.ext; unfold tripleCharges sourceA1890 sourceB1890 sourceC1890 difference raw11537; decide +kernel
    rw [ha]
    exact (canonical11537 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1890 + difference 5 3) (sourceB1890 + difference 3 5) sourceC1890) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA1890 + difference 5 3) (sourceB1890 + difference 3 5) sourceC1890) = raw11534 := by
      apply Matrix.ext; unfold tripleCharges sourceA1890 sourceB1890 sourceC1890 difference raw11534; decide +kernel
    rw [ha]
    exact (canonical11534 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1890 + difference 5 4) (sourceB1890 + difference 4 5) sourceC1890) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA1890 + difference 5 4) (sourceB1890 + difference 4 5) sourceC1890) = raw26359 := by
      apply Matrix.ext; unfold tripleCharges sourceA1890 sourceB1890 sourceC1890 difference raw26359; decide +kernel
    rw [ha]
    exact (canonical26359 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1890 sourceB1890 sourceC1890
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1890, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1891 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1891 : Charge := ![0, 1, 0, 0, 2, -3]
def sourceC1891 : Charge := ![3, 0, 0, 0, -3, 0]
def sourceForm1891 : Integer.Sparse Master := [(Sum.inr 940, 1), (Sum.inr 1820, 1), (Sum.inr 1971, 2), (Sum.inr 2063, 1), (Sum.inr 2065, 1), (Sum.inr 4085, -1)]

theorem sourceEq1891 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1891 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1891 + difference 4 0) (sourceB1891 + difference 0 4) sourceC1891) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 940) := by
    have ha : (tripleCharges (sourceA1891 + difference 4 0) (sourceB1891 + difference 0 4) sourceC1891) = raw20089 := by
      apply Matrix.ext; unfold tripleCharges sourceA1891 sourceB1891 sourceC1891 difference raw20089; decide +kernel
    rw [ha]
    exact (canonical20089 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1891 + difference 4 1) (sourceB1891 + difference 1 4) sourceC1891) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1820) := by
    have ha : (tripleCharges (sourceA1891 + difference 4 1) (sourceB1891 + difference 1 4) sourceC1891) = raw27309 := by
      apply Matrix.ext; unfold tripleCharges sourceA1891 sourceB1891 sourceC1891 difference raw27309; decide +kernel
    rw [ha]
    exact (canonical27309 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1891 + difference 4 2) (sourceB1891 + difference 2 4) sourceC1891) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1971) := by
    have ha : (tripleCharges (sourceA1891 + difference 4 2) (sourceB1891 + difference 2 4) sourceC1891) = raw27310 := by
      apply Matrix.ext; unfold tripleCharges sourceA1891 sourceB1891 sourceC1891 difference raw27310; decide +kernel
    rw [ha]
    exact (canonical27310 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1891 + difference 4 3) (sourceB1891 + difference 3 4) sourceC1891) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1971) := by
    have ha : (tripleCharges (sourceA1891 + difference 4 3) (sourceB1891 + difference 3 4) sourceC1891) = raw27311 := by
      apply Matrix.ext; unfold tripleCharges sourceA1891 sourceB1891 sourceC1891 difference raw27311; decide +kernel
    rw [ha]
    exact (canonical27311 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1891 + difference 4 4) (sourceB1891 + difference 4 4) sourceC1891) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2063) := by
    have ha : (tripleCharges (sourceA1891 + difference 4 4) (sourceB1891 + difference 4 4) sourceC1891) = raw3529 := by
      apply Matrix.ext; unfold tripleCharges sourceA1891 sourceB1891 sourceC1891 difference raw3529; decide +kernel
    rw [ha]
    exact (canonical3529 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1891 + difference 4 5) (sourceB1891 + difference 5 4) sourceC1891) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2065) := by
    have ha : (tripleCharges (sourceA1891 + difference 4 5) (sourceB1891 + difference 5 4) sourceC1891) = raw27312 := by
      apply Matrix.ext; unfold tripleCharges sourceA1891 sourceB1891 sourceC1891 difference raw27312; decide +kernel
    rw [ha]
    exact (canonical27312 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1891 + sourceB1891) sourceC1891) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA1891 + sourceB1891) sourceC1891) = raw3517 := by
      apply Matrix.ext; unfold doubleCharges sourceA1891 sourceB1891 sourceC1891 raw3517; decide +kernel
    rw [ha]
    exact (canonical3517 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1891 sourceB1891 sourceC1891
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1891, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1892 : Charge := ![0, 1, 0, 0, 2, -3]
def sourceB1892 : Charge := ![3, 0, 0, 0, -3, 0]
def sourceC1892 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceForm1892 : Integer.Sparse Master := [(Sum.inr 2220, 2), (Sum.inr 2222, 1), (Sum.inr 2230, 1), (Sum.inr 2282, 1), (Sum.inr 2287, 1), (Sum.inr 4081, -1)]

theorem sourceEq1892 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1892 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1892 + difference 0 4) (sourceB1892 + difference 4 0) sourceC1892) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2287) := by
    have ha : (tripleCharges (sourceA1892 + difference 0 4) (sourceB1892 + difference 4 0) sourceC1892) = raw27313 := by
      apply Matrix.ext; unfold tripleCharges sourceA1892 sourceB1892 sourceC1892 difference raw27313; decide +kernel
    rw [ha]
    exact (canonical27313 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1892 + difference 1 4) (sourceB1892 + difference 4 1) sourceC1892) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2282) := by
    have ha : (tripleCharges (sourceA1892 + difference 1 4) (sourceB1892 + difference 4 1) sourceC1892) = raw27314 := by
      apply Matrix.ext; unfold tripleCharges sourceA1892 sourceB1892 sourceC1892 difference raw27314; decide +kernel
    rw [ha]
    exact (canonical27314 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1892 + difference 2 4) (sourceB1892 + difference 4 2) sourceC1892) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2220) := by
    have ha : (tripleCharges (sourceA1892 + difference 2 4) (sourceB1892 + difference 4 2) sourceC1892) = raw27315 := by
      apply Matrix.ext; unfold tripleCharges sourceA1892 sourceB1892 sourceC1892 difference raw27315; decide +kernel
    rw [ha]
    exact (canonical27315 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1892 + difference 3 4) (sourceB1892 + difference 4 3) sourceC1892) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2220) := by
    have ha : (tripleCharges (sourceA1892 + difference 3 4) (sourceB1892 + difference 4 3) sourceC1892) = raw27316 := by
      apply Matrix.ext; unfold tripleCharges sourceA1892 sourceB1892 sourceC1892 difference raw27316; decide +kernel
    rw [ha]
    exact (canonical27316 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1892 + difference 4 4) (sourceB1892 + difference 4 4) sourceC1892) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2222) := by
    have ha : (tripleCharges (sourceA1892 + difference 4 4) (sourceB1892 + difference 4 4) sourceC1892) = raw27317 := by
      apply Matrix.ext; unfold tripleCharges sourceA1892 sourceB1892 sourceC1892 difference raw27317; decide +kernel
    rw [ha]
    exact (canonical27317 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1892 + difference 5 4) (sourceB1892 + difference 4 5) sourceC1892) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2230) := by
    have ha : (tripleCharges (sourceA1892 + difference 5 4) (sourceB1892 + difference 4 5) sourceC1892) = raw27318 := by
      apply Matrix.ext; unfold tripleCharges sourceA1892 sourceB1892 sourceC1892 difference raw27318; decide +kernel
    rw [ha]
    exact (canonical27318 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1892 + sourceB1892) sourceC1892) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1892 + sourceB1892) sourceC1892) = raw27319 := by
      apply Matrix.ext; unfold doubleCharges sourceA1892 sourceB1892 sourceC1892 raw27319; decide +kernel
    rw [ha]
    exact (canonical27319 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1892 sourceB1892 sourceC1892
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1892, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1893 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1893 : Charge := ![0, 1, 0, 1, 1, -3]
def sourceC1893 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceForm1893 : Integer.Sparse Master := [(Sum.inr 931, 1), (Sum.inr 1813, 1), (Sum.inr 1965, 1), (Sum.inr 2026, 1), (Sum.inr 2037, 1), (Sum.inr 2058, 1), (Sum.inr 4084, -1)]

theorem sourceEq1893 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1893 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1893 + difference 3 0) (sourceB1893 + difference 0 3) sourceC1893) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 931) := by
    have ha : (tripleCharges (sourceA1893 + difference 3 0) (sourceB1893 + difference 0 3) sourceC1893) = raw20109 := by
      apply Matrix.ext; unfold tripleCharges sourceA1893 sourceB1893 sourceC1893 difference raw20109; decide +kernel
    rw [ha]
    exact (canonical20109 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1893 + difference 3 1) (sourceB1893 + difference 1 3) sourceC1893) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1813) := by
    have ha : (tripleCharges (sourceA1893 + difference 3 1) (sourceB1893 + difference 1 3) sourceC1893) = raw27320 := by
      apply Matrix.ext; unfold tripleCharges sourceA1893 sourceB1893 sourceC1893 difference raw27320; decide +kernel
    rw [ha]
    exact (canonical27320 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1893 + difference 3 2) (sourceB1893 + difference 2 3) sourceC1893) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1965) := by
    have ha : (tripleCharges (sourceA1893 + difference 3 2) (sourceB1893 + difference 2 3) sourceC1893) = raw27321 := by
      apply Matrix.ext; unfold tripleCharges sourceA1893 sourceB1893 sourceC1893 difference raw27321; decide +kernel
    rw [ha]
    exact (canonical27321 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1893 + difference 3 3) (sourceB1893 + difference 3 3) sourceC1893) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2026) := by
    have ha : (tripleCharges (sourceA1893 + difference 3 3) (sourceB1893 + difference 3 3) sourceC1893) = raw3642 := by
      apply Matrix.ext; unfold tripleCharges sourceA1893 sourceB1893 sourceC1893 difference raw3642; decide +kernel
    rw [ha]
    exact (canonical3642 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1893 + difference 3 4) (sourceB1893 + difference 4 3) sourceC1893) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2037) := by
    have ha : (tripleCharges (sourceA1893 + difference 3 4) (sourceB1893 + difference 4 3) sourceC1893) = raw3641 := by
      apply Matrix.ext; unfold tripleCharges sourceA1893 sourceB1893 sourceC1893 difference raw3641; decide +kernel
    rw [ha]
    exact (canonical3641 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1893 + difference 3 5) (sourceB1893 + difference 5 3) sourceC1893) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2058) := by
    have ha : (tripleCharges (sourceA1893 + difference 3 5) (sourceB1893 + difference 5 3) sourceC1893) = raw27322 := by
      apply Matrix.ext; unfold tripleCharges sourceA1893 sourceB1893 sourceC1893 difference raw27322; decide +kernel
    rw [ha]
    exact (canonical27322 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1893 + sourceB1893) sourceC1893) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1893 + sourceB1893) sourceC1893) = raw3630 := by
      apply Matrix.ext; unfold doubleCharges sourceA1893 sourceB1893 sourceC1893 raw3630; decide +kernel
    rw [ha]
    exact (canonical3630 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1893 sourceB1893 sourceC1893
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1893, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1894 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1894 : Charge := ![0, 1, 0, 1, 1, -3]
def sourceC1894 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceForm1894 : Integer.Sparse Master := [(Sum.inr 914, 1), (Sum.inr 1797, 1), (Sum.inr 1957, 1), (Sum.inr 1980, 1), (Sum.inr 2026, 1), (Sum.inr 2028, 1), (Sum.inr 4084, -1)]

theorem sourceEq1894 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1894 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1894 + difference 4 0) (sourceB1894 + difference 0 4) sourceC1894) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 914) := by
    have ha : (tripleCharges (sourceA1894 + difference 4 0) (sourceB1894 + difference 0 4) sourceC1894) = raw20113 := by
      apply Matrix.ext; unfold tripleCharges sourceA1894 sourceB1894 sourceC1894 difference raw20113; decide +kernel
    rw [ha]
    exact (canonical20113 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1894 + difference 4 1) (sourceB1894 + difference 1 4) sourceC1894) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1797) := by
    have ha : (tripleCharges (sourceA1894 + difference 4 1) (sourceB1894 + difference 1 4) sourceC1894) = raw27323 := by
      apply Matrix.ext; unfold tripleCharges sourceA1894 sourceB1894 sourceC1894 difference raw27323; decide +kernel
    rw [ha]
    exact (canonical27323 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1894 + difference 4 2) (sourceB1894 + difference 2 4) sourceC1894) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1957) := by
    have ha : (tripleCharges (sourceA1894 + difference 4 2) (sourceB1894 + difference 2 4) sourceC1894) = raw27324 := by
      apply Matrix.ext; unfold tripleCharges sourceA1894 sourceB1894 sourceC1894 difference raw27324; decide +kernel
    rw [ha]
    exact (canonical27324 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1894 + difference 4 3) (sourceB1894 + difference 3 4) sourceC1894) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1980) := by
    have ha : (tripleCharges (sourceA1894 + difference 4 3) (sourceB1894 + difference 3 4) sourceC1894) = raw27325 := by
      apply Matrix.ext; unfold tripleCharges sourceA1894 sourceB1894 sourceC1894 difference raw27325; decide +kernel
    rw [ha]
    exact (canonical27325 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1894 + difference 4 4) (sourceB1894 + difference 4 4) sourceC1894) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2026) := by
    have ha : (tripleCharges (sourceA1894 + difference 4 4) (sourceB1894 + difference 4 4) sourceC1894) = raw3642 := by
      apply Matrix.ext; unfold tripleCharges sourceA1894 sourceB1894 sourceC1894 difference raw3642; decide +kernel
    rw [ha]
    exact (canonical3642 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1894 + difference 4 5) (sourceB1894 + difference 5 4) sourceC1894) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2028) := by
    have ha : (tripleCharges (sourceA1894 + difference 4 5) (sourceB1894 + difference 5 4) sourceC1894) = raw27326 := by
      apply Matrix.ext; unfold tripleCharges sourceA1894 sourceB1894 sourceC1894 difference raw27326; decide +kernel
    rw [ha]
    exact (canonical27326 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1894 + sourceB1894) sourceC1894) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1894 + sourceB1894) sourceC1894) = raw3630 := by
      apply Matrix.ext; unfold doubleCharges sourceA1894 sourceB1894 sourceC1894 raw3630; decide +kernel
    rw [ha]
    exact (canonical3630 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1894 sourceB1894 sourceC1894
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1894, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1895 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1895 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceC1895 : Charge := ![0, 1, 0, 1, 1, -3]
def sourceForm1895 : Integer.Sparse Master := [(Sum.inr 949, 1), (Sum.inr 1828, 1), (Sum.inr 1976, 1), (Sum.inr 2092, 2), (Sum.inr 2110, 1), (Sum.inr 4083, -1)]

theorem sourceEq1895 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1895 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1895 + difference 0 3) (sourceB1895 + difference 3 0) sourceC1895) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2110) := by
    have ha : (tripleCharges (sourceA1895 + difference 0 3) (sourceB1895 + difference 3 0) sourceC1895) = raw27327 := by
      apply Matrix.ext; unfold tripleCharges sourceA1895 sourceB1895 sourceC1895 difference raw27327; decide +kernel
    rw [ha]
    exact (canonical27327 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1895 + difference 1 3) (sourceB1895 + difference 3 1) sourceC1895) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2092) := by
    have ha : (tripleCharges (sourceA1895 + difference 1 3) (sourceB1895 + difference 3 1) sourceC1895) = raw27328 := by
      apply Matrix.ext; unfold tripleCharges sourceA1895 sourceB1895 sourceC1895 difference raw27328; decide +kernel
    rw [ha]
    exact (canonical27328 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1895 + difference 2 3) (sourceB1895 + difference 3 2) sourceC1895) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1976) := by
    have ha : (tripleCharges (sourceA1895 + difference 2 3) (sourceB1895 + difference 3 2) sourceC1895) = raw27329 := by
      apply Matrix.ext; unfold tripleCharges sourceA1895 sourceB1895 sourceC1895 difference raw27329; decide +kernel
    rw [ha]
    exact (canonical27329 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1895 + difference 3 3) (sourceB1895 + difference 3 3) sourceC1895) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2092) := by
    have ha : (tripleCharges (sourceA1895 + difference 3 3) (sourceB1895 + difference 3 3) sourceC1895) = raw27330 := by
      apply Matrix.ext; unfold tripleCharges sourceA1895 sourceB1895 sourceC1895 difference raw27330; decide +kernel
    rw [ha]
    exact (canonical27330 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1895 + difference 4 3) (sourceB1895 + difference 3 4) sourceC1895) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1828) := by
    have ha : (tripleCharges (sourceA1895 + difference 4 3) (sourceB1895 + difference 3 4) sourceC1895) = raw27331 := by
      apply Matrix.ext; unfold tripleCharges sourceA1895 sourceB1895 sourceC1895 difference raw27331; decide +kernel
    rw [ha]
    exact (canonical27331 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1895 + difference 5 3) (sourceB1895 + difference 3 5) sourceC1895) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 949) := by
    have ha : (tripleCharges (sourceA1895 + difference 5 3) (sourceB1895 + difference 3 5) sourceC1895) = raw27332 := by
      apply Matrix.ext; unfold tripleCharges sourceA1895 sourceB1895 sourceC1895 difference raw27332; decide +kernel
    rw [ha]
    exact (canonical27332 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1895 + sourceB1895) sourceC1895) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA1895 + sourceB1895) sourceC1895) = raw27333 := by
      apply Matrix.ext; unfold doubleCharges sourceA1895 sourceB1895 sourceC1895 raw27333; decide +kernel
    rw [ha]
    exact (canonical27333 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1895 sourceB1895 sourceC1895
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1895, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1896 : Charge := ![0, 1, 0, 1, 1, -3]
def sourceB1896 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceC1896 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceForm1896 : Integer.Sparse Master := [(Sum.inr 1930, 1), (Sum.inr 1932, 1), (Sum.inr 1934, 1), (Sum.inr 1946, 1), (Sum.inr 2220, 1), (Sum.inr 2259, 1), (Sum.inr 4081, -1)]

theorem sourceEq1896 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1896 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1896 + difference 0 1) (sourceB1896 + difference 1 0) sourceC1896) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2259) := by
    have ha : (tripleCharges (sourceA1896 + difference 0 1) (sourceB1896 + difference 1 0) sourceC1896) = raw27334 := by
      apply Matrix.ext; unfold tripleCharges sourceA1896 sourceB1896 sourceC1896 difference raw27334; decide +kernel
    rw [ha]
    exact (canonical27334 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1896 + difference 1 1) (sourceB1896 + difference 1 1) sourceC1896) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2220) := by
    have ha : (tripleCharges (sourceA1896 + difference 1 1) (sourceB1896 + difference 1 1) sourceC1896) = raw27316 := by
      apply Matrix.ext; unfold tripleCharges sourceA1896 sourceB1896 sourceC1896 difference raw27316; decide +kernel
    rw [ha]
    exact (canonical27316 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1896 + difference 2 1) (sourceB1896 + difference 1 2) sourceC1896) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1930) := by
    have ha : (tripleCharges (sourceA1896 + difference 2 1) (sourceB1896 + difference 1 2) sourceC1896) = raw27335 := by
      apply Matrix.ext; unfold tripleCharges sourceA1896 sourceB1896 sourceC1896 difference raw27335; decide +kernel
    rw [ha]
    exact (canonical27335 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1896 + difference 3 1) (sourceB1896 + difference 1 3) sourceC1896) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1934) := by
    have ha : (tripleCharges (sourceA1896 + difference 3 1) (sourceB1896 + difference 1 3) sourceC1896) = raw27336 := by
      apply Matrix.ext; unfold tripleCharges sourceA1896 sourceB1896 sourceC1896 difference raw27336; decide +kernel
    rw [ha]
    exact (canonical27336 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1896 + difference 4 1) (sourceB1896 + difference 1 4) sourceC1896) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1932) := by
    have ha : (tripleCharges (sourceA1896 + difference 4 1) (sourceB1896 + difference 1 4) sourceC1896) = raw27337 := by
      apply Matrix.ext; unfold tripleCharges sourceA1896 sourceB1896 sourceC1896 difference raw27337; decide +kernel
    rw [ha]
    exact (canonical27337 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1896 + difference 5 1) (sourceB1896 + difference 1 5) sourceC1896) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1946) := by
    have ha : (tripleCharges (sourceA1896 + difference 5 1) (sourceB1896 + difference 1 5) sourceC1896) = raw27338 := by
      apply Matrix.ext; unfold tripleCharges sourceA1896 sourceB1896 sourceC1896 difference raw27338; decide +kernel
    rw [ha]
    exact (canonical27338 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1896 + sourceB1896) sourceC1896) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1896 + sourceB1896) sourceC1896) = raw27319 := by
      apply Matrix.ext; unfold doubleCharges sourceA1896 sourceB1896 sourceC1896 raw27319; decide +kernel
    rw [ha]
    exact (canonical27319 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1896 sourceB1896 sourceC1896
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1896, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1897 : Charge := ![0, 1, 0, 1, 1, -3]
def sourceB1897 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceC1897 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceForm1897 : Integer.Sparse Master := [(Sum.inr 2219, 1), (Sum.inr 2220, 2), (Sum.inr 2221, 1), (Sum.inr 2224, 2), (Sum.inr 4081, -1)]

theorem sourceEq1897 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1897 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1897 + difference 0 4) (sourceB1897 + difference 4 0) sourceC1897) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2224) := by
    have ha : (tripleCharges (sourceA1897 + difference 0 4) (sourceB1897 + difference 4 0) sourceC1897) = raw27339 := by
      apply Matrix.ext; unfold tripleCharges sourceA1897 sourceB1897 sourceC1897 difference raw27339; decide +kernel
    rw [ha]
    exact (canonical27339 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1897 + difference 1 4) (sourceB1897 + difference 4 1) sourceC1897) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2220) := by
    have ha : (tripleCharges (sourceA1897 + difference 1 4) (sourceB1897 + difference 4 1) sourceC1897) = raw27340 := by
      apply Matrix.ext; unfold tripleCharges sourceA1897 sourceB1897 sourceC1897 difference raw27340; decide +kernel
    rw [ha]
    exact (canonical27340 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1897 + difference 2 4) (sourceB1897 + difference 4 2) sourceC1897) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2219) := by
    have ha : (tripleCharges (sourceA1897 + difference 2 4) (sourceB1897 + difference 4 2) sourceC1897) = raw27341 := by
      apply Matrix.ext; unfold tripleCharges sourceA1897 sourceB1897 sourceC1897 difference raw27341; decide +kernel
    rw [ha]
    exact (canonical27341 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1897 + difference 3 4) (sourceB1897 + difference 4 3) sourceC1897) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2221) := by
    have ha : (tripleCharges (sourceA1897 + difference 3 4) (sourceB1897 + difference 4 3) sourceC1897) = raw27342 := by
      apply Matrix.ext; unfold tripleCharges sourceA1897 sourceB1897 sourceC1897 difference raw27342; decide +kernel
    rw [ha]
    exact (canonical27342 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1897 + difference 4 4) (sourceB1897 + difference 4 4) sourceC1897) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2220) := by
    have ha : (tripleCharges (sourceA1897 + difference 4 4) (sourceB1897 + difference 4 4) sourceC1897) = raw27316 := by
      apply Matrix.ext; unfold tripleCharges sourceA1897 sourceB1897 sourceC1897 difference raw27316; decide +kernel
    rw [ha]
    exact (canonical27316 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1897 + difference 5 4) (sourceB1897 + difference 4 5) sourceC1897) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2224) := by
    have ha : (tripleCharges (sourceA1897 + difference 5 4) (sourceB1897 + difference 4 5) sourceC1897) = raw27343 := by
      apply Matrix.ext; unfold tripleCharges sourceA1897 sourceB1897 sourceC1897 difference raw27343; decide +kernel
    rw [ha]
    exact (canonical27343 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1897 + sourceB1897) sourceC1897) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1897 + sourceB1897) sourceC1897) = raw27319 := by
      apply Matrix.ext; unfold doubleCharges sourceA1897 sourceB1897 sourceC1897 raw27319; decide +kernel
    rw [ha]
    exact (canonical27319 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1897 sourceB1897 sourceC1897
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1897, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1898 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1898 : Charge := ![0, 1, 0, 2, -1, -2]
def sourceC1898 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceForm1898 : Integer.Sparse Master := [(Sum.inr 925, 1), (Sum.inr 1808, 1), (Sum.inr 1961, 1), (Sum.inr 2035, 1), (Sum.inr 2054, 1), (Sum.inr 2062, 1), (Sum.inr 4084, -1)]

theorem sourceEq1898 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1898 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1898 + difference 3 0) (sourceB1898 + difference 0 3) sourceC1898) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 925) := by
    have ha : (tripleCharges (sourceA1898 + difference 3 0) (sourceB1898 + difference 0 3) sourceC1898) = raw20137 := by
      apply Matrix.ext; unfold tripleCharges sourceA1898 sourceB1898 sourceC1898 difference raw20137; decide +kernel
    rw [ha]
    exact (canonical20137 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1898 + difference 3 1) (sourceB1898 + difference 1 3) sourceC1898) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1808) := by
    have ha : (tripleCharges (sourceA1898 + difference 3 1) (sourceB1898 + difference 1 3) sourceC1898) = raw27344 := by
      apply Matrix.ext; unfold tripleCharges sourceA1898 sourceB1898 sourceC1898 difference raw27344; decide +kernel
    rw [ha]
    exact (canonical27344 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1898 + difference 3 2) (sourceB1898 + difference 2 3) sourceC1898) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1961) := by
    have ha : (tripleCharges (sourceA1898 + difference 3 2) (sourceB1898 + difference 2 3) sourceC1898) = raw27345 := by
      apply Matrix.ext; unfold tripleCharges sourceA1898 sourceB1898 sourceC1898 difference raw27345; decide +kernel
    rw [ha]
    exact (canonical27345 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1898 + difference 3 3) (sourceB1898 + difference 3 3) sourceC1898) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2035) := by
    have ha : (tripleCharges (sourceA1898 + difference 3 3) (sourceB1898 + difference 3 3) sourceC1898) = raw27346 := by
      apply Matrix.ext; unfold tripleCharges sourceA1898 sourceB1898 sourceC1898 difference raw27346; decide +kernel
    rw [ha]
    exact (canonical27346 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1898 + difference 3 4) (sourceB1898 + difference 4 3) sourceC1898) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2062) := by
    have ha : (tripleCharges (sourceA1898 + difference 3 4) (sourceB1898 + difference 4 3) sourceC1898) = raw27347 := by
      apply Matrix.ext; unfold tripleCharges sourceA1898 sourceB1898 sourceC1898 difference raw27347; decide +kernel
    rw [ha]
    exact (canonical27347 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1898 + difference 3 5) (sourceB1898 + difference 5 3) sourceC1898) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2054) := by
    have ha : (tripleCharges (sourceA1898 + difference 3 5) (sourceB1898 + difference 5 3) sourceC1898) = raw27348 := by
      apply Matrix.ext; unfold tripleCharges sourceA1898 sourceB1898 sourceC1898 difference raw27348; decide +kernel
    rw [ha]
    exact (canonical27348 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1898 + sourceB1898) sourceC1898) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1898 + sourceB1898) sourceC1898) = raw20142 := by
      apply Matrix.ext; unfold doubleCharges sourceA1898 sourceB1898 sourceC1898 raw20142; decide +kernel
    rw [ha]
    exact (canonical20142 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1898 sourceB1898 sourceC1898
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1898, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1899 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1899 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC1899 : Charge := ![0, 1, 0, 2, -1, -2]
def sourceForm1899 : Integer.Sparse Master := [(Sum.inr 1137, 1), (Sum.inr 2340, 1), (Sum.inr 2430, 1), (Sum.inr 2486, 1), (Sum.inr 2497, 1), (Sum.inr 2515, 1), (Sum.inr 4092, -1)]

theorem sourceEq1899 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1899 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1899 + difference 0 3) (sourceB1899 + difference 3 0) sourceC1899) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2515) := by
    have ha : (tripleCharges (sourceA1899 + difference 0 3) (sourceB1899 + difference 3 0) sourceC1899) = raw27349 := by
      apply Matrix.ext; unfold tripleCharges sourceA1899 sourceB1899 sourceC1899 difference raw27349; decide +kernel
    rw [ha]
    exact (canonical27349 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1899 + difference 1 3) (sourceB1899 + difference 3 1) sourceC1899) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2486) := by
    have ha : (tripleCharges (sourceA1899 + difference 1 3) (sourceB1899 + difference 3 1) sourceC1899) = raw27350 := by
      apply Matrix.ext; unfold tripleCharges sourceA1899 sourceB1899 sourceC1899 difference raw27350; decide +kernel
    rw [ha]
    exact (canonical27350 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1899 + difference 2 3) (sourceB1899 + difference 3 2) sourceC1899) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2430) := by
    have ha : (tripleCharges (sourceA1899 + difference 2 3) (sourceB1899 + difference 3 2) sourceC1899) = raw27351 := by
      apply Matrix.ext; unfold tripleCharges sourceA1899 sourceB1899 sourceC1899 difference raw27351; decide +kernel
    rw [ha]
    exact (canonical27351 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1899 + difference 3 3) (sourceB1899 + difference 3 3) sourceC1899) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2497) := by
    have ha : (tripleCharges (sourceA1899 + difference 3 3) (sourceB1899 + difference 3 3) sourceC1899) = raw27352 := by
      apply Matrix.ext; unfold tripleCharges sourceA1899 sourceB1899 sourceC1899 difference raw27352; decide +kernel
    rw [ha]
    exact (canonical27352 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1899 + difference 4 3) (sourceB1899 + difference 3 4) sourceC1899) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2340) := by
    have ha : (tripleCharges (sourceA1899 + difference 4 3) (sourceB1899 + difference 3 4) sourceC1899) = raw27353 := by
      apply Matrix.ext; unfold tripleCharges sourceA1899 sourceB1899 sourceC1899 difference raw27353; decide +kernel
    rw [ha]
    exact (canonical27353 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1899 + difference 5 3) (sourceB1899 + difference 3 5) sourceC1899) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1137) := by
    have ha : (tripleCharges (sourceA1899 + difference 5 3) (sourceB1899 + difference 3 5) sourceC1899) = raw27354 := by
      apply Matrix.ext; unfold tripleCharges sourceA1899 sourceB1899 sourceC1899 difference raw27354; decide +kernel
    rw [ha]
    exact (canonical27354 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1899 + sourceB1899) sourceC1899) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1899 + sourceB1899) sourceC1899) = raw27355 := by
      apply Matrix.ext; unfold doubleCharges sourceA1899 sourceB1899 sourceC1899 raw27355; decide +kernel
    rw [ha]
    exact (canonical27355 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1899 sourceB1899 sourceC1899
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1899, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1900 : Charge := ![0, 1, 0, 2, -1, -2]
def sourceB1900 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC1900 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceForm1900 : Integer.Sparse Master := [(Sum.inr 1948, 1), (Sum.inr 2207, 1), (Sum.inr 3358, 1), (Sum.inr 3437, 1), (Sum.inr 3472, 1), (Sum.inr 3481, 1), (Sum.inr 4081, -1)]

theorem sourceEq1900 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1900 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1900 + difference 0 0) (sourceB1900 + difference 0 0) sourceC1900) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2207) := by
    have ha : (tripleCharges (sourceA1900 + difference 0 0) (sourceB1900 + difference 0 0) sourceC1900) = raw27356 := by
      apply Matrix.ext; unfold tripleCharges sourceA1900 sourceB1900 sourceC1900 difference raw27356; decide +kernel
    rw [ha]
    exact (canonical27356 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1900 + difference 0 1) (sourceB1900 + difference 1 0) sourceC1900) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3472) := by
    have ha : (tripleCharges (sourceA1900 + difference 0 1) (sourceB1900 + difference 1 0) sourceC1900) = raw27357 := by
      apply Matrix.ext; unfold tripleCharges sourceA1900 sourceB1900 sourceC1900 difference raw27357; decide +kernel
    rw [ha]
    exact (canonical27357 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1900 + difference 0 2) (sourceB1900 + difference 2 0) sourceC1900) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3437) := by
    have ha : (tripleCharges (sourceA1900 + difference 0 2) (sourceB1900 + difference 2 0) sourceC1900) = raw27358 := by
      apply Matrix.ext; unfold tripleCharges sourceA1900 sourceB1900 sourceC1900 difference raw27358; decide +kernel
    rw [ha]
    exact (canonical27358 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1900 + difference 0 3) (sourceB1900 + difference 3 0) sourceC1900) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3481) := by
    have ha : (tripleCharges (sourceA1900 + difference 0 3) (sourceB1900 + difference 3 0) sourceC1900) = raw27359 := by
      apply Matrix.ext; unfold tripleCharges sourceA1900 sourceB1900 sourceC1900 difference raw27359; decide +kernel
    rw [ha]
    exact (canonical27359 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1900 + difference 0 4) (sourceB1900 + difference 4 0) sourceC1900) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3358) := by
    have ha : (tripleCharges (sourceA1900 + difference 0 4) (sourceB1900 + difference 4 0) sourceC1900) = raw27360 := by
      apply Matrix.ext; unfold tripleCharges sourceA1900 sourceB1900 sourceC1900 difference raw27360; decide +kernel
    rw [ha]
    exact (canonical27360 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1900 + difference 0 5) (sourceB1900 + difference 5 0) sourceC1900) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1948) := by
    have ha : (tripleCharges (sourceA1900 + difference 0 5) (sourceB1900 + difference 5 0) sourceC1900) = raw27361 := by
      apply Matrix.ext; unfold tripleCharges sourceA1900 sourceB1900 sourceC1900 difference raw27361; decide +kernel
    rw [ha]
    exact (canonical27361 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1900 + sourceB1900) sourceC1900) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1900 + sourceB1900) sourceC1900) = raw27319 := by
      apply Matrix.ext; unfold doubleCharges sourceA1900 sourceB1900 sourceC1900 raw27319; decide +kernel
    rw [ha]
    exact (canonical27319 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1900 sourceB1900 sourceC1900
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1900, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1901 : Charge := ![0, 1, 0, 2, -1, -2]
def sourceB1901 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC1901 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceForm1901 : Integer.Sparse Master := [(Sum.inr 1910, 1), (Sum.inr 1916, 1), (Sum.inr 1917, 1), (Sum.inr 1948, 1), (Sum.inr 2207, 1), (Sum.inr 3472, 1), (Sum.inr 4081, -1)]

theorem sourceEq1901 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1901 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1901 + difference 0 1) (sourceB1901 + difference 1 0) sourceC1901) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3472) := by
    have ha : (tripleCharges (sourceA1901 + difference 0 1) (sourceB1901 + difference 1 0) sourceC1901) = raw27357 := by
      apply Matrix.ext; unfold tripleCharges sourceA1901 sourceB1901 sourceC1901 difference raw27357; decide +kernel
    rw [ha]
    exact (canonical27357 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1901 + difference 1 1) (sourceB1901 + difference 1 1) sourceC1901) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2207) := by
    have ha : (tripleCharges (sourceA1901 + difference 1 1) (sourceB1901 + difference 1 1) sourceC1901) = raw27356 := by
      apply Matrix.ext; unfold tripleCharges sourceA1901 sourceB1901 sourceC1901 difference raw27356; decide +kernel
    rw [ha]
    exact (canonical27356 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1901 + difference 2 1) (sourceB1901 + difference 1 2) sourceC1901) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1910) := by
    have ha : (tripleCharges (sourceA1901 + difference 2 1) (sourceB1901 + difference 1 2) sourceC1901) = raw27362 := by
      apply Matrix.ext; unfold tripleCharges sourceA1901 sourceB1901 sourceC1901 difference raw27362; decide +kernel
    rw [ha]
    exact (canonical27362 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1901 + difference 3 1) (sourceB1901 + difference 1 3) sourceC1901) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1916) := by
    have ha : (tripleCharges (sourceA1901 + difference 3 1) (sourceB1901 + difference 1 3) sourceC1901) = raw27363 := by
      apply Matrix.ext; unfold tripleCharges sourceA1901 sourceB1901 sourceC1901 difference raw27363; decide +kernel
    rw [ha]
    exact (canonical27363 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1901 + difference 4 1) (sourceB1901 + difference 1 4) sourceC1901) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1948) := by
    have ha : (tripleCharges (sourceA1901 + difference 4 1) (sourceB1901 + difference 1 4) sourceC1901) = raw27364 := by
      apply Matrix.ext; unfold tripleCharges sourceA1901 sourceB1901 sourceC1901 difference raw27364; decide +kernel
    rw [ha]
    exact (canonical27364 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1901 + difference 5 1) (sourceB1901 + difference 1 5) sourceC1901) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1917) := by
    have ha : (tripleCharges (sourceA1901 + difference 5 1) (sourceB1901 + difference 1 5) sourceC1901) = raw27365 := by
      apply Matrix.ext; unfold tripleCharges sourceA1901 sourceB1901 sourceC1901 difference raw27365; decide +kernel
    rw [ha]
    exact (canonical27365 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1901 + sourceB1901) sourceC1901) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1901 + sourceB1901) sourceC1901) = raw27319 := by
      apply Matrix.ext; unfold doubleCharges sourceA1901 sourceB1901 sourceC1901 raw27319; decide +kernel
    rw [ha]
    exact (canonical27319 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1901 sourceB1901 sourceC1901
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1901, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1902 : Charge := ![0, 1, 0, 2, -1, -2]
def sourceB1902 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC1902 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceForm1902 : Integer.Sparse Master := [(Sum.inr 2201, 1), (Sum.inr 2203, 1), (Sum.inr 2207, 1), (Sum.inr 2224, 1), (Sum.inr 2259, 1), (Sum.inr 3481, 1), (Sum.inr 4081, -1)]

theorem sourceEq1902 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1902 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1902 + difference 0 3) (sourceB1902 + difference 3 0) sourceC1902) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3481) := by
    have ha : (tripleCharges (sourceA1902 + difference 0 3) (sourceB1902 + difference 3 0) sourceC1902) = raw27359 := by
      apply Matrix.ext; unfold tripleCharges sourceA1902 sourceB1902 sourceC1902 difference raw27359; decide +kernel
    rw [ha]
    exact (canonical27359 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1902 + difference 1 3) (sourceB1902 + difference 3 1) sourceC1902) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2259) := by
    have ha : (tripleCharges (sourceA1902 + difference 1 3) (sourceB1902 + difference 3 1) sourceC1902) = raw27366 := by
      apply Matrix.ext; unfold tripleCharges sourceA1902 sourceB1902 sourceC1902 difference raw27366; decide +kernel
    rw [ha]
    exact (canonical27366 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1902 + difference 2 3) (sourceB1902 + difference 3 2) sourceC1902) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2201) := by
    have ha : (tripleCharges (sourceA1902 + difference 2 3) (sourceB1902 + difference 3 2) sourceC1902) = raw27367 := by
      apply Matrix.ext; unfold tripleCharges sourceA1902 sourceB1902 sourceC1902 difference raw27367; decide +kernel
    rw [ha]
    exact (canonical27367 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1902 + difference 3 3) (sourceB1902 + difference 3 3) sourceC1902) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2207) := by
    have ha : (tripleCharges (sourceA1902 + difference 3 3) (sourceB1902 + difference 3 3) sourceC1902) = raw27356 := by
      apply Matrix.ext; unfold tripleCharges sourceA1902 sourceB1902 sourceC1902 difference raw27356; decide +kernel
    rw [ha]
    exact (canonical27356 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1902 + difference 4 3) (sourceB1902 + difference 3 4) sourceC1902) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2224) := by
    have ha : (tripleCharges (sourceA1902 + difference 4 3) (sourceB1902 + difference 3 4) sourceC1902) = raw27343 := by
      apply Matrix.ext; unfold tripleCharges sourceA1902 sourceB1902 sourceC1902 difference raw27343; decide +kernel
    rw [ha]
    exact (canonical27343 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1902 + difference 5 3) (sourceB1902 + difference 3 5) sourceC1902) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2203) := by
    have ha : (tripleCharges (sourceA1902 + difference 5 3) (sourceB1902 + difference 3 5) sourceC1902) = raw27368 := by
      apply Matrix.ext; unfold tripleCharges sourceA1902 sourceB1902 sourceC1902 difference raw27368; decide +kernel
    rw [ha]
    exact (canonical27368 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1902 + sourceB1902) sourceC1902) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1902 + sourceB1902) sourceC1902) = raw27319 := by
      apply Matrix.ext; unfold doubleCharges sourceA1902 sourceB1902 sourceC1902 raw27319; decide +kernel
    rw [ha]
    exact (canonical27319 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1902 sourceB1902 sourceC1902
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1902, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1903 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1903 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceC1903 : Charge := ![3, 0, -1, -1, 0, -1]
def sourceForm1903 : Integer.Sparse Master := [(Sum.inr 905, 1), (Sum.inr 1790, 1), (Sum.inr 1973, 1), (Sum.inr 2009, 1), (Sum.inr 2020, 1), (Sum.inr 2025, 1), (Sum.inr 4083, -1)]

theorem sourceEq1903 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1903 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1903 + difference 2 0) (sourceB1903 + difference 0 2) sourceC1903) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 905) := by
    have ha : (tripleCharges (sourceA1903 + difference 2 0) (sourceB1903 + difference 0 2) sourceC1903) = raw20191 := by
      apply Matrix.ext; unfold tripleCharges sourceA1903 sourceB1903 sourceC1903 difference raw20191; decide +kernel
    rw [ha]
    exact (canonical20191 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1903 + difference 2 1) (sourceB1903 + difference 1 2) sourceC1903) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1790) := by
    have ha : (tripleCharges (sourceA1903 + difference 2 1) (sourceB1903 + difference 1 2) sourceC1903) = raw27369 := by
      apply Matrix.ext; unfold tripleCharges sourceA1903 sourceB1903 sourceC1903 difference raw27369; decide +kernel
    rw [ha]
    exact (canonical27369 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1903 + difference 2 2) (sourceB1903 + difference 2 2) sourceC1903) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2009) := by
    have ha : (tripleCharges (sourceA1903 + difference 2 2) (sourceB1903 + difference 2 2) sourceC1903) = raw27370 := by
      apply Matrix.ext; unfold tripleCharges sourceA1903 sourceB1903 sourceC1903 difference raw27370; decide +kernel
    rw [ha]
    exact (canonical27370 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1903 + difference 2 3) (sourceB1903 + difference 3 2) sourceC1903) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1973) := by
    have ha : (tripleCharges (sourceA1903 + difference 2 3) (sourceB1903 + difference 3 2) sourceC1903) = raw27371 := by
      apply Matrix.ext; unfold tripleCharges sourceA1903 sourceB1903 sourceC1903 difference raw27371; decide +kernel
    rw [ha]
    exact (canonical27371 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1903 + difference 2 4) (sourceB1903 + difference 4 2) sourceC1903) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2025) := by
    have ha : (tripleCharges (sourceA1903 + difference 2 4) (sourceB1903 + difference 4 2) sourceC1903) = raw27372 := by
      apply Matrix.ext; unfold tripleCharges sourceA1903 sourceB1903 sourceC1903 difference raw27372; decide +kernel
    rw [ha]
    exact (canonical27372 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1903 + difference 2 5) (sourceB1903 + difference 5 2) sourceC1903) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2020) := by
    have ha : (tripleCharges (sourceA1903 + difference 2 5) (sourceB1903 + difference 5 2) sourceC1903) = raw27373 := by
      apply Matrix.ext; unfold tripleCharges sourceA1903 sourceB1903 sourceC1903 difference raw27373; decide +kernel
    rw [ha]
    exact (canonical27373 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1903 + sourceB1903) sourceC1903) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA1903 + sourceB1903) sourceC1903) = raw20196 := by
      apply Matrix.ext; unfold doubleCharges sourceA1903 sourceB1903 sourceC1903 raw20196; decide +kernel
    rw [ha]
    exact (canonical20196 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1903 sourceB1903 sourceC1903
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1903, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1904 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1904 : Charge := ![3, 0, -1, -1, 0, -1]
def sourceC1904 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceForm1904 : Integer.Sparse Master := [(Sum.inr 1116, 1), (Sum.inr 2323, 1), (Sum.inr 2440, 1), (Sum.inr 2471, 2), (Sum.inr 2483, 1), (Sum.inr 4091, -1)]

theorem sourceEq1904 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1904 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1904 + difference 0 2) (sourceB1904 + difference 2 0) sourceC1904) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2483) := by
    have ha : (tripleCharges (sourceA1904 + difference 0 2) (sourceB1904 + difference 2 0) sourceC1904) = raw27374 := by
      apply Matrix.ext; unfold tripleCharges sourceA1904 sourceB1904 sourceC1904 difference raw27374; decide +kernel
    rw [ha]
    exact (canonical27374 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1904 + difference 1 2) (sourceB1904 + difference 2 1) sourceC1904) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2471) := by
    have ha : (tripleCharges (sourceA1904 + difference 1 2) (sourceB1904 + difference 2 1) sourceC1904) = raw5656 := by
      apply Matrix.ext; unfold tripleCharges sourceA1904 sourceB1904 sourceC1904 difference raw5656; decide +kernel
    rw [ha]
    exact (canonical5656 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1904 + difference 2 2) (sourceB1904 + difference 2 2) sourceC1904) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2471) := by
    have ha : (tripleCharges (sourceA1904 + difference 2 2) (sourceB1904 + difference 2 2) sourceC1904) = raw5649 := by
      apply Matrix.ext; unfold tripleCharges sourceA1904 sourceB1904 sourceC1904 difference raw5649; decide +kernel
    rw [ha]
    exact (canonical5649 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1904 + difference 3 2) (sourceB1904 + difference 2 3) sourceC1904) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2440) := by
    have ha : (tripleCharges (sourceA1904 + difference 3 2) (sourceB1904 + difference 2 3) sourceC1904) = raw27375 := by
      apply Matrix.ext; unfold tripleCharges sourceA1904 sourceB1904 sourceC1904 difference raw27375; decide +kernel
    rw [ha]
    exact (canonical27375 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1904 + difference 4 2) (sourceB1904 + difference 2 4) sourceC1904) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2323) := by
    have ha : (tripleCharges (sourceA1904 + difference 4 2) (sourceB1904 + difference 2 4) sourceC1904) = raw27376 := by
      apply Matrix.ext; unfold tripleCharges sourceA1904 sourceB1904 sourceC1904 difference raw27376; decide +kernel
    rw [ha]
    exact (canonical27376 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1904 + difference 5 2) (sourceB1904 + difference 2 5) sourceC1904) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1116) := by
    have ha : (tripleCharges (sourceA1904 + difference 5 2) (sourceB1904 + difference 2 5) sourceC1904) = raw27377 := by
      apply Matrix.ext; unfold tripleCharges sourceA1904 sourceB1904 sourceC1904 difference raw27377; decide +kernel
    rw [ha]
    exact (canonical27377 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1904 + sourceB1904) sourceC1904) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1904 + sourceB1904) sourceC1904) = raw5636 := by
      apply Matrix.ext; unfold doubleCharges sourceA1904 sourceB1904 sourceC1904 raw5636; decide +kernel
    rw [ha]
    exact (canonical5636 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1904 sourceB1904 sourceC1904
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1904, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1905 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceB1905 : Charge := ![3, 0, -1, -1, 0, -1]
def sourceC1905 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceForm1905 : Integer.Sparse Master := [(Sum.inr 1940, 1), (Sum.inr 2201, 1), (Sum.inr 3350, 1), (Sum.inr 3466, 1), (Sum.inr 3481, 2), (Sum.inr 4081, -1)]

theorem sourceEq1905 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1905 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1905 + difference 0 0) (sourceB1905 + difference 0 0) sourceC1905) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2201) := by
    have ha : (tripleCharges (sourceA1905 + difference 0 0) (sourceB1905 + difference 0 0) sourceC1905) = raw27367 := by
      apply Matrix.ext; unfold tripleCharges sourceA1905 sourceB1905 sourceC1905 difference raw27367; decide +kernel
    rw [ha]
    exact (canonical27367 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1905 + difference 0 1) (sourceB1905 + difference 1 0) sourceC1905) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3466) := by
    have ha : (tripleCharges (sourceA1905 + difference 0 1) (sourceB1905 + difference 1 0) sourceC1905) = raw27378 := by
      apply Matrix.ext; unfold tripleCharges sourceA1905 sourceB1905 sourceC1905 difference raw27378; decide +kernel
    rw [ha]
    exact (canonical27378 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1905 + difference 0 2) (sourceB1905 + difference 2 0) sourceC1905) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3481) := by
    have ha : (tripleCharges (sourceA1905 + difference 0 2) (sourceB1905 + difference 2 0) sourceC1905) = raw27359 := by
      apply Matrix.ext; unfold tripleCharges sourceA1905 sourceB1905 sourceC1905 difference raw27359; decide +kernel
    rw [ha]
    exact (canonical27359 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1905 + difference 0 3) (sourceB1905 + difference 3 0) sourceC1905) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3481) := by
    have ha : (tripleCharges (sourceA1905 + difference 0 3) (sourceB1905 + difference 3 0) sourceC1905) = raw27379 := by
      apply Matrix.ext; unfold tripleCharges sourceA1905 sourceB1905 sourceC1905 difference raw27379; decide +kernel
    rw [ha]
    exact (canonical27379 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1905 + difference 0 4) (sourceB1905 + difference 4 0) sourceC1905) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3350) := by
    have ha : (tripleCharges (sourceA1905 + difference 0 4) (sourceB1905 + difference 4 0) sourceC1905) = raw27380 := by
      apply Matrix.ext; unfold tripleCharges sourceA1905 sourceB1905 sourceC1905 difference raw27380; decide +kernel
    rw [ha]
    exact (canonical27380 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1905 + difference 0 5) (sourceB1905 + difference 5 0) sourceC1905) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1940) := by
    have ha : (tripleCharges (sourceA1905 + difference 0 5) (sourceB1905 + difference 5 0) sourceC1905) = raw27381 := by
      apply Matrix.ext; unfold tripleCharges sourceA1905 sourceB1905 sourceC1905 difference raw27381; decide +kernel
    rw [ha]
    exact (canonical27381 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1905 + sourceB1905) sourceC1905) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1905 + sourceB1905) sourceC1905) = raw27319 := by
      apply Matrix.ext; unfold doubleCharges sourceA1905 sourceB1905 sourceC1905 raw27319; decide +kernel
    rw [ha]
    exact (canonical27319 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1905 sourceB1905 sourceC1905
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1905, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1906 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceB1906 : Charge := ![3, 0, -1, -1, 0, -1]
def sourceC1906 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceForm1906 : Integer.Sparse Master := [(Sum.inr 1907, 1), (Sum.inr 1910, 2), (Sum.inr 1940, 1), (Sum.inr 2201, 1), (Sum.inr 3466, 1), (Sum.inr 4081, -1)]

theorem sourceEq1906 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1906 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1906 + difference 0 1) (sourceB1906 + difference 1 0) sourceC1906) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3466) := by
    have ha : (tripleCharges (sourceA1906 + difference 0 1) (sourceB1906 + difference 1 0) sourceC1906) = raw27378 := by
      apply Matrix.ext; unfold tripleCharges sourceA1906 sourceB1906 sourceC1906 difference raw27378; decide +kernel
    rw [ha]
    exact (canonical27378 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1906 + difference 1 1) (sourceB1906 + difference 1 1) sourceC1906) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2201) := by
    have ha : (tripleCharges (sourceA1906 + difference 1 1) (sourceB1906 + difference 1 1) sourceC1906) = raw27367 := by
      apply Matrix.ext; unfold tripleCharges sourceA1906 sourceB1906 sourceC1906 difference raw27367; decide +kernel
    rw [ha]
    exact (canonical27367 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1906 + difference 2 1) (sourceB1906 + difference 1 2) sourceC1906) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1910) := by
    have ha : (tripleCharges (sourceA1906 + difference 2 1) (sourceB1906 + difference 1 2) sourceC1906) = raw27382 := by
      apply Matrix.ext; unfold tripleCharges sourceA1906 sourceB1906 sourceC1906 difference raw27382; decide +kernel
    rw [ha]
    exact (canonical27382 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1906 + difference 3 1) (sourceB1906 + difference 1 3) sourceC1906) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1910) := by
    have ha : (tripleCharges (sourceA1906 + difference 3 1) (sourceB1906 + difference 1 3) sourceC1906) = raw27362 := by
      apply Matrix.ext; unfold tripleCharges sourceA1906 sourceB1906 sourceC1906 difference raw27362; decide +kernel
    rw [ha]
    exact (canonical27362 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1906 + difference 4 1) (sourceB1906 + difference 1 4) sourceC1906) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1940) := by
    have ha : (tripleCharges (sourceA1906 + difference 4 1) (sourceB1906 + difference 1 4) sourceC1906) = raw27383 := by
      apply Matrix.ext; unfold tripleCharges sourceA1906 sourceB1906 sourceC1906 difference raw27383; decide +kernel
    rw [ha]
    exact (canonical27383 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1906 + difference 5 1) (sourceB1906 + difference 1 5) sourceC1906) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1907) := by
    have ha : (tripleCharges (sourceA1906 + difference 5 1) (sourceB1906 + difference 1 5) sourceC1906) = raw27384 := by
      apply Matrix.ext; unfold tripleCharges sourceA1906 sourceB1906 sourceC1906 difference raw27384; decide +kernel
    rw [ha]
    exact (canonical27384 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1906 + sourceB1906) sourceC1906) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1906 + sourceB1906) sourceC1906) = raw27319 := by
      apply Matrix.ext; unfold doubleCharges sourceA1906 sourceB1906 sourceC1906 raw27319; decide +kernel
    rw [ha]
    exact (canonical27319 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1906 sourceB1906 sourceC1906
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1906, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1907 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1907 : Charge := ![0, 1, 1, 1, 0, -3]
def sourceC1907 : Charge := ![3, 0, -1, -1, -1, 0]
def sourceForm1907 : Integer.Sparse Master := [(Sum.inr 909, 1), (Sum.inr 1793, 1), (Sum.inr 1976, 1), (Sum.inr 2010, 2), (Sum.inr 2023, 1), (Sum.inr 4083, -1)]

theorem sourceEq1907 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1907 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1907 + difference 2 0) (sourceB1907 + difference 0 2) sourceC1907) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 909) := by
    have ha : (tripleCharges (sourceA1907 + difference 2 0) (sourceB1907 + difference 0 2) sourceC1907) = raw20218 := by
      apply Matrix.ext; unfold tripleCharges sourceA1907 sourceB1907 sourceC1907 difference raw20218; decide +kernel
    rw [ha]
    exact (canonical20218 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1907 + difference 2 1) (sourceB1907 + difference 1 2) sourceC1907) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1793) := by
    have ha : (tripleCharges (sourceA1907 + difference 2 1) (sourceB1907 + difference 1 2) sourceC1907) = raw27385 := by
      apply Matrix.ext; unfold tripleCharges sourceA1907 sourceB1907 sourceC1907 difference raw27385; decide +kernel
    rw [ha]
    exact (canonical27385 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1907 + difference 2 2) (sourceB1907 + difference 2 2) sourceC1907) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2010) := by
    have ha : (tripleCharges (sourceA1907 + difference 2 2) (sourceB1907 + difference 2 2) sourceC1907) = raw3846 := by
      apply Matrix.ext; unfold tripleCharges sourceA1907 sourceB1907 sourceC1907 difference raw3846; decide +kernel
    rw [ha]
    exact (canonical3846 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1907 + difference 2 3) (sourceB1907 + difference 3 2) sourceC1907) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1976) := by
    have ha : (tripleCharges (sourceA1907 + difference 2 3) (sourceB1907 + difference 3 2) sourceC1907) = raw27386 := by
      apply Matrix.ext; unfold tripleCharges sourceA1907 sourceB1907 sourceC1907 difference raw27386; decide +kernel
    rw [ha]
    exact (canonical27386 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1907 + difference 2 4) (sourceB1907 + difference 4 2) sourceC1907) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2010) := by
    have ha : (tripleCharges (sourceA1907 + difference 2 4) (sourceB1907 + difference 4 2) sourceC1907) = raw3844 := by
      apply Matrix.ext; unfold tripleCharges sourceA1907 sourceB1907 sourceC1907 difference raw3844; decide +kernel
    rw [ha]
    exact (canonical3844 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1907 + difference 2 5) (sourceB1907 + difference 5 2) sourceC1907) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2023) := by
    have ha : (tripleCharges (sourceA1907 + difference 2 5) (sourceB1907 + difference 5 2) sourceC1907) = raw27387 := by
      apply Matrix.ext; unfold tripleCharges sourceA1907 sourceB1907 sourceC1907 difference raw27387; decide +kernel
    rw [ha]
    exact (canonical27387 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1907 + sourceB1907) sourceC1907) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA1907 + sourceB1907) sourceC1907) = raw3834 := by
      apply Matrix.ext; unfold doubleCharges sourceA1907 sourceB1907 sourceC1907 raw3834; decide +kernel
    rw [ha]
    exact (canonical3834 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1907 sourceB1907 sourceC1907
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1907, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1908 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1908 : Charge := ![3, 0, -1, -2, 0, 0]
def sourceC1908 : Charge := ![0, 1, 1, 2, -1, -3]
def sourceForm1908 : Integer.Sparse Master := [(Sum.inr 1903, 1), (Sum.inr 1904, 1), (Sum.inr 1913, 1), (Sum.inr 1925, 1), (Sum.inr 2196, 1), (Sum.inr 3464, 1), (Sum.inr 4080, -1)]

theorem sourceEq1908 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1908 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1908 + difference 0 0) (sourceB1908 + difference 0 0) sourceC1908) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1903) := by
    have ha : (tripleCharges (sourceA1908 + difference 0 0) (sourceB1908 + difference 0 0) sourceC1908) = raw27388 := by
      apply Matrix.ext; unfold tripleCharges sourceA1908 sourceB1908 sourceC1908 difference raw27388; decide +kernel
    rw [ha]
    exact (canonical27388 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1908 + difference 0 1) (sourceB1908 + difference 1 0) sourceC1908) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1904) := by
    have ha : (tripleCharges (sourceA1908 + difference 0 1) (sourceB1908 + difference 1 0) sourceC1908) = raw27389 := by
      apply Matrix.ext; unfold tripleCharges sourceA1908 sourceB1908 sourceC1908 difference raw27389; decide +kernel
    rw [ha]
    exact (canonical27389 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1908 + difference 0 2) (sourceB1908 + difference 2 0) sourceC1908) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1925) := by
    have ha : (tripleCharges (sourceA1908 + difference 0 2) (sourceB1908 + difference 2 0) sourceC1908) = raw27390 := by
      apply Matrix.ext; unfold tripleCharges sourceA1908 sourceB1908 sourceC1908 difference raw27390; decide +kernel
    rw [ha]
    exact (canonical27390 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1908 + difference 0 3) (sourceB1908 + difference 3 0) sourceC1908) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1913) := by
    have ha : (tripleCharges (sourceA1908 + difference 0 3) (sourceB1908 + difference 3 0) sourceC1908) = raw27391 := by
      apply Matrix.ext; unfold tripleCharges sourceA1908 sourceB1908 sourceC1908 difference raw27391; decide +kernel
    rw [ha]
    exact (canonical27391 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1908 + difference 0 4) (sourceB1908 + difference 4 0) sourceC1908) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2196) := by
    have ha : (tripleCharges (sourceA1908 + difference 0 4) (sourceB1908 + difference 4 0) sourceC1908) = raw27392 := by
      apply Matrix.ext; unfold tripleCharges sourceA1908 sourceB1908 sourceC1908 difference raw27392; decide +kernel
    rw [ha]
    exact (canonical27392 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1908 + difference 0 5) (sourceB1908 + difference 5 0) sourceC1908) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3464) := by
    have ha : (tripleCharges (sourceA1908 + difference 0 5) (sourceB1908 + difference 5 0) sourceC1908) = raw27393 := by
      apply Matrix.ext; unfold tripleCharges sourceA1908 sourceB1908 sourceC1908 difference raw27393; decide +kernel
    rw [ha]
    exact (canonical27393 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1908 + sourceB1908) sourceC1908) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1908 + sourceB1908) sourceC1908) = raw27394 := by
      apply Matrix.ext; unfold doubleCharges sourceA1908 sourceB1908 sourceC1908 raw27394; decide +kernel
    rw [ha]
    exact (canonical27394 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1908 sourceB1908 sourceC1908
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1908, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1909 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1909 : Charge := ![0, 2, 0, 0, 1, -3]
def sourceC1909 : Charge := ![3, -1, 0, 0, -2, 0]
def sourceForm1909 : Integer.Sparse Master := [(Sum.inr 954, 1), (Sum.inr 1832, 1), (Sum.inr 1980, 2), (Sum.inr 2113, 1), (Sum.inr 2115, 1), (Sum.inr 4084, -1)]

theorem sourceEq1909 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1909 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1909 + difference 4 0) (sourceB1909 + difference 0 4) sourceC1909) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 954) := by
    have ha : (tripleCharges (sourceA1909 + difference 4 0) (sourceB1909 + difference 0 4) sourceC1909) = raw23032 := by
      apply Matrix.ext; unfold tripleCharges sourceA1909 sourceB1909 sourceC1909 difference raw23032; decide +kernel
    rw [ha]
    exact (canonical23032 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1909 + difference 4 1) (sourceB1909 + difference 1 4) sourceC1909) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1832) := by
    have ha : (tripleCharges (sourceA1909 + difference 4 1) (sourceB1909 + difference 1 4) sourceC1909) = raw27395 := by
      apply Matrix.ext; unfold tripleCharges sourceA1909 sourceB1909 sourceC1909 difference raw27395; decide +kernel
    rw [ha]
    exact (canonical27395 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1909 + difference 4 2) (sourceB1909 + difference 2 4) sourceC1909) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1980) := by
    have ha : (tripleCharges (sourceA1909 + difference 4 2) (sourceB1909 + difference 2 4) sourceC1909) = raw27396 := by
      apply Matrix.ext; unfold tripleCharges sourceA1909 sourceB1909 sourceC1909 difference raw27396; decide +kernel
    rw [ha]
    exact (canonical27396 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1909 + difference 4 3) (sourceB1909 + difference 3 4) sourceC1909) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1980) := by
    have ha : (tripleCharges (sourceA1909 + difference 4 3) (sourceB1909 + difference 3 4) sourceC1909) = raw27397 := by
      apply Matrix.ext; unfold tripleCharges sourceA1909 sourceB1909 sourceC1909 difference raw27397; decide +kernel
    rw [ha]
    exact (canonical27397 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1909 + difference 4 4) (sourceB1909 + difference 4 4) sourceC1909) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2113) := by
    have ha : (tripleCharges (sourceA1909 + difference 4 4) (sourceB1909 + difference 4 4) sourceC1909) = raw27398 := by
      apply Matrix.ext; unfold tripleCharges sourceA1909 sourceB1909 sourceC1909 difference raw27398; decide +kernel
    rw [ha]
    exact (canonical27398 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1909 + difference 4 5) (sourceB1909 + difference 5 4) sourceC1909) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2115) := by
    have ha : (tripleCharges (sourceA1909 + difference 4 5) (sourceB1909 + difference 5 4) sourceC1909) = raw23028 := by
      apply Matrix.ext; unfold tripleCharges sourceA1909 sourceB1909 sourceC1909 difference raw23028; decide +kernel
    rw [ha]
    exact (canonical23028 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1909 + sourceB1909) sourceC1909) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1909 + sourceB1909) sourceC1909) = raw23023 := by
      apply Matrix.ext; unfold doubleCharges sourceA1909 sourceB1909 sourceC1909 raw23023; decide +kernel
    rw [ha]
    exact (canonical23023 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1909 sourceB1909 sourceC1909
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1909, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1910 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1910 : Charge := ![0, 2, 0, 1, -1, -2]
def sourceC1910 : Charge := ![3, -1, 0, -1, 0, -1]
def sourceForm1910 : Integer.Sparse Master := [(Sum.inr 945, 1), (Sum.inr 1825, 1), (Sum.inr 1973, 1), (Sum.inr 2090, 1), (Sum.inr 2107, 1), (Sum.inr 2112, 1), (Sum.inr 4083, -1)]

theorem sourceEq1910 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1910 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1910 + difference 3 0) (sourceB1910 + difference 0 3) sourceC1910) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 945) := by
    have ha : (tripleCharges (sourceA1910 + difference 3 0) (sourceB1910 + difference 0 3) sourceC1910) = raw25240 := by
      apply Matrix.ext; unfold tripleCharges sourceA1910 sourceB1910 sourceC1910 difference raw25240; decide +kernel
    rw [ha]
    exact (canonical25240 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1910 + difference 3 1) (sourceB1910 + difference 1 3) sourceC1910) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1825) := by
    have ha : (tripleCharges (sourceA1910 + difference 3 1) (sourceB1910 + difference 1 3) sourceC1910) = raw27399 := by
      apply Matrix.ext; unfold tripleCharges sourceA1910 sourceB1910 sourceC1910 difference raw27399; decide +kernel
    rw [ha]
    exact (canonical27399 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1910 + difference 3 2) (sourceB1910 + difference 2 3) sourceC1910) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1973) := by
    have ha : (tripleCharges (sourceA1910 + difference 3 2) (sourceB1910 + difference 2 3) sourceC1910) = raw27400 := by
      apply Matrix.ext; unfold tripleCharges sourceA1910 sourceB1910 sourceC1910 difference raw27400; decide +kernel
    rw [ha]
    exact (canonical27400 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1910 + difference 3 3) (sourceB1910 + difference 3 3) sourceC1910) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2090) := by
    have ha : (tripleCharges (sourceA1910 + difference 3 3) (sourceB1910 + difference 3 3) sourceC1910) = raw27401 := by
      apply Matrix.ext; unfold tripleCharges sourceA1910 sourceB1910 sourceC1910 difference raw27401; decide +kernel
    rw [ha]
    exact (canonical27401 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1910 + difference 3 4) (sourceB1910 + difference 4 3) sourceC1910) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2112) := by
    have ha : (tripleCharges (sourceA1910 + difference 3 4) (sourceB1910 + difference 4 3) sourceC1910) = raw27402 := by
      apply Matrix.ext; unfold tripleCharges sourceA1910 sourceB1910 sourceC1910 difference raw27402; decide +kernel
    rw [ha]
    exact (canonical27402 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1910 + difference 3 5) (sourceB1910 + difference 5 3) sourceC1910) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2107) := by
    have ha : (tripleCharges (sourceA1910 + difference 3 5) (sourceB1910 + difference 5 3) sourceC1910) = raw25236 := by
      apply Matrix.ext; unfold tripleCharges sourceA1910 sourceB1910 sourceC1910 difference raw25236; decide +kernel
    rw [ha]
    exact (canonical25236 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1910 + sourceB1910) sourceC1910) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA1910 + sourceB1910) sourceC1910) = raw25231 := by
      apply Matrix.ext; unfold doubleCharges sourceA1910 sourceB1910 sourceC1910 raw25231; decide +kernel
    rw [ha]
    exact (canonical25231 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1910 sourceB1910 sourceC1910
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1910, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1911 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1911 : Charge := ![3, -1, 0, -1, 0, -1]
def sourceC1911 : Charge := ![0, 2, 0, 1, -1, -2]
def sourceForm1911 : Integer.Sparse Master := [(Sum.inr 1121, 1), (Sum.inr 2327, 1), (Sum.inr 2423, 1), (Sum.inr 2443, 1), (Sum.inr 2486, 1), (Sum.inr 2488, 1), (Sum.inr 4092, -1)]

theorem sourceEq1911 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1911 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1911 + difference 0 1) (sourceB1911 + difference 1 0) sourceC1911) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2488) := by
    have ha : (tripleCharges (sourceA1911 + difference 0 1) (sourceB1911 + difference 1 0) sourceC1911) = raw27403 := by
      apply Matrix.ext; unfold tripleCharges sourceA1911 sourceB1911 sourceC1911 difference raw27403; decide +kernel
    rw [ha]
    exact (canonical27403 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1911 + difference 1 1) (sourceB1911 + difference 1 1) sourceC1911) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2486) := by
    have ha : (tripleCharges (sourceA1911 + difference 1 1) (sourceB1911 + difference 1 1) sourceC1911) = raw27404 := by
      apply Matrix.ext; unfold tripleCharges sourceA1911 sourceB1911 sourceC1911 difference raw27404; decide +kernel
    rw [ha]
    exact (canonical27404 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1911 + difference 2 1) (sourceB1911 + difference 1 2) sourceC1911) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2423) := by
    have ha : (tripleCharges (sourceA1911 + difference 2 1) (sourceB1911 + difference 1 2) sourceC1911) = raw27405 := by
      apply Matrix.ext; unfold tripleCharges sourceA1911 sourceB1911 sourceC1911 difference raw27405; decide +kernel
    rw [ha]
    exact (canonical27405 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1911 + difference 3 1) (sourceB1911 + difference 1 3) sourceC1911) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2443) := by
    have ha : (tripleCharges (sourceA1911 + difference 3 1) (sourceB1911 + difference 1 3) sourceC1911) = raw27406 := by
      apply Matrix.ext; unfold tripleCharges sourceA1911 sourceB1911 sourceC1911 difference raw27406; decide +kernel
    rw [ha]
    exact (canonical27406 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1911 + difference 4 1) (sourceB1911 + difference 1 4) sourceC1911) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2327) := by
    have ha : (tripleCharges (sourceA1911 + difference 4 1) (sourceB1911 + difference 1 4) sourceC1911) = raw27407 := by
      apply Matrix.ext; unfold tripleCharges sourceA1911 sourceB1911 sourceC1911 difference raw27407; decide +kernel
    rw [ha]
    exact (canonical27407 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1911 + difference 5 1) (sourceB1911 + difference 1 5) sourceC1911) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1121) := by
    have ha : (tripleCharges (sourceA1911 + difference 5 1) (sourceB1911 + difference 1 5) sourceC1911) = raw27408 := by
      apply Matrix.ext; unfold tripleCharges sourceA1911 sourceB1911 sourceC1911 difference raw27408; decide +kernel
    rw [ha]
    exact (canonical27408 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1911 + sourceB1911) sourceC1911) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1911 + sourceB1911) sourceC1911) = raw27409 := by
      apply Matrix.ext; unfold doubleCharges sourceA1911 sourceB1911 sourceC1911 raw27409; decide +kernel
    rw [ha]
    exact (canonical27409 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1911 sourceB1911 sourceC1911
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1911, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1912 : Charge := ![0, 2, 0, 1, -1, -2]
def sourceB1912 : Charge := ![3, -1, 0, -1, 0, -1]
def sourceC1912 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceForm1912 : Integer.Sparse Master := [(Sum.inr 1946, 1), (Sum.inr 2259, 1), (Sum.inr 3355, 1), (Sum.inr 3434, 1), (Sum.inr 3481, 1), (Sum.inr 3486, 1), (Sum.inr 4081, -1)]

theorem sourceEq1912 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1912 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1912 + difference 0 0) (sourceB1912 + difference 0 0) sourceC1912) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2259) := by
    have ha : (tripleCharges (sourceA1912 + difference 0 0) (sourceB1912 + difference 0 0) sourceC1912) = raw27366 := by
      apply Matrix.ext; unfold tripleCharges sourceA1912 sourceB1912 sourceC1912 difference raw27366; decide +kernel
    rw [ha]
    exact (canonical27366 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1912 + difference 0 1) (sourceB1912 + difference 1 0) sourceC1912) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3481) := by
    have ha : (tripleCharges (sourceA1912 + difference 0 1) (sourceB1912 + difference 1 0) sourceC1912) = raw27359 := by
      apply Matrix.ext; unfold tripleCharges sourceA1912 sourceB1912 sourceC1912 difference raw27359; decide +kernel
    rw [ha]
    exact (canonical27359 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1912 + difference 0 2) (sourceB1912 + difference 2 0) sourceC1912) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3434) := by
    have ha : (tripleCharges (sourceA1912 + difference 0 2) (sourceB1912 + difference 2 0) sourceC1912) = raw27410 := by
      apply Matrix.ext; unfold tripleCharges sourceA1912 sourceB1912 sourceC1912 difference raw27410; decide +kernel
    rw [ha]
    exact (canonical27410 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1912 + difference 0 3) (sourceB1912 + difference 3 0) sourceC1912) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3486) := by
    have ha : (tripleCharges (sourceA1912 + difference 0 3) (sourceB1912 + difference 3 0) sourceC1912) = raw27411 := by
      apply Matrix.ext; unfold tripleCharges sourceA1912 sourceB1912 sourceC1912 difference raw27411; decide +kernel
    rw [ha]
    exact (canonical27411 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1912 + difference 0 4) (sourceB1912 + difference 4 0) sourceC1912) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3355) := by
    have ha : (tripleCharges (sourceA1912 + difference 0 4) (sourceB1912 + difference 4 0) sourceC1912) = raw27412 := by
      apply Matrix.ext; unfold tripleCharges sourceA1912 sourceB1912 sourceC1912 difference raw27412; decide +kernel
    rw [ha]
    exact (canonical27412 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1912 + difference 0 5) (sourceB1912 + difference 5 0) sourceC1912) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1946) := by
    have ha : (tripleCharges (sourceA1912 + difference 0 5) (sourceB1912 + difference 5 0) sourceC1912) = raw27413 := by
      apply Matrix.ext; unfold tripleCharges sourceA1912 sourceB1912 sourceC1912 difference raw27413; decide +kernel
    rw [ha]
    exact (canonical27413 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1912 + sourceB1912) sourceC1912) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1912 + sourceB1912) sourceC1912) = raw27319 := by
      apply Matrix.ext; unfold doubleCharges sourceA1912 sourceB1912 sourceC1912 raw27319; decide +kernel
    rw [ha]
    exact (canonical27319 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1912 sourceB1912 sourceC1912
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1912, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1913 : Charge := ![0, 2, 0, 1, -1, -2]
def sourceB1913 : Charge := ![3, -1, 0, -1, 0, -1]
def sourceC1913 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceForm1913 : Integer.Sparse Master := [(Sum.inr 2259, 2), (Sum.inr 2261, 1), (Sum.inr 2267, 1), (Sum.inr 2287, 1), (Sum.inr 3486, 1), (Sum.inr 4081, -1)]

theorem sourceEq1913 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1913 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1913 + difference 0 3) (sourceB1913 + difference 3 0) sourceC1913) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3486) := by
    have ha : (tripleCharges (sourceA1913 + difference 0 3) (sourceB1913 + difference 3 0) sourceC1913) = raw27411 := by
      apply Matrix.ext; unfold tripleCharges sourceA1913 sourceB1913 sourceC1913 difference raw27411; decide +kernel
    rw [ha]
    exact (canonical27411 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1913 + difference 1 3) (sourceB1913 + difference 3 1) sourceC1913) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2267) := by
    have ha : (tripleCharges (sourceA1913 + difference 1 3) (sourceB1913 + difference 3 1) sourceC1913) = raw27414 := by
      apply Matrix.ext; unfold tripleCharges sourceA1913 sourceB1913 sourceC1913 difference raw27414; decide +kernel
    rw [ha]
    exact (canonical27414 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1913 + difference 2 3) (sourceB1913 + difference 3 2) sourceC1913) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2259) := by
    have ha : (tripleCharges (sourceA1913 + difference 2 3) (sourceB1913 + difference 3 2) sourceC1913) = raw27415 := by
      apply Matrix.ext; unfold tripleCharges sourceA1913 sourceB1913 sourceC1913 difference raw27415; decide +kernel
    rw [ha]
    exact (canonical27415 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1913 + difference 3 3) (sourceB1913 + difference 3 3) sourceC1913) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2259) := by
    have ha : (tripleCharges (sourceA1913 + difference 3 3) (sourceB1913 + difference 3 3) sourceC1913) = raw27366 := by
      apply Matrix.ext; unfold tripleCharges sourceA1913 sourceB1913 sourceC1913 difference raw27366; decide +kernel
    rw [ha]
    exact (canonical27366 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1913 + difference 4 3) (sourceB1913 + difference 3 4) sourceC1913) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2287) := by
    have ha : (tripleCharges (sourceA1913 + difference 4 3) (sourceB1913 + difference 3 4) sourceC1913) = raw27416 := by
      apply Matrix.ext; unfold tripleCharges sourceA1913 sourceB1913 sourceC1913 difference raw27416; decide +kernel
    rw [ha]
    exact (canonical27416 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1913 + difference 5 3) (sourceB1913 + difference 3 5) sourceC1913) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2261) := by
    have ha : (tripleCharges (sourceA1913 + difference 5 3) (sourceB1913 + difference 3 5) sourceC1913) = raw27417 := by
      apply Matrix.ext; unfold tripleCharges sourceA1913 sourceB1913 sourceC1913 difference raw27417; decide +kernel
    rw [ha]
    exact (canonical27417 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1913 + sourceB1913) sourceC1913) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1913 + sourceB1913) sourceC1913) = raw27319 := by
      apply Matrix.ext; unfold doubleCharges sourceA1913 sourceB1913 sourceC1913 raw27319; decide +kernel
    rw [ha]
    exact (canonical27319 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1913 sourceB1913 sourceC1913
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1913, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1914 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1914 : Charge := ![3, -1, 0, -2, 0, 0]
def sourceC1914 : Charge := ![0, 2, 0, 2, -1, -3]
def sourceForm1914 : Integer.Sparse Master := [(Sum.inr 1923, 1), (Sum.inr 1927, 1), (Sum.inr 1928, 1), (Sum.inr 1949, 1), (Sum.inr 2217, 1), (Sum.inr 3480, 1), (Sum.inr 4082, -1)]

theorem sourceEq1914 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1914 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1914 + difference 0 0) (sourceB1914 + difference 0 0) sourceC1914) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1927) := by
    have ha : (tripleCharges (sourceA1914 + difference 0 0) (sourceB1914 + difference 0 0) sourceC1914) = raw27418 := by
      apply Matrix.ext; unfold tripleCharges sourceA1914 sourceB1914 sourceC1914 difference raw27418; decide +kernel
    rw [ha]
    exact (canonical27418 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1914 + difference 0 1) (sourceB1914 + difference 1 0) sourceC1914) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1928) := by
    have ha : (tripleCharges (sourceA1914 + difference 0 1) (sourceB1914 + difference 1 0) sourceC1914) = raw27419 := by
      apply Matrix.ext; unfold tripleCharges sourceA1914 sourceB1914 sourceC1914 difference raw27419; decide +kernel
    rw [ha]
    exact (canonical27419 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1914 + difference 0 2) (sourceB1914 + difference 2 0) sourceC1914) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1923) := by
    have ha : (tripleCharges (sourceA1914 + difference 0 2) (sourceB1914 + difference 2 0) sourceC1914) = raw27420 := by
      apply Matrix.ext; unfold tripleCharges sourceA1914 sourceB1914 sourceC1914 difference raw27420; decide +kernel
    rw [ha]
    exact (canonical27420 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1914 + difference 0 3) (sourceB1914 + difference 3 0) sourceC1914) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1949) := by
    have ha : (tripleCharges (sourceA1914 + difference 0 3) (sourceB1914 + difference 3 0) sourceC1914) = raw27421 := by
      apply Matrix.ext; unfold tripleCharges sourceA1914 sourceB1914 sourceC1914 difference raw27421; decide +kernel
    rw [ha]
    exact (canonical27421 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1914 + difference 0 4) (sourceB1914 + difference 4 0) sourceC1914) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2217) := by
    have ha : (tripleCharges (sourceA1914 + difference 0 4) (sourceB1914 + difference 4 0) sourceC1914) = raw27422 := by
      apply Matrix.ext; unfold tripleCharges sourceA1914 sourceB1914 sourceC1914 difference raw27422; decide +kernel
    rw [ha]
    exact (canonical27422 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1914 + difference 0 5) (sourceB1914 + difference 5 0) sourceC1914) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3480) := by
    have ha : (tripleCharges (sourceA1914 + difference 0 5) (sourceB1914 + difference 5 0) sourceC1914) = raw27423 := by
      apply Matrix.ext; unfold tripleCharges sourceA1914 sourceB1914 sourceC1914 difference raw27423; decide +kernel
    rw [ha]
    exact (canonical27423 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1914 + sourceB1914) sourceC1914) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA1914 + sourceB1914) sourceC1914) = raw27424 := by
      apply Matrix.ext; unfold doubleCharges sourceA1914 sourceB1914 sourceC1914 raw27424; decide +kernel
    rw [ha]
    exact (canonical27424 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1914 sourceB1914 sourceC1914
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1914, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1915 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1915 : Charge := ![3, -2, 0, 0, 0, -1]
def sourceC1915 : Charge := ![0, 3, 0, 0, -1, -2]
def sourceForm1915 : Integer.Sparse Master := [(Sum.inr 1146, 1), (Sum.inr 2346, 1), (Sum.inr 2435, 2), (Sum.inr 2520, 1), (Sum.inr 2522, 1), (Sum.inr 4084, -1)]

theorem sourceEq1915 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1915 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1915 + difference 0 1) (sourceB1915 + difference 1 0) sourceC1915) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2522) := by
    have ha : (tripleCharges (sourceA1915 + difference 0 1) (sourceB1915 + difference 1 0) sourceC1915) = raw27425 := by
      apply Matrix.ext; unfold tripleCharges sourceA1915 sourceB1915 sourceC1915 difference raw27425; decide +kernel
    rw [ha]
    exact (canonical27425 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1915 + difference 1 1) (sourceB1915 + difference 1 1) sourceC1915) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2520) := by
    have ha : (tripleCharges (sourceA1915 + difference 1 1) (sourceB1915 + difference 1 1) sourceC1915) = raw27426 := by
      apply Matrix.ext; unfold tripleCharges sourceA1915 sourceB1915 sourceC1915 difference raw27426; decide +kernel
    rw [ha]
    exact (canonical27426 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1915 + difference 2 1) (sourceB1915 + difference 1 2) sourceC1915) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2435) := by
    have ha : (tripleCharges (sourceA1915 + difference 2 1) (sourceB1915 + difference 1 2) sourceC1915) = raw27427 := by
      apply Matrix.ext; unfold tripleCharges sourceA1915 sourceB1915 sourceC1915 difference raw27427; decide +kernel
    rw [ha]
    exact (canonical27427 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1915 + difference 3 1) (sourceB1915 + difference 1 3) sourceC1915) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2435) := by
    have ha : (tripleCharges (sourceA1915 + difference 3 1) (sourceB1915 + difference 1 3) sourceC1915) = raw27428 := by
      apply Matrix.ext; unfold tripleCharges sourceA1915 sourceB1915 sourceC1915 difference raw27428; decide +kernel
    rw [ha]
    exact (canonical27428 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1915 + difference 4 1) (sourceB1915 + difference 1 4) sourceC1915) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2346) := by
    have ha : (tripleCharges (sourceA1915 + difference 4 1) (sourceB1915 + difference 1 4) sourceC1915) = raw27429 := by
      apply Matrix.ext; unfold tripleCharges sourceA1915 sourceB1915 sourceC1915 difference raw27429; decide +kernel
    rw [ha]
    exact (canonical27429 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1915 + difference 5 1) (sourceB1915 + difference 1 5) sourceC1915) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1146) := by
    have ha : (tripleCharges (sourceA1915 + difference 5 1) (sourceB1915 + difference 1 5) sourceC1915) = raw27430 := by
      apply Matrix.ext; unfold tripleCharges sourceA1915 sourceB1915 sourceC1915 difference raw27430; decide +kernel
    rw [ha]
    exact (canonical27430 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1915 + sourceB1915) sourceC1915) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1915 + sourceB1915) sourceC1915) = raw27431 := by
      apply Matrix.ext; unfold doubleCharges sourceA1915 sourceB1915 sourceC1915 raw27431; decide +kernel
    rw [ha]
    exact (canonical27431 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1915 sourceB1915 sourceC1915
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1915, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1916 : Charge := ![0, 3, 0, 0, -1, -2]
def sourceB1916 : Charge := ![3, -2, 0, 0, 0, -1]
def sourceC1916 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceForm1916 : Integer.Sparse Master := [(Sum.inr 1951, 1), (Sum.inr 2267, 1), (Sum.inr 2837, 2), (Sum.inr 2842, 1), (Sum.inr 3486, 1), (Sum.inr 4081, -1)]

theorem sourceEq1916 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1916 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1916 + difference 0 0) (sourceB1916 + difference 0 0) sourceC1916) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2267) := by
    have ha : (tripleCharges (sourceA1916 + difference 0 0) (sourceB1916 + difference 0 0) sourceC1916) = raw27414 := by
      apply Matrix.ext; unfold tripleCharges sourceA1916 sourceB1916 sourceC1916 difference raw27414; decide +kernel
    rw [ha]
    exact (canonical27414 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1916 + difference 0 1) (sourceB1916 + difference 1 0) sourceC1916) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3486) := by
    have ha : (tripleCharges (sourceA1916 + difference 0 1) (sourceB1916 + difference 1 0) sourceC1916) = raw27411 := by
      apply Matrix.ext; unfold tripleCharges sourceA1916 sourceB1916 sourceC1916 difference raw27411; decide +kernel
    rw [ha]
    exact (canonical27411 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1916 + difference 0 2) (sourceB1916 + difference 2 0) sourceC1916) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2837) := by
    have ha : (tripleCharges (sourceA1916 + difference 0 2) (sourceB1916 + difference 2 0) sourceC1916) = raw27432 := by
      apply Matrix.ext; unfold tripleCharges sourceA1916 sourceB1916 sourceC1916 difference raw27432; decide +kernel
    rw [ha]
    exact (canonical27432 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1916 + difference 0 3) (sourceB1916 + difference 3 0) sourceC1916) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2837) := by
    have ha : (tripleCharges (sourceA1916 + difference 0 3) (sourceB1916 + difference 3 0) sourceC1916) = raw27433 := by
      apply Matrix.ext; unfold tripleCharges sourceA1916 sourceB1916 sourceC1916 difference raw27433; decide +kernel
    rw [ha]
    exact (canonical27433 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1916 + difference 0 4) (sourceB1916 + difference 4 0) sourceC1916) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2842) := by
    have ha : (tripleCharges (sourceA1916 + difference 0 4) (sourceB1916 + difference 4 0) sourceC1916) = raw27434 := by
      apply Matrix.ext; unfold tripleCharges sourceA1916 sourceB1916 sourceC1916 difference raw27434; decide +kernel
    rw [ha]
    exact (canonical27434 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1916 + difference 0 5) (sourceB1916 + difference 5 0) sourceC1916) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1951) := by
    have ha : (tripleCharges (sourceA1916 + difference 0 5) (sourceB1916 + difference 5 0) sourceC1916) = raw27435 := by
      apply Matrix.ext; unfold tripleCharges sourceA1916 sourceB1916 sourceC1916 difference raw27435; decide +kernel
    rw [ha]
    exact (canonical27435 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1916 + sourceB1916) sourceC1916) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1916 + sourceB1916) sourceC1916) = raw27319 := by
      apply Matrix.ext; unfold doubleCharges sourceA1916 sourceB1916 sourceC1916 raw27319; decide +kernel
    rw [ha]
    exact (canonical27319 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1916 sourceB1916 sourceC1916
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1916, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1917 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB1917 : Charge := ![1, 0, 0, 2, -1, -2]
def sourceC1917 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceForm1917 : Integer.Sparse Master := [(Sum.inr 1132, 1), (Sum.inr 2335, 1), (Sum.inr 2426, 1), (Sum.inr 2495, 1), (Sum.inr 2512, 1), (Sum.inr 2519, 1), (Sum.inr 4092, -1)]

theorem sourceEq1917 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1917 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1917 + difference 3 0) (sourceB1917 + difference 0 3) sourceC1917) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1132) := by
    have ha : (tripleCharges (sourceA1917 + difference 3 0) (sourceB1917 + difference 0 3) sourceC1917) = raw27436 := by
      apply Matrix.ext; unfold tripleCharges sourceA1917 sourceB1917 sourceC1917 difference raw27436; decide +kernel
    rw [ha]
    exact (canonical27436 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1917 + difference 3 1) (sourceB1917 + difference 1 3) sourceC1917) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2335) := by
    have ha : (tripleCharges (sourceA1917 + difference 3 1) (sourceB1917 + difference 1 3) sourceC1917) = raw27437 := by
      apply Matrix.ext; unfold tripleCharges sourceA1917 sourceB1917 sourceC1917 difference raw27437; decide +kernel
    rw [ha]
    exact (canonical27437 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1917 + difference 3 2) (sourceB1917 + difference 2 3) sourceC1917) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2426) := by
    have ha : (tripleCharges (sourceA1917 + difference 3 2) (sourceB1917 + difference 2 3) sourceC1917) = raw27438 := by
      apply Matrix.ext; unfold tripleCharges sourceA1917 sourceB1917 sourceC1917 difference raw27438; decide +kernel
    rw [ha]
    exact (canonical27438 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1917 + difference 3 3) (sourceB1917 + difference 3 3) sourceC1917) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2495) := by
    have ha : (tripleCharges (sourceA1917 + difference 3 3) (sourceB1917 + difference 3 3) sourceC1917) = raw6566 := by
      apply Matrix.ext; unfold tripleCharges sourceA1917 sourceB1917 sourceC1917 difference raw6566; decide +kernel
    rw [ha]
    exact (canonical6566 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1917 + difference 3 4) (sourceB1917 + difference 4 3) sourceC1917) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2519) := by
    have ha : (tripleCharges (sourceA1917 + difference 3 4) (sourceB1917 + difference 4 3) sourceC1917) = raw27439 := by
      apply Matrix.ext; unfold tripleCharges sourceA1917 sourceB1917 sourceC1917 difference raw27439; decide +kernel
    rw [ha]
    exact (canonical27439 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1917 + difference 3 5) (sourceB1917 + difference 5 3) sourceC1917) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2512) := by
    have ha : (tripleCharges (sourceA1917 + difference 3 5) (sourceB1917 + difference 5 3) sourceC1917) = raw6564 := by
      apply Matrix.ext; unfold tripleCharges sourceA1917 sourceB1917 sourceC1917 difference raw6564; decide +kernel
    rw [ha]
    exact (canonical6564 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1917 + sourceB1917) sourceC1917) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1917 + sourceB1917) sourceC1917) = raw6553 := by
      apply Matrix.ext; unfold doubleCharges sourceA1917 sourceB1917 sourceC1917 raw6553; decide +kernel
    rw [ha]
    exact (canonical6553 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1917 sourceB1917 sourceC1917
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1917, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1918 : Charge := ![1, 0, 0, 2, -1, -2]
def sourceB1918 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC1918 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceForm1918 : Integer.Sparse Master := [(Sum.inr 1917, 1), (Sum.inr 3343, 1), (Sum.inr 3368, 1), (Sum.inr 3385, 1), (Sum.inr 3468, 1), (Sum.inr 3472, 1), (Sum.inr 4081, -1)]

theorem sourceEq1918 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1918 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1918 + difference 0 0) (sourceB1918 + difference 0 0) sourceC1918) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3472) := by
    have ha : (tripleCharges (sourceA1918 + difference 0 0) (sourceB1918 + difference 0 0) sourceC1918) = raw27357 := by
      apply Matrix.ext; unfold tripleCharges sourceA1918 sourceB1918 sourceC1918 difference raw27357; decide +kernel
    rw [ha]
    exact (canonical27357 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1918 + difference 0 1) (sourceB1918 + difference 1 0) sourceC1918) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3385) := by
    have ha : (tripleCharges (sourceA1918 + difference 0 1) (sourceB1918 + difference 1 0) sourceC1918) = raw27440 := by
      apply Matrix.ext; unfold tripleCharges sourceA1918 sourceB1918 sourceC1918 difference raw27440; decide +kernel
    rw [ha]
    exact (canonical27440 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1918 + difference 0 2) (sourceB1918 + difference 2 0) sourceC1918) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3368) := by
    have ha : (tripleCharges (sourceA1918 + difference 0 2) (sourceB1918 + difference 2 0) sourceC1918) = raw27441 := by
      apply Matrix.ext; unfold tripleCharges sourceA1918 sourceB1918 sourceC1918 difference raw27441; decide +kernel
    rw [ha]
    exact (canonical27441 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1918 + difference 0 3) (sourceB1918 + difference 3 0) sourceC1918) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3468) := by
    have ha : (tripleCharges (sourceA1918 + difference 0 3) (sourceB1918 + difference 3 0) sourceC1918) = raw27442 := by
      apply Matrix.ext; unfold tripleCharges sourceA1918 sourceB1918 sourceC1918 difference raw27442; decide +kernel
    rw [ha]
    exact (canonical27442 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1918 + difference 0 4) (sourceB1918 + difference 4 0) sourceC1918) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3343) := by
    have ha : (tripleCharges (sourceA1918 + difference 0 4) (sourceB1918 + difference 4 0) sourceC1918) = raw27443 := by
      apply Matrix.ext; unfold tripleCharges sourceA1918 sourceB1918 sourceC1918 difference raw27443; decide +kernel
    rw [ha]
    exact (canonical27443 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1918 + difference 0 5) (sourceB1918 + difference 5 0) sourceC1918) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1917) := by
    have ha : (tripleCharges (sourceA1918 + difference 0 5) (sourceB1918 + difference 5 0) sourceC1918) = raw27444 := by
      apply Matrix.ext; unfold tripleCharges sourceA1918 sourceB1918 sourceC1918 difference raw27444; decide +kernel
    rw [ha]
    exact (canonical27444 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1918 + sourceB1918) sourceC1918) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1918 + sourceB1918) sourceC1918) = raw27319 := by
      apply Matrix.ext; unfold doubleCharges sourceA1918 sourceB1918 sourceC1918 raw27319; decide +kernel
    rw [ha]
    exact (canonical27319 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1918 sourceB1918 sourceC1918
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1918, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1919 : Charge := ![1, 0, 0, 2, -1, -2]
def sourceB1919 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC1919 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceForm1919 : Integer.Sparse Master := [(Sum.inr 3466, 1), (Sum.inr 3468, 2), (Sum.inr 3472, 1), (Sum.inr 3481, 2), (Sum.inr 4081, -1)]

theorem sourceEq1919 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1919 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1919 + difference 0 3) (sourceB1919 + difference 3 0) sourceC1919) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3468) := by
    have ha : (tripleCharges (sourceA1919 + difference 0 3) (sourceB1919 + difference 3 0) sourceC1919) = raw27442 := by
      apply Matrix.ext; unfold tripleCharges sourceA1919 sourceB1919 sourceC1919 difference raw27442; decide +kernel
    rw [ha]
    exact (canonical27442 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1919 + difference 1 3) (sourceB1919 + difference 3 1) sourceC1919) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3481) := by
    have ha : (tripleCharges (sourceA1919 + difference 1 3) (sourceB1919 + difference 3 1) sourceC1919) = raw27359 := by
      apply Matrix.ext; unfold tripleCharges sourceA1919 sourceB1919 sourceC1919 difference raw27359; decide +kernel
    rw [ha]
    exact (canonical27359 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1919 + difference 2 3) (sourceB1919 + difference 3 2) sourceC1919) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3466) := by
    have ha : (tripleCharges (sourceA1919 + difference 2 3) (sourceB1919 + difference 3 2) sourceC1919) = raw27378 := by
      apply Matrix.ext; unfold tripleCharges sourceA1919 sourceB1919 sourceC1919 difference raw27378; decide +kernel
    rw [ha]
    exact (canonical27378 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1919 + difference 3 3) (sourceB1919 + difference 3 3) sourceC1919) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3472) := by
    have ha : (tripleCharges (sourceA1919 + difference 3 3) (sourceB1919 + difference 3 3) sourceC1919) = raw27357 := by
      apply Matrix.ext; unfold tripleCharges sourceA1919 sourceB1919 sourceC1919 difference raw27357; decide +kernel
    rw [ha]
    exact (canonical27357 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1919 + difference 4 3) (sourceB1919 + difference 3 4) sourceC1919) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3481) := by
    have ha : (tripleCharges (sourceA1919 + difference 4 3) (sourceB1919 + difference 3 4) sourceC1919) = raw27445 := by
      apply Matrix.ext; unfold tripleCharges sourceA1919 sourceB1919 sourceC1919 difference raw27445; decide +kernel
    rw [ha]
    exact (canonical27445 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1919 + difference 5 3) (sourceB1919 + difference 3 5) sourceC1919) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3468) := by
    have ha : (tripleCharges (sourceA1919 + difference 5 3) (sourceB1919 + difference 3 5) sourceC1919) = raw27446 := by
      apply Matrix.ext; unfold tripleCharges sourceA1919 sourceB1919 sourceC1919 difference raw27446; decide +kernel
    rw [ha]
    exact (canonical27446 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1919 + sourceB1919) sourceC1919) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1919 + sourceB1919) sourceC1919) = raw27319 := by
      apply Matrix.ext; unfold doubleCharges sourceA1919 sourceB1919 sourceC1919 raw27319; decide +kernel
    rw [ha]
    exact (canonical27319 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1919 sourceB1919 sourceC1919
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1919, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
