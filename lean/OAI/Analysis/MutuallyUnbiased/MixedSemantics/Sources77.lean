import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical86
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical88
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical111
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical117
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical142
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical143
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical155
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical157
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical170
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical200
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical201
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical202
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical203
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical204
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical213
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical228
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical245
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical246
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical251
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical252
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical253
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical256
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical257
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical258
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical259
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical261
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical262
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical263
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical264
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical265
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical266
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical267
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical268

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA2464 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2464 : Charge := ![3, 0, -1, -1, -1, 0]
def sourceC2464 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceForm2464 : Integer.Sparse Master := [(Sum.inr 4199, 1), (Sum.inr 4200, 2), (Sum.inr 4217, 1), (Sum.inr 4252, 1), (Sum.inr 4633, 1), (Sum.inr 4634, 2), (Sum.inr 4648, 1), (Sum.inr 4764, 1), (Sum.inr 4766, 2), (Sum.inr 4798, 2), (Sum.inr 4805, 1), (Sum.inr 4807, 2), (Sum.inr 4810, 2), (Sum.inr 4826, 1), (Sum.inr 4839, 2), (Sum.inr 4864, 1), (Sum.inr 4889, 2), (Sum.inr 5354, 1), (Sum.inr 5417, 1), (Sum.inr 5431, 1), (Sum.inr 5435, 2)]

theorem sourceEq2464 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2464 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2464 + difference 0 1) (sourceB2464 + difference 1 0) sourceC2464) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5354) := by
    have ha : (tripleCharges (sourceA2464 + difference 0 1) (sourceB2464 + difference 1 0) sourceC2464) = raw33845 := by
      apply Matrix.ext; unfold tripleCharges sourceA2464 sourceB2464 sourceC2464 difference raw33845; decide +kernel
    rw [ha]
    exact (canonical33845 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2464 + difference 0 2) (sourceB2464 + difference 2 0) sourceC2464) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5417) := by
    have ha : (tripleCharges (sourceA2464 + difference 0 2) (sourceB2464 + difference 2 0) sourceC2464) = raw33846 := by
      apply Matrix.ext; unfold tripleCharges sourceA2464 sourceB2464 sourceC2464 difference raw33846; decide +kernel
    rw [ha]
    exact (canonical33846 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2464 + difference 0 3) (sourceB2464 + difference 3 0) sourceC2464) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA2464 + difference 0 3) (sourceB2464 + difference 3 0) sourceC2464) = raw11102 := by
      apply Matrix.ext; unfold tripleCharges sourceA2464 sourceB2464 sourceC2464 difference raw11102; decide +kernel
    rw [ha]
    exact (canonical11102 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2464 + difference 0 4) (sourceB2464 + difference 4 0) sourceC2464) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA2464 + difference 0 4) (sourceB2464 + difference 4 0) sourceC2464) = raw33847 := by
      apply Matrix.ext; unfold tripleCharges sourceA2464 sourceB2464 sourceC2464 difference raw33847; decide +kernel
    rw [ha]
    exact (canonical33847 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2464 + difference 0 5) (sourceB2464 + difference 5 0) sourceC2464) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA2464 + difference 0 5) (sourceB2464 + difference 5 0) sourceC2464) = raw33848 := by
      apply Matrix.ext; unfold tripleCharges sourceA2464 sourceB2464 sourceC2464 difference raw33848; decide +kernel
    rw [ha]
    exact (canonical33848 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2464 + difference 1 0) (sourceB2464 + difference 0 1) sourceC2464) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4252) := by
    have ha : (tripleCharges (sourceA2464 + difference 1 0) (sourceB2464 + difference 0 1) sourceC2464) = raw11117 := by
      apply Matrix.ext; unfold tripleCharges sourceA2464 sourceB2464 sourceC2464 difference raw11117; decide +kernel
    rw [ha]
    exact (canonical11117 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2464 + difference 1 2) (sourceB2464 + difference 2 1) sourceC2464) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4805) := by
    have ha : (tripleCharges (sourceA2464 + difference 1 2) (sourceB2464 + difference 2 1) sourceC2464) = raw11119 := by
      apply Matrix.ext; unfold tripleCharges sourceA2464 sourceB2464 sourceC2464 difference raw11119; decide +kernel
    rw [ha]
    exact (canonical11119 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2464 + difference 1 3) (sourceB2464 + difference 3 1) sourceC2464) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA2464 + difference 1 3) (sourceB2464 + difference 3 1) sourceC2464) = raw31384 := by
      apply Matrix.ext; unfold tripleCharges sourceA2464 sourceB2464 sourceC2464 difference raw31384; decide +kernel
    rw [ha]
    exact (canonical31384 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2464 + difference 1 4) (sourceB2464 + difference 4 1) sourceC2464) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA2464 + difference 1 4) (sourceB2464 + difference 4 1) sourceC2464) = raw11120 := by
      apply Matrix.ext; unfold tripleCharges sourceA2464 sourceB2464 sourceC2464 difference raw11120; decide +kernel
    rw [ha]
    exact (canonical11120 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2464 + difference 1 5) (sourceB2464 + difference 5 1) sourceC2464) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4864) := by
    have ha : (tripleCharges (sourceA2464 + difference 1 5) (sourceB2464 + difference 5 1) sourceC2464) = raw11121 := by
      apply Matrix.ext; unfold tripleCharges sourceA2464 sourceB2464 sourceC2464 difference raw11121; decide +kernel
    rw [ha]
    exact (canonical11121 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2464 + difference 2 0) (sourceB2464 + difference 0 2) sourceC2464) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4217) := by
    have ha : (tripleCharges (sourceA2464 + difference 2 0) (sourceB2464 + difference 0 2) sourceC2464) = raw33849 := by
      apply Matrix.ext; unfold tripleCharges sourceA2464 sourceB2464 sourceC2464 difference raw33849; decide +kernel
    rw [ha]
    exact (canonical33849 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2464 + difference 2 1) (sourceB2464 + difference 1 2) sourceC2464) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4648) := by
    have ha : (tripleCharges (sourceA2464 + difference 2 1) (sourceB2464 + difference 1 2) sourceC2464) = raw33850 := by
      apply Matrix.ext; unfold tripleCharges sourceA2464 sourceB2464 sourceC2464 difference raw33850; decide +kernel
    rw [ha]
    exact (canonical33850 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2464 + difference 2 3) (sourceB2464 + difference 3 2) sourceC2464) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4839) := by
    have ha : (tripleCharges (sourceA2464 + difference 2 3) (sourceB2464 + difference 3 2) sourceC2464) = raw11113 := by
      apply Matrix.ext; unfold tripleCharges sourceA2464 sourceB2464 sourceC2464 difference raw11113; decide +kernel
    rw [ha]
    exact (canonical11113 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2464 + difference 2 4) (sourceB2464 + difference 4 2) sourceC2464) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4839) := by
    have ha : (tripleCharges (sourceA2464 + difference 2 4) (sourceB2464 + difference 4 2) sourceC2464) = raw33851 := by
      apply Matrix.ext; unfold tripleCharges sourceA2464 sourceB2464 sourceC2464 difference raw33851; decide +kernel
    rw [ha]
    exact (canonical33851 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2464 + difference 2 5) (sourceB2464 + difference 5 2) sourceC2464) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4826) := by
    have ha : (tripleCharges (sourceA2464 + difference 2 5) (sourceB2464 + difference 5 2) sourceC2464) = raw33852 := by
      apply Matrix.ext; unfold tripleCharges sourceA2464 sourceB2464 sourceC2464 difference raw33852; decide +kernel
    rw [ha]
    exact (canonical33852 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2464 + difference 3 0) (sourceB2464 + difference 0 3) sourceC2464) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4200) := by
    have ha : (tripleCharges (sourceA2464 + difference 3 0) (sourceB2464 + difference 0 3) sourceC2464) = raw33853 := by
      apply Matrix.ext; unfold tripleCharges sourceA2464 sourceB2464 sourceC2464 difference raw33853; decide +kernel
    rw [ha]
    exact (canonical33853 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2464 + difference 3 1) (sourceB2464 + difference 1 3) sourceC2464) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4634) := by
    have ha : (tripleCharges (sourceA2464 + difference 3 1) (sourceB2464 + difference 1 3) sourceC2464) = raw33854 := by
      apply Matrix.ext; unfold tripleCharges sourceA2464 sourceB2464 sourceC2464 difference raw33854; decide +kernel
    rw [ha]
    exact (canonical33854 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2464 + difference 3 2) (sourceB2464 + difference 2 3) sourceC2464) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4766) := by
    have ha : (tripleCharges (sourceA2464 + difference 3 2) (sourceB2464 + difference 2 3) sourceC2464) = raw33855 := by
      apply Matrix.ext; unfold tripleCharges sourceA2464 sourceB2464 sourceC2464 difference raw33855; decide +kernel
    rw [ha]
    exact (canonical33855 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2464 + difference 3 4) (sourceB2464 + difference 4 3) sourceC2464) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4810) := by
    have ha : (tripleCharges (sourceA2464 + difference 3 4) (sourceB2464 + difference 4 3) sourceC2464) = raw33856 := by
      apply Matrix.ext; unfold tripleCharges sourceA2464 sourceB2464 sourceC2464 difference raw33856; decide +kernel
    rw [ha]
    exact (canonical33856 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2464 + difference 3 5) (sourceB2464 + difference 5 3) sourceC2464) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4798) := by
    have ha : (tripleCharges (sourceA2464 + difference 3 5) (sourceB2464 + difference 5 3) sourceC2464) = raw33857 := by
      apply Matrix.ext; unfold tripleCharges sourceA2464 sourceB2464 sourceC2464 difference raw33857; decide +kernel
    rw [ha]
    exact (canonical33857 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2464 + difference 4 0) (sourceB2464 + difference 0 4) sourceC2464) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4200) := by
    have ha : (tripleCharges (sourceA2464 + difference 4 0) (sourceB2464 + difference 0 4) sourceC2464) = raw31389 := by
      apply Matrix.ext; unfold tripleCharges sourceA2464 sourceB2464 sourceC2464 difference raw31389; decide +kernel
    rw [ha]
    exact (canonical31389 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2464 + difference 4 1) (sourceB2464 + difference 1 4) sourceC2464) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4634) := by
    have ha : (tripleCharges (sourceA2464 + difference 4 1) (sourceB2464 + difference 1 4) sourceC2464) = raw31390 := by
      apply Matrix.ext; unfold tripleCharges sourceA2464 sourceB2464 sourceC2464 difference raw31390; decide +kernel
    rw [ha]
    exact (canonical31390 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2464 + difference 4 2) (sourceB2464 + difference 2 4) sourceC2464) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4766) := by
    have ha : (tripleCharges (sourceA2464 + difference 4 2) (sourceB2464 + difference 2 4) sourceC2464) = raw31391 := by
      apply Matrix.ext; unfold tripleCharges sourceA2464 sourceB2464 sourceC2464 difference raw31391; decide +kernel
    rw [ha]
    exact (canonical31391 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2464 + difference 4 3) (sourceB2464 + difference 3 4) sourceC2464) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4810) := by
    have ha : (tripleCharges (sourceA2464 + difference 4 3) (sourceB2464 + difference 3 4) sourceC2464) = raw11123 := by
      apply Matrix.ext; unfold tripleCharges sourceA2464 sourceB2464 sourceC2464 difference raw11123; decide +kernel
    rw [ha]
    exact (canonical11123 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2464 + difference 4 5) (sourceB2464 + difference 5 4) sourceC2464) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4798) := by
    have ha : (tripleCharges (sourceA2464 + difference 4 5) (sourceB2464 + difference 5 4) sourceC2464) = raw31392 := by
      apply Matrix.ext; unfold tripleCharges sourceA2464 sourceB2464 sourceC2464 difference raw31392; decide +kernel
    rw [ha]
    exact (canonical31392 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2464 + difference 5 0) (sourceB2464 + difference 0 5) sourceC2464) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4199) := by
    have ha : (tripleCharges (sourceA2464 + difference 5 0) (sourceB2464 + difference 0 5) sourceC2464) = raw33858 := by
      apply Matrix.ext; unfold tripleCharges sourceA2464 sourceB2464 sourceC2464 difference raw33858; decide +kernel
    rw [ha]
    exact (canonical33858 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2464 + difference 5 1) (sourceB2464 + difference 1 5) sourceC2464) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4633) := by
    have ha : (tripleCharges (sourceA2464 + difference 5 1) (sourceB2464 + difference 1 5) sourceC2464) = raw33859 := by
      apply Matrix.ext; unfold tripleCharges sourceA2464 sourceB2464 sourceC2464 difference raw33859; decide +kernel
    rw [ha]
    exact (canonical33859 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2464 + difference 5 2) (sourceB2464 + difference 2 5) sourceC2464) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4764) := by
    have ha : (tripleCharges (sourceA2464 + difference 5 2) (sourceB2464 + difference 2 5) sourceC2464) = raw33860 := by
      apply Matrix.ext; unfold tripleCharges sourceA2464 sourceB2464 sourceC2464 difference raw33860; decide +kernel
    rw [ha]
    exact (canonical33860 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2464 + difference 5 3) (sourceB2464 + difference 3 5) sourceC2464) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA2464 + difference 5 3) (sourceB2464 + difference 3 5) sourceC2464) = raw11128 := by
      apply Matrix.ext; unfold tripleCharges sourceA2464 sourceB2464 sourceC2464 difference raw11128; decide +kernel
    rw [ha]
    exact (canonical11128 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2464 + difference 5 4) (sourceB2464 + difference 4 5) sourceC2464) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA2464 + difference 5 4) (sourceB2464 + difference 4 5) sourceC2464) = raw33861 := by
      apply Matrix.ext; unfold tripleCharges sourceA2464 sourceB2464 sourceC2464 difference raw33861; decide +kernel
    rw [ha]
    exact (canonical33861 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2464 sourceB2464 sourceC2464
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2464, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2465 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceB2465 : Charge := ![3, 0, -1, -1, -1, 0]
def sourceC2465 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceForm2465 : Integer.Sparse Master := [(Sum.inr 4407, 2), (Sum.inr 4409, 1), (Sum.inr 4417, 1), (Sum.inr 4469, 1), (Sum.inr 4739, 1), (Sum.inr 4740, 2), (Sum.inr 4746, 1), (Sum.inr 4802, 2), (Sum.inr 4803, 2), (Sum.inr 4806, 2), (Sum.inr 4816, 2), (Sum.inr 4818, 1), (Sum.inr 4838, 1), (Sum.inr 4839, 2), (Sum.inr 4852, 2), (Sum.inr 4854, 1), (Sum.inr 4869, 1), (Sum.inr 5076, 1), (Sum.inr 5149, 2), (Sum.inr 5150, 1), (Sum.inr 5172, 1)]

theorem sourceEq2465 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2465 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2465 + difference 0 1) (sourceB2465 + difference 1 0) sourceC2465) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5076) := by
    have ha : (tripleCharges (sourceA2465 + difference 0 1) (sourceB2465 + difference 1 0) sourceC2465) = raw32236 := by
      apply Matrix.ext; unfold tripleCharges sourceA2465 sourceB2465 sourceC2465 difference raw32236; decide +kernel
    rw [ha]
    exact (canonical32236 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2465 + difference 0 2) (sourceB2465 + difference 2 0) sourceC2465) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5172) := by
    have ha : (tripleCharges (sourceA2465 + difference 0 2) (sourceB2465 + difference 2 0) sourceC2465) = raw32487 := by
      apply Matrix.ext; unfold tripleCharges sourceA2465 sourceB2465 sourceC2465 difference raw32487; decide +kernel
    rw [ha]
    exact (canonical32487 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2465 + difference 0 3) (sourceB2465 + difference 3 0) sourceC2465) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5149) := by
    have ha : (tripleCharges (sourceA2465 + difference 0 3) (sourceB2465 + difference 3 0) sourceC2465) = raw32237 := by
      apply Matrix.ext; unfold tripleCharges sourceA2465 sourceB2465 sourceC2465 difference raw32237; decide +kernel
    rw [ha]
    exact (canonical32237 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2465 + difference 0 4) (sourceB2465 + difference 4 0) sourceC2465) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5149) := by
    have ha : (tripleCharges (sourceA2465 + difference 0 4) (sourceB2465 + difference 4 0) sourceC2465) = raw32238 := by
      apply Matrix.ext; unfold tripleCharges sourceA2465 sourceB2465 sourceC2465 difference raw32238; decide +kernel
    rw [ha]
    exact (canonical32238 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2465 + difference 0 5) (sourceB2465 + difference 5 0) sourceC2465) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5150) := by
    have ha : (tripleCharges (sourceA2465 + difference 0 5) (sourceB2465 + difference 5 0) sourceC2465) = raw32239 := by
      apply Matrix.ext; unfold tripleCharges sourceA2465 sourceB2465 sourceC2465 difference raw32239; decide +kernel
    rw [ha]
    exact (canonical32239 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2465 + difference 1 0) (sourceB2465 + difference 0 1) sourceC2465) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4469) := by
    have ha : (tripleCharges (sourceA2465 + difference 1 0) (sourceB2465 + difference 0 1) sourceC2465) = raw33555 := by
      apply Matrix.ext; unfold tripleCharges sourceA2465 sourceB2465 sourceC2465 difference raw33555; decide +kernel
    rw [ha]
    exact (canonical33555 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2465 + difference 1 2) (sourceB2465 + difference 2 1) sourceC2465) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4869) := by
    have ha : (tripleCharges (sourceA2465 + difference 1 2) (sourceB2465 + difference 2 1) sourceC2465) = raw32230 := by
      apply Matrix.ext; unfold tripleCharges sourceA2465 sourceB2465 sourceC2465 difference raw32230; decide +kernel
    rw [ha]
    exact (canonical32230 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2465 + difference 1 3) (sourceB2465 + difference 3 1) sourceC2465) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4852) := by
    have ha : (tripleCharges (sourceA2465 + difference 1 3) (sourceB2465 + difference 3 1) sourceC2465) = raw32480 := by
      apply Matrix.ext; unfold tripleCharges sourceA2465 sourceB2465 sourceC2465 difference raw32480; decide +kernel
    rw [ha]
    exact (canonical32480 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2465 + difference 1 4) (sourceB2465 + difference 4 1) sourceC2465) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4852) := by
    have ha : (tripleCharges (sourceA2465 + difference 1 4) (sourceB2465 + difference 4 1) sourceC2465) = raw33556 := by
      apply Matrix.ext; unfold tripleCharges sourceA2465 sourceB2465 sourceC2465 difference raw33556; decide +kernel
    rw [ha]
    exact (canonical33556 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2465 + difference 1 5) (sourceB2465 + difference 5 1) sourceC2465) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4854) := by
    have ha : (tripleCharges (sourceA2465 + difference 1 5) (sourceB2465 + difference 5 1) sourceC2465) = raw33557 := by
      apply Matrix.ext; unfold tripleCharges sourceA2465 sourceB2465 sourceC2465 difference raw33557; decide +kernel
    rw [ha]
    exact (canonical33557 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2465 + difference 2 0) (sourceB2465 + difference 0 2) sourceC2465) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4409) := by
    have ha : (tripleCharges (sourceA2465 + difference 2 0) (sourceB2465 + difference 0 2) sourceC2465) = raw33862 := by
      apply Matrix.ext; unfold tripleCharges sourceA2465 sourceB2465 sourceC2465 difference raw33862; decide +kernel
    rw [ha]
    exact (canonical33862 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2465 + difference 2 1) (sourceB2465 + difference 1 2) sourceC2465) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4746) := by
    have ha : (tripleCharges (sourceA2465 + difference 2 1) (sourceB2465 + difference 1 2) sourceC2465) = raw33863 := by
      apply Matrix.ext; unfold tripleCharges sourceA2465 sourceB2465 sourceC2465 difference raw33863; decide +kernel
    rw [ha]
    exact (canonical33863 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2465 + difference 2 3) (sourceB2465 + difference 3 2) sourceC2465) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4816) := by
    have ha : (tripleCharges (sourceA2465 + difference 2 3) (sourceB2465 + difference 3 2) sourceC2465) = raw32483 := by
      apply Matrix.ext; unfold tripleCharges sourceA2465 sourceB2465 sourceC2465 difference raw32483; decide +kernel
    rw [ha]
    exact (canonical32483 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2465 + difference 2 4) (sourceB2465 + difference 4 2) sourceC2465) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4816) := by
    have ha : (tripleCharges (sourceA2465 + difference 2 4) (sourceB2465 + difference 4 2) sourceC2465) = raw33864 := by
      apply Matrix.ext; unfold tripleCharges sourceA2465 sourceB2465 sourceC2465 difference raw33864; decide +kernel
    rw [ha]
    exact (canonical33864 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2465 + difference 2 5) (sourceB2465 + difference 5 2) sourceC2465) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4818) := by
    have ha : (tripleCharges (sourceA2465 + difference 2 5) (sourceB2465 + difference 5 2) sourceC2465) = raw33865 := by
      apply Matrix.ext; unfold tripleCharges sourceA2465 sourceB2465 sourceC2465 difference raw33865; decide +kernel
    rw [ha]
    exact (canonical33865 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2465 + difference 3 0) (sourceB2465 + difference 0 3) sourceC2465) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4407) := by
    have ha : (tripleCharges (sourceA2465 + difference 3 0) (sourceB2465 + difference 0 3) sourceC2465) = raw33866 := by
      apply Matrix.ext; unfold tripleCharges sourceA2465 sourceB2465 sourceC2465 difference raw33866; decide +kernel
    rw [ha]
    exact (canonical33866 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2465 + difference 3 1) (sourceB2465 + difference 1 3) sourceC2465) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4740) := by
    have ha : (tripleCharges (sourceA2465 + difference 3 1) (sourceB2465 + difference 1 3) sourceC2465) = raw33867 := by
      apply Matrix.ext; unfold tripleCharges sourceA2465 sourceB2465 sourceC2465 difference raw33867; decide +kernel
    rw [ha]
    exact (canonical33867 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2465 + difference 3 2) (sourceB2465 + difference 2 3) sourceC2465) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4839) := by
    have ha : (tripleCharges (sourceA2465 + difference 3 2) (sourceB2465 + difference 2 3) sourceC2465) = raw32240 := by
      apply Matrix.ext; unfold tripleCharges sourceA2465 sourceB2465 sourceC2465 difference raw32240; decide +kernel
    rw [ha]
    exact (canonical32240 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2465 + difference 3 4) (sourceB2465 + difference 4 3) sourceC2465) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4803) := by
    have ha : (tripleCharges (sourceA2465 + difference 3 4) (sourceB2465 + difference 4 3) sourceC2465) = raw33868 := by
      apply Matrix.ext; unfold tripleCharges sourceA2465 sourceB2465 sourceC2465 difference raw33868; decide +kernel
    rw [ha]
    exact (canonical33868 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2465 + difference 3 5) (sourceB2465 + difference 5 3) sourceC2465) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4806) := by
    have ha : (tripleCharges (sourceA2465 + difference 3 5) (sourceB2465 + difference 5 3) sourceC2465) = raw33869 := by
      apply Matrix.ext; unfold tripleCharges sourceA2465 sourceB2465 sourceC2465 difference raw33869; decide +kernel
    rw [ha]
    exact (canonical33869 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2465 + difference 4 0) (sourceB2465 + difference 0 4) sourceC2465) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4407) := by
    have ha : (tripleCharges (sourceA2465 + difference 4 0) (sourceB2465 + difference 0 4) sourceC2465) = raw33870 := by
      apply Matrix.ext; unfold tripleCharges sourceA2465 sourceB2465 sourceC2465 difference raw33870; decide +kernel
    rw [ha]
    exact (canonical33870 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2465 + difference 4 1) (sourceB2465 + difference 1 4) sourceC2465) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4740) := by
    have ha : (tripleCharges (sourceA2465 + difference 4 1) (sourceB2465 + difference 1 4) sourceC2465) = raw33871 := by
      apply Matrix.ext; unfold tripleCharges sourceA2465 sourceB2465 sourceC2465 difference raw33871; decide +kernel
    rw [ha]
    exact (canonical33871 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2465 + difference 4 2) (sourceB2465 + difference 2 4) sourceC2465) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4839) := by
    have ha : (tripleCharges (sourceA2465 + difference 4 2) (sourceB2465 + difference 2 4) sourceC2465) = raw32245 := by
      apply Matrix.ext; unfold tripleCharges sourceA2465 sourceB2465 sourceC2465 difference raw32245; decide +kernel
    rw [ha]
    exact (canonical32245 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2465 + difference 4 3) (sourceB2465 + difference 3 4) sourceC2465) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4803) := by
    have ha : (tripleCharges (sourceA2465 + difference 4 3) (sourceB2465 + difference 3 4) sourceC2465) = raw32488 := by
      apply Matrix.ext; unfold tripleCharges sourceA2465 sourceB2465 sourceC2465 difference raw32488; decide +kernel
    rw [ha]
    exact (canonical32488 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2465 + difference 4 5) (sourceB2465 + difference 5 4) sourceC2465) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4806) := by
    have ha : (tripleCharges (sourceA2465 + difference 4 5) (sourceB2465 + difference 5 4) sourceC2465) = raw33872 := by
      apply Matrix.ext; unfold tripleCharges sourceA2465 sourceB2465 sourceC2465 difference raw33872; decide +kernel
    rw [ha]
    exact (canonical33872 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2465 + difference 5 0) (sourceB2465 + difference 0 5) sourceC2465) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4417) := by
    have ha : (tripleCharges (sourceA2465 + difference 5 0) (sourceB2465 + difference 0 5) sourceC2465) = raw33873 := by
      apply Matrix.ext; unfold tripleCharges sourceA2465 sourceB2465 sourceC2465 difference raw33873; decide +kernel
    rw [ha]
    exact (canonical33873 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2465 + difference 5 1) (sourceB2465 + difference 1 5) sourceC2465) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4739) := by
    have ha : (tripleCharges (sourceA2465 + difference 5 1) (sourceB2465 + difference 1 5) sourceC2465) = raw33145 := by
      apply Matrix.ext; unfold tripleCharges sourceA2465 sourceB2465 sourceC2465 difference raw33145; decide +kernel
    rw [ha]
    exact (canonical33145 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2465 + difference 5 2) (sourceB2465 + difference 2 5) sourceC2465) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4838) := by
    have ha : (tripleCharges (sourceA2465 + difference 5 2) (sourceB2465 + difference 2 5) sourceC2465) = raw32250 := by
      apply Matrix.ext; unfold tripleCharges sourceA2465 sourceB2465 sourceC2465 difference raw32250; decide +kernel
    rw [ha]
    exact (canonical32250 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2465 + difference 5 3) (sourceB2465 + difference 3 5) sourceC2465) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA2465 + difference 5 3) (sourceB2465 + difference 3 5) sourceC2465) = raw32330 := by
      apply Matrix.ext; unfold tripleCharges sourceA2465 sourceB2465 sourceC2465 difference raw32330; decide +kernel
    rw [ha]
    exact (canonical32330 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2465 + difference 5 4) (sourceB2465 + difference 4 5) sourceC2465) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA2465 + difference 5 4) (sourceB2465 + difference 4 5) sourceC2465) = raw32327 := by
      apply Matrix.ext; unfold tripleCharges sourceA2465 sourceB2465 sourceC2465 difference raw32327; decide +kernel
    rw [ha]
    exact (canonical32327 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2465 sourceB2465 sourceC2465
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2465, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2466 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2466 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC2466 : Charge := ![3, 0, -1, -1, 0, -1]
def sourceForm2466 : Integer.Sparse Master := [(Sum.inr 4327, 1), (Sum.inr 4329, 1), (Sum.inr 4332, 1), (Sum.inr 4344, 1), (Sum.inr 4458, 1), (Sum.inr 4664, 1), (Sum.inr 4666, 1), (Sum.inr 4668, 1), (Sum.inr 4679, 1), (Sum.inr 4772, 1), (Sum.inr 4774, 1), (Sum.inr 4775, 1), (Sum.inr 4792, 1), (Sum.inr 4795, 1), (Sum.inr 4802, 2), (Sum.inr 4805, 1), (Sum.inr 4807, 1), (Sum.inr 4811, 1), (Sum.inr 4833, 1), (Sum.inr 4838, 1), (Sum.inr 4866, 1), (Sum.inr 4888, 1), (Sum.inr 4893, 1), (Sum.inr 4895, 1), (Sum.inr 5226, 1), (Sum.inr 5255, 1), (Sum.inr 5256, 1), (Sum.inr 5257, 1), (Sum.inr 5271, 1)]

theorem sourceEq2466 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2466 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2466 + difference 0 1) (sourceB2466 + difference 1 0) sourceC2466) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5226) := by
    have ha : (tripleCharges (sourceA2466 + difference 0 1) (sourceB2466 + difference 1 0) sourceC2466) = raw33874 := by
      apply Matrix.ext; unfold tripleCharges sourceA2466 sourceB2466 sourceC2466 difference raw33874; decide +kernel
    rw [ha]
    exact (canonical33874 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2466 + difference 0 2) (sourceB2466 + difference 2 0) sourceC2466) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5255) := by
    have ha : (tripleCharges (sourceA2466 + difference 0 2) (sourceB2466 + difference 2 0) sourceC2466) = raw33875 := by
      apply Matrix.ext; unfold tripleCharges sourceA2466 sourceB2466 sourceC2466 difference raw33875; decide +kernel
    rw [ha]
    exact (canonical33875 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2466 + difference 0 3) (sourceB2466 + difference 3 0) sourceC2466) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5256) := by
    have ha : (tripleCharges (sourceA2466 + difference 0 3) (sourceB2466 + difference 3 0) sourceC2466) = raw33876 := by
      apply Matrix.ext; unfold tripleCharges sourceA2466 sourceB2466 sourceC2466 difference raw33876; decide +kernel
    rw [ha]
    exact (canonical33876 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2466 + difference 0 4) (sourceB2466 + difference 4 0) sourceC2466) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA2466 + difference 0 4) (sourceB2466 + difference 4 0) sourceC2466) = raw33877 := by
      apply Matrix.ext; unfold tripleCharges sourceA2466 sourceB2466 sourceC2466 difference raw33877; decide +kernel
    rw [ha]
    exact (canonical33877 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2466 + difference 0 5) (sourceB2466 + difference 5 0) sourceC2466) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA2466 + difference 0 5) (sourceB2466 + difference 5 0) sourceC2466) = raw33878 := by
      apply Matrix.ext; unfold tripleCharges sourceA2466 sourceB2466 sourceC2466 difference raw33878; decide +kernel
    rw [ha]
    exact (canonical33878 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2466 + difference 1 0) (sourceB2466 + difference 0 1) sourceC2466) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA2466 + difference 1 0) (sourceB2466 + difference 0 1) sourceC2466) = raw33879 := by
      apply Matrix.ext; unfold tripleCharges sourceA2466 sourceB2466 sourceC2466 difference raw33879; decide +kernel
    rw [ha]
    exact (canonical33879 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2466 + difference 1 2) (sourceB2466 + difference 2 1) sourceC2466) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA2466 + difference 1 2) (sourceB2466 + difference 2 1) sourceC2466) = raw33880 := by
      apply Matrix.ext; unfold tripleCharges sourceA2466 sourceB2466 sourceC2466 difference raw33880; decide +kernel
    rw [ha]
    exact (canonical33880 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2466 + difference 1 3) (sourceB2466 + difference 3 1) sourceC2466) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA2466 + difference 1 3) (sourceB2466 + difference 3 1) sourceC2466) = raw33881 := by
      apply Matrix.ext; unfold tripleCharges sourceA2466 sourceB2466 sourceC2466 difference raw33881; decide +kernel
    rw [ha]
    exact (canonical33881 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2466 + difference 1 4) (sourceB2466 + difference 4 1) sourceC2466) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA2466 + difference 1 4) (sourceB2466 + difference 4 1) sourceC2466) = raw33882 := by
      apply Matrix.ext; unfold tripleCharges sourceA2466 sourceB2466 sourceC2466 difference raw33882; decide +kernel
    rw [ha]
    exact (canonical33882 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2466 + difference 1 5) (sourceB2466 + difference 5 1) sourceC2466) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4893) := by
    have ha : (tripleCharges (sourceA2466 + difference 1 5) (sourceB2466 + difference 5 1) sourceC2466) = raw33883 := by
      apply Matrix.ext; unfold tripleCharges sourceA2466 sourceB2466 sourceC2466 difference raw33883; decide +kernel
    rw [ha]
    exact (canonical33883 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2466 + difference 2 0) (sourceB2466 + difference 0 2) sourceC2466) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4344) := by
    have ha : (tripleCharges (sourceA2466 + difference 2 0) (sourceB2466 + difference 0 2) sourceC2466) = raw33884 := by
      apply Matrix.ext; unfold tripleCharges sourceA2466 sourceB2466 sourceC2466 difference raw33884; decide +kernel
    rw [ha]
    exact (canonical33884 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2466 + difference 2 1) (sourceB2466 + difference 1 2) sourceC2466) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4679) := by
    have ha : (tripleCharges (sourceA2466 + difference 2 1) (sourceB2466 + difference 1 2) sourceC2466) = raw33885 := by
      apply Matrix.ext; unfold tripleCharges sourceA2466 sourceB2466 sourceC2466 difference raw33885; decide +kernel
    rw [ha]
    exact (canonical33885 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2466 + difference 2 3) (sourceB2466 + difference 3 2) sourceC2466) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA2466 + difference 2 3) (sourceB2466 + difference 3 2) sourceC2466) = raw33886 := by
      apply Matrix.ext; unfold tripleCharges sourceA2466 sourceB2466 sourceC2466 difference raw33886; decide +kernel
    rw [ha]
    exact (canonical33886 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2466 + difference 2 4) (sourceB2466 + difference 4 2) sourceC2466) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4838) := by
    have ha : (tripleCharges (sourceA2466 + difference 2 4) (sourceB2466 + difference 4 2) sourceC2466) = raw33887 := by
      apply Matrix.ext; unfold tripleCharges sourceA2466 sourceB2466 sourceC2466 difference raw33887; decide +kernel
    rw [ha]
    exact (canonical33887 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2466 + difference 2 5) (sourceB2466 + difference 5 2) sourceC2466) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4833) := by
    have ha : (tripleCharges (sourceA2466 + difference 2 5) (sourceB2466 + difference 5 2) sourceC2466) = raw33888 := by
      apply Matrix.ext; unfold tripleCharges sourceA2466 sourceB2466 sourceC2466 difference raw33888; decide +kernel
    rw [ha]
    exact (canonical33888 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2466 + difference 3 0) (sourceB2466 + difference 0 3) sourceC2466) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4329) := by
    have ha : (tripleCharges (sourceA2466 + difference 3 0) (sourceB2466 + difference 0 3) sourceC2466) = raw33889 := by
      apply Matrix.ext; unfold tripleCharges sourceA2466 sourceB2466 sourceC2466 difference raw33889; decide +kernel
    rw [ha]
    exact (canonical33889 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2466 + difference 3 1) (sourceB2466 + difference 1 3) sourceC2466) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4666) := by
    have ha : (tripleCharges (sourceA2466 + difference 3 1) (sourceB2466 + difference 1 3) sourceC2466) = raw33890 := by
      apply Matrix.ext; unfold tripleCharges sourceA2466 sourceB2466 sourceC2466 difference raw33890; decide +kernel
    rw [ha]
    exact (canonical33890 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2466 + difference 3 2) (sourceB2466 + difference 2 3) sourceC2466) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4774) := by
    have ha : (tripleCharges (sourceA2466 + difference 3 2) (sourceB2466 + difference 2 3) sourceC2466) = raw33891 := by
      apply Matrix.ext; unfold tripleCharges sourceA2466 sourceB2466 sourceC2466 difference raw33891; decide +kernel
    rw [ha]
    exact (canonical33891 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2466 + difference 3 4) (sourceB2466 + difference 4 3) sourceC2466) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4811) := by
    have ha : (tripleCharges (sourceA2466 + difference 3 4) (sourceB2466 + difference 4 3) sourceC2466) = raw33892 := by
      apply Matrix.ext; unfold tripleCharges sourceA2466 sourceB2466 sourceC2466 difference raw33892; decide +kernel
    rw [ha]
    exact (canonical33892 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2466 + difference 3 5) (sourceB2466 + difference 5 3) sourceC2466) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA2466 + difference 3 5) (sourceB2466 + difference 5 3) sourceC2466) = raw33893 := by
      apply Matrix.ext; unfold tripleCharges sourceA2466 sourceB2466 sourceC2466 difference raw33893; decide +kernel
    rw [ha]
    exact (canonical33893 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2466 + difference 4 0) (sourceB2466 + difference 0 4) sourceC2466) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4332) := by
    have ha : (tripleCharges (sourceA2466 + difference 4 0) (sourceB2466 + difference 0 4) sourceC2466) = raw33894 := by
      apply Matrix.ext; unfold tripleCharges sourceA2466 sourceB2466 sourceC2466 difference raw33894; decide +kernel
    rw [ha]
    exact (canonical33894 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2466 + difference 4 1) (sourceB2466 + difference 1 4) sourceC2466) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4668) := by
    have ha : (tripleCharges (sourceA2466 + difference 4 1) (sourceB2466 + difference 1 4) sourceC2466) = raw33895 := by
      apply Matrix.ext; unfold tripleCharges sourceA2466 sourceB2466 sourceC2466 difference raw33895; decide +kernel
    rw [ha]
    exact (canonical33895 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2466 + difference 4 2) (sourceB2466 + difference 2 4) sourceC2466) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4775) := by
    have ha : (tripleCharges (sourceA2466 + difference 4 2) (sourceB2466 + difference 2 4) sourceC2466) = raw33896 := by
      apply Matrix.ext; unfold tripleCharges sourceA2466 sourceB2466 sourceC2466 difference raw33896; decide +kernel
    rw [ha]
    exact (canonical33896 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2466 + difference 4 3) (sourceB2466 + difference 3 4) sourceC2466) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4795) := by
    have ha : (tripleCharges (sourceA2466 + difference 4 3) (sourceB2466 + difference 3 4) sourceC2466) = raw33897 := by
      apply Matrix.ext; unfold tripleCharges sourceA2466 sourceB2466 sourceC2466 difference raw33897; decide +kernel
    rw [ha]
    exact (canonical33897 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2466 + difference 4 5) (sourceB2466 + difference 5 4) sourceC2466) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4805) := by
    have ha : (tripleCharges (sourceA2466 + difference 4 5) (sourceB2466 + difference 5 4) sourceC2466) = raw33898 := by
      apply Matrix.ext; unfold tripleCharges sourceA2466 sourceB2466 sourceC2466 difference raw33898; decide +kernel
    rw [ha]
    exact (canonical33898 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2466 + difference 5 0) (sourceB2466 + difference 0 5) sourceC2466) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4327) := by
    have ha : (tripleCharges (sourceA2466 + difference 5 0) (sourceB2466 + difference 0 5) sourceC2466) = raw33899 := by
      apply Matrix.ext; unfold tripleCharges sourceA2466 sourceB2466 sourceC2466 difference raw33899; decide +kernel
    rw [ha]
    exact (canonical33899 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2466 + difference 5 1) (sourceB2466 + difference 1 5) sourceC2466) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4664) := by
    have ha : (tripleCharges (sourceA2466 + difference 5 1) (sourceB2466 + difference 1 5) sourceC2466) = raw33900 := by
      apply Matrix.ext; unfold tripleCharges sourceA2466 sourceB2466 sourceC2466 difference raw33900; decide +kernel
    rw [ha]
    exact (canonical33900 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2466 + difference 5 2) (sourceB2466 + difference 2 5) sourceC2466) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4772) := by
    have ha : (tripleCharges (sourceA2466 + difference 5 2) (sourceB2466 + difference 2 5) sourceC2466) = raw33901 := by
      apply Matrix.ext; unfold tripleCharges sourceA2466 sourceB2466 sourceC2466 difference raw33901; decide +kernel
    rw [ha]
    exact (canonical33901 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2466 + difference 5 3) (sourceB2466 + difference 3 5) sourceC2466) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4792) := by
    have ha : (tripleCharges (sourceA2466 + difference 5 3) (sourceB2466 + difference 3 5) sourceC2466) = raw33902 := by
      apply Matrix.ext; unfold tripleCharges sourceA2466 sourceB2466 sourceC2466 difference raw33902; decide +kernel
    rw [ha]
    exact (canonical33902 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2466 + difference 5 4) (sourceB2466 + difference 4 5) sourceC2466) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA2466 + difference 5 4) (sourceB2466 + difference 4 5) sourceC2466) = raw33903 := by
      apply Matrix.ext; unfold tripleCharges sourceA2466 sourceB2466 sourceC2466 difference raw33903; decide +kernel
    rw [ha]
    exact (canonical33903 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2466 sourceB2466 sourceC2466
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2466, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2467 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2467 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC2467 : Charge := ![3, 0, -1, -1, 0, -1]
def sourceForm2467 : Integer.Sparse Master := [(Sum.inr 1327, 1), (Sum.inr 1328, 1), (Sum.inr 1331, 1), (Sum.inr 1339, 1), (Sum.inr 1411, 1), (Sum.inr 2423, 1), (Sum.inr 2430, 1), (Sum.inr 2471, 1), (Sum.inr 2574, 1), (Sum.inr 3084, 1), (Sum.inr 3085, 1), (Sum.inr 3087, 1), (Sum.inr 3091, 1), (Sum.inr 3109, 1), (Sum.inr 3133, 1), (Sum.inr 3135, 1), (Sum.inr 3139, 1), (Sum.inr 3162, 1), (Sum.inr 3164, 1), (Sum.inr 3184, 1), (Sum.inr 3199, 1), (Sum.inr 3203, 1), (Sum.inr 3204, 2), (Sum.inr 3207, 1), (Sum.inr 3212, 1), (Sum.inr 3213, 1), (Sum.inr 3227, 1), (Sum.inr 3228, 1), (Sum.inr 3229, 1)]

theorem sourceEq2467 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2467 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2467 + difference 0 1) (sourceB2467 + difference 1 0) sourceC2467) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3091) := by
    have ha : (tripleCharges (sourceA2467 + difference 0 1) (sourceB2467 + difference 1 0) sourceC2467) = raw33904 := by
      apply Matrix.ext; unfold tripleCharges sourceA2467 sourceB2467 sourceC2467 difference raw33904; decide +kernel
    rw [ha]
    exact (canonical33904 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2467 + difference 0 2) (sourceB2467 + difference 2 0) sourceC2467) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3084) := by
    have ha : (tripleCharges (sourceA2467 + difference 0 2) (sourceB2467 + difference 2 0) sourceC2467) = raw33905 := by
      apply Matrix.ext; unfold tripleCharges sourceA2467 sourceB2467 sourceC2467 difference raw33905; decide +kernel
    rw [ha]
    exact (canonical33905 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2467 + difference 0 3) (sourceB2467 + difference 3 0) sourceC2467) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3085) := by
    have ha : (tripleCharges (sourceA2467 + difference 0 3) (sourceB2467 + difference 3 0) sourceC2467) = raw33906 := by
      apply Matrix.ext; unfold tripleCharges sourceA2467 sourceB2467 sourceC2467 difference raw33906; decide +kernel
    rw [ha]
    exact (canonical33906 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2467 + difference 0 4) (sourceB2467 + difference 4 0) sourceC2467) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3109) := by
    have ha : (tripleCharges (sourceA2467 + difference 0 4) (sourceB2467 + difference 4 0) sourceC2467) = raw33907 := by
      apply Matrix.ext; unfold tripleCharges sourceA2467 sourceB2467 sourceC2467 difference raw33907; decide +kernel
    rw [ha]
    exact (canonical33907 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2467 + difference 0 5) (sourceB2467 + difference 5 0) sourceC2467) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3087) := by
    have ha : (tripleCharges (sourceA2467 + difference 0 5) (sourceB2467 + difference 5 0) sourceC2467) = raw33908 := by
      apply Matrix.ext; unfold tripleCharges sourceA2467 sourceB2467 sourceC2467 difference raw33908; decide +kernel
    rw [ha]
    exact (canonical33908 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2467 + difference 1 0) (sourceB2467 + difference 0 1) sourceC2467) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1411) := by
    have ha : (tripleCharges (sourceA2467 + difference 1 0) (sourceB2467 + difference 0 1) sourceC2467) = raw33909 := by
      apply Matrix.ext; unfold tripleCharges sourceA2467 sourceB2467 sourceC2467 difference raw33909; decide +kernel
    rw [ha]
    exact (canonical33909 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2467 + difference 1 2) (sourceB2467 + difference 2 1) sourceC2467) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3184) := by
    have ha : (tripleCharges (sourceA2467 + difference 1 2) (sourceB2467 + difference 2 1) sourceC2467) = raw33910 := by
      apply Matrix.ext; unfold tripleCharges sourceA2467 sourceB2467 sourceC2467 difference raw33910; decide +kernel
    rw [ha]
    exact (canonical33910 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2467 + difference 1 3) (sourceB2467 + difference 3 1) sourceC2467) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3227) := by
    have ha : (tripleCharges (sourceA2467 + difference 1 3) (sourceB2467 + difference 3 1) sourceC2467) = raw33911 := by
      apply Matrix.ext; unfold tripleCharges sourceA2467 sourceB2467 sourceC2467 difference raw33911; decide +kernel
    rw [ha]
    exact (canonical33911 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2467 + difference 1 4) (sourceB2467 + difference 4 1) sourceC2467) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3229) := by
    have ha : (tripleCharges (sourceA2467 + difference 1 4) (sourceB2467 + difference 4 1) sourceC2467) = raw33912 := by
      apply Matrix.ext; unfold tripleCharges sourceA2467 sourceB2467 sourceC2467 difference raw33912; decide +kernel
    rw [ha]
    exact (canonical33912 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2467 + difference 1 5) (sourceB2467 + difference 5 1) sourceC2467) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3228) := by
    have ha : (tripleCharges (sourceA2467 + difference 1 5) (sourceB2467 + difference 5 1) sourceC2467) = raw33913 := by
      apply Matrix.ext; unfold tripleCharges sourceA2467 sourceB2467 sourceC2467 difference raw33913; decide +kernel
    rw [ha]
    exact (canonical33913 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2467 + difference 2 0) (sourceB2467 + difference 0 2) sourceC2467) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1339) := by
    have ha : (tripleCharges (sourceA2467 + difference 2 0) (sourceB2467 + difference 0 2) sourceC2467) = raw33914 := by
      apply Matrix.ext; unfold tripleCharges sourceA2467 sourceB2467 sourceC2467 difference raw33914; decide +kernel
    rw [ha]
    exact (canonical33914 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2467 + difference 2 1) (sourceB2467 + difference 1 2) sourceC2467) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3139) := by
    have ha : (tripleCharges (sourceA2467 + difference 2 1) (sourceB2467 + difference 1 2) sourceC2467) = raw33915 := by
      apply Matrix.ext; unfold tripleCharges sourceA2467 sourceB2467 sourceC2467 difference raw33915; decide +kernel
    rw [ha]
    exact (canonical33915 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2467 + difference 2 3) (sourceB2467 + difference 3 2) sourceC2467) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3204) := by
    have ha : (tripleCharges (sourceA2467 + difference 2 3) (sourceB2467 + difference 3 2) sourceC2467) = raw33916 := by
      apply Matrix.ext; unfold tripleCharges sourceA2467 sourceB2467 sourceC2467 difference raw33916; decide +kernel
    rw [ha]
    exact (canonical33916 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2467 + difference 2 4) (sourceB2467 + difference 4 2) sourceC2467) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3213) := by
    have ha : (tripleCharges (sourceA2467 + difference 2 4) (sourceB2467 + difference 4 2) sourceC2467) = raw33917 := by
      apply Matrix.ext; unfold tripleCharges sourceA2467 sourceB2467 sourceC2467 difference raw33917; decide +kernel
    rw [ha]
    exact (canonical33917 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2467 + difference 2 5) (sourceB2467 + difference 5 2) sourceC2467) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3212) := by
    have ha : (tripleCharges (sourceA2467 + difference 2 5) (sourceB2467 + difference 5 2) sourceC2467) = raw33918 := by
      apply Matrix.ext; unfold tripleCharges sourceA2467 sourceB2467 sourceC2467 difference raw33918; decide +kernel
    rw [ha]
    exact (canonical33918 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2467 + difference 3 0) (sourceB2467 + difference 0 3) sourceC2467) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1331) := by
    have ha : (tripleCharges (sourceA2467 + difference 3 0) (sourceB2467 + difference 0 3) sourceC2467) = raw33919 := by
      apply Matrix.ext; unfold tripleCharges sourceA2467 sourceB2467 sourceC2467 difference raw33919; decide +kernel
    rw [ha]
    exact (canonical33919 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2467 + difference 3 1) (sourceB2467 + difference 1 3) sourceC2467) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3135) := by
    have ha : (tripleCharges (sourceA2467 + difference 3 1) (sourceB2467 + difference 1 3) sourceC2467) = raw33920 := by
      apply Matrix.ext; unfold tripleCharges sourceA2467 sourceB2467 sourceC2467 difference raw33920; decide +kernel
    rw [ha]
    exact (canonical33920 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2467 + difference 3 2) (sourceB2467 + difference 2 3) sourceC2467) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3164) := by
    have ha : (tripleCharges (sourceA2467 + difference 3 2) (sourceB2467 + difference 2 3) sourceC2467) = raw33921 := by
      apply Matrix.ext; unfold tripleCharges sourceA2467 sourceB2467 sourceC2467 difference raw33921; decide +kernel
    rw [ha]
    exact (canonical33921 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2467 + difference 3 4) (sourceB2467 + difference 4 3) sourceC2467) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3207) := by
    have ha : (tripleCharges (sourceA2467 + difference 3 4) (sourceB2467 + difference 4 3) sourceC2467) = raw33922 := by
      apply Matrix.ext; unfold tripleCharges sourceA2467 sourceB2467 sourceC2467 difference raw33922; decide +kernel
    rw [ha]
    exact (canonical33922 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2467 + difference 3 5) (sourceB2467 + difference 5 3) sourceC2467) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3204) := by
    have ha : (tripleCharges (sourceA2467 + difference 3 5) (sourceB2467 + difference 5 3) sourceC2467) = raw33923 := by
      apply Matrix.ext; unfold tripleCharges sourceA2467 sourceB2467 sourceC2467 difference raw33923; decide +kernel
    rw [ha]
    exact (canonical33923 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2467 + difference 4 0) (sourceB2467 + difference 0 4) sourceC2467) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1328) := by
    have ha : (tripleCharges (sourceA2467 + difference 4 0) (sourceB2467 + difference 0 4) sourceC2467) = raw33924 := by
      apply Matrix.ext; unfold tripleCharges sourceA2467 sourceB2467 sourceC2467 difference raw33924; decide +kernel
    rw [ha]
    exact (canonical33924 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2467 + difference 4 1) (sourceB2467 + difference 1 4) sourceC2467) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3133) := by
    have ha : (tripleCharges (sourceA2467 + difference 4 1) (sourceB2467 + difference 1 4) sourceC2467) = raw33925 := by
      apply Matrix.ext; unfold tripleCharges sourceA2467 sourceB2467 sourceC2467 difference raw33925; decide +kernel
    rw [ha]
    exact (canonical33925 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2467 + difference 4 2) (sourceB2467 + difference 2 4) sourceC2467) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3162) := by
    have ha : (tripleCharges (sourceA2467 + difference 4 2) (sourceB2467 + difference 2 4) sourceC2467) = raw33926 := by
      apply Matrix.ext; unfold tripleCharges sourceA2467 sourceB2467 sourceC2467 difference raw33926; decide +kernel
    rw [ha]
    exact (canonical33926 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2467 + difference 4 3) (sourceB2467 + difference 3 4) sourceC2467) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3199) := by
    have ha : (tripleCharges (sourceA2467 + difference 4 3) (sourceB2467 + difference 3 4) sourceC2467) = raw33927 := by
      apply Matrix.ext; unfold tripleCharges sourceA2467 sourceB2467 sourceC2467 difference raw33927; decide +kernel
    rw [ha]
    exact (canonical33927 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2467 + difference 4 5) (sourceB2467 + difference 5 4) sourceC2467) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3203) := by
    have ha : (tripleCharges (sourceA2467 + difference 4 5) (sourceB2467 + difference 5 4) sourceC2467) = raw33928 := by
      apply Matrix.ext; unfold tripleCharges sourceA2467 sourceB2467 sourceC2467 difference raw33928; decide +kernel
    rw [ha]
    exact (canonical33928 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2467 + difference 5 0) (sourceB2467 + difference 0 5) sourceC2467) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1327) := by
    have ha : (tripleCharges (sourceA2467 + difference 5 0) (sourceB2467 + difference 0 5) sourceC2467) = raw33929 := by
      apply Matrix.ext; unfold tripleCharges sourceA2467 sourceB2467 sourceC2467 difference raw33929; decide +kernel
    rw [ha]
    exact (canonical33929 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2467 + difference 5 1) (sourceB2467 + difference 1 5) sourceC2467) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2423) := by
    have ha : (tripleCharges (sourceA2467 + difference 5 1) (sourceB2467 + difference 1 5) sourceC2467) = raw33930 := by
      apply Matrix.ext; unfold tripleCharges sourceA2467 sourceB2467 sourceC2467 difference raw33930; decide +kernel
    rw [ha]
    exact (canonical33930 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2467 + difference 5 2) (sourceB2467 + difference 2 5) sourceC2467) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2430) := by
    have ha : (tripleCharges (sourceA2467 + difference 5 2) (sourceB2467 + difference 2 5) sourceC2467) = raw33931 := by
      apply Matrix.ext; unfold tripleCharges sourceA2467 sourceB2467 sourceC2467 difference raw33931; decide +kernel
    rw [ha]
    exact (canonical33931 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2467 + difference 5 3) (sourceB2467 + difference 3 5) sourceC2467) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2471) := by
    have ha : (tripleCharges (sourceA2467 + difference 5 3) (sourceB2467 + difference 3 5) sourceC2467) = raw33932 := by
      apply Matrix.ext; unfold tripleCharges sourceA2467 sourceB2467 sourceC2467 difference raw33932; decide +kernel
    rw [ha]
    exact (canonical33932 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2467 + difference 5 4) (sourceB2467 + difference 4 5) sourceC2467) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2574) := by
    have ha : (tripleCharges (sourceA2467 + difference 5 4) (sourceB2467 + difference 4 5) sourceC2467) = raw33933 := by
      apply Matrix.ext; unfold tripleCharges sourceA2467 sourceB2467 sourceC2467 difference raw33933; decide +kernel
    rw [ha]
    exact (canonical33933 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2467 sourceB2467 sourceC2467
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2467, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2468 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2468 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC2468 : Charge := ![3, 0, -1, -1, 0, -1]
def sourceForm2468 : Integer.Sparse Master := [(Sum.inr 1670, 1), (Sum.inr 1671, 1), (Sum.inr 1673, 1), (Sum.inr 1678, 1), (Sum.inr 1724, 1), (Sum.inr 2147, 1), (Sum.inr 2148, 1), (Sum.inr 2150, 1), (Sum.inr 2154, 1), (Sum.inr 2198, 1), (Sum.inr 2199, 1), (Sum.inr 2201, 1), (Sum.inr 2202, 2), (Sum.inr 2204, 1), (Sum.inr 2211, 1), (Sum.inr 2213, 1), (Sum.inr 2214, 1), (Sum.inr 2224, 1), (Sum.inr 2225, 1), (Sum.inr 2227, 1), (Sum.inr 2260, 1), (Sum.inr 2262, 1), (Sum.inr 2263, 1), (Sum.inr 2291, 1), (Sum.inr 2669, 1), (Sum.inr 2718, 1), (Sum.inr 2720, 1), (Sum.inr 2721, 1), (Sum.inr 2739, 1)]

theorem sourceEq2468 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2468 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2468 + difference 0 1) (sourceB2468 + difference 1 0) sourceC2468) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2669) := by
    have ha : (tripleCharges (sourceA2468 + difference 0 1) (sourceB2468 + difference 1 0) sourceC2468) = raw33934 := by
      apply Matrix.ext; unfold tripleCharges sourceA2468 sourceB2468 sourceC2468 difference raw33934; decide +kernel
    rw [ha]
    exact (canonical33934 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2468 + difference 0 2) (sourceB2468 + difference 2 0) sourceC2468) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2718) := by
    have ha : (tripleCharges (sourceA2468 + difference 0 2) (sourceB2468 + difference 2 0) sourceC2468) = raw33935 := by
      apply Matrix.ext; unfold tripleCharges sourceA2468 sourceB2468 sourceC2468 difference raw33935; decide +kernel
    rw [ha]
    exact (canonical33935 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2468 + difference 0 3) (sourceB2468 + difference 3 0) sourceC2468) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2720) := by
    have ha : (tripleCharges (sourceA2468 + difference 0 3) (sourceB2468 + difference 3 0) sourceC2468) = raw33936 := by
      apply Matrix.ext; unfold tripleCharges sourceA2468 sourceB2468 sourceC2468 difference raw33936; decide +kernel
    rw [ha]
    exact (canonical33936 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2468 + difference 0 4) (sourceB2468 + difference 4 0) sourceC2468) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2739) := by
    have ha : (tripleCharges (sourceA2468 + difference 0 4) (sourceB2468 + difference 4 0) sourceC2468) = raw33937 := by
      apply Matrix.ext; unfold tripleCharges sourceA2468 sourceB2468 sourceC2468 difference raw33937; decide +kernel
    rw [ha]
    exact (canonical33937 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2468 + difference 0 5) (sourceB2468 + difference 5 0) sourceC2468) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2721) := by
    have ha : (tripleCharges (sourceA2468 + difference 0 5) (sourceB2468 + difference 5 0) sourceC2468) = raw33938 := by
      apply Matrix.ext; unfold tripleCharges sourceA2468 sourceB2468 sourceC2468 difference raw33938; decide +kernel
    rw [ha]
    exact (canonical33938 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2468 + difference 1 0) (sourceB2468 + difference 0 1) sourceC2468) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1724) := by
    have ha : (tripleCharges (sourceA2468 + difference 1 0) (sourceB2468 + difference 0 1) sourceC2468) = raw33939 := by
      apply Matrix.ext; unfold tripleCharges sourceA2468 sourceB2468 sourceC2468 difference raw33939; decide +kernel
    rw [ha]
    exact (canonical33939 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2468 + difference 1 2) (sourceB2468 + difference 2 1) sourceC2468) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2260) := by
    have ha : (tripleCharges (sourceA2468 + difference 1 2) (sourceB2468 + difference 2 1) sourceC2468) = raw33940 := by
      apply Matrix.ext; unfold tripleCharges sourceA2468 sourceB2468 sourceC2468 difference raw33940; decide +kernel
    rw [ha]
    exact (canonical33940 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2468 + difference 1 3) (sourceB2468 + difference 3 1) sourceC2468) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2262) := by
    have ha : (tripleCharges (sourceA2468 + difference 1 3) (sourceB2468 + difference 3 1) sourceC2468) = raw33941 := by
      apply Matrix.ext; unfold tripleCharges sourceA2468 sourceB2468 sourceC2468 difference raw33941; decide +kernel
    rw [ha]
    exact (canonical33941 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2468 + difference 1 4) (sourceB2468 + difference 4 1) sourceC2468) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2291) := by
    have ha : (tripleCharges (sourceA2468 + difference 1 4) (sourceB2468 + difference 4 1) sourceC2468) = raw33942 := by
      apply Matrix.ext; unfold tripleCharges sourceA2468 sourceB2468 sourceC2468 difference raw33942; decide +kernel
    rw [ha]
    exact (canonical33942 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2468 + difference 1 5) (sourceB2468 + difference 5 1) sourceC2468) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2263) := by
    have ha : (tripleCharges (sourceA2468 + difference 1 5) (sourceB2468 + difference 5 1) sourceC2468) = raw33943 := by
      apply Matrix.ext; unfold tripleCharges sourceA2468 sourceB2468 sourceC2468 difference raw33943; decide +kernel
    rw [ha]
    exact (canonical33943 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2468 + difference 2 0) (sourceB2468 + difference 0 2) sourceC2468) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1673) := by
    have ha : (tripleCharges (sourceA2468 + difference 2 0) (sourceB2468 + difference 0 2) sourceC2468) = raw33944 := by
      apply Matrix.ext; unfold tripleCharges sourceA2468 sourceB2468 sourceC2468 difference raw33944; decide +kernel
    rw [ha]
    exact (canonical33944 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2468 + difference 2 1) (sourceB2468 + difference 1 2) sourceC2468) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2150) := by
    have ha : (tripleCharges (sourceA2468 + difference 2 1) (sourceB2468 + difference 1 2) sourceC2468) = raw33945 := by
      apply Matrix.ext; unfold tripleCharges sourceA2468 sourceB2468 sourceC2468 difference raw33945; decide +kernel
    rw [ha]
    exact (canonical33945 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2468 + difference 2 3) (sourceB2468 + difference 3 2) sourceC2468) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2202) := by
    have ha : (tripleCharges (sourceA2468 + difference 2 3) (sourceB2468 + difference 3 2) sourceC2468) = raw33946 := by
      apply Matrix.ext; unfold tripleCharges sourceA2468 sourceB2468 sourceC2468 difference raw33946; decide +kernel
    rw [ha]
    exact (canonical33946 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2468 + difference 2 4) (sourceB2468 + difference 4 2) sourceC2468) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2227) := by
    have ha : (tripleCharges (sourceA2468 + difference 2 4) (sourceB2468 + difference 4 2) sourceC2468) = raw33947 := by
      apply Matrix.ext; unfold tripleCharges sourceA2468 sourceB2468 sourceC2468 difference raw33947; decide +kernel
    rw [ha]
    exact (canonical33947 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2468 + difference 2 5) (sourceB2468 + difference 5 2) sourceC2468) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2204) := by
    have ha : (tripleCharges (sourceA2468 + difference 2 5) (sourceB2468 + difference 5 2) sourceC2468) = raw33948 := by
      apply Matrix.ext; unfold tripleCharges sourceA2468 sourceB2468 sourceC2468 difference raw33948; decide +kernel
    rw [ha]
    exact (canonical33948 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2468 + difference 3 0) (sourceB2468 + difference 0 3) sourceC2468) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1671) := by
    have ha : (tripleCharges (sourceA2468 + difference 3 0) (sourceB2468 + difference 0 3) sourceC2468) = raw33949 := by
      apply Matrix.ext; unfold tripleCharges sourceA2468 sourceB2468 sourceC2468 difference raw33949; decide +kernel
    rw [ha]
    exact (canonical33949 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2468 + difference 3 1) (sourceB2468 + difference 1 3) sourceC2468) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2148) := by
    have ha : (tripleCharges (sourceA2468 + difference 3 1) (sourceB2468 + difference 1 3) sourceC2468) = raw33950 := by
      apply Matrix.ext; unfold tripleCharges sourceA2468 sourceB2468 sourceC2468 difference raw33950; decide +kernel
    rw [ha]
    exact (canonical33950 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2468 + difference 3 2) (sourceB2468 + difference 2 3) sourceC2468) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2199) := by
    have ha : (tripleCharges (sourceA2468 + difference 3 2) (sourceB2468 + difference 2 3) sourceC2468) = raw33951 := by
      apply Matrix.ext; unfold tripleCharges sourceA2468 sourceB2468 sourceC2468 difference raw33951; decide +kernel
    rw [ha]
    exact (canonical33951 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2468 + difference 3 4) (sourceB2468 + difference 4 3) sourceC2468) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2225) := by
    have ha : (tripleCharges (sourceA2468 + difference 3 4) (sourceB2468 + difference 4 3) sourceC2468) = raw33952 := by
      apply Matrix.ext; unfold tripleCharges sourceA2468 sourceB2468 sourceC2468 difference raw33952; decide +kernel
    rw [ha]
    exact (canonical33952 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2468 + difference 3 5) (sourceB2468 + difference 5 3) sourceC2468) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2202) := by
    have ha : (tripleCharges (sourceA2468 + difference 3 5) (sourceB2468 + difference 5 3) sourceC2468) = raw33953 := by
      apply Matrix.ext; unfold tripleCharges sourceA2468 sourceB2468 sourceC2468 difference raw33953; decide +kernel
    rw [ha]
    exact (canonical33953 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2468 + difference 4 0) (sourceB2468 + difference 0 4) sourceC2468) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1678) := by
    have ha : (tripleCharges (sourceA2468 + difference 4 0) (sourceB2468 + difference 0 4) sourceC2468) = raw33954 := by
      apply Matrix.ext; unfold tripleCharges sourceA2468 sourceB2468 sourceC2468 difference raw33954; decide +kernel
    rw [ha]
    exact (canonical33954 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2468 + difference 4 1) (sourceB2468 + difference 1 4) sourceC2468) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2154) := by
    have ha : (tripleCharges (sourceA2468 + difference 4 1) (sourceB2468 + difference 1 4) sourceC2468) = raw33955 := by
      apply Matrix.ext; unfold tripleCharges sourceA2468 sourceB2468 sourceC2468 difference raw33955; decide +kernel
    rw [ha]
    exact (canonical33955 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2468 + difference 4 2) (sourceB2468 + difference 2 4) sourceC2468) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2211) := by
    have ha : (tripleCharges (sourceA2468 + difference 4 2) (sourceB2468 + difference 2 4) sourceC2468) = raw33956 := by
      apply Matrix.ext; unfold tripleCharges sourceA2468 sourceB2468 sourceC2468 difference raw33956; decide +kernel
    rw [ha]
    exact (canonical33956 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2468 + difference 4 3) (sourceB2468 + difference 3 4) sourceC2468) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2213) := by
    have ha : (tripleCharges (sourceA2468 + difference 4 3) (sourceB2468 + difference 3 4) sourceC2468) = raw33957 := by
      apply Matrix.ext; unfold tripleCharges sourceA2468 sourceB2468 sourceC2468 difference raw33957; decide +kernel
    rw [ha]
    exact (canonical33957 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2468 + difference 4 5) (sourceB2468 + difference 5 4) sourceC2468) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2214) := by
    have ha : (tripleCharges (sourceA2468 + difference 4 5) (sourceB2468 + difference 5 4) sourceC2468) = raw33958 := by
      apply Matrix.ext; unfold tripleCharges sourceA2468 sourceB2468 sourceC2468 difference raw33958; decide +kernel
    rw [ha]
    exact (canonical33958 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2468 + difference 5 0) (sourceB2468 + difference 0 5) sourceC2468) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1670) := by
    have ha : (tripleCharges (sourceA2468 + difference 5 0) (sourceB2468 + difference 0 5) sourceC2468) = raw33959 := by
      apply Matrix.ext; unfold tripleCharges sourceA2468 sourceB2468 sourceC2468 difference raw33959; decide +kernel
    rw [ha]
    exact (canonical33959 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2468 + difference 5 1) (sourceB2468 + difference 1 5) sourceC2468) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2147) := by
    have ha : (tripleCharges (sourceA2468 + difference 5 1) (sourceB2468 + difference 1 5) sourceC2468) = raw33960 := by
      apply Matrix.ext; unfold tripleCharges sourceA2468 sourceB2468 sourceC2468 difference raw33960; decide +kernel
    rw [ha]
    exact (canonical33960 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2468 + difference 5 2) (sourceB2468 + difference 2 5) sourceC2468) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2198) := by
    have ha : (tripleCharges (sourceA2468 + difference 5 2) (sourceB2468 + difference 2 5) sourceC2468) = raw33961 := by
      apply Matrix.ext; unfold tripleCharges sourceA2468 sourceB2468 sourceC2468 difference raw33961; decide +kernel
    rw [ha]
    exact (canonical33961 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2468 + difference 5 3) (sourceB2468 + difference 3 5) sourceC2468) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2201) := by
    have ha : (tripleCharges (sourceA2468 + difference 5 3) (sourceB2468 + difference 3 5) sourceC2468) = raw33962 := by
      apply Matrix.ext; unfold tripleCharges sourceA2468 sourceB2468 sourceC2468 difference raw33962; decide +kernel
    rw [ha]
    exact (canonical33962 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2468 + difference 5 4) (sourceB2468 + difference 4 5) sourceC2468) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2224) := by
    have ha : (tripleCharges (sourceA2468 + difference 5 4) (sourceB2468 + difference 4 5) sourceC2468) = raw33963 := by
      apply Matrix.ext; unfold tripleCharges sourceA2468 sourceB2468 sourceC2468 difference raw33963; decide +kernel
    rw [ha]
    exact (canonical33963 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2468 sourceB2468 sourceC2468
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2468, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2469 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2469 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC2469 : Charge := ![3, 0, -1, -1, 0, -1]
def sourceForm2469 : Integer.Sparse Master := [(Sum.inr 1790, 1), (Sum.inr 1792, 1), (Sum.inr 1794, 1), (Sum.inr 1805, 1), (Sum.inr 2020, 1), (Sum.inr 3376, 1), (Sum.inr 4083, -1)]

theorem sourceEq2469 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2469 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2469 + difference 0 1) (sourceB2469 + difference 1 0) sourceC2469) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3376) := by
    have ha : (tripleCharges (sourceA2469 + difference 0 1) (sourceB2469 + difference 1 0) sourceC2469) = raw33964 := by
      apply Matrix.ext; unfold tripleCharges sourceA2469 sourceB2469 sourceC2469 difference raw33964; decide +kernel
    rw [ha]
    exact (canonical33964 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2469 + difference 1 1) (sourceB2469 + difference 1 1) sourceC2469) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2020) := by
    have ha : (tripleCharges (sourceA2469 + difference 1 1) (sourceB2469 + difference 1 1) sourceC2469) = raw33965 := by
      apply Matrix.ext; unfold tripleCharges sourceA2469 sourceB2469 sourceC2469 difference raw33965; decide +kernel
    rw [ha]
    exact (canonical33965 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2469 + difference 2 1) (sourceB2469 + difference 1 2) sourceC2469) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1805) := by
    have ha : (tripleCharges (sourceA2469 + difference 2 1) (sourceB2469 + difference 1 2) sourceC2469) = raw33966 := by
      apply Matrix.ext; unfold tripleCharges sourceA2469 sourceB2469 sourceC2469 difference raw33966; decide +kernel
    rw [ha]
    exact (canonical33966 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2469 + difference 3 1) (sourceB2469 + difference 1 3) sourceC2469) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1792) := by
    have ha : (tripleCharges (sourceA2469 + difference 3 1) (sourceB2469 + difference 1 3) sourceC2469) = raw33967 := by
      apply Matrix.ext; unfold tripleCharges sourceA2469 sourceB2469 sourceC2469 difference raw33967; decide +kernel
    rw [ha]
    exact (canonical33967 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2469 + difference 4 1) (sourceB2469 + difference 1 4) sourceC2469) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1794) := by
    have ha : (tripleCharges (sourceA2469 + difference 4 1) (sourceB2469 + difference 1 4) sourceC2469) = raw33968 := by
      apply Matrix.ext; unfold tripleCharges sourceA2469 sourceB2469 sourceC2469 difference raw33968; decide +kernel
    rw [ha]
    exact (canonical33968 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2469 + difference 5 1) (sourceB2469 + difference 1 5) sourceC2469) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1790) := by
    have ha : (tripleCharges (sourceA2469 + difference 5 1) (sourceB2469 + difference 1 5) sourceC2469) = raw33969 := by
      apply Matrix.ext; unfold tripleCharges sourceA2469 sourceB2469 sourceC2469 difference raw33969; decide +kernel
    rw [ha]
    exact (canonical33969 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2469 + sourceB2469) sourceC2469) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA2469 + sourceB2469) sourceC2469) = raw20196 := by
      apply Matrix.ext; unfold doubleCharges sourceA2469 sourceB2469 sourceC2469 raw20196; decide +kernel
    rw [ha]
    exact (canonical20196 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2469 sourceB2469 sourceC2469
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2469, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2470 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2470 : Charge := ![3, 0, -1, -1, 0, -1]
def sourceC2470 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceForm2470 : Integer.Sparse Master := [(Sum.inr 4196, 1), (Sum.inr 4197, 1), (Sum.inr 4201, 1), (Sum.inr 4210, 1), (Sum.inr 4249, 1), (Sum.inr 4631, 1), (Sum.inr 4632, 1), (Sum.inr 4635, 1), (Sum.inr 4642, 1), (Sum.inr 4760, 1), (Sum.inr 4763, 1), (Sum.inr 4767, 1), (Sum.inr 4779, 1), (Sum.inr 4782, 1), (Sum.inr 4787, 1), (Sum.inr 4801, 1), (Sum.inr 4802, 2), (Sum.inr 4804, 1), (Sum.inr 4811, 1), (Sum.inr 4831, 2), (Sum.inr 4835, 1), (Sum.inr 4887, 1), (Sum.inr 4888, 1), (Sum.inr 5352, 1), (Sum.inr 5416, 1), (Sum.inr 5424, 1), (Sum.inr 5433, 1), (Sum.inr 5434, 1)]

theorem sourceEq2470 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2470 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2470 + difference 0 1) (sourceB2470 + difference 1 0) sourceC2470) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5352) := by
    have ha : (tripleCharges (sourceA2470 + difference 0 1) (sourceB2470 + difference 1 0) sourceC2470) = raw33970 := by
      apply Matrix.ext; unfold tripleCharges sourceA2470 sourceB2470 sourceC2470 difference raw33970; decide +kernel
    rw [ha]
    exact (canonical33970 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2470 + difference 0 2) (sourceB2470 + difference 2 0) sourceC2470) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5416) := by
    have ha : (tripleCharges (sourceA2470 + difference 0 2) (sourceB2470 + difference 2 0) sourceC2470) = raw33971 := by
      apply Matrix.ext; unfold tripleCharges sourceA2470 sourceB2470 sourceC2470 difference raw33971; decide +kernel
    rw [ha]
    exact (canonical33971 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2470 + difference 0 3) (sourceB2470 + difference 3 0) sourceC2470) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA2470 + difference 0 3) (sourceB2470 + difference 3 0) sourceC2470) = raw11315 := by
      apply Matrix.ext; unfold tripleCharges sourceA2470 sourceB2470 sourceC2470 difference raw11315; decide +kernel
    rw [ha]
    exact (canonical11315 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2470 + difference 0 4) (sourceB2470 + difference 4 0) sourceC2470) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA2470 + difference 0 4) (sourceB2470 + difference 4 0) sourceC2470) = raw33972 := by
      apply Matrix.ext; unfold tripleCharges sourceA2470 sourceB2470 sourceC2470 difference raw33972; decide +kernel
    rw [ha]
    exact (canonical33972 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2470 + difference 0 5) (sourceB2470 + difference 5 0) sourceC2470) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA2470 + difference 0 5) (sourceB2470 + difference 5 0) sourceC2470) = raw14308 := by
      apply Matrix.ext; unfold tripleCharges sourceA2470 sourceB2470 sourceC2470 difference raw14308; decide +kernel
    rw [ha]
    exact (canonical14308 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2470 + difference 1 0) (sourceB2470 + difference 0 1) sourceC2470) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4249) := by
    have ha : (tripleCharges (sourceA2470 + difference 1 0) (sourceB2470 + difference 0 1) sourceC2470) = raw11330 := by
      apply Matrix.ext; unfold tripleCharges sourceA2470 sourceB2470 sourceC2470 difference raw11330; decide +kernel
    rw [ha]
    exact (canonical11330 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2470 + difference 1 2) (sourceB2470 + difference 2 1) sourceC2470) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA2470 + difference 1 2) (sourceB2470 + difference 2 1) sourceC2470) = raw11332 := by
      apply Matrix.ext; unfold tripleCharges sourceA2470 sourceB2470 sourceC2470 difference raw11332; decide +kernel
    rw [ha]
    exact (canonical11332 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2470 + difference 1 3) (sourceB2470 + difference 3 1) sourceC2470) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA2470 + difference 1 3) (sourceB2470 + difference 3 1) sourceC2470) = raw14329 := by
      apply Matrix.ext; unfold tripleCharges sourceA2470 sourceB2470 sourceC2470 difference raw14329; decide +kernel
    rw [ha]
    exact (canonical14329 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2470 + difference 1 4) (sourceB2470 + difference 4 1) sourceC2470) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4831) := by
    have ha : (tripleCharges (sourceA2470 + difference 1 4) (sourceB2470 + difference 4 1) sourceC2470) = raw11333 := by
      apply Matrix.ext; unfold tripleCharges sourceA2470 sourceB2470 sourceC2470 difference raw11333; decide +kernel
    rw [ha]
    exact (canonical11333 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2470 + difference 1 5) (sourceB2470 + difference 5 1) sourceC2470) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4887) := by
    have ha : (tripleCharges (sourceA2470 + difference 1 5) (sourceB2470 + difference 5 1) sourceC2470) = raw11334 := by
      apply Matrix.ext; unfold tripleCharges sourceA2470 sourceB2470 sourceC2470 difference raw11334; decide +kernel
    rw [ha]
    exact (canonical11334 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2470 + difference 2 0) (sourceB2470 + difference 0 2) sourceC2470) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4210) := by
    have ha : (tripleCharges (sourceA2470 + difference 2 0) (sourceB2470 + difference 0 2) sourceC2470) = raw33973 := by
      apply Matrix.ext; unfold tripleCharges sourceA2470 sourceB2470 sourceC2470 difference raw33973; decide +kernel
    rw [ha]
    exact (canonical33973 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2470 + difference 2 1) (sourceB2470 + difference 1 2) sourceC2470) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4642) := by
    have ha : (tripleCharges (sourceA2470 + difference 2 1) (sourceB2470 + difference 1 2) sourceC2470) = raw33974 := by
      apply Matrix.ext; unfold tripleCharges sourceA2470 sourceB2470 sourceC2470 difference raw33974; decide +kernel
    rw [ha]
    exact (canonical33974 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2470 + difference 2 3) (sourceB2470 + difference 3 2) sourceC2470) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4835) := by
    have ha : (tripleCharges (sourceA2470 + difference 2 3) (sourceB2470 + difference 3 2) sourceC2470) = raw11326 := by
      apply Matrix.ext; unfold tripleCharges sourceA2470 sourceB2470 sourceC2470 difference raw11326; decide +kernel
    rw [ha]
    exact (canonical11326 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2470 + difference 2 4) (sourceB2470 + difference 4 2) sourceC2470) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4787) := by
    have ha : (tripleCharges (sourceA2470 + difference 2 4) (sourceB2470 + difference 4 2) sourceC2470) = raw33975 := by
      apply Matrix.ext; unfold tripleCharges sourceA2470 sourceB2470 sourceC2470 difference raw33975; decide +kernel
    rw [ha]
    exact (canonical33975 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2470 + difference 2 5) (sourceB2470 + difference 5 2) sourceC2470) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4831) := by
    have ha : (tripleCharges (sourceA2470 + difference 2 5) (sourceB2470 + difference 5 2) sourceC2470) = raw14317 := by
      apply Matrix.ext; unfold tripleCharges sourceA2470 sourceB2470 sourceC2470 difference raw14317; decide +kernel
    rw [ha]
    exact (canonical14317 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2470 + difference 3 0) (sourceB2470 + difference 0 3) sourceC2470) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4197) := by
    have ha : (tripleCharges (sourceA2470 + difference 3 0) (sourceB2470 + difference 0 3) sourceC2470) = raw33976 := by
      apply Matrix.ext; unfold tripleCharges sourceA2470 sourceB2470 sourceC2470 difference raw33976; decide +kernel
    rw [ha]
    exact (canonical33976 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2470 + difference 3 1) (sourceB2470 + difference 1 3) sourceC2470) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4632) := by
    have ha : (tripleCharges (sourceA2470 + difference 3 1) (sourceB2470 + difference 1 3) sourceC2470) = raw33977 := by
      apply Matrix.ext; unfold tripleCharges sourceA2470 sourceB2470 sourceC2470 difference raw33977; decide +kernel
    rw [ha]
    exact (canonical33977 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2470 + difference 3 2) (sourceB2470 + difference 2 3) sourceC2470) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4763) := by
    have ha : (tripleCharges (sourceA2470 + difference 3 2) (sourceB2470 + difference 2 3) sourceC2470) = raw33978 := by
      apply Matrix.ext; unfold tripleCharges sourceA2470 sourceB2470 sourceC2470 difference raw33978; decide +kernel
    rw [ha]
    exact (canonical33978 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2470 + difference 3 4) (sourceB2470 + difference 4 3) sourceC2470) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4782) := by
    have ha : (tripleCharges (sourceA2470 + difference 3 4) (sourceB2470 + difference 4 3) sourceC2470) = raw33979 := by
      apply Matrix.ext; unfold tripleCharges sourceA2470 sourceB2470 sourceC2470 difference raw33979; decide +kernel
    rw [ha]
    exact (canonical33979 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2470 + difference 3 5) (sourceB2470 + difference 5 3) sourceC2470) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4801) := by
    have ha : (tripleCharges (sourceA2470 + difference 3 5) (sourceB2470 + difference 5 3) sourceC2470) = raw14321 := by
      apply Matrix.ext; unfold tripleCharges sourceA2470 sourceB2470 sourceC2470 difference raw14321; decide +kernel
    rw [ha]
    exact (canonical14321 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2470 + difference 4 0) (sourceB2470 + difference 0 4) sourceC2470) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4201) := by
    have ha : (tripleCharges (sourceA2470 + difference 4 0) (sourceB2470 + difference 0 4) sourceC2470) = raw31570 := by
      apply Matrix.ext; unfold tripleCharges sourceA2470 sourceB2470 sourceC2470 difference raw31570; decide +kernel
    rw [ha]
    exact (canonical31570 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2470 + difference 4 1) (sourceB2470 + difference 1 4) sourceC2470) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4635) := by
    have ha : (tripleCharges (sourceA2470 + difference 4 1) (sourceB2470 + difference 1 4) sourceC2470) = raw31571 := by
      apply Matrix.ext; unfold tripleCharges sourceA2470 sourceB2470 sourceC2470 difference raw31571; decide +kernel
    rw [ha]
    exact (canonical31571 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2470 + difference 4 2) (sourceB2470 + difference 2 4) sourceC2470) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4767) := by
    have ha : (tripleCharges (sourceA2470 + difference 4 2) (sourceB2470 + difference 2 4) sourceC2470) = raw31572 := by
      apply Matrix.ext; unfold tripleCharges sourceA2470 sourceB2470 sourceC2470 difference raw31572; decide +kernel
    rw [ha]
    exact (canonical31572 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2470 + difference 4 3) (sourceB2470 + difference 3 4) sourceC2470) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4811) := by
    have ha : (tripleCharges (sourceA2470 + difference 4 3) (sourceB2470 + difference 3 4) sourceC2470) = raw11336 := by
      apply Matrix.ext; unfold tripleCharges sourceA2470 sourceB2470 sourceC2470 difference raw11336; decide +kernel
    rw [ha]
    exact (canonical11336 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2470 + difference 4 5) (sourceB2470 + difference 5 4) sourceC2470) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA2470 + difference 4 5) (sourceB2470 + difference 5 4) sourceC2470) = raw14326 := by
      apply Matrix.ext; unfold tripleCharges sourceA2470 sourceB2470 sourceC2470 difference raw14326; decide +kernel
    rw [ha]
    exact (canonical14326 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2470 + difference 5 0) (sourceB2470 + difference 0 5) sourceC2470) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4196) := by
    have ha : (tripleCharges (sourceA2470 + difference 5 0) (sourceB2470 + difference 0 5) sourceC2470) = raw33980 := by
      apply Matrix.ext; unfold tripleCharges sourceA2470 sourceB2470 sourceC2470 difference raw33980; decide +kernel
    rw [ha]
    exact (canonical33980 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2470 + difference 5 1) (sourceB2470 + difference 1 5) sourceC2470) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4631) := by
    have ha : (tripleCharges (sourceA2470 + difference 5 1) (sourceB2470 + difference 1 5) sourceC2470) = raw33981 := by
      apply Matrix.ext; unfold tripleCharges sourceA2470 sourceB2470 sourceC2470 difference raw33981; decide +kernel
    rw [ha]
    exact (canonical33981 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2470 + difference 5 2) (sourceB2470 + difference 2 5) sourceC2470) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4760) := by
    have ha : (tripleCharges (sourceA2470 + difference 5 2) (sourceB2470 + difference 2 5) sourceC2470) = raw33982 := by
      apply Matrix.ext; unfold tripleCharges sourceA2470 sourceB2470 sourceC2470 difference raw33982; decide +kernel
    rw [ha]
    exact (canonical33982 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2470 + difference 5 3) (sourceB2470 + difference 3 5) sourceC2470) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA2470 + difference 5 3) (sourceB2470 + difference 3 5) sourceC2470) = raw11341 := by
      apply Matrix.ext; unfold tripleCharges sourceA2470 sourceB2470 sourceC2470 difference raw11341; decide +kernel
    rw [ha]
    exact (canonical11341 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2470 + difference 5 4) (sourceB2470 + difference 4 5) sourceC2470) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4779) := by
    have ha : (tripleCharges (sourceA2470 + difference 5 4) (sourceB2470 + difference 4 5) sourceC2470) = raw33983 := by
      apply Matrix.ext; unfold tripleCharges sourceA2470 sourceB2470 sourceC2470 difference raw33983; decide +kernel
    rw [ha]
    exact (canonical33983 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2470 sourceB2470 sourceC2470
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2470, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2471 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceB2471 : Charge := ![3, 0, -1, -1, 0, -1]
def sourceC2471 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceForm2471 : Integer.Sparse Master := [(Sum.inr 4396, 1), (Sum.inr 4397, 1), (Sum.inr 4400, 1), (Sum.inr 4417, 1), (Sum.inr 4449, 1), (Sum.inr 4736, 1), (Sum.inr 4737, 1), (Sum.inr 4739, 1), (Sum.inr 4740, 1), (Sum.inr 4798, 1), (Sum.inr 4799, 1), (Sum.inr 4801, 1), (Sum.inr 4802, 1), (Sum.inr 4803, 1), (Sum.inr 4805, 1), (Sum.inr 4813, 1), (Sum.inr 4815, 1), (Sum.inr 4816, 1), (Sum.inr 4834, 1), (Sum.inr 4835, 1), (Sum.inr 4838, 1), (Sum.inr 4849, 1), (Sum.inr 4851, 1), (Sum.inr 4852, 1), (Sum.inr 4866, 1), (Sum.inr 5073, 1), (Sum.inr 5145, 1), (Sum.inr 5148, 1), (Sum.inr 5149, 1), (Sum.inr 5169, 1)]

theorem sourceEq2471 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2471 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2471 + difference 0 1) (sourceB2471 + difference 1 0) sourceC2471) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5073) := by
    have ha : (tripleCharges (sourceA2471 + difference 0 1) (sourceB2471 + difference 1 0) sourceC2471) = raw32328 := by
      apply Matrix.ext; unfold tripleCharges sourceA2471 sourceB2471 sourceC2471 difference raw32328; decide +kernel
    rw [ha]
    exact (canonical32328 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2471 + difference 0 2) (sourceB2471 + difference 2 0) sourceC2471) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA2471 + difference 0 2) (sourceB2471 + difference 2 0) sourceC2471) = raw32254 := by
      apply Matrix.ext; unfold tripleCharges sourceA2471 sourceB2471 sourceC2471 difference raw32254; decide +kernel
    rw [ha]
    exact (canonical32254 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2471 + difference 0 3) (sourceB2471 + difference 3 0) sourceC2471) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5148) := by
    have ha : (tripleCharges (sourceA2471 + difference 0 3) (sourceB2471 + difference 3 0) sourceC2471) = raw32492 := by
      apply Matrix.ext; unfold tripleCharges sourceA2471 sourceB2471 sourceC2471 difference raw32492; decide +kernel
    rw [ha]
    exact (canonical32492 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2471 + difference 0 4) (sourceB2471 + difference 4 0) sourceC2471) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5145) := by
    have ha : (tripleCharges (sourceA2471 + difference 0 4) (sourceB2471 + difference 4 0) sourceC2471) = raw32329 := by
      apply Matrix.ext; unfold tripleCharges sourceA2471 sourceB2471 sourceC2471 difference raw32329; decide +kernel
    rw [ha]
    exact (canonical32329 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2471 + difference 0 5) (sourceB2471 + difference 5 0) sourceC2471) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5149) := by
    have ha : (tripleCharges (sourceA2471 + difference 0 5) (sourceB2471 + difference 5 0) sourceC2471) = raw32238 := by
      apply Matrix.ext; unfold tripleCharges sourceA2471 sourceB2471 sourceC2471 difference raw32238; decide +kernel
    rw [ha]
    exact (canonical32238 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2471 + difference 1 0) (sourceB2471 + difference 0 1) sourceC2471) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4449) := by
    have ha : (tripleCharges (sourceA2471 + difference 1 0) (sourceB2471 + difference 0 1) sourceC2471) = raw33646 := by
      apply Matrix.ext; unfold tripleCharges sourceA2471 sourceB2471 sourceC2471 difference raw33646; decide +kernel
    rw [ha]
    exact (canonical33646 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2471 + difference 1 2) (sourceB2471 + difference 2 1) sourceC2471) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA2471 + difference 1 2) (sourceB2471 + difference 2 1) sourceC2471) = raw33568 := by
      apply Matrix.ext; unfold tripleCharges sourceA2471 sourceB2471 sourceC2471 difference raw33568; decide +kernel
    rw [ha]
    exact (canonical33568 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2471 + difference 1 3) (sourceB2471 + difference 3 1) sourceC2471) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4851) := by
    have ha : (tripleCharges (sourceA2471 + difference 1 3) (sourceB2471 + difference 3 1) sourceC2471) = raw32317 := by
      apply Matrix.ext; unfold tripleCharges sourceA2471 sourceB2471 sourceC2471 difference raw32317; decide +kernel
    rw [ha]
    exact (canonical32317 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2471 + difference 1 4) (sourceB2471 + difference 4 1) sourceC2471) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4849) := by
    have ha : (tripleCharges (sourceA2471 + difference 1 4) (sourceB2471 + difference 4 1) sourceC2471) = raw33647 := by
      apply Matrix.ext; unfold tripleCharges sourceA2471 sourceB2471 sourceC2471 difference raw33647; decide +kernel
    rw [ha]
    exact (canonical33647 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2471 + difference 1 5) (sourceB2471 + difference 5 1) sourceC2471) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4852) := by
    have ha : (tripleCharges (sourceA2471 + difference 1 5) (sourceB2471 + difference 5 1) sourceC2471) = raw33556 := by
      apply Matrix.ext; unfold tripleCharges sourceA2471 sourceB2471 sourceC2471 difference raw33556; decide +kernel
    rw [ha]
    exact (canonical33556 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2471 + difference 2 0) (sourceB2471 + difference 0 2) sourceC2471) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4400) := by
    have ha : (tripleCharges (sourceA2471 + difference 2 0) (sourceB2471 + difference 0 2) sourceC2471) = raw33984 := by
      apply Matrix.ext; unfold tripleCharges sourceA2471 sourceB2471 sourceC2471 difference raw33984; decide +kernel
    rw [ha]
    exact (canonical33984 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2471 + difference 2 1) (sourceB2471 + difference 1 2) sourceC2471) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4740) := by
    have ha : (tripleCharges (sourceA2471 + difference 2 1) (sourceB2471 + difference 1 2) sourceC2471) = raw33136 := by
      apply Matrix.ext; unfold tripleCharges sourceA2471 sourceB2471 sourceC2471 difference raw33136; decide +kernel
    rw [ha]
    exact (canonical33136 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2471 + difference 2 3) (sourceB2471 + difference 3 2) sourceC2471) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4815) := by
    have ha : (tripleCharges (sourceA2471 + difference 2 3) (sourceB2471 + difference 3 2) sourceC2471) = raw32322 := by
      apply Matrix.ext; unfold tripleCharges sourceA2471 sourceB2471 sourceC2471 difference raw32322; decide +kernel
    rw [ha]
    exact (canonical32322 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2471 + difference 2 4) (sourceB2471 + difference 4 2) sourceC2471) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4813) := by
    have ha : (tripleCharges (sourceA2471 + difference 2 4) (sourceB2471 + difference 4 2) sourceC2471) = raw33985 := by
      apply Matrix.ext; unfold tripleCharges sourceA2471 sourceB2471 sourceC2471 difference raw33985; decide +kernel
    rw [ha]
    exact (canonical33985 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2471 + difference 2 5) (sourceB2471 + difference 5 2) sourceC2471) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4816) := by
    have ha : (tripleCharges (sourceA2471 + difference 2 5) (sourceB2471 + difference 5 2) sourceC2471) = raw33864 := by
      apply Matrix.ext; unfold tripleCharges sourceA2471 sourceB2471 sourceC2471 difference raw33864; decide +kernel
    rw [ha]
    exact (canonical33864 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2471 + difference 3 0) (sourceB2471 + difference 0 3) sourceC2471) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4397) := by
    have ha : (tripleCharges (sourceA2471 + difference 3 0) (sourceB2471 + difference 0 3) sourceC2471) = raw33986 := by
      apply Matrix.ext; unfold tripleCharges sourceA2471 sourceB2471 sourceC2471 difference raw33986; decide +kernel
    rw [ha]
    exact (canonical33986 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2471 + difference 3 1) (sourceB2471 + difference 1 3) sourceC2471) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4737) := by
    have ha : (tripleCharges (sourceA2471 + difference 3 1) (sourceB2471 + difference 1 3) sourceC2471) = raw33140 := by
      apply Matrix.ext; unfold tripleCharges sourceA2471 sourceB2471 sourceC2471 difference raw33140; decide +kernel
    rw [ha]
    exact (canonical33140 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2471 + difference 3 2) (sourceB2471 + difference 2 3) sourceC2471) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4835) := by
    have ha : (tripleCharges (sourceA2471 + difference 3 2) (sourceB2471 + difference 2 3) sourceC2471) = raw33649 := by
      apply Matrix.ext; unfold tripleCharges sourceA2471 sourceB2471 sourceC2471 difference raw33649; decide +kernel
    rw [ha]
    exact (canonical33649 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2471 + difference 3 4) (sourceB2471 + difference 4 3) sourceC2471) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4799) := by
    have ha : (tripleCharges (sourceA2471 + difference 3 4) (sourceB2471 + difference 4 3) sourceC2471) = raw33987 := by
      apply Matrix.ext; unfold tripleCharges sourceA2471 sourceB2471 sourceC2471 difference raw33987; decide +kernel
    rw [ha]
    exact (canonical33987 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2471 + difference 3 5) (sourceB2471 + difference 5 3) sourceC2471) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4803) := by
    have ha : (tripleCharges (sourceA2471 + difference 3 5) (sourceB2471 + difference 5 3) sourceC2471) = raw33868 := by
      apply Matrix.ext; unfold tripleCharges sourceA2471 sourceB2471 sourceC2471 difference raw33868; decide +kernel
    rw [ha]
    exact (canonical33868 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2471 + difference 4 0) (sourceB2471 + difference 0 4) sourceC2471) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4417) := by
    have ha : (tripleCharges (sourceA2471 + difference 4 0) (sourceB2471 + difference 0 4) sourceC2471) = raw33873 := by
      apply Matrix.ext; unfold tripleCharges sourceA2471 sourceB2471 sourceC2471 difference raw33873; decide +kernel
    rw [ha]
    exact (canonical33873 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2471 + difference 4 1) (sourceB2471 + difference 1 4) sourceC2471) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4739) := by
    have ha : (tripleCharges (sourceA2471 + difference 4 1) (sourceB2471 + difference 1 4) sourceC2471) = raw33145 := by
      apply Matrix.ext; unfold tripleCharges sourceA2471 sourceB2471 sourceC2471 difference raw33145; decide +kernel
    rw [ha]
    exact (canonical33145 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2471 + difference 4 2) (sourceB2471 + difference 2 4) sourceC2471) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4838) := by
    have ha : (tripleCharges (sourceA2471 + difference 4 2) (sourceB2471 + difference 2 4) sourceC2471) = raw32250 := by
      apply Matrix.ext; unfold tripleCharges sourceA2471 sourceB2471 sourceC2471 difference raw32250; decide +kernel
    rw [ha]
    exact (canonical32250 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2471 + difference 4 3) (sourceB2471 + difference 3 4) sourceC2471) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA2471 + difference 4 3) (sourceB2471 + difference 3 4) sourceC2471) = raw32330 := by
      apply Matrix.ext; unfold tripleCharges sourceA2471 sourceB2471 sourceC2471 difference raw32330; decide +kernel
    rw [ha]
    exact (canonical32330 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2471 + difference 4 5) (sourceB2471 + difference 5 4) sourceC2471) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4805) := by
    have ha : (tripleCharges (sourceA2471 + difference 4 5) (sourceB2471 + difference 5 4) sourceC2471) = raw32235 := by
      apply Matrix.ext; unfold tripleCharges sourceA2471 sourceB2471 sourceC2471 difference raw32235; decide +kernel
    rw [ha]
    exact (canonical32235 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2471 + difference 5 0) (sourceB2471 + difference 0 5) sourceC2471) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4396) := by
    have ha : (tripleCharges (sourceA2471 + difference 5 0) (sourceB2471 + difference 0 5) sourceC2471) = raw33988 := by
      apply Matrix.ext; unfold tripleCharges sourceA2471 sourceB2471 sourceC2471 difference raw33988; decide +kernel
    rw [ha]
    exact (canonical33988 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2471 + difference 5 1) (sourceB2471 + difference 1 5) sourceC2471) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4736) := by
    have ha : (tripleCharges (sourceA2471 + difference 5 1) (sourceB2471 + difference 1 5) sourceC2471) = raw33147 := by
      apply Matrix.ext; unfold tripleCharges sourceA2471 sourceB2471 sourceC2471 difference raw33147; decide +kernel
    rw [ha]
    exact (canonical33147 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2471 + difference 5 2) (sourceB2471 + difference 2 5) sourceC2471) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4834) := by
    have ha : (tripleCharges (sourceA2471 + difference 5 2) (sourceB2471 + difference 2 5) sourceC2471) = raw32835 := by
      apply Matrix.ext; unfold tripleCharges sourceA2471 sourceB2471 sourceC2471 difference raw32835; decide +kernel
    rw [ha]
    exact (canonical32835 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2471 + difference 5 3) (sourceB2471 + difference 3 5) sourceC2471) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4801) := by
    have ha : (tripleCharges (sourceA2471 + difference 5 3) (sourceB2471 + difference 3 5) sourceC2471) = raw32333 := by
      apply Matrix.ext; unfold tripleCharges sourceA2471 sourceB2471 sourceC2471 difference raw32333; decide +kernel
    rw [ha]
    exact (canonical32333 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2471 + difference 5 4) (sourceB2471 + difference 4 5) sourceC2471) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4798) := by
    have ha : (tripleCharges (sourceA2471 + difference 5 4) (sourceB2471 + difference 4 5) sourceC2471) = raw32827 := by
      apply Matrix.ext; unfold tripleCharges sourceA2471 sourceB2471 sourceC2471 difference raw32827; decide +kernel
    rw [ha]
    exact (canonical32827 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2471 sourceB2471 sourceC2471
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2471, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2472 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2472 : Charge := ![0, 1, 1, -1, -1, 0]
def sourceC2472 : Charge := ![3, 0, -1, 0, 0, -2]
def sourceForm2472 : Integer.Sparse Master := [(Sum.inr 4326, 1), (Sum.inr 4328, 2), (Sum.inr 4341, 1), (Sum.inr 4457, 1), (Sum.inr 4663, 1), (Sum.inr 4665, 2), (Sum.inr 4676, 1), (Sum.inr 4771, 1), (Sum.inr 4773, 2), (Sum.inr 4803, 2), (Sum.inr 4804, 2), (Sum.inr 4810, 2), (Sum.inr 4831, 1), (Sum.inr 4834, 2), (Sum.inr 4865, 1), (Sum.inr 4888, 1), (Sum.inr 4894, 2), (Sum.inr 5219, 1), (Sum.inr 5249, 1), (Sum.inr 5250, 1), (Sum.inr 5258, 2)]

theorem sourceEq2472 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2472 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2472 + difference 0 1) (sourceB2472 + difference 1 0) sourceC2472) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5219) := by
    have ha : (tripleCharges (sourceA2472 + difference 0 1) (sourceB2472 + difference 1 0) sourceC2472) = raw33989 := by
      apply Matrix.ext; unfold tripleCharges sourceA2472 sourceB2472 sourceC2472 difference raw33989; decide +kernel
    rw [ha]
    exact (canonical33989 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2472 + difference 0 2) (sourceB2472 + difference 2 0) sourceC2472) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5249) := by
    have ha : (tripleCharges (sourceA2472 + difference 0 2) (sourceB2472 + difference 2 0) sourceC2472) = raw33990 := by
      apply Matrix.ext; unfold tripleCharges sourceA2472 sourceB2472 sourceC2472 difference raw33990; decide +kernel
    rw [ha]
    exact (canonical33990 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2472 + difference 0 3) (sourceB2472 + difference 3 0) sourceC2472) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA2472 + difference 0 3) (sourceB2472 + difference 3 0) sourceC2472) = raw33991 := by
      apply Matrix.ext; unfold tripleCharges sourceA2472 sourceB2472 sourceC2472 difference raw33991; decide +kernel
    rw [ha]
    exact (canonical33991 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2472 + difference 0 4) (sourceB2472 + difference 4 0) sourceC2472) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA2472 + difference 0 4) (sourceB2472 + difference 4 0) sourceC2472) = raw33992 := by
      apply Matrix.ext; unfold tripleCharges sourceA2472 sourceB2472 sourceC2472 difference raw33992; decide +kernel
    rw [ha]
    exact (canonical33992 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2472 + difference 0 5) (sourceB2472 + difference 5 0) sourceC2472) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5250) := by
    have ha : (tripleCharges (sourceA2472 + difference 0 5) (sourceB2472 + difference 5 0) sourceC2472) = raw33993 := by
      apply Matrix.ext; unfold tripleCharges sourceA2472 sourceB2472 sourceC2472 difference raw33993; decide +kernel
    rw [ha]
    exact (canonical33993 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2472 + difference 1 0) (sourceB2472 + difference 0 1) sourceC2472) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4457) := by
    have ha : (tripleCharges (sourceA2472 + difference 1 0) (sourceB2472 + difference 0 1) sourceC2472) = raw33994 := by
      apply Matrix.ext; unfold tripleCharges sourceA2472 sourceB2472 sourceC2472 difference raw33994; decide +kernel
    rw [ha]
    exact (canonical33994 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2472 + difference 1 2) (sourceB2472 + difference 2 1) sourceC2472) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4865) := by
    have ha : (tripleCharges (sourceA2472 + difference 1 2) (sourceB2472 + difference 2 1) sourceC2472) = raw33995 := by
      apply Matrix.ext; unfold tripleCharges sourceA2472 sourceB2472 sourceC2472 difference raw33995; decide +kernel
    rw [ha]
    exact (canonical33995 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2472 + difference 1 3) (sourceB2472 + difference 3 1) sourceC2472) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4894) := by
    have ha : (tripleCharges (sourceA2472 + difference 1 3) (sourceB2472 + difference 3 1) sourceC2472) = raw33996 := by
      apply Matrix.ext; unfold tripleCharges sourceA2472 sourceB2472 sourceC2472 difference raw33996; decide +kernel
    rw [ha]
    exact (canonical33996 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2472 + difference 1 4) (sourceB2472 + difference 4 1) sourceC2472) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4894) := by
    have ha : (tripleCharges (sourceA2472 + difference 1 4) (sourceB2472 + difference 4 1) sourceC2472) = raw33997 := by
      apply Matrix.ext; unfold tripleCharges sourceA2472 sourceB2472 sourceC2472 difference raw33997; decide +kernel
    rw [ha]
    exact (canonical33997 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2472 + difference 1 5) (sourceB2472 + difference 5 1) sourceC2472) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA2472 + difference 1 5) (sourceB2472 + difference 5 1) sourceC2472) = raw33998 := by
      apply Matrix.ext; unfold tripleCharges sourceA2472 sourceB2472 sourceC2472 difference raw33998; decide +kernel
    rw [ha]
    exact (canonical33998 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2472 + difference 2 0) (sourceB2472 + difference 0 2) sourceC2472) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4341) := by
    have ha : (tripleCharges (sourceA2472 + difference 2 0) (sourceB2472 + difference 0 2) sourceC2472) = raw33999 := by
      apply Matrix.ext; unfold tripleCharges sourceA2472 sourceB2472 sourceC2472 difference raw33999; decide +kernel
    rw [ha]
    exact (canonical33999 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2472 + difference 2 1) (sourceB2472 + difference 1 2) sourceC2472) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4676) := by
    have ha : (tripleCharges (sourceA2472 + difference 2 1) (sourceB2472 + difference 1 2) sourceC2472) = raw34000 := by
      apply Matrix.ext; unfold tripleCharges sourceA2472 sourceB2472 sourceC2472 difference raw34000; decide +kernel
    rw [ha]
    exact (canonical34000 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2472 + difference 2 3) (sourceB2472 + difference 3 2) sourceC2472) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4834) := by
    have ha : (tripleCharges (sourceA2472 + difference 2 3) (sourceB2472 + difference 3 2) sourceC2472) = raw34001 := by
      apply Matrix.ext; unfold tripleCharges sourceA2472 sourceB2472 sourceC2472 difference raw34001; decide +kernel
    rw [ha]
    exact (canonical34001 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2472 + difference 2 4) (sourceB2472 + difference 4 2) sourceC2472) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4834) := by
    have ha : (tripleCharges (sourceA2472 + difference 2 4) (sourceB2472 + difference 4 2) sourceC2472) = raw34002 := by
      apply Matrix.ext; unfold tripleCharges sourceA2472 sourceB2472 sourceC2472 difference raw34002; decide +kernel
    rw [ha]
    exact (canonical34002 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2472 + difference 2 5) (sourceB2472 + difference 5 2) sourceC2472) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4831) := by
    have ha : (tripleCharges (sourceA2472 + difference 2 5) (sourceB2472 + difference 5 2) sourceC2472) = raw34003 := by
      apply Matrix.ext; unfold tripleCharges sourceA2472 sourceB2472 sourceC2472 difference raw34003; decide +kernel
    rw [ha]
    exact (canonical34003 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2472 + difference 3 0) (sourceB2472 + difference 0 3) sourceC2472) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4328) := by
    have ha : (tripleCharges (sourceA2472 + difference 3 0) (sourceB2472 + difference 0 3) sourceC2472) = raw34004 := by
      apply Matrix.ext; unfold tripleCharges sourceA2472 sourceB2472 sourceC2472 difference raw34004; decide +kernel
    rw [ha]
    exact (canonical34004 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2472 + difference 3 1) (sourceB2472 + difference 1 3) sourceC2472) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4665) := by
    have ha : (tripleCharges (sourceA2472 + difference 3 1) (sourceB2472 + difference 1 3) sourceC2472) = raw34005 := by
      apply Matrix.ext; unfold tripleCharges sourceA2472 sourceB2472 sourceC2472 difference raw34005; decide +kernel
    rw [ha]
    exact (canonical34005 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2472 + difference 3 2) (sourceB2472 + difference 2 3) sourceC2472) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4773) := by
    have ha : (tripleCharges (sourceA2472 + difference 3 2) (sourceB2472 + difference 2 3) sourceC2472) = raw34006 := by
      apply Matrix.ext; unfold tripleCharges sourceA2472 sourceB2472 sourceC2472 difference raw34006; decide +kernel
    rw [ha]
    exact (canonical34006 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2472 + difference 3 4) (sourceB2472 + difference 4 3) sourceC2472) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4810) := by
    have ha : (tripleCharges (sourceA2472 + difference 3 4) (sourceB2472 + difference 4 3) sourceC2472) = raw34007 := by
      apply Matrix.ext; unfold tripleCharges sourceA2472 sourceB2472 sourceC2472 difference raw34007; decide +kernel
    rw [ha]
    exact (canonical34007 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2472 + difference 3 5) (sourceB2472 + difference 5 3) sourceC2472) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4803) := by
    have ha : (tripleCharges (sourceA2472 + difference 3 5) (sourceB2472 + difference 5 3) sourceC2472) = raw34008 := by
      apply Matrix.ext; unfold tripleCharges sourceA2472 sourceB2472 sourceC2472 difference raw34008; decide +kernel
    rw [ha]
    exact (canonical34008 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2472 + difference 4 0) (sourceB2472 + difference 0 4) sourceC2472) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4328) := by
    have ha : (tripleCharges (sourceA2472 + difference 4 0) (sourceB2472 + difference 0 4) sourceC2472) = raw34009 := by
      apply Matrix.ext; unfold tripleCharges sourceA2472 sourceB2472 sourceC2472 difference raw34009; decide +kernel
    rw [ha]
    exact (canonical34009 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2472 + difference 4 1) (sourceB2472 + difference 1 4) sourceC2472) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4665) := by
    have ha : (tripleCharges (sourceA2472 + difference 4 1) (sourceB2472 + difference 1 4) sourceC2472) = raw34010 := by
      apply Matrix.ext; unfold tripleCharges sourceA2472 sourceB2472 sourceC2472 difference raw34010; decide +kernel
    rw [ha]
    exact (canonical34010 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2472 + difference 4 2) (sourceB2472 + difference 2 4) sourceC2472) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4773) := by
    have ha : (tripleCharges (sourceA2472 + difference 4 2) (sourceB2472 + difference 2 4) sourceC2472) = raw34011 := by
      apply Matrix.ext; unfold tripleCharges sourceA2472 sourceB2472 sourceC2472 difference raw34011; decide +kernel
    rw [ha]
    exact (canonical34011 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2472 + difference 4 3) (sourceB2472 + difference 3 4) sourceC2472) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4810) := by
    have ha : (tripleCharges (sourceA2472 + difference 4 3) (sourceB2472 + difference 3 4) sourceC2472) = raw34012 := by
      apply Matrix.ext; unfold tripleCharges sourceA2472 sourceB2472 sourceC2472 difference raw34012; decide +kernel
    rw [ha]
    exact (canonical34012 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2472 + difference 4 5) (sourceB2472 + difference 5 4) sourceC2472) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4803) := by
    have ha : (tripleCharges (sourceA2472 + difference 4 5) (sourceB2472 + difference 5 4) sourceC2472) = raw34013 := by
      apply Matrix.ext; unfold tripleCharges sourceA2472 sourceB2472 sourceC2472 difference raw34013; decide +kernel
    rw [ha]
    exact (canonical34013 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2472 + difference 5 0) (sourceB2472 + difference 0 5) sourceC2472) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4326) := by
    have ha : (tripleCharges (sourceA2472 + difference 5 0) (sourceB2472 + difference 0 5) sourceC2472) = raw34014 := by
      apply Matrix.ext; unfold tripleCharges sourceA2472 sourceB2472 sourceC2472 difference raw34014; decide +kernel
    rw [ha]
    exact (canonical34014 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2472 + difference 5 1) (sourceB2472 + difference 1 5) sourceC2472) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4663) := by
    have ha : (tripleCharges (sourceA2472 + difference 5 1) (sourceB2472 + difference 1 5) sourceC2472) = raw34015 := by
      apply Matrix.ext; unfold tripleCharges sourceA2472 sourceB2472 sourceC2472 difference raw34015; decide +kernel
    rw [ha]
    exact (canonical34015 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2472 + difference 5 2) (sourceB2472 + difference 2 5) sourceC2472) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4771) := by
    have ha : (tripleCharges (sourceA2472 + difference 5 2) (sourceB2472 + difference 2 5) sourceC2472) = raw34016 := by
      apply Matrix.ext; unfold tripleCharges sourceA2472 sourceB2472 sourceC2472 difference raw34016; decide +kernel
    rw [ha]
    exact (canonical34016 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2472 + difference 5 3) (sourceB2472 + difference 3 5) sourceC2472) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA2472 + difference 5 3) (sourceB2472 + difference 3 5) sourceC2472) = raw34017 := by
      apply Matrix.ext; unfold tripleCharges sourceA2472 sourceB2472 sourceC2472 difference raw34017; decide +kernel
    rw [ha]
    exact (canonical34017 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2472 + difference 5 4) (sourceB2472 + difference 4 5) sourceC2472) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA2472 + difference 5 4) (sourceB2472 + difference 4 5) sourceC2472) = raw34018 := by
      apply Matrix.ext; unfold tripleCharges sourceA2472 sourceB2472 sourceC2472 difference raw34018; decide +kernel
    rw [ha]
    exact (canonical34018 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2472 sourceB2472 sourceC2472
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2472, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2473 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2473 : Charge := ![0, 1, 1, -1, -1, 0]
def sourceC2473 : Charge := ![3, 0, -1, 0, 0, -2]
def sourceForm2473 : Integer.Sparse Master := [(Sum.inr 1329, 1), (Sum.inr 1330, 2), (Sum.inr 1341, 1), (Sum.inr 1414, 1), (Sum.inr 2890, 1), (Sum.inr 2895, 1), (Sum.inr 2941, 2), (Sum.inr 3065, 1), (Sum.inr 3066, 1), (Sum.inr 3069, 1), (Sum.inr 3089, 2), (Sum.inr 3134, 2), (Sum.inr 3140, 1), (Sum.inr 3163, 2), (Sum.inr 3185, 1), (Sum.inr 3202, 2), (Sum.inr 3206, 2), (Sum.inr 3209, 1), (Sum.inr 3214, 2), (Sum.inr 3227, 1), (Sum.inr 3230, 2)]

theorem sourceEq2473 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2473 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2473 + difference 0 1) (sourceB2473 + difference 1 0) sourceC2473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3069) := by
    have ha : (tripleCharges (sourceA2473 + difference 0 1) (sourceB2473 + difference 1 0) sourceC2473) = raw34019 := by
      apply Matrix.ext; unfold tripleCharges sourceA2473 sourceB2473 sourceC2473 difference raw34019; decide +kernel
    rw [ha]
    exact (canonical34019 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2473 + difference 0 2) (sourceB2473 + difference 2 0) sourceC2473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3066) := by
    have ha : (tripleCharges (sourceA2473 + difference 0 2) (sourceB2473 + difference 2 0) sourceC2473) = raw34020 := by
      apply Matrix.ext; unfold tripleCharges sourceA2473 sourceB2473 sourceC2473 difference raw34020; decide +kernel
    rw [ha]
    exact (canonical34020 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2473 + difference 0 3) (sourceB2473 + difference 3 0) sourceC2473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3089) := by
    have ha : (tripleCharges (sourceA2473 + difference 0 3) (sourceB2473 + difference 3 0) sourceC2473) = raw34021 := by
      apply Matrix.ext; unfold tripleCharges sourceA2473 sourceB2473 sourceC2473 difference raw34021; decide +kernel
    rw [ha]
    exact (canonical34021 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2473 + difference 0 4) (sourceB2473 + difference 4 0) sourceC2473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3089) := by
    have ha : (tripleCharges (sourceA2473 + difference 0 4) (sourceB2473 + difference 4 0) sourceC2473) = raw34022 := by
      apply Matrix.ext; unfold tripleCharges sourceA2473 sourceB2473 sourceC2473 difference raw34022; decide +kernel
    rw [ha]
    exact (canonical34022 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2473 + difference 0 5) (sourceB2473 + difference 5 0) sourceC2473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3065) := by
    have ha : (tripleCharges (sourceA2473 + difference 0 5) (sourceB2473 + difference 5 0) sourceC2473) = raw34023 := by
      apply Matrix.ext; unfold tripleCharges sourceA2473 sourceB2473 sourceC2473 difference raw34023; decide +kernel
    rw [ha]
    exact (canonical34023 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2473 + difference 1 0) (sourceB2473 + difference 0 1) sourceC2473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1414) := by
    have ha : (tripleCharges (sourceA2473 + difference 1 0) (sourceB2473 + difference 0 1) sourceC2473) = raw34024 := by
      apply Matrix.ext; unfold tripleCharges sourceA2473 sourceB2473 sourceC2473 difference raw34024; decide +kernel
    rw [ha]
    exact (canonical34024 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2473 + difference 1 2) (sourceB2473 + difference 2 1) sourceC2473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3185) := by
    have ha : (tripleCharges (sourceA2473 + difference 1 2) (sourceB2473 + difference 2 1) sourceC2473) = raw34025 := by
      apply Matrix.ext; unfold tripleCharges sourceA2473 sourceB2473 sourceC2473 difference raw34025; decide +kernel
    rw [ha]
    exact (canonical34025 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2473 + difference 1 3) (sourceB2473 + difference 3 1) sourceC2473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3230) := by
    have ha : (tripleCharges (sourceA2473 + difference 1 3) (sourceB2473 + difference 3 1) sourceC2473) = raw34026 := by
      apply Matrix.ext; unfold tripleCharges sourceA2473 sourceB2473 sourceC2473 difference raw34026; decide +kernel
    rw [ha]
    exact (canonical34026 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2473 + difference 1 4) (sourceB2473 + difference 4 1) sourceC2473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3230) := by
    have ha : (tripleCharges (sourceA2473 + difference 1 4) (sourceB2473 + difference 4 1) sourceC2473) = raw34027 := by
      apply Matrix.ext; unfold tripleCharges sourceA2473 sourceB2473 sourceC2473 difference raw34027; decide +kernel
    rw [ha]
    exact (canonical34027 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2473 + difference 1 5) (sourceB2473 + difference 5 1) sourceC2473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3227) := by
    have ha : (tripleCharges (sourceA2473 + difference 1 5) (sourceB2473 + difference 5 1) sourceC2473) = raw34028 := by
      apply Matrix.ext; unfold tripleCharges sourceA2473 sourceB2473 sourceC2473 difference raw34028; decide +kernel
    rw [ha]
    exact (canonical34028 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2473 + difference 2 0) (sourceB2473 + difference 0 2) sourceC2473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1341) := by
    have ha : (tripleCharges (sourceA2473 + difference 2 0) (sourceB2473 + difference 0 2) sourceC2473) = raw34029 := by
      apply Matrix.ext; unfold tripleCharges sourceA2473 sourceB2473 sourceC2473 difference raw34029; decide +kernel
    rw [ha]
    exact (canonical34029 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2473 + difference 2 1) (sourceB2473 + difference 1 2) sourceC2473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3140) := by
    have ha : (tripleCharges (sourceA2473 + difference 2 1) (sourceB2473 + difference 1 2) sourceC2473) = raw34030 := by
      apply Matrix.ext; unfold tripleCharges sourceA2473 sourceB2473 sourceC2473 difference raw34030; decide +kernel
    rw [ha]
    exact (canonical34030 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2473 + difference 2 3) (sourceB2473 + difference 3 2) sourceC2473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3214) := by
    have ha : (tripleCharges (sourceA2473 + difference 2 3) (sourceB2473 + difference 3 2) sourceC2473) = raw34031 := by
      apply Matrix.ext; unfold tripleCharges sourceA2473 sourceB2473 sourceC2473 difference raw34031; decide +kernel
    rw [ha]
    exact (canonical34031 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2473 + difference 2 4) (sourceB2473 + difference 4 2) sourceC2473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3214) := by
    have ha : (tripleCharges (sourceA2473 + difference 2 4) (sourceB2473 + difference 4 2) sourceC2473) = raw34032 := by
      apply Matrix.ext; unfold tripleCharges sourceA2473 sourceB2473 sourceC2473 difference raw34032; decide +kernel
    rw [ha]
    exact (canonical34032 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2473 + difference 2 5) (sourceB2473 + difference 5 2) sourceC2473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3209) := by
    have ha : (tripleCharges (sourceA2473 + difference 2 5) (sourceB2473 + difference 5 2) sourceC2473) = raw34033 := by
      apply Matrix.ext; unfold tripleCharges sourceA2473 sourceB2473 sourceC2473 difference raw34033; decide +kernel
    rw [ha]
    exact (canonical34033 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2473 + difference 3 0) (sourceB2473 + difference 0 3) sourceC2473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1330) := by
    have ha : (tripleCharges (sourceA2473 + difference 3 0) (sourceB2473 + difference 0 3) sourceC2473) = raw34034 := by
      apply Matrix.ext; unfold tripleCharges sourceA2473 sourceB2473 sourceC2473 difference raw34034; decide +kernel
    rw [ha]
    exact (canonical34034 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2473 + difference 3 1) (sourceB2473 + difference 1 3) sourceC2473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3134) := by
    have ha : (tripleCharges (sourceA2473 + difference 3 1) (sourceB2473 + difference 1 3) sourceC2473) = raw34035 := by
      apply Matrix.ext; unfold tripleCharges sourceA2473 sourceB2473 sourceC2473 difference raw34035; decide +kernel
    rw [ha]
    exact (canonical34035 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2473 + difference 3 2) (sourceB2473 + difference 2 3) sourceC2473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3163) := by
    have ha : (tripleCharges (sourceA2473 + difference 3 2) (sourceB2473 + difference 2 3) sourceC2473) = raw34036 := by
      apply Matrix.ext; unfold tripleCharges sourceA2473 sourceB2473 sourceC2473 difference raw34036; decide +kernel
    rw [ha]
    exact (canonical34036 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2473 + difference 3 4) (sourceB2473 + difference 4 3) sourceC2473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3206) := by
    have ha : (tripleCharges (sourceA2473 + difference 3 4) (sourceB2473 + difference 4 3) sourceC2473) = raw34037 := by
      apply Matrix.ext; unfold tripleCharges sourceA2473 sourceB2473 sourceC2473 difference raw34037; decide +kernel
    rw [ha]
    exact (canonical34037 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2473 + difference 3 5) (sourceB2473 + difference 5 3) sourceC2473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3202) := by
    have ha : (tripleCharges (sourceA2473 + difference 3 5) (sourceB2473 + difference 5 3) sourceC2473) = raw34038 := by
      apply Matrix.ext; unfold tripleCharges sourceA2473 sourceB2473 sourceC2473 difference raw34038; decide +kernel
    rw [ha]
    exact (canonical34038 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2473 + difference 4 0) (sourceB2473 + difference 0 4) sourceC2473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1330) := by
    have ha : (tripleCharges (sourceA2473 + difference 4 0) (sourceB2473 + difference 0 4) sourceC2473) = raw34039 := by
      apply Matrix.ext; unfold tripleCharges sourceA2473 sourceB2473 sourceC2473 difference raw34039; decide +kernel
    rw [ha]
    exact (canonical34039 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2473 + difference 4 1) (sourceB2473 + difference 1 4) sourceC2473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3134) := by
    have ha : (tripleCharges (sourceA2473 + difference 4 1) (sourceB2473 + difference 1 4) sourceC2473) = raw34040 := by
      apply Matrix.ext; unfold tripleCharges sourceA2473 sourceB2473 sourceC2473 difference raw34040; decide +kernel
    rw [ha]
    exact (canonical34040 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2473 + difference 4 2) (sourceB2473 + difference 2 4) sourceC2473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3163) := by
    have ha : (tripleCharges (sourceA2473 + difference 4 2) (sourceB2473 + difference 2 4) sourceC2473) = raw34041 := by
      apply Matrix.ext; unfold tripleCharges sourceA2473 sourceB2473 sourceC2473 difference raw34041; decide +kernel
    rw [ha]
    exact (canonical34041 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2473 + difference 4 3) (sourceB2473 + difference 3 4) sourceC2473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3206) := by
    have ha : (tripleCharges (sourceA2473 + difference 4 3) (sourceB2473 + difference 3 4) sourceC2473) = raw34042 := by
      apply Matrix.ext; unfold tripleCharges sourceA2473 sourceB2473 sourceC2473 difference raw34042; decide +kernel
    rw [ha]
    exact (canonical34042 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2473 + difference 4 5) (sourceB2473 + difference 5 4) sourceC2473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3202) := by
    have ha : (tripleCharges (sourceA2473 + difference 4 5) (sourceB2473 + difference 5 4) sourceC2473) = raw34043 := by
      apply Matrix.ext; unfold tripleCharges sourceA2473 sourceB2473 sourceC2473 difference raw34043; decide +kernel
    rw [ha]
    exact (canonical34043 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2473 + difference 5 0) (sourceB2473 + difference 0 5) sourceC2473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1329) := by
    have ha : (tripleCharges (sourceA2473 + difference 5 0) (sourceB2473 + difference 0 5) sourceC2473) = raw34044 := by
      apply Matrix.ext; unfold tripleCharges sourceA2473 sourceB2473 sourceC2473 difference raw34044; decide +kernel
    rw [ha]
    exact (canonical34044 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2473 + difference 5 1) (sourceB2473 + difference 1 5) sourceC2473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2890) := by
    have ha : (tripleCharges (sourceA2473 + difference 5 1) (sourceB2473 + difference 1 5) sourceC2473) = raw34045 := by
      apply Matrix.ext; unfold tripleCharges sourceA2473 sourceB2473 sourceC2473 difference raw34045; decide +kernel
    rw [ha]
    exact (canonical34045 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2473 + difference 5 2) (sourceB2473 + difference 2 5) sourceC2473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2895) := by
    have ha : (tripleCharges (sourceA2473 + difference 5 2) (sourceB2473 + difference 2 5) sourceC2473) = raw34046 := by
      apply Matrix.ext; unfold tripleCharges sourceA2473 sourceB2473 sourceC2473 difference raw34046; decide +kernel
    rw [ha]
    exact (canonical34046 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2473 + difference 5 3) (sourceB2473 + difference 3 5) sourceC2473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2941) := by
    have ha : (tripleCharges (sourceA2473 + difference 5 3) (sourceB2473 + difference 3 5) sourceC2473) = raw34047 := by
      apply Matrix.ext; unfold tripleCharges sourceA2473 sourceB2473 sourceC2473 difference raw34047; decide +kernel
    rw [ha]
    exact (canonical34047 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2473 + difference 5 4) (sourceB2473 + difference 4 5) sourceC2473) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2941) := by
    have ha : (tripleCharges (sourceA2473 + difference 5 4) (sourceB2473 + difference 4 5) sourceC2473) = raw34048 := by
      apply Matrix.ext; unfold tripleCharges sourceA2473 sourceB2473 sourceC2473 difference raw34048; decide +kernel
    rw [ha]
    exact (canonical34048 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2473 sourceB2473 sourceC2473
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2473, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2474 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2474 : Charge := ![0, 1, 1, -1, -1, 0]
def sourceC2474 : Charge := ![3, 0, -1, 0, 0, -2]
def sourceForm2474 : Integer.Sparse Master := [(Sum.inr 1663, 1), (Sum.inr 1664, 1), (Sum.inr 1667, 2), (Sum.inr 1707, 1), (Sum.inr 2140, 1), (Sum.inr 2141, 1), (Sum.inr 2144, 2), (Sum.inr 2189, 1), (Sum.inr 2191, 1), (Sum.inr 2194, 2), (Sum.inr 2195, 2), (Sum.inr 2203, 2), (Sum.inr 2205, 2), (Sum.inr 2215, 2), (Sum.inr 2242, 1), (Sum.inr 2244, 1), (Sum.inr 2264, 2), (Sum.inr 2661, 1), (Sum.inr 2708, 1), (Sum.inr 2709, 1), (Sum.inr 2722, 2)]

theorem sourceEq2474 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2474 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2474 + difference 0 1) (sourceB2474 + difference 1 0) sourceC2474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2661) := by
    have ha : (tripleCharges (sourceA2474 + difference 0 1) (sourceB2474 + difference 1 0) sourceC2474) = raw34049 := by
      apply Matrix.ext; unfold tripleCharges sourceA2474 sourceB2474 sourceC2474 difference raw34049; decide +kernel
    rw [ha]
    exact (canonical34049 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2474 + difference 0 2) (sourceB2474 + difference 2 0) sourceC2474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2708) := by
    have ha : (tripleCharges (sourceA2474 + difference 0 2) (sourceB2474 + difference 2 0) sourceC2474) = raw34050 := by
      apply Matrix.ext; unfold tripleCharges sourceA2474 sourceB2474 sourceC2474 difference raw34050; decide +kernel
    rw [ha]
    exact (canonical34050 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2474 + difference 0 3) (sourceB2474 + difference 3 0) sourceC2474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA2474 + difference 0 3) (sourceB2474 + difference 3 0) sourceC2474) = raw34051 := by
      apply Matrix.ext; unfold tripleCharges sourceA2474 sourceB2474 sourceC2474 difference raw34051; decide +kernel
    rw [ha]
    exact (canonical34051 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2474 + difference 0 4) (sourceB2474 + difference 4 0) sourceC2474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA2474 + difference 0 4) (sourceB2474 + difference 4 0) sourceC2474) = raw34052 := by
      apply Matrix.ext; unfold tripleCharges sourceA2474 sourceB2474 sourceC2474 difference raw34052; decide +kernel
    rw [ha]
    exact (canonical34052 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2474 + difference 0 5) (sourceB2474 + difference 5 0) sourceC2474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2709) := by
    have ha : (tripleCharges (sourceA2474 + difference 0 5) (sourceB2474 + difference 5 0) sourceC2474) = raw34053 := by
      apply Matrix.ext; unfold tripleCharges sourceA2474 sourceB2474 sourceC2474 difference raw34053; decide +kernel
    rw [ha]
    exact (canonical34053 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2474 + difference 1 0) (sourceB2474 + difference 0 1) sourceC2474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1707) := by
    have ha : (tripleCharges (sourceA2474 + difference 1 0) (sourceB2474 + difference 0 1) sourceC2474) = raw34054 := by
      apply Matrix.ext; unfold tripleCharges sourceA2474 sourceB2474 sourceC2474 difference raw34054; decide +kernel
    rw [ha]
    exact (canonical34054 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2474 + difference 1 2) (sourceB2474 + difference 2 1) sourceC2474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2242) := by
    have ha : (tripleCharges (sourceA2474 + difference 1 2) (sourceB2474 + difference 2 1) sourceC2474) = raw34055 := by
      apply Matrix.ext; unfold tripleCharges sourceA2474 sourceB2474 sourceC2474 difference raw34055; decide +kernel
    rw [ha]
    exact (canonical34055 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2474 + difference 1 3) (sourceB2474 + difference 3 1) sourceC2474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2264) := by
    have ha : (tripleCharges (sourceA2474 + difference 1 3) (sourceB2474 + difference 3 1) sourceC2474) = raw34056 := by
      apply Matrix.ext; unfold tripleCharges sourceA2474 sourceB2474 sourceC2474 difference raw34056; decide +kernel
    rw [ha]
    exact (canonical34056 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2474 + difference 1 4) (sourceB2474 + difference 4 1) sourceC2474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2264) := by
    have ha : (tripleCharges (sourceA2474 + difference 1 4) (sourceB2474 + difference 4 1) sourceC2474) = raw34057 := by
      apply Matrix.ext; unfold tripleCharges sourceA2474 sourceB2474 sourceC2474 difference raw34057; decide +kernel
    rw [ha]
    exact (canonical34057 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2474 + difference 1 5) (sourceB2474 + difference 5 1) sourceC2474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2244) := by
    have ha : (tripleCharges (sourceA2474 + difference 1 5) (sourceB2474 + difference 5 1) sourceC2474) = raw34058 := by
      apply Matrix.ext; unfold tripleCharges sourceA2474 sourceB2474 sourceC2474 difference raw34058; decide +kernel
    rw [ha]
    exact (canonical34058 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2474 + difference 2 0) (sourceB2474 + difference 0 2) sourceC2474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1664) := by
    have ha : (tripleCharges (sourceA2474 + difference 2 0) (sourceB2474 + difference 0 2) sourceC2474) = raw34059 := by
      apply Matrix.ext; unfold tripleCharges sourceA2474 sourceB2474 sourceC2474 difference raw34059; decide +kernel
    rw [ha]
    exact (canonical34059 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2474 + difference 2 1) (sourceB2474 + difference 1 2) sourceC2474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2141) := by
    have ha : (tripleCharges (sourceA2474 + difference 2 1) (sourceB2474 + difference 1 2) sourceC2474) = raw34060 := by
      apply Matrix.ext; unfold tripleCharges sourceA2474 sourceB2474 sourceC2474 difference raw34060; decide +kernel
    rw [ha]
    exact (canonical34060 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2474 + difference 2 3) (sourceB2474 + difference 3 2) sourceC2474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2205) := by
    have ha : (tripleCharges (sourceA2474 + difference 2 3) (sourceB2474 + difference 3 2) sourceC2474) = raw34061 := by
      apply Matrix.ext; unfold tripleCharges sourceA2474 sourceB2474 sourceC2474 difference raw34061; decide +kernel
    rw [ha]
    exact (canonical34061 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2474 + difference 2 4) (sourceB2474 + difference 4 2) sourceC2474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2205) := by
    have ha : (tripleCharges (sourceA2474 + difference 2 4) (sourceB2474 + difference 4 2) sourceC2474) = raw34062 := by
      apply Matrix.ext; unfold tripleCharges sourceA2474 sourceB2474 sourceC2474 difference raw34062; decide +kernel
    rw [ha]
    exact (canonical34062 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2474 + difference 2 5) (sourceB2474 + difference 5 2) sourceC2474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2191) := by
    have ha : (tripleCharges (sourceA2474 + difference 2 5) (sourceB2474 + difference 5 2) sourceC2474) = raw34063 := by
      apply Matrix.ext; unfold tripleCharges sourceA2474 sourceB2474 sourceC2474 difference raw34063; decide +kernel
    rw [ha]
    exact (canonical34063 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2474 + difference 3 0) (sourceB2474 + difference 0 3) sourceC2474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1667) := by
    have ha : (tripleCharges (sourceA2474 + difference 3 0) (sourceB2474 + difference 0 3) sourceC2474) = raw34064 := by
      apply Matrix.ext; unfold tripleCharges sourceA2474 sourceB2474 sourceC2474 difference raw34064; decide +kernel
    rw [ha]
    exact (canonical34064 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2474 + difference 3 1) (sourceB2474 + difference 1 3) sourceC2474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2144) := by
    have ha : (tripleCharges (sourceA2474 + difference 3 1) (sourceB2474 + difference 1 3) sourceC2474) = raw34065 := by
      apply Matrix.ext; unfold tripleCharges sourceA2474 sourceB2474 sourceC2474 difference raw34065; decide +kernel
    rw [ha]
    exact (canonical34065 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2474 + difference 3 2) (sourceB2474 + difference 2 3) sourceC2474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2194) := by
    have ha : (tripleCharges (sourceA2474 + difference 3 2) (sourceB2474 + difference 2 3) sourceC2474) = raw34066 := by
      apply Matrix.ext; unfold tripleCharges sourceA2474 sourceB2474 sourceC2474 difference raw34066; decide +kernel
    rw [ha]
    exact (canonical34066 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2474 + difference 3 4) (sourceB2474 + difference 4 3) sourceC2474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2215) := by
    have ha : (tripleCharges (sourceA2474 + difference 3 4) (sourceB2474 + difference 4 3) sourceC2474) = raw34067 := by
      apply Matrix.ext; unfold tripleCharges sourceA2474 sourceB2474 sourceC2474 difference raw34067; decide +kernel
    rw [ha]
    exact (canonical34067 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2474 + difference 3 5) (sourceB2474 + difference 5 3) sourceC2474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2195) := by
    have ha : (tripleCharges (sourceA2474 + difference 3 5) (sourceB2474 + difference 5 3) sourceC2474) = raw34068 := by
      apply Matrix.ext; unfold tripleCharges sourceA2474 sourceB2474 sourceC2474 difference raw34068; decide +kernel
    rw [ha]
    exact (canonical34068 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2474 + difference 4 0) (sourceB2474 + difference 0 4) sourceC2474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1667) := by
    have ha : (tripleCharges (sourceA2474 + difference 4 0) (sourceB2474 + difference 0 4) sourceC2474) = raw34069 := by
      apply Matrix.ext; unfold tripleCharges sourceA2474 sourceB2474 sourceC2474 difference raw34069; decide +kernel
    rw [ha]
    exact (canonical34069 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2474 + difference 4 1) (sourceB2474 + difference 1 4) sourceC2474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2144) := by
    have ha : (tripleCharges (sourceA2474 + difference 4 1) (sourceB2474 + difference 1 4) sourceC2474) = raw34070 := by
      apply Matrix.ext; unfold tripleCharges sourceA2474 sourceB2474 sourceC2474 difference raw34070; decide +kernel
    rw [ha]
    exact (canonical34070 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2474 + difference 4 2) (sourceB2474 + difference 2 4) sourceC2474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2194) := by
    have ha : (tripleCharges (sourceA2474 + difference 4 2) (sourceB2474 + difference 2 4) sourceC2474) = raw34071 := by
      apply Matrix.ext; unfold tripleCharges sourceA2474 sourceB2474 sourceC2474 difference raw34071; decide +kernel
    rw [ha]
    exact (canonical34071 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2474 + difference 4 3) (sourceB2474 + difference 3 4) sourceC2474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2215) := by
    have ha : (tripleCharges (sourceA2474 + difference 4 3) (sourceB2474 + difference 3 4) sourceC2474) = raw34072 := by
      apply Matrix.ext; unfold tripleCharges sourceA2474 sourceB2474 sourceC2474 difference raw34072; decide +kernel
    rw [ha]
    exact (canonical34072 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2474 + difference 4 5) (sourceB2474 + difference 5 4) sourceC2474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2195) := by
    have ha : (tripleCharges (sourceA2474 + difference 4 5) (sourceB2474 + difference 5 4) sourceC2474) = raw34073 := by
      apply Matrix.ext; unfold tripleCharges sourceA2474 sourceB2474 sourceC2474 difference raw34073; decide +kernel
    rw [ha]
    exact (canonical34073 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2474 + difference 5 0) (sourceB2474 + difference 0 5) sourceC2474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1663) := by
    have ha : (tripleCharges (sourceA2474 + difference 5 0) (sourceB2474 + difference 0 5) sourceC2474) = raw34074 := by
      apply Matrix.ext; unfold tripleCharges sourceA2474 sourceB2474 sourceC2474 difference raw34074; decide +kernel
    rw [ha]
    exact (canonical34074 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2474 + difference 5 1) (sourceB2474 + difference 1 5) sourceC2474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2140) := by
    have ha : (tripleCharges (sourceA2474 + difference 5 1) (sourceB2474 + difference 1 5) sourceC2474) = raw34075 := by
      apply Matrix.ext; unfold tripleCharges sourceA2474 sourceB2474 sourceC2474 difference raw34075; decide +kernel
    rw [ha]
    exact (canonical34075 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2474 + difference 5 2) (sourceB2474 + difference 2 5) sourceC2474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2189) := by
    have ha : (tripleCharges (sourceA2474 + difference 5 2) (sourceB2474 + difference 2 5) sourceC2474) = raw34076 := by
      apply Matrix.ext; unfold tripleCharges sourceA2474 sourceB2474 sourceC2474 difference raw34076; decide +kernel
    rw [ha]
    exact (canonical34076 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2474 + difference 5 3) (sourceB2474 + difference 3 5) sourceC2474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2203) := by
    have ha : (tripleCharges (sourceA2474 + difference 5 3) (sourceB2474 + difference 3 5) sourceC2474) = raw34077 := by
      apply Matrix.ext; unfold tripleCharges sourceA2474 sourceB2474 sourceC2474 difference raw34077; decide +kernel
    rw [ha]
    exact (canonical34077 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2474 + difference 5 4) (sourceB2474 + difference 4 5) sourceC2474) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2203) := by
    have ha : (tripleCharges (sourceA2474 + difference 5 4) (sourceB2474 + difference 4 5) sourceC2474) = raw34078 := by
      apply Matrix.ext; unfold tripleCharges sourceA2474 sourceB2474 sourceC2474 difference raw34078; decide +kernel
    rw [ha]
    exact (canonical34078 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2474 sourceB2474 sourceC2474
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2474, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2475 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2475 : Charge := ![3, 0, -1, 0, 0, -2]
def sourceC2475 : Charge := ![0, 1, 1, -1, -1, 0]
def sourceForm2475 : Integer.Sparse Master := [(Sum.inr 4195, 1), (Sum.inr 4197, 2), (Sum.inr 4207, 1), (Sum.inr 4248, 1), (Sum.inr 4630, 1), (Sum.inr 4632, 2), (Sum.inr 4640, 1), (Sum.inr 4759, 1), (Sum.inr 4763, 2), (Sum.inr 4778, 2), (Sum.inr 4782, 4), (Sum.inr 4801, 3), (Sum.inr 4802, 2), (Sum.inr 4831, 1), (Sum.inr 4887, 1), (Sum.inr 5351, 1), (Sum.inr 5415, 1), (Sum.inr 5423, 2), (Sum.inr 5433, 1)]

theorem sourceEq2475 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2475 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2475 + difference 0 1) (sourceB2475 + difference 1 0) sourceC2475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5351) := by
    have ha : (tripleCharges (sourceA2475 + difference 0 1) (sourceB2475 + difference 1 0) sourceC2475) = raw18280 := by
      apply Matrix.ext; unfold tripleCharges sourceA2475 sourceB2475 sourceC2475 difference raw18280; decide +kernel
    rw [ha]
    exact (canonical18280 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2475 + difference 0 2) (sourceB2475 + difference 2 0) sourceC2475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5415) := by
    have ha : (tripleCharges (sourceA2475 + difference 0 2) (sourceB2475 + difference 2 0) sourceC2475) = raw18281 := by
      apply Matrix.ext; unfold tripleCharges sourceA2475 sourceB2475 sourceC2475 difference raw18281; decide +kernel
    rw [ha]
    exact (canonical18281 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2475 + difference 0 3) (sourceB2475 + difference 3 0) sourceC2475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5423) := by
    have ha : (tripleCharges (sourceA2475 + difference 0 3) (sourceB2475 + difference 3 0) sourceC2475) = raw18402 := by
      apply Matrix.ext; unfold tripleCharges sourceA2475 sourceB2475 sourceC2475 difference raw18402; decide +kernel
    rw [ha]
    exact (canonical18402 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2475 + difference 0 4) (sourceB2475 + difference 4 0) sourceC2475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5423) := by
    have ha : (tripleCharges (sourceA2475 + difference 0 4) (sourceB2475 + difference 4 0) sourceC2475) = raw18282 := by
      apply Matrix.ext; unfold tripleCharges sourceA2475 sourceB2475 sourceC2475 difference raw18282; decide +kernel
    rw [ha]
    exact (canonical18282 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2475 + difference 0 5) (sourceB2475 + difference 5 0) sourceC2475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA2475 + difference 0 5) (sourceB2475 + difference 5 0) sourceC2475) = raw18283 := by
      apply Matrix.ext; unfold tripleCharges sourceA2475 sourceB2475 sourceC2475 difference raw18283; decide +kernel
    rw [ha]
    exact (canonical18283 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2475 + difference 1 0) (sourceB2475 + difference 0 1) sourceC2475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4248) := by
    have ha : (tripleCharges (sourceA2475 + difference 1 0) (sourceB2475 + difference 0 1) sourceC2475) = raw34079 := by
      apply Matrix.ext; unfold tripleCharges sourceA2475 sourceB2475 sourceC2475 difference raw34079; decide +kernel
    rw [ha]
    exact (canonical34079 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2475 + difference 1 2) (sourceB2475 + difference 2 1) sourceC2475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4801) := by
    have ha : (tripleCharges (sourceA2475 + difference 1 2) (sourceB2475 + difference 2 1) sourceC2475) = raw34080 := by
      apply Matrix.ext; unfold tripleCharges sourceA2475 sourceB2475 sourceC2475 difference raw34080; decide +kernel
    rw [ha]
    exact (canonical34080 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2475 + difference 1 3) (sourceB2475 + difference 3 1) sourceC2475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4801) := by
    have ha : (tripleCharges (sourceA2475 + difference 1 3) (sourceB2475 + difference 3 1) sourceC2475) = raw18269 := by
      apply Matrix.ext; unfold tripleCharges sourceA2475 sourceB2475 sourceC2475 difference raw18269; decide +kernel
    rw [ha]
    exact (canonical18269 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2475 + difference 1 4) (sourceB2475 + difference 4 1) sourceC2475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4801) := by
    have ha : (tripleCharges (sourceA2475 + difference 1 4) (sourceB2475 + difference 4 1) sourceC2475) = raw34081 := by
      apply Matrix.ext; unfold tripleCharges sourceA2475 sourceB2475 sourceC2475 difference raw34081; decide +kernel
    rw [ha]
    exact (canonical34081 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2475 + difference 1 5) (sourceB2475 + difference 5 1) sourceC2475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4887) := by
    have ha : (tripleCharges (sourceA2475 + difference 1 5) (sourceB2475 + difference 5 1) sourceC2475) = raw18385 := by
      apply Matrix.ext; unfold tripleCharges sourceA2475 sourceB2475 sourceC2475 difference raw18385; decide +kernel
    rw [ha]
    exact (canonical18385 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2475 + difference 2 0) (sourceB2475 + difference 0 2) sourceC2475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4207) := by
    have ha : (tripleCharges (sourceA2475 + difference 2 0) (sourceB2475 + difference 0 2) sourceC2475) = raw34082 := by
      apply Matrix.ext; unfold tripleCharges sourceA2475 sourceB2475 sourceC2475 difference raw34082; decide +kernel
    rw [ha]
    exact (canonical34082 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2475 + difference 2 1) (sourceB2475 + difference 1 2) sourceC2475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4640) := by
    have ha : (tripleCharges (sourceA2475 + difference 2 1) (sourceB2475 + difference 1 2) sourceC2475) = raw34083 := by
      apply Matrix.ext; unfold tripleCharges sourceA2475 sourceB2475 sourceC2475 difference raw34083; decide +kernel
    rw [ha]
    exact (canonical34083 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2475 + difference 2 3) (sourceB2475 + difference 3 2) sourceC2475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4782) := by
    have ha : (tripleCharges (sourceA2475 + difference 2 3) (sourceB2475 + difference 3 2) sourceC2475) = raw18274 := by
      apply Matrix.ext; unfold tripleCharges sourceA2475 sourceB2475 sourceC2475 difference raw18274; decide +kernel
    rw [ha]
    exact (canonical18274 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2475 + difference 2 4) (sourceB2475 + difference 4 2) sourceC2475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4782) := by
    have ha : (tripleCharges (sourceA2475 + difference 2 4) (sourceB2475 + difference 4 2) sourceC2475) = raw34084 := by
      apply Matrix.ext; unfold tripleCharges sourceA2475 sourceB2475 sourceC2475 difference raw34084; decide +kernel
    rw [ha]
    exact (canonical34084 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2475 + difference 2 5) (sourceB2475 + difference 5 2) sourceC2475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4831) := by
    have ha : (tripleCharges (sourceA2475 + difference 2 5) (sourceB2475 + difference 5 2) sourceC2475) = raw18389 := by
      apply Matrix.ext; unfold tripleCharges sourceA2475 sourceB2475 sourceC2475 difference raw18389; decide +kernel
    rw [ha]
    exact (canonical18389 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2475 + difference 3 0) (sourceB2475 + difference 0 3) sourceC2475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4197) := by
    have ha : (tripleCharges (sourceA2475 + difference 3 0) (sourceB2475 + difference 0 3) sourceC2475) = raw34085 := by
      apply Matrix.ext; unfold tripleCharges sourceA2475 sourceB2475 sourceC2475 difference raw34085; decide +kernel
    rw [ha]
    exact (canonical34085 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2475 + difference 3 1) (sourceB2475 + difference 1 3) sourceC2475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4632) := by
    have ha : (tripleCharges (sourceA2475 + difference 3 1) (sourceB2475 + difference 1 3) sourceC2475) = raw34086 := by
      apply Matrix.ext; unfold tripleCharges sourceA2475 sourceB2475 sourceC2475 difference raw34086; decide +kernel
    rw [ha]
    exact (canonical34086 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2475 + difference 3 2) (sourceB2475 + difference 2 3) sourceC2475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4763) := by
    have ha : (tripleCharges (sourceA2475 + difference 3 2) (sourceB2475 + difference 2 3) sourceC2475) = raw34087 := by
      apply Matrix.ext; unfold tripleCharges sourceA2475 sourceB2475 sourceC2475 difference raw34087; decide +kernel
    rw [ha]
    exact (canonical34087 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2475 + difference 3 4) (sourceB2475 + difference 4 3) sourceC2475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4782) := by
    have ha : (tripleCharges (sourceA2475 + difference 3 4) (sourceB2475 + difference 4 3) sourceC2475) = raw34088 := by
      apply Matrix.ext; unfold tripleCharges sourceA2475 sourceB2475 sourceC2475 difference raw34088; decide +kernel
    rw [ha]
    exact (canonical34088 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2475 + difference 3 5) (sourceB2475 + difference 5 3) sourceC2475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA2475 + difference 3 5) (sourceB2475 + difference 5 3) sourceC2475) = raw18393 := by
      apply Matrix.ext; unfold tripleCharges sourceA2475 sourceB2475 sourceC2475 difference raw18393; decide +kernel
    rw [ha]
    exact (canonical18393 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2475 + difference 4 0) (sourceB2475 + difference 0 4) sourceC2475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4197) := by
    have ha : (tripleCharges (sourceA2475 + difference 4 0) (sourceB2475 + difference 0 4) sourceC2475) = raw34089 := by
      apply Matrix.ext; unfold tripleCharges sourceA2475 sourceB2475 sourceC2475 difference raw34089; decide +kernel
    rw [ha]
    exact (canonical34089 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2475 + difference 4 1) (sourceB2475 + difference 1 4) sourceC2475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4632) := by
    have ha : (tripleCharges (sourceA2475 + difference 4 1) (sourceB2475 + difference 1 4) sourceC2475) = raw34090 := by
      apply Matrix.ext; unfold tripleCharges sourceA2475 sourceB2475 sourceC2475 difference raw34090; decide +kernel
    rw [ha]
    exact (canonical34090 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2475 + difference 4 2) (sourceB2475 + difference 2 4) sourceC2475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4763) := by
    have ha : (tripleCharges (sourceA2475 + difference 4 2) (sourceB2475 + difference 2 4) sourceC2475) = raw34091 := by
      apply Matrix.ext; unfold tripleCharges sourceA2475 sourceB2475 sourceC2475 difference raw34091; decide +kernel
    rw [ha]
    exact (canonical34091 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2475 + difference 4 3) (sourceB2475 + difference 3 4) sourceC2475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4782) := by
    have ha : (tripleCharges (sourceA2475 + difference 4 3) (sourceB2475 + difference 3 4) sourceC2475) = raw18284 := by
      apply Matrix.ext; unfold tripleCharges sourceA2475 sourceB2475 sourceC2475 difference raw18284; decide +kernel
    rw [ha]
    exact (canonical18284 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2475 + difference 4 5) (sourceB2475 + difference 5 4) sourceC2475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA2475 + difference 4 5) (sourceB2475 + difference 5 4) sourceC2475) = raw18398 := by
      apply Matrix.ext; unfold tripleCharges sourceA2475 sourceB2475 sourceC2475 difference raw18398; decide +kernel
    rw [ha]
    exact (canonical18398 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2475 + difference 5 0) (sourceB2475 + difference 0 5) sourceC2475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4195) := by
    have ha : (tripleCharges (sourceA2475 + difference 5 0) (sourceB2475 + difference 0 5) sourceC2475) = raw34092 := by
      apply Matrix.ext; unfold tripleCharges sourceA2475 sourceB2475 sourceC2475 difference raw34092; decide +kernel
    rw [ha]
    exact (canonical34092 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2475 + difference 5 1) (sourceB2475 + difference 1 5) sourceC2475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4630) := by
    have ha : (tripleCharges (sourceA2475 + difference 5 1) (sourceB2475 + difference 1 5) sourceC2475) = raw34093 := by
      apply Matrix.ext; unfold tripleCharges sourceA2475 sourceB2475 sourceC2475 difference raw34093; decide +kernel
    rw [ha]
    exact (canonical34093 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2475 + difference 5 2) (sourceB2475 + difference 2 5) sourceC2475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4759) := by
    have ha : (tripleCharges (sourceA2475 + difference 5 2) (sourceB2475 + difference 2 5) sourceC2475) = raw34094 := by
      apply Matrix.ext; unfold tripleCharges sourceA2475 sourceB2475 sourceC2475 difference raw34094; decide +kernel
    rw [ha]
    exact (canonical34094 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2475 + difference 5 3) (sourceB2475 + difference 3 5) sourceC2475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4778) := by
    have ha : (tripleCharges (sourceA2475 + difference 5 3) (sourceB2475 + difference 3 5) sourceC2475) = raw18289 := by
      apply Matrix.ext; unfold tripleCharges sourceA2475 sourceB2475 sourceC2475 difference raw18289; decide +kernel
    rw [ha]
    exact (canonical18289 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2475 + difference 5 4) (sourceB2475 + difference 4 5) sourceC2475) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4778) := by
    have ha : (tripleCharges (sourceA2475 + difference 5 4) (sourceB2475 + difference 4 5) sourceC2475) = raw34095 := by
      apply Matrix.ext; unfold tripleCharges sourceA2475 sourceB2475 sourceC2475 difference raw34095; decide +kernel
    rw [ha]
    exact (canonical34095 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2475 sourceB2475 sourceC2475
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2475, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2476 : Charge := ![0, 1, 1, -1, -1, 0]
def sourceB2476 : Charge := ![3, 0, -1, 0, 0, -2]
def sourceC2476 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceForm2476 : Integer.Sparse Master := [(Sum.inr 4390, 1), (Sum.inr 4392, 1), (Sum.inr 4396, 2), (Sum.inr 4435, 1), (Sum.inr 4728, 1), (Sum.inr 4731, 1), (Sum.inr 4736, 2), (Sum.inr 4797, 2), (Sum.inr 4798, 2), (Sum.inr 4802, 2), (Sum.inr 4812, 2), (Sum.inr 4815, 1), (Sum.inr 4832, 1), (Sum.inr 4834, 2), (Sum.inr 4848, 2), (Sum.inr 4851, 1), (Sum.inr 4865, 1), (Sum.inr 5072, 1), (Sum.inr 5144, 2), (Sum.inr 5148, 1), (Sum.inr 5168, 1)]

theorem sourceEq2476 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2476 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2476 + difference 0 1) (sourceB2476 + difference 1 0) sourceC2476) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5072) := by
    have ha : (tripleCharges (sourceA2476 + difference 0 1) (sourceB2476 + difference 1 0) sourceC2476) = raw32334 := by
      apply Matrix.ext; unfold tripleCharges sourceA2476 sourceB2476 sourceC2476 difference raw32334; decide +kernel
    rw [ha]
    exact (canonical32334 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2476 + difference 0 2) (sourceB2476 + difference 2 0) sourceC2476) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5168) := by
    have ha : (tripleCharges (sourceA2476 + difference 0 2) (sourceB2476 + difference 2 0) sourceC2476) = raw32335 := by
      apply Matrix.ext; unfold tripleCharges sourceA2476 sourceB2476 sourceC2476 difference raw32335; decide +kernel
    rw [ha]
    exact (canonical32335 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2476 + difference 0 3) (sourceB2476 + difference 3 0) sourceC2476) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5144) := by
    have ha : (tripleCharges (sourceA2476 + difference 0 3) (sourceB2476 + difference 3 0) sourceC2476) = raw32336 := by
      apply Matrix.ext; unfold tripleCharges sourceA2476 sourceB2476 sourceC2476 difference raw32336; decide +kernel
    rw [ha]
    exact (canonical32336 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2476 + difference 0 4) (sourceB2476 + difference 4 0) sourceC2476) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5144) := by
    have ha : (tripleCharges (sourceA2476 + difference 0 4) (sourceB2476 + difference 4 0) sourceC2476) = raw32337 := by
      apply Matrix.ext; unfold tripleCharges sourceA2476 sourceB2476 sourceC2476 difference raw32337; decide +kernel
    rw [ha]
    exact (canonical32337 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2476 + difference 0 5) (sourceB2476 + difference 5 0) sourceC2476) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5148) := by
    have ha : (tripleCharges (sourceA2476 + difference 0 5) (sourceB2476 + difference 5 0) sourceC2476) = raw32492 := by
      apply Matrix.ext; unfold tripleCharges sourceA2476 sourceB2476 sourceC2476 difference raw32492; decide +kernel
    rw [ha]
    exact (canonical32492 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2476 + difference 1 0) (sourceB2476 + difference 0 1) sourceC2476) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4435) := by
    have ha : (tripleCharges (sourceA2476 + difference 1 0) (sourceB2476 + difference 0 1) sourceC2476) = raw33771 := by
      apply Matrix.ext; unfold tripleCharges sourceA2476 sourceB2476 sourceC2476 difference raw33771; decide +kernel
    rw [ha]
    exact (canonical33771 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2476 + difference 1 2) (sourceB2476 + difference 2 1) sourceC2476) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4865) := by
    have ha : (tripleCharges (sourceA2476 + difference 1 2) (sourceB2476 + difference 2 1) sourceC2476) = raw33653 := by
      apply Matrix.ext; unfold tripleCharges sourceA2476 sourceB2476 sourceC2476 difference raw33653; decide +kernel
    rw [ha]
    exact (canonical33653 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2476 + difference 1 3) (sourceB2476 + difference 3 1) sourceC2476) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4848) := by
    have ha : (tripleCharges (sourceA2476 + difference 1 3) (sourceB2476 + difference 3 1) sourceC2476) = raw33772 := by
      apply Matrix.ext; unfold tripleCharges sourceA2476 sourceB2476 sourceC2476 difference raw33772; decide +kernel
    rw [ha]
    exact (canonical33772 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2476 + difference 1 4) (sourceB2476 + difference 4 1) sourceC2476) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4848) := by
    have ha : (tripleCharges (sourceA2476 + difference 1 4) (sourceB2476 + difference 4 1) sourceC2476) = raw33773 := by
      apply Matrix.ext; unfold tripleCharges sourceA2476 sourceB2476 sourceC2476 difference raw33773; decide +kernel
    rw [ha]
    exact (canonical33773 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2476 + difference 1 5) (sourceB2476 + difference 5 1) sourceC2476) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4851) := by
    have ha : (tripleCharges (sourceA2476 + difference 1 5) (sourceB2476 + difference 5 1) sourceC2476) = raw32317 := by
      apply Matrix.ext; unfold tripleCharges sourceA2476 sourceB2476 sourceC2476 difference raw32317; decide +kernel
    rw [ha]
    exact (canonical32317 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2476 + difference 2 0) (sourceB2476 + difference 0 2) sourceC2476) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4392) := by
    have ha : (tripleCharges (sourceA2476 + difference 2 0) (sourceB2476 + difference 0 2) sourceC2476) = raw34096 := by
      apply Matrix.ext; unfold tripleCharges sourceA2476 sourceB2476 sourceC2476 difference raw34096; decide +kernel
    rw [ha]
    exact (canonical34096 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2476 + difference 2 1) (sourceB2476 + difference 1 2) sourceC2476) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4731) := by
    have ha : (tripleCharges (sourceA2476 + difference 2 1) (sourceB2476 + difference 1 2) sourceC2476) = raw33233 := by
      apply Matrix.ext; unfold tripleCharges sourceA2476 sourceB2476 sourceC2476 difference raw33233; decide +kernel
    rw [ha]
    exact (canonical33233 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2476 + difference 2 3) (sourceB2476 + difference 3 2) sourceC2476) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4812) := by
    have ha : (tripleCharges (sourceA2476 + difference 2 3) (sourceB2476 + difference 3 2) sourceC2476) = raw34097 := by
      apply Matrix.ext; unfold tripleCharges sourceA2476 sourceB2476 sourceC2476 difference raw34097; decide +kernel
    rw [ha]
    exact (canonical34097 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2476 + difference 2 4) (sourceB2476 + difference 4 2) sourceC2476) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4812) := by
    have ha : (tripleCharges (sourceA2476 + difference 2 4) (sourceB2476 + difference 4 2) sourceC2476) = raw34098 := by
      apply Matrix.ext; unfold tripleCharges sourceA2476 sourceB2476 sourceC2476 difference raw34098; decide +kernel
    rw [ha]
    exact (canonical34098 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2476 + difference 2 5) (sourceB2476 + difference 5 2) sourceC2476) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4815) := by
    have ha : (tripleCharges (sourceA2476 + difference 2 5) (sourceB2476 + difference 5 2) sourceC2476) = raw32322 := by
      apply Matrix.ext; unfold tripleCharges sourceA2476 sourceB2476 sourceC2476 difference raw32322; decide +kernel
    rw [ha]
    exact (canonical32322 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2476 + difference 3 0) (sourceB2476 + difference 0 3) sourceC2476) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4396) := by
    have ha : (tripleCharges (sourceA2476 + difference 3 0) (sourceB2476 + difference 0 3) sourceC2476) = raw33988 := by
      apply Matrix.ext; unfold tripleCharges sourceA2476 sourceB2476 sourceC2476 difference raw33988; decide +kernel
    rw [ha]
    exact (canonical33988 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2476 + difference 3 1) (sourceB2476 + difference 1 3) sourceC2476) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4736) := by
    have ha : (tripleCharges (sourceA2476 + difference 3 1) (sourceB2476 + difference 1 3) sourceC2476) = raw33147 := by
      apply Matrix.ext; unfold tripleCharges sourceA2476 sourceB2476 sourceC2476 difference raw33147; decide +kernel
    rw [ha]
    exact (canonical33147 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2476 + difference 3 2) (sourceB2476 + difference 2 3) sourceC2476) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4834) := by
    have ha : (tripleCharges (sourceA2476 + difference 3 2) (sourceB2476 + difference 2 3) sourceC2476) = raw32835 := by
      apply Matrix.ext; unfold tripleCharges sourceA2476 sourceB2476 sourceC2476 difference raw32835; decide +kernel
    rw [ha]
    exact (canonical32835 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2476 + difference 3 4) (sourceB2476 + difference 4 3) sourceC2476) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4798) := by
    have ha : (tripleCharges (sourceA2476 + difference 3 4) (sourceB2476 + difference 4 3) sourceC2476) = raw32827 := by
      apply Matrix.ext; unfold tripleCharges sourceA2476 sourceB2476 sourceC2476 difference raw32827; decide +kernel
    rw [ha]
    exact (canonical32827 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2476 + difference 3 5) (sourceB2476 + difference 5 3) sourceC2476) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA2476 + difference 3 5) (sourceB2476 + difference 5 3) sourceC2476) = raw32327 := by
      apply Matrix.ext; unfold tripleCharges sourceA2476 sourceB2476 sourceC2476 difference raw32327; decide +kernel
    rw [ha]
    exact (canonical32327 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2476 + difference 4 0) (sourceB2476 + difference 0 4) sourceC2476) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4396) := by
    have ha : (tripleCharges (sourceA2476 + difference 4 0) (sourceB2476 + difference 0 4) sourceC2476) = raw34099 := by
      apply Matrix.ext; unfold tripleCharges sourceA2476 sourceB2476 sourceC2476 difference raw34099; decide +kernel
    rw [ha]
    exact (canonical34099 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2476 + difference 4 1) (sourceB2476 + difference 1 4) sourceC2476) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4736) := by
    have ha : (tripleCharges (sourceA2476 + difference 4 1) (sourceB2476 + difference 1 4) sourceC2476) = raw33237 := by
      apply Matrix.ext; unfold tripleCharges sourceA2476 sourceB2476 sourceC2476 difference raw33237; decide +kernel
    rw [ha]
    exact (canonical33237 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2476 + difference 4 2) (sourceB2476 + difference 2 4) sourceC2476) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4834) := by
    have ha : (tripleCharges (sourceA2476 + difference 4 2) (sourceB2476 + difference 2 4) sourceC2476) = raw33775 := by
      apply Matrix.ext; unfold tripleCharges sourceA2476 sourceB2476 sourceC2476 difference raw33775; decide +kernel
    rw [ha]
    exact (canonical33775 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2476 + difference 4 3) (sourceB2476 + difference 3 4) sourceC2476) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4798) := by
    have ha : (tripleCharges (sourceA2476 + difference 4 3) (sourceB2476 + difference 3 4) sourceC2476) = raw34100 := by
      apply Matrix.ext; unfold tripleCharges sourceA2476 sourceB2476 sourceC2476 difference raw34100; decide +kernel
    rw [ha]
    exact (canonical34100 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2476 + difference 4 5) (sourceB2476 + difference 5 4) sourceC2476) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA2476 + difference 4 5) (sourceB2476 + difference 5 4) sourceC2476) = raw32330 := by
      apply Matrix.ext; unfold tripleCharges sourceA2476 sourceB2476 sourceC2476 difference raw32330; decide +kernel
    rw [ha]
    exact (canonical32330 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2476 + difference 5 0) (sourceB2476 + difference 0 5) sourceC2476) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4390) := by
    have ha : (tripleCharges (sourceA2476 + difference 5 0) (sourceB2476 + difference 0 5) sourceC2476) = raw34101 := by
      apply Matrix.ext; unfold tripleCharges sourceA2476 sourceB2476 sourceC2476 difference raw34101; decide +kernel
    rw [ha]
    exact (canonical34101 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2476 + difference 5 1) (sourceB2476 + difference 1 5) sourceC2476) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4728) := by
    have ha : (tripleCharges (sourceA2476 + difference 5 1) (sourceB2476 + difference 1 5) sourceC2476) = raw33241 := by
      apply Matrix.ext; unfold tripleCharges sourceA2476 sourceB2476 sourceC2476 difference raw33241; decide +kernel
    rw [ha]
    exact (canonical33241 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2476 + difference 5 2) (sourceB2476 + difference 2 5) sourceC2476) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4832) := by
    have ha : (tripleCharges (sourceA2476 + difference 5 2) (sourceB2476 + difference 2 5) sourceC2476) = raw33779 := by
      apply Matrix.ext; unfold tripleCharges sourceA2476 sourceB2476 sourceC2476 difference raw33779; decide +kernel
    rw [ha]
    exact (canonical33779 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2476 + difference 5 3) (sourceB2476 + difference 3 5) sourceC2476) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4797) := by
    have ha : (tripleCharges (sourceA2476 + difference 5 3) (sourceB2476 + difference 3 5) sourceC2476) = raw34102 := by
      apply Matrix.ext; unfold tripleCharges sourceA2476 sourceB2476 sourceC2476 difference raw34102; decide +kernel
    rw [ha]
    exact (canonical34102 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2476 + difference 5 4) (sourceB2476 + difference 4 5) sourceC2476) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4797) := by
    have ha : (tripleCharges (sourceA2476 + difference 5 4) (sourceB2476 + difference 4 5) sourceC2476) = raw34103 := by
      apply Matrix.ext; unfold tripleCharges sourceA2476 sourceB2476 sourceC2476 difference raw34103; decide +kernel
    rw [ha]
    exact (canonical34103 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2476 sourceB2476 sourceC2476
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2476, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2477 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2477 : Charge := ![0, 1, 0, 1, 0, -2]
def sourceC2477 : Charge := ![3, 0, 0, -2, -1, 0]
def sourceForm2477 : Integer.Sparse Master := [(Sum.inr 4345, 1), (Sum.inr 4353, 1), (Sum.inr 4354, 1), (Sum.inr 4357, 1), (Sum.inr 4503, 1), (Sum.inr 4680, 1), (Sum.inr 4687, 1), (Sum.inr 4688, 1), (Sum.inr 4690, 1), (Sum.inr 4765, 1), (Sum.inr 4766, 1), (Sum.inr 4768, 1), (Sum.inr 4803, 1), (Sum.inr 4808, 1), (Sum.inr 4810, 1), (Sum.inr 4816, 1), (Sum.inr 4819, 1), (Sum.inr 4821, 1), (Sum.inr 4831, 1), (Sum.inr 4834, 1), (Sum.inr 4835, 1), (Sum.inr 4839, 1), (Sum.inr 4895, 1), (Sum.inr 4896, 1), (Sum.inr 4898, 1), (Sum.inr 5233, 1), (Sum.inr 5244, 1), (Sum.inr 5259, 1), (Sum.inr 5266, 1), (Sum.inr 5267, 1)]

theorem sourceEq2477 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2477 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2477 + difference 0 1) (sourceB2477 + difference 1 0) sourceC2477) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5233) := by
    have ha : (tripleCharges (sourceA2477 + difference 0 1) (sourceB2477 + difference 1 0) sourceC2477) = raw34104 := by
      apply Matrix.ext; unfold tripleCharges sourceA2477 sourceB2477 sourceC2477 difference raw34104; decide +kernel
    rw [ha]
    exact (canonical34104 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2477 + difference 0 2) (sourceB2477 + difference 2 0) sourceC2477) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5244) := by
    have ha : (tripleCharges (sourceA2477 + difference 0 2) (sourceB2477 + difference 2 0) sourceC2477) = raw34105 := by
      apply Matrix.ext; unfold tripleCharges sourceA2477 sourceB2477 sourceC2477 difference raw34105; decide +kernel
    rw [ha]
    exact (canonical34105 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2477 + difference 0 3) (sourceB2477 + difference 3 0) sourceC2477) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5267) := by
    have ha : (tripleCharges (sourceA2477 + difference 0 3) (sourceB2477 + difference 3 0) sourceC2477) = raw34106 := by
      apply Matrix.ext; unfold tripleCharges sourceA2477 sourceB2477 sourceC2477 difference raw34106; decide +kernel
    rw [ha]
    exact (canonical34106 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2477 + difference 0 4) (sourceB2477 + difference 4 0) sourceC2477) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA2477 + difference 0 4) (sourceB2477 + difference 4 0) sourceC2477) = raw34107 := by
      apply Matrix.ext; unfold tripleCharges sourceA2477 sourceB2477 sourceC2477 difference raw34107; decide +kernel
    rw [ha]
    exact (canonical34107 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2477 + difference 0 5) (sourceB2477 + difference 5 0) sourceC2477) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA2477 + difference 0 5) (sourceB2477 + difference 5 0) sourceC2477) = raw34108 := by
      apply Matrix.ext; unfold tripleCharges sourceA2477 sourceB2477 sourceC2477 difference raw34108; decide +kernel
    rw [ha]
    exact (canonical34108 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2477 + difference 1 0) (sourceB2477 + difference 0 1) sourceC2477) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4503) := by
    have ha : (tripleCharges (sourceA2477 + difference 1 0) (sourceB2477 + difference 0 1) sourceC2477) = raw34109 := by
      apply Matrix.ext; unfold tripleCharges sourceA2477 sourceB2477 sourceC2477 difference raw34109; decide +kernel
    rw [ha]
    exact (canonical34109 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2477 + difference 1 2) (sourceB2477 + difference 2 1) sourceC2477) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4839) := by
    have ha : (tripleCharges (sourceA2477 + difference 1 2) (sourceB2477 + difference 2 1) sourceC2477) = raw25604 := by
      apply Matrix.ext; unfold tripleCharges sourceA2477 sourceB2477 sourceC2477 difference raw25604; decide +kernel
    rw [ha]
    exact (canonical25604 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2477 + difference 1 3) (sourceB2477 + difference 3 1) sourceC2477) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4898) := by
    have ha : (tripleCharges (sourceA2477 + difference 1 3) (sourceB2477 + difference 3 1) sourceC2477) = raw25605 := by
      apply Matrix.ext; unfold tripleCharges sourceA2477 sourceB2477 sourceC2477 difference raw25605; decide +kernel
    rw [ha]
    exact (canonical25605 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2477 + difference 1 4) (sourceB2477 + difference 4 1) sourceC2477) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4896) := by
    have ha : (tripleCharges (sourceA2477 + difference 1 4) (sourceB2477 + difference 4 1) sourceC2477) = raw25606 := by
      apply Matrix.ext; unfold tripleCharges sourceA2477 sourceB2477 sourceC2477 difference raw25606; decide +kernel
    rw [ha]
    exact (canonical25606 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2477 + difference 1 5) (sourceB2477 + difference 5 1) sourceC2477) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA2477 + difference 1 5) (sourceB2477 + difference 5 1) sourceC2477) = raw25607 := by
      apply Matrix.ext; unfold tripleCharges sourceA2477 sourceB2477 sourceC2477 difference raw25607; decide +kernel
    rw [ha]
    exact (canonical25607 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2477 + difference 2 0) (sourceB2477 + difference 0 2) sourceC2477) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4345) := by
    have ha : (tripleCharges (sourceA2477 + difference 2 0) (sourceB2477 + difference 0 2) sourceC2477) = raw25614 := by
      apply Matrix.ext; unfold tripleCharges sourceA2477 sourceB2477 sourceC2477 difference raw25614; decide +kernel
    rw [ha]
    exact (canonical25614 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2477 + difference 2 1) (sourceB2477 + difference 1 2) sourceC2477) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4680) := by
    have ha : (tripleCharges (sourceA2477 + difference 2 1) (sourceB2477 + difference 1 2) sourceC2477) = raw34110 := by
      apply Matrix.ext; unfold tripleCharges sourceA2477 sourceB2477 sourceC2477 difference raw34110; decide +kernel
    rw [ha]
    exact (canonical34110 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2477 + difference 2 3) (sourceB2477 + difference 3 2) sourceC2477) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4816) := by
    have ha : (tripleCharges (sourceA2477 + difference 2 3) (sourceB2477 + difference 3 2) sourceC2477) = raw34111 := by
      apply Matrix.ext; unfold tripleCharges sourceA2477 sourceB2477 sourceC2477 difference raw34111; decide +kernel
    rw [ha]
    exact (canonical34111 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2477 + difference 2 4) (sourceB2477 + difference 4 2) sourceC2477) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4803) := by
    have ha : (tripleCharges (sourceA2477 + difference 2 4) (sourceB2477 + difference 4 2) sourceC2477) = raw34112 := by
      apply Matrix.ext; unfold tripleCharges sourceA2477 sourceB2477 sourceC2477 difference raw34112; decide +kernel
    rw [ha]
    exact (canonical34112 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2477 + difference 2 5) (sourceB2477 + difference 5 2) sourceC2477) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4831) := by
    have ha : (tripleCharges (sourceA2477 + difference 2 5) (sourceB2477 + difference 5 2) sourceC2477) = raw34113 := by
      apply Matrix.ext; unfold tripleCharges sourceA2477 sourceB2477 sourceC2477 difference raw34113; decide +kernel
    rw [ha]
    exact (canonical34113 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2477 + difference 3 0) (sourceB2477 + difference 0 3) sourceC2477) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4354) := by
    have ha : (tripleCharges (sourceA2477 + difference 3 0) (sourceB2477 + difference 0 3) sourceC2477) = raw25619 := by
      apply Matrix.ext; unfold tripleCharges sourceA2477 sourceB2477 sourceC2477 difference raw25619; decide +kernel
    rw [ha]
    exact (canonical25619 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2477 + difference 3 1) (sourceB2477 + difference 1 3) sourceC2477) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4688) := by
    have ha : (tripleCharges (sourceA2477 + difference 3 1) (sourceB2477 + difference 1 3) sourceC2477) = raw34114 := by
      apply Matrix.ext; unfold tripleCharges sourceA2477 sourceB2477 sourceC2477 difference raw34114; decide +kernel
    rw [ha]
    exact (canonical34114 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2477 + difference 3 2) (sourceB2477 + difference 2 3) sourceC2477) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4766) := by
    have ha : (tripleCharges (sourceA2477 + difference 3 2) (sourceB2477 + difference 2 3) sourceC2477) = raw34115 := by
      apply Matrix.ext; unfold tripleCharges sourceA2477 sourceB2477 sourceC2477 difference raw34115; decide +kernel
    rw [ha]
    exact (canonical34115 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2477 + difference 3 4) (sourceB2477 + difference 4 3) sourceC2477) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4810) := by
    have ha : (tripleCharges (sourceA2477 + difference 3 4) (sourceB2477 + difference 4 3) sourceC2477) = raw34116 := by
      apply Matrix.ext; unfold tripleCharges sourceA2477 sourceB2477 sourceC2477 difference raw34116; decide +kernel
    rw [ha]
    exact (canonical34116 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2477 + difference 3 5) (sourceB2477 + difference 5 3) sourceC2477) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4834) := by
    have ha : (tripleCharges (sourceA2477 + difference 3 5) (sourceB2477 + difference 5 3) sourceC2477) = raw34117 := by
      apply Matrix.ext; unfold tripleCharges sourceA2477 sourceB2477 sourceC2477 difference raw34117; decide +kernel
    rw [ha]
    exact (canonical34117 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2477 + difference 4 0) (sourceB2477 + difference 0 4) sourceC2477) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4357) := by
    have ha : (tripleCharges (sourceA2477 + difference 4 0) (sourceB2477 + difference 0 4) sourceC2477) = raw25624 := by
      apply Matrix.ext; unfold tripleCharges sourceA2477 sourceB2477 sourceC2477 difference raw25624; decide +kernel
    rw [ha]
    exact (canonical25624 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2477 + difference 4 1) (sourceB2477 + difference 1 4) sourceC2477) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4690) := by
    have ha : (tripleCharges (sourceA2477 + difference 4 1) (sourceB2477 + difference 1 4) sourceC2477) = raw34118 := by
      apply Matrix.ext; unfold tripleCharges sourceA2477 sourceB2477 sourceC2477 difference raw34118; decide +kernel
    rw [ha]
    exact (canonical34118 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2477 + difference 4 2) (sourceB2477 + difference 2 4) sourceC2477) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4768) := by
    have ha : (tripleCharges (sourceA2477 + difference 4 2) (sourceB2477 + difference 2 4) sourceC2477) = raw34119 := by
      apply Matrix.ext; unfold tripleCharges sourceA2477 sourceB2477 sourceC2477 difference raw34119; decide +kernel
    rw [ha]
    exact (canonical34119 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2477 + difference 4 3) (sourceB2477 + difference 3 4) sourceC2477) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4821) := by
    have ha : (tripleCharges (sourceA2477 + difference 4 3) (sourceB2477 + difference 3 4) sourceC2477) = raw34120 := by
      apply Matrix.ext; unfold tripleCharges sourceA2477 sourceB2477 sourceC2477 difference raw34120; decide +kernel
    rw [ha]
    exact (canonical34120 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2477 + difference 4 5) (sourceB2477 + difference 5 4) sourceC2477) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4835) := by
    have ha : (tripleCharges (sourceA2477 + difference 4 5) (sourceB2477 + difference 5 4) sourceC2477) = raw34121 := by
      apply Matrix.ext; unfold tripleCharges sourceA2477 sourceB2477 sourceC2477 difference raw34121; decide +kernel
    rw [ha]
    exact (canonical34121 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2477 + difference 5 0) (sourceB2477 + difference 0 5) sourceC2477) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4353) := by
    have ha : (tripleCharges (sourceA2477 + difference 5 0) (sourceB2477 + difference 0 5) sourceC2477) = raw25629 := by
      apply Matrix.ext; unfold tripleCharges sourceA2477 sourceB2477 sourceC2477 difference raw25629; decide +kernel
    rw [ha]
    exact (canonical25629 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2477 + difference 5 1) (sourceB2477 + difference 1 5) sourceC2477) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4687) := by
    have ha : (tripleCharges (sourceA2477 + difference 5 1) (sourceB2477 + difference 1 5) sourceC2477) = raw34122 := by
      apply Matrix.ext; unfold tripleCharges sourceA2477 sourceB2477 sourceC2477 difference raw34122; decide +kernel
    rw [ha]
    exact (canonical34122 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2477 + difference 5 2) (sourceB2477 + difference 2 5) sourceC2477) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4765) := by
    have ha : (tripleCharges (sourceA2477 + difference 5 2) (sourceB2477 + difference 2 5) sourceC2477) = raw34123 := by
      apply Matrix.ext; unfold tripleCharges sourceA2477 sourceB2477 sourceC2477 difference raw34123; decide +kernel
    rw [ha]
    exact (canonical34123 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2477 + difference 5 3) (sourceB2477 + difference 3 5) sourceC2477) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4819) := by
    have ha : (tripleCharges (sourceA2477 + difference 5 3) (sourceB2477 + difference 3 5) sourceC2477) = raw34124 := by
      apply Matrix.ext; unfold tripleCharges sourceA2477 sourceB2477 sourceC2477 difference raw34124; decide +kernel
    rw [ha]
    exact (canonical34124 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2477 + difference 5 4) (sourceB2477 + difference 4 5) sourceC2477) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4808) := by
    have ha : (tripleCharges (sourceA2477 + difference 5 4) (sourceB2477 + difference 4 5) sourceC2477) = raw34125 := by
      apply Matrix.ext; unfold tripleCharges sourceA2477 sourceB2477 sourceC2477 difference raw34125; decide +kernel
    rw [ha]
    exact (canonical34125 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2477 sourceB2477 sourceC2477
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2477, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2478 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2478 : Charge := ![0, 1, 0, 1, 0, -2]
def sourceC2478 : Charge := ![3, 0, 0, -2, -1, 0]
def sourceForm2478 : Integer.Sparse Master := [(Sum.inr 1668, 1), (Sum.inr 1681, 1), (Sum.inr 1682, 1), (Sum.inr 1686, 1), (Sum.inr 1739, 1), (Sum.inr 2145, 1), (Sum.inr 2157, 1), (Sum.inr 2158, 1), (Sum.inr 2162, 1), (Sum.inr 2177, 1), (Sum.inr 2178, 1), (Sum.inr 2179, 1), (Sum.inr 2191, 1), (Sum.inr 2195, 1), (Sum.inr 2196, 1), (Sum.inr 2205, 1), (Sum.inr 2206, 1), (Sum.inr 2215, 1), (Sum.inr 2216, 1), (Sum.inr 2217, 1), (Sum.inr 2220, 1), (Sum.inr 2221, 1), (Sum.inr 2265, 1), (Sum.inr 2278, 1), (Sum.inr 2279, 1), (Sum.inr 2678, 1), (Sum.inr 2698, 1), (Sum.inr 2723, 1), (Sum.inr 2731, 1), (Sum.inr 2732, 1)]

theorem sourceEq2478 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2478 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2478 + difference 0 1) (sourceB2478 + difference 1 0) sourceC2478) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2678) := by
    have ha : (tripleCharges (sourceA2478 + difference 0 1) (sourceB2478 + difference 1 0) sourceC2478) = raw34126 := by
      apply Matrix.ext; unfold tripleCharges sourceA2478 sourceB2478 sourceC2478 difference raw34126; decide +kernel
    rw [ha]
    exact (canonical34126 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2478 + difference 0 2) (sourceB2478 + difference 2 0) sourceC2478) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2698) := by
    have ha : (tripleCharges (sourceA2478 + difference 0 2) (sourceB2478 + difference 2 0) sourceC2478) = raw34127 := by
      apply Matrix.ext; unfold tripleCharges sourceA2478 sourceB2478 sourceC2478 difference raw34127; decide +kernel
    rw [ha]
    exact (canonical34127 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2478 + difference 0 3) (sourceB2478 + difference 3 0) sourceC2478) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2732) := by
    have ha : (tripleCharges (sourceA2478 + difference 0 3) (sourceB2478 + difference 3 0) sourceC2478) = raw34128 := by
      apply Matrix.ext; unfold tripleCharges sourceA2478 sourceB2478 sourceC2478 difference raw34128; decide +kernel
    rw [ha]
    exact (canonical34128 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2478 + difference 0 4) (sourceB2478 + difference 4 0) sourceC2478) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2731) := by
    have ha : (tripleCharges (sourceA2478 + difference 0 4) (sourceB2478 + difference 4 0) sourceC2478) = raw34129 := by
      apply Matrix.ext; unfold tripleCharges sourceA2478 sourceB2478 sourceC2478 difference raw34129; decide +kernel
    rw [ha]
    exact (canonical34129 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2478 + difference 0 5) (sourceB2478 + difference 5 0) sourceC2478) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA2478 + difference 0 5) (sourceB2478 + difference 5 0) sourceC2478) = raw34130 := by
      apply Matrix.ext; unfold tripleCharges sourceA2478 sourceB2478 sourceC2478 difference raw34130; decide +kernel
    rw [ha]
    exact (canonical34130 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2478 + difference 1 0) (sourceB2478 + difference 0 1) sourceC2478) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1739) := by
    have ha : (tripleCharges (sourceA2478 + difference 1 0) (sourceB2478 + difference 0 1) sourceC2478) = raw34131 := by
      apply Matrix.ext; unfold tripleCharges sourceA2478 sourceB2478 sourceC2478 difference raw34131; decide +kernel
    rw [ha]
    exact (canonical34131 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2478 + difference 1 2) (sourceB2478 + difference 2 1) sourceC2478) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2216) := by
    have ha : (tripleCharges (sourceA2478 + difference 1 2) (sourceB2478 + difference 2 1) sourceC2478) = raw25634 := by
      apply Matrix.ext; unfold tripleCharges sourceA2478 sourceB2478 sourceC2478 difference raw25634; decide +kernel
    rw [ha]
    exact (canonical25634 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2478 + difference 1 3) (sourceB2478 + difference 3 1) sourceC2478) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2279) := by
    have ha : (tripleCharges (sourceA2478 + difference 1 3) (sourceB2478 + difference 3 1) sourceC2478) = raw25635 := by
      apply Matrix.ext; unfold tripleCharges sourceA2478 sourceB2478 sourceC2478 difference raw25635; decide +kernel
    rw [ha]
    exact (canonical25635 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2478 + difference 1 4) (sourceB2478 + difference 4 1) sourceC2478) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2278) := by
    have ha : (tripleCharges (sourceA2478 + difference 1 4) (sourceB2478 + difference 4 1) sourceC2478) = raw25636 := by
      apply Matrix.ext; unfold tripleCharges sourceA2478 sourceB2478 sourceC2478 difference raw25636; decide +kernel
    rw [ha]
    exact (canonical25636 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2478 + difference 1 5) (sourceB2478 + difference 5 1) sourceC2478) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2265) := by
    have ha : (tripleCharges (sourceA2478 + difference 1 5) (sourceB2478 + difference 5 1) sourceC2478) = raw25637 := by
      apply Matrix.ext; unfold tripleCharges sourceA2478 sourceB2478 sourceC2478 difference raw25637; decide +kernel
    rw [ha]
    exact (canonical25637 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2478 + difference 2 0) (sourceB2478 + difference 0 2) sourceC2478) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1668) := by
    have ha : (tripleCharges (sourceA2478 + difference 2 0) (sourceB2478 + difference 0 2) sourceC2478) = raw25644 := by
      apply Matrix.ext; unfold tripleCharges sourceA2478 sourceB2478 sourceC2478 difference raw25644; decide +kernel
    rw [ha]
    exact (canonical25644 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2478 + difference 2 1) (sourceB2478 + difference 1 2) sourceC2478) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2145) := by
    have ha : (tripleCharges (sourceA2478 + difference 2 1) (sourceB2478 + difference 1 2) sourceC2478) = raw34132 := by
      apply Matrix.ext; unfold tripleCharges sourceA2478 sourceB2478 sourceC2478 difference raw34132; decide +kernel
    rw [ha]
    exact (canonical34132 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2478 + difference 2 3) (sourceB2478 + difference 3 2) sourceC2478) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2196) := by
    have ha : (tripleCharges (sourceA2478 + difference 2 3) (sourceB2478 + difference 3 2) sourceC2478) = raw34133 := by
      apply Matrix.ext; unfold tripleCharges sourceA2478 sourceB2478 sourceC2478 difference raw34133; decide +kernel
    rw [ha]
    exact (canonical34133 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2478 + difference 2 4) (sourceB2478 + difference 4 2) sourceC2478) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2195) := by
    have ha : (tripleCharges (sourceA2478 + difference 2 4) (sourceB2478 + difference 4 2) sourceC2478) = raw34134 := by
      apply Matrix.ext; unfold tripleCharges sourceA2478 sourceB2478 sourceC2478 difference raw34134; decide +kernel
    rw [ha]
    exact (canonical34134 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2478 + difference 2 5) (sourceB2478 + difference 5 2) sourceC2478) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2191) := by
    have ha : (tripleCharges (sourceA2478 + difference 2 5) (sourceB2478 + difference 5 2) sourceC2478) = raw34135 := by
      apply Matrix.ext; unfold tripleCharges sourceA2478 sourceB2478 sourceC2478 difference raw34135; decide +kernel
    rw [ha]
    exact (canonical34135 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2478 + difference 3 0) (sourceB2478 + difference 0 3) sourceC2478) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1681) := by
    have ha : (tripleCharges (sourceA2478 + difference 3 0) (sourceB2478 + difference 0 3) sourceC2478) = raw25649 := by
      apply Matrix.ext; unfold tripleCharges sourceA2478 sourceB2478 sourceC2478 difference raw25649; decide +kernel
    rw [ha]
    exact (canonical25649 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2478 + difference 3 1) (sourceB2478 + difference 1 3) sourceC2478) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2157) := by
    have ha : (tripleCharges (sourceA2478 + difference 3 1) (sourceB2478 + difference 1 3) sourceC2478) = raw34136 := by
      apply Matrix.ext; unfold tripleCharges sourceA2478 sourceB2478 sourceC2478 difference raw34136; decide +kernel
    rw [ha]
    exact (canonical34136 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2478 + difference 3 2) (sourceB2478 + difference 2 3) sourceC2478) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2177) := by
    have ha : (tripleCharges (sourceA2478 + difference 3 2) (sourceB2478 + difference 2 3) sourceC2478) = raw34137 := by
      apply Matrix.ext; unfold tripleCharges sourceA2478 sourceB2478 sourceC2478 difference raw34137; decide +kernel
    rw [ha]
    exact (canonical34137 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2478 + difference 3 4) (sourceB2478 + difference 4 3) sourceC2478) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2215) := by
    have ha : (tripleCharges (sourceA2478 + difference 3 4) (sourceB2478 + difference 4 3) sourceC2478) = raw34138 := by
      apply Matrix.ext; unfold tripleCharges sourceA2478 sourceB2478 sourceC2478 difference raw34138; decide +kernel
    rw [ha]
    exact (canonical34138 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2478 + difference 3 5) (sourceB2478 + difference 5 3) sourceC2478) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2205) := by
    have ha : (tripleCharges (sourceA2478 + difference 3 5) (sourceB2478 + difference 5 3) sourceC2478) = raw34139 := by
      apply Matrix.ext; unfold tripleCharges sourceA2478 sourceB2478 sourceC2478 difference raw34139; decide +kernel
    rw [ha]
    exact (canonical34139 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2478 + difference 4 0) (sourceB2478 + difference 0 4) sourceC2478) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1682) := by
    have ha : (tripleCharges (sourceA2478 + difference 4 0) (sourceB2478 + difference 0 4) sourceC2478) = raw25654 := by
      apply Matrix.ext; unfold tripleCharges sourceA2478 sourceB2478 sourceC2478 difference raw25654; decide +kernel
    rw [ha]
    exact (canonical25654 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2478 + difference 4 1) (sourceB2478 + difference 1 4) sourceC2478) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2158) := by
    have ha : (tripleCharges (sourceA2478 + difference 4 1) (sourceB2478 + difference 1 4) sourceC2478) = raw34140 := by
      apply Matrix.ext; unfold tripleCharges sourceA2478 sourceB2478 sourceC2478 difference raw34140; decide +kernel
    rw [ha]
    exact (canonical34140 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2478 + difference 4 2) (sourceB2478 + difference 2 4) sourceC2478) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2178) := by
    have ha : (tripleCharges (sourceA2478 + difference 4 2) (sourceB2478 + difference 2 4) sourceC2478) = raw34141 := by
      apply Matrix.ext; unfold tripleCharges sourceA2478 sourceB2478 sourceC2478 difference raw34141; decide +kernel
    rw [ha]
    exact (canonical34141 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2478 + difference 4 3) (sourceB2478 + difference 3 4) sourceC2478) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2217) := by
    have ha : (tripleCharges (sourceA2478 + difference 4 3) (sourceB2478 + difference 3 4) sourceC2478) = raw34142 := by
      apply Matrix.ext; unfold tripleCharges sourceA2478 sourceB2478 sourceC2478 difference raw34142; decide +kernel
    rw [ha]
    exact (canonical34142 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2478 + difference 4 5) (sourceB2478 + difference 5 4) sourceC2478) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2206) := by
    have ha : (tripleCharges (sourceA2478 + difference 4 5) (sourceB2478 + difference 5 4) sourceC2478) = raw34143 := by
      apply Matrix.ext; unfold tripleCharges sourceA2478 sourceB2478 sourceC2478 difference raw34143; decide +kernel
    rw [ha]
    exact (canonical34143 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2478 + difference 5 0) (sourceB2478 + difference 0 5) sourceC2478) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1686) := by
    have ha : (tripleCharges (sourceA2478 + difference 5 0) (sourceB2478 + difference 0 5) sourceC2478) = raw25659 := by
      apply Matrix.ext; unfold tripleCharges sourceA2478 sourceB2478 sourceC2478 difference raw25659; decide +kernel
    rw [ha]
    exact (canonical25659 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2478 + difference 5 1) (sourceB2478 + difference 1 5) sourceC2478) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2162) := by
    have ha : (tripleCharges (sourceA2478 + difference 5 1) (sourceB2478 + difference 1 5) sourceC2478) = raw34144 := by
      apply Matrix.ext; unfold tripleCharges sourceA2478 sourceB2478 sourceC2478 difference raw34144; decide +kernel
    rw [ha]
    exact (canonical34144 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2478 + difference 5 2) (sourceB2478 + difference 2 5) sourceC2478) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2179) := by
    have ha : (tripleCharges (sourceA2478 + difference 5 2) (sourceB2478 + difference 2 5) sourceC2478) = raw34145 := by
      apply Matrix.ext; unfold tripleCharges sourceA2478 sourceB2478 sourceC2478 difference raw34145; decide +kernel
    rw [ha]
    exact (canonical34145 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2478 + difference 5 3) (sourceB2478 + difference 3 5) sourceC2478) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2221) := by
    have ha : (tripleCharges (sourceA2478 + difference 5 3) (sourceB2478 + difference 3 5) sourceC2478) = raw34146 := by
      apply Matrix.ext; unfold tripleCharges sourceA2478 sourceB2478 sourceC2478 difference raw34146; decide +kernel
    rw [ha]
    exact (canonical34146 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2478 + difference 5 4) (sourceB2478 + difference 4 5) sourceC2478) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2220) := by
    have ha : (tripleCharges (sourceA2478 + difference 5 4) (sourceB2478 + difference 4 5) sourceC2478) = raw34147 := by
      apply Matrix.ext; unfold tripleCharges sourceA2478 sourceB2478 sourceC2478 difference raw34147; decide +kernel
    rw [ha]
    exact (canonical34147 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2478 sourceB2478 sourceC2478
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2478, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2479 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2479 : Charge := ![0, 1, 0, 1, 0, -2]
def sourceC2479 : Charge := ![3, 0, 0, -2, -1, 0]
def sourceForm2479 : Integer.Sparse Master := [(Sum.inr 1806, 1), (Sum.inr 1813, 1), (Sum.inr 1814, 1), (Sum.inr 1816, 1), (Sum.inr 2058, 1), (Sum.inr 3395, 1), (Sum.inr 4084, -1)]

theorem sourceEq2479 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2479 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2479 + difference 0 1) (sourceB2479 + difference 1 0) sourceC2479) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3395) := by
    have ha : (tripleCharges (sourceA2479 + difference 0 1) (sourceB2479 + difference 1 0) sourceC2479) = raw34148 := by
      apply Matrix.ext; unfold tripleCharges sourceA2479 sourceB2479 sourceC2479 difference raw34148; decide +kernel
    rw [ha]
    exact (canonical34148 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2479 + difference 1 1) (sourceB2479 + difference 1 1) sourceC2479) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2058) := by
    have ha : (tripleCharges (sourceA2479 + difference 1 1) (sourceB2479 + difference 1 1) sourceC2479) = raw34149 := by
      apply Matrix.ext; unfold tripleCharges sourceA2479 sourceB2479 sourceC2479 difference raw34149; decide +kernel
    rw [ha]
    exact (canonical34149 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2479 + difference 2 1) (sourceB2479 + difference 1 2) sourceC2479) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1806) := by
    have ha : (tripleCharges (sourceA2479 + difference 2 1) (sourceB2479 + difference 1 2) sourceC2479) = raw34150 := by
      apply Matrix.ext; unfold tripleCharges sourceA2479 sourceB2479 sourceC2479 difference raw34150; decide +kernel
    rw [ha]
    exact (canonical34150 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2479 + difference 3 1) (sourceB2479 + difference 1 3) sourceC2479) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1814) := by
    have ha : (tripleCharges (sourceA2479 + difference 3 1) (sourceB2479 + difference 1 3) sourceC2479) = raw34151 := by
      apply Matrix.ext; unfold tripleCharges sourceA2479 sourceB2479 sourceC2479 difference raw34151; decide +kernel
    rw [ha]
    exact (canonical34151 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2479 + difference 4 1) (sourceB2479 + difference 1 4) sourceC2479) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1816) := by
    have ha : (tripleCharges (sourceA2479 + difference 4 1) (sourceB2479 + difference 1 4) sourceC2479) = raw34152 := by
      apply Matrix.ext; unfold tripleCharges sourceA2479 sourceB2479 sourceC2479 difference raw34152; decide +kernel
    rw [ha]
    exact (canonical34152 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2479 + difference 5 1) (sourceB2479 + difference 1 5) sourceC2479) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1813) := by
    have ha : (tripleCharges (sourceA2479 + difference 5 1) (sourceB2479 + difference 1 5) sourceC2479) = raw34153 := by
      apply Matrix.ext; unfold tripleCharges sourceA2479 sourceB2479 sourceC2479 difference raw34153; decide +kernel
    rw [ha]
    exact (canonical34153 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2479 + sourceB2479) sourceC2479) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA2479 + sourceB2479) sourceC2479) = raw34154 := by
      apply Matrix.ext; unfold doubleCharges sourceA2479 sourceB2479 sourceC2479 raw34154; decide +kernel
    rw [ha]
    exact (canonical34154 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2479 sourceB2479 sourceC2479
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2479, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2480 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2480 : Charge := ![3, 0, 0, -2, -1, 0]
def sourceC2480 : Charge := ![0, 1, 0, 1, 0, -2]
def sourceForm2480 : Integer.Sparse Master := [(Sum.inr 4217, 1), (Sum.inr 4219, 1), (Sum.inr 4220, 1), (Sum.inr 4223, 1), (Sum.inr 4268, 1), (Sum.inr 4648, 1), (Sum.inr 4650, 1), (Sum.inr 4651, 1), (Sum.inr 4653, 1), (Sum.inr 4713, 1), (Sum.inr 4714, 1), (Sum.inr 4716, 1), (Sum.inr 4740, 1), (Sum.inr 4805, 1), (Sum.inr 4807, 1), (Sum.inr 4810, 1), (Sum.inr 4826, 1), (Sum.inr 4827, 1), (Sum.inr 4828, 1), (Sum.inr 4839, 1), (Sum.inr 4843, 1), (Sum.inr 4845, 1), (Sum.inr 4866, 1), (Sum.inr 4889, 1), (Sum.inr 4896, 1), (Sum.inr 5370, 1), (Sum.inr 5397, 1), (Sum.inr 5435, 1), (Sum.inr 5438, 1), (Sum.inr 5443, 1)]

theorem sourceEq2480 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2480 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2480 + difference 0 1) (sourceB2480 + difference 1 0) sourceC2480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5370) := by
    have ha : (tripleCharges (sourceA2480 + difference 0 1) (sourceB2480 + difference 1 0) sourceC2480) = raw34155 := by
      apply Matrix.ext; unfold tripleCharges sourceA2480 sourceB2480 sourceC2480 difference raw34155; decide +kernel
    rw [ha]
    exact (canonical34155 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2480 + difference 0 2) (sourceB2480 + difference 2 0) sourceC2480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5397) := by
    have ha : (tripleCharges (sourceA2480 + difference 0 2) (sourceB2480 + difference 2 0) sourceC2480) = raw34156 := by
      apply Matrix.ext; unfold tripleCharges sourceA2480 sourceB2480 sourceC2480 difference raw34156; decide +kernel
    rw [ha]
    exact (canonical34156 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2480 + difference 0 3) (sourceB2480 + difference 3 0) sourceC2480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA2480 + difference 0 3) (sourceB2480 + difference 3 0) sourceC2480) = raw34157 := by
      apply Matrix.ext; unfold tripleCharges sourceA2480 sourceB2480 sourceC2480 difference raw34157; decide +kernel
    rw [ha]
    exact (canonical34157 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2480 + difference 0 4) (sourceB2480 + difference 4 0) sourceC2480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA2480 + difference 0 4) (sourceB2480 + difference 4 0) sourceC2480) = raw34158 := by
      apply Matrix.ext; unfold tripleCharges sourceA2480 sourceB2480 sourceC2480 difference raw34158; decide +kernel
    rw [ha]
    exact (canonical34158 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2480 + difference 0 5) (sourceB2480 + difference 5 0) sourceC2480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA2480 + difference 0 5) (sourceB2480 + difference 5 0) sourceC2480) = raw34159 := by
      apply Matrix.ext; unfold tripleCharges sourceA2480 sourceB2480 sourceC2480 difference raw34159; decide +kernel
    rw [ha]
    exact (canonical34159 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2480 + difference 1 0) (sourceB2480 + difference 0 1) sourceC2480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4268) := by
    have ha : (tripleCharges (sourceA2480 + difference 1 0) (sourceB2480 + difference 0 1) sourceC2480) = raw34160 := by
      apply Matrix.ext; unfold tripleCharges sourceA2480 sourceB2480 sourceC2480 difference raw34160; decide +kernel
    rw [ha]
    exact (canonical34160 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2480 + difference 1 2) (sourceB2480 + difference 2 1) sourceC2480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4740) := by
    have ha : (tripleCharges (sourceA2480 + difference 1 2) (sourceB2480 + difference 2 1) sourceC2480) = raw34161 := by
      apply Matrix.ext; unfold tripleCharges sourceA2480 sourceB2480 sourceC2480 difference raw34161; decide +kernel
    rw [ha]
    exact (canonical34161 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2480 + difference 1 3) (sourceB2480 + difference 3 1) sourceC2480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA2480 + difference 1 3) (sourceB2480 + difference 3 1) sourceC2480) = raw34162 := by
      apply Matrix.ext; unfold tripleCharges sourceA2480 sourceB2480 sourceC2480 difference raw34162; decide +kernel
    rw [ha]
    exact (canonical34162 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2480 + difference 1 4) (sourceB2480 + difference 4 1) sourceC2480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4896) := by
    have ha : (tripleCharges (sourceA2480 + difference 1 4) (sourceB2480 + difference 4 1) sourceC2480) = raw34163 := by
      apply Matrix.ext; unfold tripleCharges sourceA2480 sourceB2480 sourceC2480 difference raw34163; decide +kernel
    rw [ha]
    exact (canonical34163 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2480 + difference 1 5) (sourceB2480 + difference 5 1) sourceC2480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA2480 + difference 1 5) (sourceB2480 + difference 5 1) sourceC2480) = raw34164 := by
      apply Matrix.ext; unfold tripleCharges sourceA2480 sourceB2480 sourceC2480 difference raw34164; decide +kernel
    rw [ha]
    exact (canonical34164 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2480 + difference 2 0) (sourceB2480 + difference 0 2) sourceC2480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4217) := by
    have ha : (tripleCharges (sourceA2480 + difference 2 0) (sourceB2480 + difference 0 2) sourceC2480) = raw34165 := by
      apply Matrix.ext; unfold tripleCharges sourceA2480 sourceB2480 sourceC2480 difference raw34165; decide +kernel
    rw [ha]
    exact (canonical34165 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2480 + difference 2 1) (sourceB2480 + difference 1 2) sourceC2480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4648) := by
    have ha : (tripleCharges (sourceA2480 + difference 2 1) (sourceB2480 + difference 1 2) sourceC2480) = raw34166 := by
      apply Matrix.ext; unfold tripleCharges sourceA2480 sourceB2480 sourceC2480 difference raw34166; decide +kernel
    rw [ha]
    exact (canonical34166 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2480 + difference 2 3) (sourceB2480 + difference 3 2) sourceC2480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4805) := by
    have ha : (tripleCharges (sourceA2480 + difference 2 3) (sourceB2480 + difference 3 2) sourceC2480) = raw34167 := by
      apply Matrix.ext; unfold tripleCharges sourceA2480 sourceB2480 sourceC2480 difference raw34167; decide +kernel
    rw [ha]
    exact (canonical34167 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2480 + difference 2 4) (sourceB2480 + difference 4 2) sourceC2480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4839) := by
    have ha : (tripleCharges (sourceA2480 + difference 2 4) (sourceB2480 + difference 4 2) sourceC2480) = raw34168 := by
      apply Matrix.ext; unfold tripleCharges sourceA2480 sourceB2480 sourceC2480 difference raw34168; decide +kernel
    rw [ha]
    exact (canonical34168 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2480 + difference 2 5) (sourceB2480 + difference 5 2) sourceC2480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4826) := by
    have ha : (tripleCharges (sourceA2480 + difference 2 5) (sourceB2480 + difference 5 2) sourceC2480) = raw34169 := by
      apply Matrix.ext; unfold tripleCharges sourceA2480 sourceB2480 sourceC2480 difference raw34169; decide +kernel
    rw [ha]
    exact (canonical34169 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2480 + difference 3 0) (sourceB2480 + difference 0 3) sourceC2480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4220) := by
    have ha : (tripleCharges (sourceA2480 + difference 3 0) (sourceB2480 + difference 0 3) sourceC2480) = raw34170 := by
      apply Matrix.ext; unfold tripleCharges sourceA2480 sourceB2480 sourceC2480 difference raw34170; decide +kernel
    rw [ha]
    exact (canonical34170 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2480 + difference 3 1) (sourceB2480 + difference 1 3) sourceC2480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4651) := by
    have ha : (tripleCharges (sourceA2480 + difference 3 1) (sourceB2480 + difference 1 3) sourceC2480) = raw34171 := by
      apply Matrix.ext; unfold tripleCharges sourceA2480 sourceB2480 sourceC2480 difference raw34171; decide +kernel
    rw [ha]
    exact (canonical34171 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2480 + difference 3 2) (sourceB2480 + difference 2 3) sourceC2480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4714) := by
    have ha : (tripleCharges (sourceA2480 + difference 3 2) (sourceB2480 + difference 2 3) sourceC2480) = raw34172 := by
      apply Matrix.ext; unfold tripleCharges sourceA2480 sourceB2480 sourceC2480 difference raw34172; decide +kernel
    rw [ha]
    exact (canonical34172 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2480 + difference 3 4) (sourceB2480 + difference 4 3) sourceC2480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4845) := by
    have ha : (tripleCharges (sourceA2480 + difference 3 4) (sourceB2480 + difference 4 3) sourceC2480) = raw34173 := by
      apply Matrix.ext; unfold tripleCharges sourceA2480 sourceB2480 sourceC2480 difference raw34173; decide +kernel
    rw [ha]
    exact (canonical34173 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2480 + difference 3 5) (sourceB2480 + difference 5 3) sourceC2480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4827) := by
    have ha : (tripleCharges (sourceA2480 + difference 3 5) (sourceB2480 + difference 5 3) sourceC2480) = raw34174 := by
      apply Matrix.ext; unfold tripleCharges sourceA2480 sourceB2480 sourceC2480 difference raw34174; decide +kernel
    rw [ha]
    exact (canonical34174 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2480 + difference 4 0) (sourceB2480 + difference 0 4) sourceC2480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4223) := by
    have ha : (tripleCharges (sourceA2480 + difference 4 0) (sourceB2480 + difference 0 4) sourceC2480) = raw34175 := by
      apply Matrix.ext; unfold tripleCharges sourceA2480 sourceB2480 sourceC2480 difference raw34175; decide +kernel
    rw [ha]
    exact (canonical34175 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2480 + difference 4 1) (sourceB2480 + difference 1 4) sourceC2480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4653) := by
    have ha : (tripleCharges (sourceA2480 + difference 4 1) (sourceB2480 + difference 1 4) sourceC2480) = raw34176 := by
      apply Matrix.ext; unfold tripleCharges sourceA2480 sourceB2480 sourceC2480 difference raw34176; decide +kernel
    rw [ha]
    exact (canonical34176 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2480 + difference 4 2) (sourceB2480 + difference 2 4) sourceC2480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4716) := by
    have ha : (tripleCharges (sourceA2480 + difference 4 2) (sourceB2480 + difference 2 4) sourceC2480) = raw34177 := by
      apply Matrix.ext; unfold tripleCharges sourceA2480 sourceB2480 sourceC2480 difference raw34177; decide +kernel
    rw [ha]
    exact (canonical34177 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2480 + difference 4 3) (sourceB2480 + difference 3 4) sourceC2480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4810) := by
    have ha : (tripleCharges (sourceA2480 + difference 4 3) (sourceB2480 + difference 3 4) sourceC2480) = raw34178 := by
      apply Matrix.ext; unfold tripleCharges sourceA2480 sourceB2480 sourceC2480 difference raw34178; decide +kernel
    rw [ha]
    exact (canonical34178 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2480 + difference 4 5) (sourceB2480 + difference 5 4) sourceC2480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4828) := by
    have ha : (tripleCharges (sourceA2480 + difference 4 5) (sourceB2480 + difference 5 4) sourceC2480) = raw34179 := by
      apply Matrix.ext; unfold tripleCharges sourceA2480 sourceB2480 sourceC2480 difference raw34179; decide +kernel
    rw [ha]
    exact (canonical34179 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2480 + difference 5 0) (sourceB2480 + difference 0 5) sourceC2480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4219) := by
    have ha : (tripleCharges (sourceA2480 + difference 5 0) (sourceB2480 + difference 0 5) sourceC2480) = raw34180 := by
      apply Matrix.ext; unfold tripleCharges sourceA2480 sourceB2480 sourceC2480 difference raw34180; decide +kernel
    rw [ha]
    exact (canonical34180 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2480 + difference 5 1) (sourceB2480 + difference 1 5) sourceC2480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4650) := by
    have ha : (tripleCharges (sourceA2480 + difference 5 1) (sourceB2480 + difference 1 5) sourceC2480) = raw34181 := by
      apply Matrix.ext; unfold tripleCharges sourceA2480 sourceB2480 sourceC2480 difference raw34181; decide +kernel
    rw [ha]
    exact (canonical34181 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2480 + difference 5 2) (sourceB2480 + difference 2 5) sourceC2480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4713) := by
    have ha : (tripleCharges (sourceA2480 + difference 5 2) (sourceB2480 + difference 2 5) sourceC2480) = raw34182 := by
      apply Matrix.ext; unfold tripleCharges sourceA2480 sourceB2480 sourceC2480 difference raw34182; decide +kernel
    rw [ha]
    exact (canonical34182 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2480 + difference 5 3) (sourceB2480 + difference 3 5) sourceC2480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA2480 + difference 5 3) (sourceB2480 + difference 3 5) sourceC2480) = raw34183 := by
      apply Matrix.ext; unfold tripleCharges sourceA2480 sourceB2480 sourceC2480 difference raw34183; decide +kernel
    rw [ha]
    exact (canonical34183 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2480 + difference 5 4) (sourceB2480 + difference 4 5) sourceC2480) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4843) := by
    have ha : (tripleCharges (sourceA2480 + difference 5 4) (sourceB2480 + difference 4 5) sourceC2480) = raw34184 := by
      apply Matrix.ext; unfold tripleCharges sourceA2480 sourceB2480 sourceC2480 difference raw34184; decide +kernel
    rw [ha]
    exact (canonical34184 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2480 sourceB2480 sourceC2480
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2480, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2481 : Charge := ![0, 1, 0, 1, 0, -2]
def sourceB2481 : Charge := ![3, 0, 0, -2, -1, 0]
def sourceC2481 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceForm2481 : Integer.Sparse Master := [(Sum.inr 4407, 1), (Sum.inr 4410, 1), (Sum.inr 4412, 1), (Sum.inr 4424, 1), (Sum.inr 4471, 1), (Sum.inr 4740, 1), (Sum.inr 4747, 1), (Sum.inr 4750, 1), (Sum.inr 4752, 1), (Sum.inr 4783, 1), (Sum.inr 4785, 1), (Sum.inr 4787, 1), (Sum.inr 4803, 1), (Sum.inr 4805, 1), (Sum.inr 4806, 1), (Sum.inr 4813, 1), (Sum.inr 4835, 1), (Sum.inr 4836, 1), (Sum.inr 4838, 1), (Sum.inr 4839, 1), (Sum.inr 4840, 1), (Sum.inr 4842, 1), (Sum.inr 4867, 1), (Sum.inr 4869, 1), (Sum.inr 4870, 1), (Sum.inr 5105, 1), (Sum.inr 5138, 1), (Sum.inr 5170, 1), (Sum.inr 5172, 1), (Sum.inr 5173, 1)]

theorem sourceEq2481 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2481 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2481 + difference 0 1) (sourceB2481 + difference 1 0) sourceC2481) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5105) := by
    have ha : (tripleCharges (sourceA2481 + difference 0 1) (sourceB2481 + difference 1 0) sourceC2481) = raw32241 := by
      apply Matrix.ext; unfold tripleCharges sourceA2481 sourceB2481 sourceC2481 difference raw32241; decide +kernel
    rw [ha]
    exact (canonical32241 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2481 + difference 0 2) (sourceB2481 + difference 2 0) sourceC2481) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5138) := by
    have ha : (tripleCharges (sourceA2481 + difference 0 2) (sourceB2481 + difference 2 0) sourceC2481) = raw32242 := by
      apply Matrix.ext; unfold tripleCharges sourceA2481 sourceB2481 sourceC2481 difference raw32242; decide +kernel
    rw [ha]
    exact (canonical32242 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2481 + difference 0 3) (sourceB2481 + difference 3 0) sourceC2481) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5172) := by
    have ha : (tripleCharges (sourceA2481 + difference 0 3) (sourceB2481 + difference 3 0) sourceC2481) = raw32487 := by
      apply Matrix.ext; unfold tripleCharges sourceA2481 sourceB2481 sourceC2481 difference raw32487; decide +kernel
    rw [ha]
    exact (canonical32487 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2481 + difference 0 4) (sourceB2481 + difference 4 0) sourceC2481) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5170) := by
    have ha : (tripleCharges (sourceA2481 + difference 0 4) (sourceB2481 + difference 4 0) sourceC2481) = raw32243 := by
      apply Matrix.ext; unfold tripleCharges sourceA2481 sourceB2481 sourceC2481 difference raw32243; decide +kernel
    rw [ha]
    exact (canonical32243 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2481 + difference 0 5) (sourceB2481 + difference 5 0) sourceC2481) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5173) := by
    have ha : (tripleCharges (sourceA2481 + difference 0 5) (sourceB2481 + difference 5 0) sourceC2481) = raw32244 := by
      apply Matrix.ext; unfold tripleCharges sourceA2481 sourceB2481 sourceC2481 difference raw32244; decide +kernel
    rw [ha]
    exact (canonical32244 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2481 + difference 1 0) (sourceB2481 + difference 0 1) sourceC2481) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4471) := by
    have ha : (tripleCharges (sourceA2481 + difference 1 0) (sourceB2481 + difference 0 1) sourceC2481) = raw33558 := by
      apply Matrix.ext; unfold tripleCharges sourceA2481 sourceB2481 sourceC2481 difference raw33558; decide +kernel
    rw [ha]
    exact (canonical33558 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2481 + difference 1 2) (sourceB2481 + difference 2 1) sourceC2481) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4813) := by
    have ha : (tripleCharges (sourceA2481 + difference 1 2) (sourceB2481 + difference 2 1) sourceC2481) = raw33559 := by
      apply Matrix.ext; unfold tripleCharges sourceA2481 sourceB2481 sourceC2481 difference raw33559; decide +kernel
    rw [ha]
    exact (canonical33559 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2481 + difference 1 3) (sourceB2481 + difference 3 1) sourceC2481) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4869) := by
    have ha : (tripleCharges (sourceA2481 + difference 1 3) (sourceB2481 + difference 3 1) sourceC2481) = raw32230 := by
      apply Matrix.ext; unfold tripleCharges sourceA2481 sourceB2481 sourceC2481 difference raw32230; decide +kernel
    rw [ha]
    exact (canonical32230 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2481 + difference 1 4) (sourceB2481 + difference 4 1) sourceC2481) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4867) := by
    have ha : (tripleCharges (sourceA2481 + difference 1 4) (sourceB2481 + difference 4 1) sourceC2481) = raw33560 := by
      apply Matrix.ext; unfold tripleCharges sourceA2481 sourceB2481 sourceC2481 difference raw33560; decide +kernel
    rw [ha]
    exact (canonical33560 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2481 + difference 1 5) (sourceB2481 + difference 5 1) sourceC2481) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4870) := by
    have ha : (tripleCharges (sourceA2481 + difference 1 5) (sourceB2481 + difference 5 1) sourceC2481) = raw33561 := by
      apply Matrix.ext; unfold tripleCharges sourceA2481 sourceB2481 sourceC2481 difference raw33561; decide +kernel
    rw [ha]
    exact (canonical33561 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2481 + difference 2 0) (sourceB2481 + difference 0 2) sourceC2481) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4407) := by
    have ha : (tripleCharges (sourceA2481 + difference 2 0) (sourceB2481 + difference 0 2) sourceC2481) = raw33866 := by
      apply Matrix.ext; unfold tripleCharges sourceA2481 sourceB2481 sourceC2481 difference raw33866; decide +kernel
    rw [ha]
    exact (canonical33866 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2481 + difference 2 1) (sourceB2481 + difference 1 2) sourceC2481) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4740) := by
    have ha : (tripleCharges (sourceA2481 + difference 2 1) (sourceB2481 + difference 1 2) sourceC2481) = raw33867 := by
      apply Matrix.ext; unfold tripleCharges sourceA2481 sourceB2481 sourceC2481 difference raw33867; decide +kernel
    rw [ha]
    exact (canonical33867 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2481 + difference 2 3) (sourceB2481 + difference 3 2) sourceC2481) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4805) := by
    have ha : (tripleCharges (sourceA2481 + difference 2 3) (sourceB2481 + difference 3 2) sourceC2481) = raw32235 := by
      apply Matrix.ext; unfold tripleCharges sourceA2481 sourceB2481 sourceC2481 difference raw32235; decide +kernel
    rw [ha]
    exact (canonical32235 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2481 + difference 2 4) (sourceB2481 + difference 4 2) sourceC2481) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4803) := by
    have ha : (tripleCharges (sourceA2481 + difference 2 4) (sourceB2481 + difference 4 2) sourceC2481) = raw33868 := by
      apply Matrix.ext; unfold tripleCharges sourceA2481 sourceB2481 sourceC2481 difference raw33868; decide +kernel
    rw [ha]
    exact (canonical33868 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2481 + difference 2 5) (sourceB2481 + difference 5 2) sourceC2481) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4806) := by
    have ha : (tripleCharges (sourceA2481 + difference 2 5) (sourceB2481 + difference 5 2) sourceC2481) = raw33869 := by
      apply Matrix.ext; unfold tripleCharges sourceA2481 sourceB2481 sourceC2481 difference raw33869; decide +kernel
    rw [ha]
    exact (canonical33869 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2481 + difference 3 0) (sourceB2481 + difference 0 3) sourceC2481) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4410) := by
    have ha : (tripleCharges (sourceA2481 + difference 3 0) (sourceB2481 + difference 0 3) sourceC2481) = raw34185 := by
      apply Matrix.ext; unfold tripleCharges sourceA2481 sourceB2481 sourceC2481 difference raw34185; decide +kernel
    rw [ha]
    exact (canonical34185 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2481 + difference 3 1) (sourceB2481 + difference 1 3) sourceC2481) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4747) := by
    have ha : (tripleCharges (sourceA2481 + difference 3 1) (sourceB2481 + difference 1 3) sourceC2481) = raw34186 := by
      apply Matrix.ext; unfold tripleCharges sourceA2481 sourceB2481 sourceC2481 difference raw34186; decide +kernel
    rw [ha]
    exact (canonical34186 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2481 + difference 3 2) (sourceB2481 + difference 2 3) sourceC2481) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4783) := by
    have ha : (tripleCharges (sourceA2481 + difference 3 2) (sourceB2481 + difference 2 3) sourceC2481) = raw34187 := by
      apply Matrix.ext; unfold tripleCharges sourceA2481 sourceB2481 sourceC2481 difference raw34187; decide +kernel
    rw [ha]
    exact (canonical34187 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2481 + difference 3 4) (sourceB2481 + difference 4 3) sourceC2481) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4836) := by
    have ha : (tripleCharges (sourceA2481 + difference 3 4) (sourceB2481 + difference 4 3) sourceC2481) = raw34188 := by
      apply Matrix.ext; unfold tripleCharges sourceA2481 sourceB2481 sourceC2481 difference raw34188; decide +kernel
    rw [ha]
    exact (canonical34188 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2481 + difference 3 5) (sourceB2481 + difference 5 3) sourceC2481) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4840) := by
    have ha : (tripleCharges (sourceA2481 + difference 3 5) (sourceB2481 + difference 5 3) sourceC2481) = raw34189 := by
      apply Matrix.ext; unfold tripleCharges sourceA2481 sourceB2481 sourceC2481 difference raw34189; decide +kernel
    rw [ha]
    exact (canonical34189 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2481 + difference 4 0) (sourceB2481 + difference 0 4) sourceC2481) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4412) := by
    have ha : (tripleCharges (sourceA2481 + difference 4 0) (sourceB2481 + difference 0 4) sourceC2481) = raw34190 := by
      apply Matrix.ext; unfold tripleCharges sourceA2481 sourceB2481 sourceC2481 difference raw34190; decide +kernel
    rw [ha]
    exact (canonical34190 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2481 + difference 4 1) (sourceB2481 + difference 1 4) sourceC2481) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4750) := by
    have ha : (tripleCharges (sourceA2481 + difference 4 1) (sourceB2481 + difference 1 4) sourceC2481) = raw34191 := by
      apply Matrix.ext; unfold tripleCharges sourceA2481 sourceB2481 sourceC2481 difference raw34191; decide +kernel
    rw [ha]
    exact (canonical34191 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2481 + difference 4 2) (sourceB2481 + difference 2 4) sourceC2481) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4785) := by
    have ha : (tripleCharges (sourceA2481 + difference 4 2) (sourceB2481 + difference 2 4) sourceC2481) = raw34192 := by
      apply Matrix.ext; unfold tripleCharges sourceA2481 sourceB2481 sourceC2481 difference raw34192; decide +kernel
    rw [ha]
    exact (canonical34192 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2481 + difference 4 3) (sourceB2481 + difference 3 4) sourceC2481) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4839) := by
    have ha : (tripleCharges (sourceA2481 + difference 4 3) (sourceB2481 + difference 3 4) sourceC2481) = raw32245 := by
      apply Matrix.ext; unfold tripleCharges sourceA2481 sourceB2481 sourceC2481 difference raw32245; decide +kernel
    rw [ha]
    exact (canonical32245 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2481 + difference 4 5) (sourceB2481 + difference 5 4) sourceC2481) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4842) := by
    have ha : (tripleCharges (sourceA2481 + difference 4 5) (sourceB2481 + difference 5 4) sourceC2481) = raw34193 := by
      apply Matrix.ext; unfold tripleCharges sourceA2481 sourceB2481 sourceC2481 difference raw34193; decide +kernel
    rw [ha]
    exact (canonical34193 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2481 + difference 5 0) (sourceB2481 + difference 0 5) sourceC2481) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4424) := by
    have ha : (tripleCharges (sourceA2481 + difference 5 0) (sourceB2481 + difference 0 5) sourceC2481) = raw34194 := by
      apply Matrix.ext; unfold tripleCharges sourceA2481 sourceB2481 sourceC2481 difference raw34194; decide +kernel
    rw [ha]
    exact (canonical34194 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2481 + difference 5 1) (sourceB2481 + difference 1 5) sourceC2481) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4752) := by
    have ha : (tripleCharges (sourceA2481 + difference 5 1) (sourceB2481 + difference 1 5) sourceC2481) = raw34195 := by
      apply Matrix.ext; unfold tripleCharges sourceA2481 sourceB2481 sourceC2481 difference raw34195; decide +kernel
    rw [ha]
    exact (canonical34195 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2481 + difference 5 2) (sourceB2481 + difference 2 5) sourceC2481) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4787) := by
    have ha : (tripleCharges (sourceA2481 + difference 5 2) (sourceB2481 + difference 2 5) sourceC2481) = raw32906 := by
      apply Matrix.ext; unfold tripleCharges sourceA2481 sourceB2481 sourceC2481 difference raw32906; decide +kernel
    rw [ha]
    exact (canonical32906 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2481 + difference 5 3) (sourceB2481 + difference 3 5) sourceC2481) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4838) := by
    have ha : (tripleCharges (sourceA2481 + difference 5 3) (sourceB2481 + difference 3 5) sourceC2481) = raw32250 := by
      apply Matrix.ext; unfold tripleCharges sourceA2481 sourceB2481 sourceC2481 difference raw32250; decide +kernel
    rw [ha]
    exact (canonical32250 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2481 + difference 5 4) (sourceB2481 + difference 4 5) sourceC2481) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4835) := by
    have ha : (tripleCharges (sourceA2481 + difference 5 4) (sourceB2481 + difference 4 5) sourceC2481) = raw33649 := by
      apply Matrix.ext; unfold tripleCharges sourceA2481 sourceB2481 sourceC2481 difference raw33649; decide +kernel
    rw [ha]
    exact (canonical33649 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2481 sourceB2481 sourceC2481
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2481, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2482 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2482 : Charge := ![0, 1, 0, 1, -1, -1]
def sourceC2482 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceForm2482 : Integer.Sparse Master := [(Sum.inr 4342, 1), (Sum.inr 4347, 1), (Sum.inr 4349, 1), (Sum.inr 4357, 1), (Sum.inr 4499, 1), (Sum.inr 4677, 1), (Sum.inr 4682, 1), (Sum.inr 4684, 1), (Sum.inr 4690, 1), (Sum.inr 4761, 1), (Sum.inr 4763, 1), (Sum.inr 4768, 1), (Sum.inr 4815, 1), (Sum.inr 4817, 1), (Sum.inr 4821, 1), (Sum.inr 4831, 1), (Sum.inr 4834, 1), (Sum.inr 4835, 2), (Sum.inr 4839, 1), (Sum.inr 4843, 1), (Sum.inr 4846, 1), (Sum.inr 4895, 1), (Sum.inr 4896, 1), (Sum.inr 4901, 1), (Sum.inr 5229, 1), (Sum.inr 5242, 1), (Sum.inr 5259, 1), (Sum.inr 5260, 1), (Sum.inr 5275, 1)]

theorem sourceEq2482 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2482 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2482 + difference 0 1) (sourceB2482 + difference 1 0) sourceC2482) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5229) := by
    have ha : (tripleCharges (sourceA2482 + difference 0 1) (sourceB2482 + difference 1 0) sourceC2482) = raw34196 := by
      apply Matrix.ext; unfold tripleCharges sourceA2482 sourceB2482 sourceC2482 difference raw34196; decide +kernel
    rw [ha]
    exact (canonical34196 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2482 + difference 0 2) (sourceB2482 + difference 2 0) sourceC2482) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5242) := by
    have ha : (tripleCharges (sourceA2482 + difference 0 2) (sourceB2482 + difference 2 0) sourceC2482) = raw34197 := by
      apply Matrix.ext; unfold tripleCharges sourceA2482 sourceB2482 sourceC2482 difference raw34197; decide +kernel
    rw [ha]
    exact (canonical34197 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2482 + difference 0 3) (sourceB2482 + difference 3 0) sourceC2482) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5260) := by
    have ha : (tripleCharges (sourceA2482 + difference 0 3) (sourceB2482 + difference 3 0) sourceC2482) = raw34198 := by
      apply Matrix.ext; unfold tripleCharges sourceA2482 sourceB2482 sourceC2482 difference raw34198; decide +kernel
    rw [ha]
    exact (canonical34198 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2482 + difference 0 4) (sourceB2482 + difference 4 0) sourceC2482) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5275) := by
    have ha : (tripleCharges (sourceA2482 + difference 0 4) (sourceB2482 + difference 4 0) sourceC2482) = raw34199 := by
      apply Matrix.ext; unfold tripleCharges sourceA2482 sourceB2482 sourceC2482 difference raw34199; decide +kernel
    rw [ha]
    exact (canonical34199 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2482 + difference 0 5) (sourceB2482 + difference 5 0) sourceC2482) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA2482 + difference 0 5) (sourceB2482 + difference 5 0) sourceC2482) = raw34200 := by
      apply Matrix.ext; unfold tripleCharges sourceA2482 sourceB2482 sourceC2482 difference raw34200; decide +kernel
    rw [ha]
    exact (canonical34200 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2482 + difference 1 0) (sourceB2482 + difference 0 1) sourceC2482) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4499) := by
    have ha : (tripleCharges (sourceA2482 + difference 1 0) (sourceB2482 + difference 0 1) sourceC2482) = raw34201 := by
      apply Matrix.ext; unfold tripleCharges sourceA2482 sourceB2482 sourceC2482 difference raw34201; decide +kernel
    rw [ha]
    exact (canonical34201 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2482 + difference 1 2) (sourceB2482 + difference 2 1) sourceC2482) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4835) := by
    have ha : (tripleCharges (sourceA2482 + difference 1 2) (sourceB2482 + difference 2 1) sourceC2482) = raw25734 := by
      apply Matrix.ext; unfold tripleCharges sourceA2482 sourceB2482 sourceC2482 difference raw25734; decide +kernel
    rw [ha]
    exact (canonical25734 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2482 + difference 1 3) (sourceB2482 + difference 3 1) sourceC2482) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4896) := by
    have ha : (tripleCharges (sourceA2482 + difference 1 3) (sourceB2482 + difference 3 1) sourceC2482) = raw25735 := by
      apply Matrix.ext; unfold tripleCharges sourceA2482 sourceB2482 sourceC2482 difference raw25735; decide +kernel
    rw [ha]
    exact (canonical25735 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2482 + difference 1 4) (sourceB2482 + difference 4 1) sourceC2482) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4901) := by
    have ha : (tripleCharges (sourceA2482 + difference 1 4) (sourceB2482 + difference 4 1) sourceC2482) = raw25736 := by
      apply Matrix.ext; unfold tripleCharges sourceA2482 sourceB2482 sourceC2482 difference raw25736; decide +kernel
    rw [ha]
    exact (canonical25736 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2482 + difference 1 5) (sourceB2482 + difference 5 1) sourceC2482) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA2482 + difference 1 5) (sourceB2482 + difference 5 1) sourceC2482) = raw25737 := by
      apply Matrix.ext; unfold tripleCharges sourceA2482 sourceB2482 sourceC2482 difference raw25737; decide +kernel
    rw [ha]
    exact (canonical25737 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2482 + difference 2 0) (sourceB2482 + difference 0 2) sourceC2482) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4342) := by
    have ha : (tripleCharges (sourceA2482 + difference 2 0) (sourceB2482 + difference 0 2) sourceC2482) = raw25744 := by
      apply Matrix.ext; unfold tripleCharges sourceA2482 sourceB2482 sourceC2482 difference raw25744; decide +kernel
    rw [ha]
    exact (canonical25744 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2482 + difference 2 1) (sourceB2482 + difference 1 2) sourceC2482) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4677) := by
    have ha : (tripleCharges (sourceA2482 + difference 2 1) (sourceB2482 + difference 1 2) sourceC2482) = raw34202 := by
      apply Matrix.ext; unfold tripleCharges sourceA2482 sourceB2482 sourceC2482 difference raw34202; decide +kernel
    rw [ha]
    exact (canonical34202 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2482 + difference 2 3) (sourceB2482 + difference 3 2) sourceC2482) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4815) := by
    have ha : (tripleCharges (sourceA2482 + difference 2 3) (sourceB2482 + difference 3 2) sourceC2482) = raw34203 := by
      apply Matrix.ext; unfold tripleCharges sourceA2482 sourceB2482 sourceC2482 difference raw34203; decide +kernel
    rw [ha]
    exact (canonical34203 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2482 + difference 2 4) (sourceB2482 + difference 4 2) sourceC2482) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4835) := by
    have ha : (tripleCharges (sourceA2482 + difference 2 4) (sourceB2482 + difference 4 2) sourceC2482) = raw34204 := by
      apply Matrix.ext; unfold tripleCharges sourceA2482 sourceB2482 sourceC2482 difference raw34204; decide +kernel
    rw [ha]
    exact (canonical34204 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2482 + difference 2 5) (sourceB2482 + difference 5 2) sourceC2482) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4831) := by
    have ha : (tripleCharges (sourceA2482 + difference 2 5) (sourceB2482 + difference 5 2) sourceC2482) = raw34205 := by
      apply Matrix.ext; unfold tripleCharges sourceA2482 sourceB2482 sourceC2482 difference raw34205; decide +kernel
    rw [ha]
    exact (canonical34205 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2482 + difference 3 0) (sourceB2482 + difference 0 3) sourceC2482) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4349) := by
    have ha : (tripleCharges (sourceA2482 + difference 3 0) (sourceB2482 + difference 0 3) sourceC2482) = raw25749 := by
      apply Matrix.ext; unfold tripleCharges sourceA2482 sourceB2482 sourceC2482 difference raw25749; decide +kernel
    rw [ha]
    exact (canonical25749 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2482 + difference 3 1) (sourceB2482 + difference 1 3) sourceC2482) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4684) := by
    have ha : (tripleCharges (sourceA2482 + difference 3 1) (sourceB2482 + difference 1 3) sourceC2482) = raw34206 := by
      apply Matrix.ext; unfold tripleCharges sourceA2482 sourceB2482 sourceC2482 difference raw34206; decide +kernel
    rw [ha]
    exact (canonical34206 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2482 + difference 3 2) (sourceB2482 + difference 2 3) sourceC2482) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4763) := by
    have ha : (tripleCharges (sourceA2482 + difference 3 2) (sourceB2482 + difference 2 3) sourceC2482) = raw34207 := by
      apply Matrix.ext; unfold tripleCharges sourceA2482 sourceB2482 sourceC2482 difference raw34207; decide +kernel
    rw [ha]
    exact (canonical34207 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2482 + difference 3 4) (sourceB2482 + difference 4 3) sourceC2482) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4846) := by
    have ha : (tripleCharges (sourceA2482 + difference 3 4) (sourceB2482 + difference 4 3) sourceC2482) = raw34208 := by
      apply Matrix.ext; unfold tripleCharges sourceA2482 sourceB2482 sourceC2482 difference raw34208; decide +kernel
    rw [ha]
    exact (canonical34208 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2482 + difference 3 5) (sourceB2482 + difference 5 3) sourceC2482) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4834) := by
    have ha : (tripleCharges (sourceA2482 + difference 3 5) (sourceB2482 + difference 5 3) sourceC2482) = raw34209 := by
      apply Matrix.ext; unfold tripleCharges sourceA2482 sourceB2482 sourceC2482 difference raw34209; decide +kernel
    rw [ha]
    exact (canonical34209 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2482 + difference 4 0) (sourceB2482 + difference 0 4) sourceC2482) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4357) := by
    have ha : (tripleCharges (sourceA2482 + difference 4 0) (sourceB2482 + difference 0 4) sourceC2482) = raw25754 := by
      apply Matrix.ext; unfold tripleCharges sourceA2482 sourceB2482 sourceC2482 difference raw25754; decide +kernel
    rw [ha]
    exact (canonical25754 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2482 + difference 4 1) (sourceB2482 + difference 1 4) sourceC2482) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4690) := by
    have ha : (tripleCharges (sourceA2482 + difference 4 1) (sourceB2482 + difference 1 4) sourceC2482) = raw34210 := by
      apply Matrix.ext; unfold tripleCharges sourceA2482 sourceB2482 sourceC2482 difference raw34210; decide +kernel
    rw [ha]
    exact (canonical34210 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2482 + difference 4 2) (sourceB2482 + difference 2 4) sourceC2482) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4768) := by
    have ha : (tripleCharges (sourceA2482 + difference 4 2) (sourceB2482 + difference 2 4) sourceC2482) = raw34211 := by
      apply Matrix.ext; unfold tripleCharges sourceA2482 sourceB2482 sourceC2482 difference raw34211; decide +kernel
    rw [ha]
    exact (canonical34211 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2482 + difference 4 3) (sourceB2482 + difference 3 4) sourceC2482) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4821) := by
    have ha : (tripleCharges (sourceA2482 + difference 4 3) (sourceB2482 + difference 3 4) sourceC2482) = raw34212 := by
      apply Matrix.ext; unfold tripleCharges sourceA2482 sourceB2482 sourceC2482 difference raw34212; decide +kernel
    rw [ha]
    exact (canonical34212 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2482 + difference 4 5) (sourceB2482 + difference 5 4) sourceC2482) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4839) := by
    have ha : (tripleCharges (sourceA2482 + difference 4 5) (sourceB2482 + difference 5 4) sourceC2482) = raw34213 := by
      apply Matrix.ext; unfold tripleCharges sourceA2482 sourceB2482 sourceC2482 difference raw34213; decide +kernel
    rw [ha]
    exact (canonical34213 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2482 + difference 5 0) (sourceB2482 + difference 0 5) sourceC2482) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4347) := by
    have ha : (tripleCharges (sourceA2482 + difference 5 0) (sourceB2482 + difference 0 5) sourceC2482) = raw25759 := by
      apply Matrix.ext; unfold tripleCharges sourceA2482 sourceB2482 sourceC2482 difference raw25759; decide +kernel
    rw [ha]
    exact (canonical25759 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2482 + difference 5 1) (sourceB2482 + difference 1 5) sourceC2482) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4682) := by
    have ha : (tripleCharges (sourceA2482 + difference 5 1) (sourceB2482 + difference 1 5) sourceC2482) = raw34214 := by
      apply Matrix.ext; unfold tripleCharges sourceA2482 sourceB2482 sourceC2482 difference raw34214; decide +kernel
    rw [ha]
    exact (canonical34214 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2482 + difference 5 2) (sourceB2482 + difference 2 5) sourceC2482) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4761) := by
    have ha : (tripleCharges (sourceA2482 + difference 5 2) (sourceB2482 + difference 2 5) sourceC2482) = raw34215 := by
      apply Matrix.ext; unfold tripleCharges sourceA2482 sourceB2482 sourceC2482 difference raw34215; decide +kernel
    rw [ha]
    exact (canonical34215 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2482 + difference 5 3) (sourceB2482 + difference 3 5) sourceC2482) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4817) := by
    have ha : (tripleCharges (sourceA2482 + difference 5 3) (sourceB2482 + difference 3 5) sourceC2482) = raw34216 := by
      apply Matrix.ext; unfold tripleCharges sourceA2482 sourceB2482 sourceC2482 difference raw34216; decide +kernel
    rw [ha]
    exact (canonical34216 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2482 + difference 5 4) (sourceB2482 + difference 4 5) sourceC2482) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4843) := by
    have ha : (tripleCharges (sourceA2482 + difference 5 4) (sourceB2482 + difference 4 5) sourceC2482) = raw34217 := by
      apply Matrix.ext; unfold tripleCharges sourceA2482 sourceB2482 sourceC2482 difference raw34217; decide +kernel
    rw [ha]
    exact (canonical34217 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2482 sourceB2482 sourceC2482
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2482, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2483 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2483 : Charge := ![0, 1, 0, 1, -1, -1]
def sourceC2483 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceForm2483 : Integer.Sparse Master := [(Sum.inr 1665, 1), (Sum.inr 1675, 1), (Sum.inr 1676, 1), (Sum.inr 1682, 1), (Sum.inr 1728, 1), (Sum.inr 2142, 1), (Sum.inr 2152, 1), (Sum.inr 2153, 1), (Sum.inr 2158, 1), (Sum.inr 2174, 1), (Sum.inr 2175, 1), (Sum.inr 2178, 1), (Sum.inr 2191, 1), (Sum.inr 2192, 1), (Sum.inr 2205, 1), (Sum.inr 2206, 2), (Sum.inr 2207, 1), (Sum.inr 2216, 1), (Sum.inr 2217, 1), (Sum.inr 2229, 1), (Sum.inr 2230, 1), (Sum.inr 2265, 1), (Sum.inr 2266, 1), (Sum.inr 2293, 1), (Sum.inr 2673, 1), (Sum.inr 2695, 1), (Sum.inr 2723, 1), (Sum.inr 2724, 1), (Sum.inr 2743, 1)]

theorem sourceEq2483 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2483 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2483 + difference 0 1) (sourceB2483 + difference 1 0) sourceC2483) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2673) := by
    have ha : (tripleCharges (sourceA2483 + difference 0 1) (sourceB2483 + difference 1 0) sourceC2483) = raw34218 := by
      apply Matrix.ext; unfold tripleCharges sourceA2483 sourceB2483 sourceC2483 difference raw34218; decide +kernel
    rw [ha]
    exact (canonical34218 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2483 + difference 0 2) (sourceB2483 + difference 2 0) sourceC2483) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2695) := by
    have ha : (tripleCharges (sourceA2483 + difference 0 2) (sourceB2483 + difference 2 0) sourceC2483) = raw34219 := by
      apply Matrix.ext; unfold tripleCharges sourceA2483 sourceB2483 sourceC2483 difference raw34219; decide +kernel
    rw [ha]
    exact (canonical34219 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2483 + difference 0 3) (sourceB2483 + difference 3 0) sourceC2483) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2724) := by
    have ha : (tripleCharges (sourceA2483 + difference 0 3) (sourceB2483 + difference 3 0) sourceC2483) = raw34220 := by
      apply Matrix.ext; unfold tripleCharges sourceA2483 sourceB2483 sourceC2483 difference raw34220; decide +kernel
    rw [ha]
    exact (canonical34220 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2483 + difference 0 4) (sourceB2483 + difference 4 0) sourceC2483) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2743) := by
    have ha : (tripleCharges (sourceA2483 + difference 0 4) (sourceB2483 + difference 4 0) sourceC2483) = raw34221 := by
      apply Matrix.ext; unfold tripleCharges sourceA2483 sourceB2483 sourceC2483 difference raw34221; decide +kernel
    rw [ha]
    exact (canonical34221 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2483 + difference 0 5) (sourceB2483 + difference 5 0) sourceC2483) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA2483 + difference 0 5) (sourceB2483 + difference 5 0) sourceC2483) = raw34222 := by
      apply Matrix.ext; unfold tripleCharges sourceA2483 sourceB2483 sourceC2483 difference raw34222; decide +kernel
    rw [ha]
    exact (canonical34222 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2483 + difference 1 0) (sourceB2483 + difference 0 1) sourceC2483) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1728) := by
    have ha : (tripleCharges (sourceA2483 + difference 1 0) (sourceB2483 + difference 0 1) sourceC2483) = raw34223 := by
      apply Matrix.ext; unfold tripleCharges sourceA2483 sourceB2483 sourceC2483 difference raw34223; decide +kernel
    rw [ha]
    exact (canonical34223 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2483 + difference 1 2) (sourceB2483 + difference 2 1) sourceC2483) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2206) := by
    have ha : (tripleCharges (sourceA2483 + difference 1 2) (sourceB2483 + difference 2 1) sourceC2483) = raw25764 := by
      apply Matrix.ext; unfold tripleCharges sourceA2483 sourceB2483 sourceC2483 difference raw25764; decide +kernel
    rw [ha]
    exact (canonical25764 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2483 + difference 1 3) (sourceB2483 + difference 3 1) sourceC2483) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2266) := by
    have ha : (tripleCharges (sourceA2483 + difference 1 3) (sourceB2483 + difference 3 1) sourceC2483) = raw25765 := by
      apply Matrix.ext; unfold tripleCharges sourceA2483 sourceB2483 sourceC2483 difference raw25765; decide +kernel
    rw [ha]
    exact (canonical25765 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2483 + difference 1 4) (sourceB2483 + difference 4 1) sourceC2483) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2293) := by
    have ha : (tripleCharges (sourceA2483 + difference 1 4) (sourceB2483 + difference 4 1) sourceC2483) = raw25766 := by
      apply Matrix.ext; unfold tripleCharges sourceA2483 sourceB2483 sourceC2483 difference raw25766; decide +kernel
    rw [ha]
    exact (canonical25766 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2483 + difference 1 5) (sourceB2483 + difference 5 1) sourceC2483) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2265) := by
    have ha : (tripleCharges (sourceA2483 + difference 1 5) (sourceB2483 + difference 5 1) sourceC2483) = raw25767 := by
      apply Matrix.ext; unfold tripleCharges sourceA2483 sourceB2483 sourceC2483 difference raw25767; decide +kernel
    rw [ha]
    exact (canonical25767 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2483 + difference 2 0) (sourceB2483 + difference 0 2) sourceC2483) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1665) := by
    have ha : (tripleCharges (sourceA2483 + difference 2 0) (sourceB2483 + difference 0 2) sourceC2483) = raw25774 := by
      apply Matrix.ext; unfold tripleCharges sourceA2483 sourceB2483 sourceC2483 difference raw25774; decide +kernel
    rw [ha]
    exact (canonical25774 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2483 + difference 2 1) (sourceB2483 + difference 1 2) sourceC2483) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2142) := by
    have ha : (tripleCharges (sourceA2483 + difference 2 1) (sourceB2483 + difference 1 2) sourceC2483) = raw34224 := by
      apply Matrix.ext; unfold tripleCharges sourceA2483 sourceB2483 sourceC2483 difference raw34224; decide +kernel
    rw [ha]
    exact (canonical34224 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2483 + difference 2 3) (sourceB2483 + difference 3 2) sourceC2483) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2192) := by
    have ha : (tripleCharges (sourceA2483 + difference 2 3) (sourceB2483 + difference 3 2) sourceC2483) = raw34225 := by
      apply Matrix.ext; unfold tripleCharges sourceA2483 sourceB2483 sourceC2483 difference raw34225; decide +kernel
    rw [ha]
    exact (canonical34225 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2483 + difference 2 4) (sourceB2483 + difference 4 2) sourceC2483) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2206) := by
    have ha : (tripleCharges (sourceA2483 + difference 2 4) (sourceB2483 + difference 4 2) sourceC2483) = raw34226 := by
      apply Matrix.ext; unfold tripleCharges sourceA2483 sourceB2483 sourceC2483 difference raw34226; decide +kernel
    rw [ha]
    exact (canonical34226 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2483 + difference 2 5) (sourceB2483 + difference 5 2) sourceC2483) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2191) := by
    have ha : (tripleCharges (sourceA2483 + difference 2 5) (sourceB2483 + difference 5 2) sourceC2483) = raw34227 := by
      apply Matrix.ext; unfold tripleCharges sourceA2483 sourceB2483 sourceC2483 difference raw34227; decide +kernel
    rw [ha]
    exact (canonical34227 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2483 + difference 3 0) (sourceB2483 + difference 0 3) sourceC2483) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1675) := by
    have ha : (tripleCharges (sourceA2483 + difference 3 0) (sourceB2483 + difference 0 3) sourceC2483) = raw25779 := by
      apply Matrix.ext; unfold tripleCharges sourceA2483 sourceB2483 sourceC2483 difference raw25779; decide +kernel
    rw [ha]
    exact (canonical25779 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2483 + difference 3 1) (sourceB2483 + difference 1 3) sourceC2483) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2152) := by
    have ha : (tripleCharges (sourceA2483 + difference 3 1) (sourceB2483 + difference 1 3) sourceC2483) = raw34228 := by
      apply Matrix.ext; unfold tripleCharges sourceA2483 sourceB2483 sourceC2483 difference raw34228; decide +kernel
    rw [ha]
    exact (canonical34228 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2483 + difference 3 2) (sourceB2483 + difference 2 3) sourceC2483) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2174) := by
    have ha : (tripleCharges (sourceA2483 + difference 3 2) (sourceB2483 + difference 2 3) sourceC2483) = raw34229 := by
      apply Matrix.ext; unfold tripleCharges sourceA2483 sourceB2483 sourceC2483 difference raw34229; decide +kernel
    rw [ha]
    exact (canonical34229 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2483 + difference 3 4) (sourceB2483 + difference 4 3) sourceC2483) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2229) := by
    have ha : (tripleCharges (sourceA2483 + difference 3 4) (sourceB2483 + difference 4 3) sourceC2483) = raw34230 := by
      apply Matrix.ext; unfold tripleCharges sourceA2483 sourceB2483 sourceC2483 difference raw34230; decide +kernel
    rw [ha]
    exact (canonical34230 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2483 + difference 3 5) (sourceB2483 + difference 5 3) sourceC2483) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2205) := by
    have ha : (tripleCharges (sourceA2483 + difference 3 5) (sourceB2483 + difference 5 3) sourceC2483) = raw34231 := by
      apply Matrix.ext; unfold tripleCharges sourceA2483 sourceB2483 sourceC2483 difference raw34231; decide +kernel
    rw [ha]
    exact (canonical34231 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2483 + difference 4 0) (sourceB2483 + difference 0 4) sourceC2483) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1682) := by
    have ha : (tripleCharges (sourceA2483 + difference 4 0) (sourceB2483 + difference 0 4) sourceC2483) = raw25784 := by
      apply Matrix.ext; unfold tripleCharges sourceA2483 sourceB2483 sourceC2483 difference raw25784; decide +kernel
    rw [ha]
    exact (canonical25784 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2483 + difference 4 1) (sourceB2483 + difference 1 4) sourceC2483) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2158) := by
    have ha : (tripleCharges (sourceA2483 + difference 4 1) (sourceB2483 + difference 1 4) sourceC2483) = raw34232 := by
      apply Matrix.ext; unfold tripleCharges sourceA2483 sourceB2483 sourceC2483 difference raw34232; decide +kernel
    rw [ha]
    exact (canonical34232 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2483 + difference 4 2) (sourceB2483 + difference 2 4) sourceC2483) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2178) := by
    have ha : (tripleCharges (sourceA2483 + difference 4 2) (sourceB2483 + difference 2 4) sourceC2483) = raw34233 := by
      apply Matrix.ext; unfold tripleCharges sourceA2483 sourceB2483 sourceC2483 difference raw34233; decide +kernel
    rw [ha]
    exact (canonical34233 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2483 + difference 4 3) (sourceB2483 + difference 3 4) sourceC2483) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2217) := by
    have ha : (tripleCharges (sourceA2483 + difference 4 3) (sourceB2483 + difference 3 4) sourceC2483) = raw34234 := by
      apply Matrix.ext; unfold tripleCharges sourceA2483 sourceB2483 sourceC2483 difference raw34234; decide +kernel
    rw [ha]
    exact (canonical34234 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2483 + difference 4 5) (sourceB2483 + difference 5 4) sourceC2483) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2216) := by
    have ha : (tripleCharges (sourceA2483 + difference 4 5) (sourceB2483 + difference 5 4) sourceC2483) = raw34235 := by
      apply Matrix.ext; unfold tripleCharges sourceA2483 sourceB2483 sourceC2483 difference raw34235; decide +kernel
    rw [ha]
    exact (canonical34235 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2483 + difference 5 0) (sourceB2483 + difference 0 5) sourceC2483) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1676) := by
    have ha : (tripleCharges (sourceA2483 + difference 5 0) (sourceB2483 + difference 0 5) sourceC2483) = raw25789 := by
      apply Matrix.ext; unfold tripleCharges sourceA2483 sourceB2483 sourceC2483 difference raw25789; decide +kernel
    rw [ha]
    exact (canonical25789 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2483 + difference 5 1) (sourceB2483 + difference 1 5) sourceC2483) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2153) := by
    have ha : (tripleCharges (sourceA2483 + difference 5 1) (sourceB2483 + difference 1 5) sourceC2483) = raw34236 := by
      apply Matrix.ext; unfold tripleCharges sourceA2483 sourceB2483 sourceC2483 difference raw34236; decide +kernel
    rw [ha]
    exact (canonical34236 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2483 + difference 5 2) (sourceB2483 + difference 2 5) sourceC2483) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2175) := by
    have ha : (tripleCharges (sourceA2483 + difference 5 2) (sourceB2483 + difference 2 5) sourceC2483) = raw34237 := by
      apply Matrix.ext; unfold tripleCharges sourceA2483 sourceB2483 sourceC2483 difference raw34237; decide +kernel
    rw [ha]
    exact (canonical34237 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2483 + difference 5 3) (sourceB2483 + difference 3 5) sourceC2483) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2207) := by
    have ha : (tripleCharges (sourceA2483 + difference 5 3) (sourceB2483 + difference 3 5) sourceC2483) = raw34238 := by
      apply Matrix.ext; unfold tripleCharges sourceA2483 sourceB2483 sourceC2483 difference raw34238; decide +kernel
    rw [ha]
    exact (canonical34238 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2483 + difference 5 4) (sourceB2483 + difference 4 5) sourceC2483) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2230) := by
    have ha : (tripleCharges (sourceA2483 + difference 5 4) (sourceB2483 + difference 4 5) sourceC2483) = raw34239 := by
      apply Matrix.ext; unfold tripleCharges sourceA2483 sourceB2483 sourceC2483 difference raw34239; decide +kernel
    rw [ha]
    exact (canonical34239 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2483 sourceB2483 sourceC2483
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2483, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2484 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2484 : Charge := ![0, 1, 0, 1, -1, -1]
def sourceC2484 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceForm2484 : Integer.Sparse Master := [(Sum.inr 1803, 1), (Sum.inr 1808, 1), (Sum.inr 1810, 1), (Sum.inr 1816, 1), (Sum.inr 2054, 1), (Sum.inr 3392, 1), (Sum.inr 4084, -1)]

theorem sourceEq2484 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2484 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2484 + difference 0 1) (sourceB2484 + difference 1 0) sourceC2484) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3392) := by
    have ha : (tripleCharges (sourceA2484 + difference 0 1) (sourceB2484 + difference 1 0) sourceC2484) = raw34240 := by
      apply Matrix.ext; unfold tripleCharges sourceA2484 sourceB2484 sourceC2484 difference raw34240; decide +kernel
    rw [ha]
    exact (canonical34240 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2484 + difference 1 1) (sourceB2484 + difference 1 1) sourceC2484) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2054) := by
    have ha : (tripleCharges (sourceA2484 + difference 1 1) (sourceB2484 + difference 1 1) sourceC2484) = raw27348 := by
      apply Matrix.ext; unfold tripleCharges sourceA2484 sourceB2484 sourceC2484 difference raw27348; decide +kernel
    rw [ha]
    exact (canonical27348 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2484 + difference 2 1) (sourceB2484 + difference 1 2) sourceC2484) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1803) := by
    have ha : (tripleCharges (sourceA2484 + difference 2 1) (sourceB2484 + difference 1 2) sourceC2484) = raw34241 := by
      apply Matrix.ext; unfold tripleCharges sourceA2484 sourceB2484 sourceC2484 difference raw34241; decide +kernel
    rw [ha]
    exact (canonical34241 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2484 + difference 3 1) (sourceB2484 + difference 1 3) sourceC2484) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1810) := by
    have ha : (tripleCharges (sourceA2484 + difference 3 1) (sourceB2484 + difference 1 3) sourceC2484) = raw34242 := by
      apply Matrix.ext; unfold tripleCharges sourceA2484 sourceB2484 sourceC2484 difference raw34242; decide +kernel
    rw [ha]
    exact (canonical34242 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2484 + difference 4 1) (sourceB2484 + difference 1 4) sourceC2484) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1816) := by
    have ha : (tripleCharges (sourceA2484 + difference 4 1) (sourceB2484 + difference 1 4) sourceC2484) = raw29305 := by
      apply Matrix.ext; unfold tripleCharges sourceA2484 sourceB2484 sourceC2484 difference raw29305; decide +kernel
    rw [ha]
    exact (canonical29305 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2484 + difference 5 1) (sourceB2484 + difference 1 5) sourceC2484) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1808) := by
    have ha : (tripleCharges (sourceA2484 + difference 5 1) (sourceB2484 + difference 1 5) sourceC2484) = raw27344 := by
      apply Matrix.ext; unfold tripleCharges sourceA2484 sourceB2484 sourceC2484 difference raw27344; decide +kernel
    rw [ha]
    exact (canonical27344 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2484 + sourceB2484) sourceC2484) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA2484 + sourceB2484) sourceC2484) = raw20142 := by
      apply Matrix.ext; unfold doubleCharges sourceA2484 sourceB2484 sourceC2484 raw20142; decide +kernel
    rw [ha]
    exact (canonical20142 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2484 sourceB2484 sourceC2484
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2484, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2485 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2485 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC2485 : Charge := ![0, 1, 0, 1, -1, -1]
def sourceForm2485 : Integer.Sparse Master := [(Sum.inr 4210, 1), (Sum.inr 4212, 1), (Sum.inr 4213, 1), (Sum.inr 4224, 1), (Sum.inr 4265, 1), (Sum.inr 4642, 1), (Sum.inr 4644, 1), (Sum.inr 4645, 1), (Sum.inr 4654, 1), (Sum.inr 4709, 1), (Sum.inr 4710, 1), (Sum.inr 4717, 1), (Sum.inr 4737, 1), (Sum.inr 4787, 1), (Sum.inr 4788, 2), (Sum.inr 4802, 1), (Sum.inr 4804, 1), (Sum.inr 4811, 1), (Sum.inr 4831, 1), (Sum.inr 4832, 1), (Sum.inr 4835, 2), (Sum.inr 4888, 2), (Sum.inr 5368, 1), (Sum.inr 5395, 1), (Sum.inr 5428, 1), (Sum.inr 5434, 1), (Sum.inr 5439, 1)]

theorem sourceEq2485 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2485 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2485 + difference 0 1) (sourceB2485 + difference 1 0) sourceC2485) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5368) := by
    have ha : (tripleCharges (sourceA2485 + difference 0 1) (sourceB2485 + difference 1 0) sourceC2485) = raw15071 := by
      apply Matrix.ext; unfold tripleCharges sourceA2485 sourceB2485 sourceC2485 difference raw15071; decide +kernel
    rw [ha]
    exact (canonical15071 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2485 + difference 0 2) (sourceB2485 + difference 2 0) sourceC2485) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5395) := by
    have ha : (tripleCharges (sourceA2485 + difference 0 2) (sourceB2485 + difference 2 0) sourceC2485) = raw15072 := by
      apply Matrix.ext; unfold tripleCharges sourceA2485 sourceB2485 sourceC2485 difference raw15072; decide +kernel
    rw [ha]
    exact (canonical15072 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2485 + difference 0 3) (sourceB2485 + difference 3 0) sourceC2485) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA2485 + difference 0 3) (sourceB2485 + difference 3 0) sourceC2485) = raw3426 := by
      apply Matrix.ext; unfold tripleCharges sourceA2485 sourceB2485 sourceC2485 difference raw3426; decide +kernel
    rw [ha]
    exact (canonical3426 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2485 + difference 0 4) (sourceB2485 + difference 4 0) sourceC2485) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5428) := by
    have ha : (tripleCharges (sourceA2485 + difference 0 4) (sourceB2485 + difference 4 0) sourceC2485) = raw15073 := by
      apply Matrix.ext; unfold tripleCharges sourceA2485 sourceB2485 sourceC2485 difference raw15073; decide +kernel
    rw [ha]
    exact (canonical15073 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2485 + difference 0 5) (sourceB2485 + difference 5 0) sourceC2485) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA2485 + difference 0 5) (sourceB2485 + difference 5 0) sourceC2485) = raw3416 := by
      apply Matrix.ext; unfold tripleCharges sourceA2485 sourceB2485 sourceC2485 difference raw3416; decide +kernel
    rw [ha]
    exact (canonical3416 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2485 + difference 1 0) (sourceB2485 + difference 0 1) sourceC2485) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4265) := by
    have ha : (tripleCharges (sourceA2485 + difference 1 0) (sourceB2485 + difference 0 1) sourceC2485) = raw34243 := by
      apply Matrix.ext; unfold tripleCharges sourceA2485 sourceB2485 sourceC2485 difference raw34243; decide +kernel
    rw [ha]
    exact (canonical34243 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2485 + difference 1 2) (sourceB2485 + difference 2 1) sourceC2485) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4737) := by
    have ha : (tripleCharges (sourceA2485 + difference 1 2) (sourceB2485 + difference 2 1) sourceC2485) = raw34244 := by
      apply Matrix.ext; unfold tripleCharges sourceA2485 sourceB2485 sourceC2485 difference raw34244; decide +kernel
    rw [ha]
    exact (canonical34244 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2485 + difference 1 3) (sourceB2485 + difference 3 1) sourceC2485) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA2485 + difference 1 3) (sourceB2485 + difference 3 1) sourceC2485) = raw15062 := by
      apply Matrix.ext; unfold tripleCharges sourceA2485 sourceB2485 sourceC2485 difference raw15062; decide +kernel
    rw [ha]
    exact (canonical15062 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2485 + difference 1 4) (sourceB2485 + difference 4 1) sourceC2485) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4835) := by
    have ha : (tripleCharges (sourceA2485 + difference 1 4) (sourceB2485 + difference 4 1) sourceC2485) = raw34245 := by
      apply Matrix.ext; unfold tripleCharges sourceA2485 sourceB2485 sourceC2485 difference raw34245; decide +kernel
    rw [ha]
    exact (canonical34245 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2485 + difference 1 5) (sourceB2485 + difference 5 1) sourceC2485) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA2485 + difference 1 5) (sourceB2485 + difference 5 1) sourceC2485) = raw34246 := by
      apply Matrix.ext; unfold tripleCharges sourceA2485 sourceB2485 sourceC2485 difference raw34246; decide +kernel
    rw [ha]
    exact (canonical34246 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2485 + difference 2 0) (sourceB2485 + difference 0 2) sourceC2485) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4210) := by
    have ha : (tripleCharges (sourceA2485 + difference 2 0) (sourceB2485 + difference 0 2) sourceC2485) = raw34247 := by
      apply Matrix.ext; unfold tripleCharges sourceA2485 sourceB2485 sourceC2485 difference raw34247; decide +kernel
    rw [ha]
    exact (canonical34247 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2485 + difference 2 1) (sourceB2485 + difference 1 2) sourceC2485) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4642) := by
    have ha : (tripleCharges (sourceA2485 + difference 2 1) (sourceB2485 + difference 1 2) sourceC2485) = raw34248 := by
      apply Matrix.ext; unfold tripleCharges sourceA2485 sourceB2485 sourceC2485 difference raw34248; decide +kernel
    rw [ha]
    exact (canonical34248 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2485 + difference 2 3) (sourceB2485 + difference 3 2) sourceC2485) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA2485 + difference 2 3) (sourceB2485 + difference 3 2) sourceC2485) = raw15066 := by
      apply Matrix.ext; unfold tripleCharges sourceA2485 sourceB2485 sourceC2485 difference raw15066; decide +kernel
    rw [ha]
    exact (canonical15066 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2485 + difference 2 4) (sourceB2485 + difference 4 2) sourceC2485) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4787) := by
    have ha : (tripleCharges (sourceA2485 + difference 2 4) (sourceB2485 + difference 4 2) sourceC2485) = raw34249 := by
      apply Matrix.ext; unfold tripleCharges sourceA2485 sourceB2485 sourceC2485 difference raw34249; decide +kernel
    rw [ha]
    exact (canonical34249 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2485 + difference 2 5) (sourceB2485 + difference 5 2) sourceC2485) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4831) := by
    have ha : (tripleCharges (sourceA2485 + difference 2 5) (sourceB2485 + difference 5 2) sourceC2485) = raw34250 := by
      apply Matrix.ext; unfold tripleCharges sourceA2485 sourceB2485 sourceC2485 difference raw34250; decide +kernel
    rw [ha]
    exact (canonical34250 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2485 + difference 3 0) (sourceB2485 + difference 0 3) sourceC2485) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4213) := by
    have ha : (tripleCharges (sourceA2485 + difference 3 0) (sourceB2485 + difference 0 3) sourceC2485) = raw34251 := by
      apply Matrix.ext; unfold tripleCharges sourceA2485 sourceB2485 sourceC2485 difference raw34251; decide +kernel
    rw [ha]
    exact (canonical34251 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2485 + difference 3 1) (sourceB2485 + difference 1 3) sourceC2485) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4645) := by
    have ha : (tripleCharges (sourceA2485 + difference 3 1) (sourceB2485 + difference 1 3) sourceC2485) = raw34252 := by
      apply Matrix.ext; unfold tripleCharges sourceA2485 sourceB2485 sourceC2485 difference raw34252; decide +kernel
    rw [ha]
    exact (canonical34252 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2485 + difference 3 2) (sourceB2485 + difference 2 3) sourceC2485) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4710) := by
    have ha : (tripleCharges (sourceA2485 + difference 3 2) (sourceB2485 + difference 2 3) sourceC2485) = raw34253 := by
      apply Matrix.ext; unfold tripleCharges sourceA2485 sourceB2485 sourceC2485 difference raw34253; decide +kernel
    rw [ha]
    exact (canonical34253 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2485 + difference 3 4) (sourceB2485 + difference 4 3) sourceC2485) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4788) := by
    have ha : (tripleCharges (sourceA2485 + difference 3 4) (sourceB2485 + difference 4 3) sourceC2485) = raw34254 := by
      apply Matrix.ext; unfold tripleCharges sourceA2485 sourceB2485 sourceC2485 difference raw34254; decide +kernel
    rw [ha]
    exact (canonical34254 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2485 + difference 3 5) (sourceB2485 + difference 5 3) sourceC2485) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4832) := by
    have ha : (tripleCharges (sourceA2485 + difference 3 5) (sourceB2485 + difference 5 3) sourceC2485) = raw34255 := by
      apply Matrix.ext; unfold tripleCharges sourceA2485 sourceB2485 sourceC2485 difference raw34255; decide +kernel
    rw [ha]
    exact (canonical34255 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2485 + difference 4 0) (sourceB2485 + difference 0 4) sourceC2485) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4224) := by
    have ha : (tripleCharges (sourceA2485 + difference 4 0) (sourceB2485 + difference 0 4) sourceC2485) = raw34256 := by
      apply Matrix.ext; unfold tripleCharges sourceA2485 sourceB2485 sourceC2485 difference raw34256; decide +kernel
    rw [ha]
    exact (canonical34256 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2485 + difference 4 1) (sourceB2485 + difference 1 4) sourceC2485) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4654) := by
    have ha : (tripleCharges (sourceA2485 + difference 4 1) (sourceB2485 + difference 1 4) sourceC2485) = raw34257 := by
      apply Matrix.ext; unfold tripleCharges sourceA2485 sourceB2485 sourceC2485 difference raw34257; decide +kernel
    rw [ha]
    exact (canonical34257 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2485 + difference 4 2) (sourceB2485 + difference 2 4) sourceC2485) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4717) := by
    have ha : (tripleCharges (sourceA2485 + difference 4 2) (sourceB2485 + difference 2 4) sourceC2485) = raw34258 := by
      apply Matrix.ext; unfold tripleCharges sourceA2485 sourceB2485 sourceC2485 difference raw34258; decide +kernel
    rw [ha]
    exact (canonical34258 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2485 + difference 4 3) (sourceB2485 + difference 3 4) sourceC2485) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4811) := by
    have ha : (tripleCharges (sourceA2485 + difference 4 3) (sourceB2485 + difference 3 4) sourceC2485) = raw15074 := by
      apply Matrix.ext; unfold tripleCharges sourceA2485 sourceB2485 sourceC2485 difference raw15074; decide +kernel
    rw [ha]
    exact (canonical15074 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2485 + difference 4 5) (sourceB2485 + difference 5 4) sourceC2485) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4835) := by
    have ha : (tripleCharges (sourceA2485 + difference 4 5) (sourceB2485 + difference 5 4) sourceC2485) = raw34259 := by
      apply Matrix.ext; unfold tripleCharges sourceA2485 sourceB2485 sourceC2485 difference raw34259; decide +kernel
    rw [ha]
    exact (canonical34259 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2485 + difference 5 0) (sourceB2485 + difference 0 5) sourceC2485) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4212) := by
    have ha : (tripleCharges (sourceA2485 + difference 5 0) (sourceB2485 + difference 0 5) sourceC2485) = raw34260 := by
      apply Matrix.ext; unfold tripleCharges sourceA2485 sourceB2485 sourceC2485 difference raw34260; decide +kernel
    rw [ha]
    exact (canonical34260 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2485 + difference 5 1) (sourceB2485 + difference 1 5) sourceC2485) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4644) := by
    have ha : (tripleCharges (sourceA2485 + difference 5 1) (sourceB2485 + difference 1 5) sourceC2485) = raw34261 := by
      apply Matrix.ext; unfold tripleCharges sourceA2485 sourceB2485 sourceC2485 difference raw34261; decide +kernel
    rw [ha]
    exact (canonical34261 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2485 + difference 5 2) (sourceB2485 + difference 2 5) sourceC2485) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4709) := by
    have ha : (tripleCharges (sourceA2485 + difference 5 2) (sourceB2485 + difference 2 5) sourceC2485) = raw34262 := by
      apply Matrix.ext; unfold tripleCharges sourceA2485 sourceB2485 sourceC2485 difference raw34262; decide +kernel
    rw [ha]
    exact (canonical34262 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2485 + difference 5 3) (sourceB2485 + difference 3 5) sourceC2485) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA2485 + difference 5 3) (sourceB2485 + difference 3 5) sourceC2485) = raw15078 := by
      apply Matrix.ext; unfold tripleCharges sourceA2485 sourceB2485 sourceC2485 difference raw15078; decide +kernel
    rw [ha]
    exact (canonical15078 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2485 + difference 5 4) (sourceB2485 + difference 4 5) sourceC2485) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4788) := by
    have ha : (tripleCharges (sourceA2485 + difference 5 4) (sourceB2485 + difference 4 5) sourceC2485) = raw34263 := by
      apply Matrix.ext; unfold tripleCharges sourceA2485 sourceB2485 sourceC2485 difference raw34263; decide +kernel
    rw [ha]
    exact (canonical34263 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2485 sourceB2485 sourceC2485
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2485, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2486 : Charge := ![0, 1, 0, 1, -1, -1]
def sourceB2486 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC2486 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceForm2486 : Integer.Sparse Master := [(Sum.inr 4397, 1), (Sum.inr 4402, 1), (Sum.inr 4404, 1), (Sum.inr 4424, 1), (Sum.inr 4453, 1), (Sum.inr 4737, 1), (Sum.inr 4742, 1), (Sum.inr 4745, 1), (Sum.inr 4752, 1), (Sum.inr 4780, 1), (Sum.inr 4782, 1), (Sum.inr 4787, 1), (Sum.inr 4799, 2), (Sum.inr 4802, 1), (Sum.inr 4803, 1), (Sum.inr 4828, 1), (Sum.inr 4829, 1), (Sum.inr 4834, 1), (Sum.inr 4836, 1), (Sum.inr 4838, 1), (Sum.inr 4839, 1), (Sum.inr 4861, 1), (Sum.inr 4866, 1), (Sum.inr 4867, 1), (Sum.inr 5102, 1), (Sum.inr 5135, 1), (Sum.inr 5164, 1), (Sum.inr 5169, 1), (Sum.inr 5170, 1)]

theorem sourceEq2486 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2486 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2486 + difference 0 1) (sourceB2486 + difference 1 0) sourceC2486) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5102) := by
    have ha : (tripleCharges (sourceA2486 + difference 0 1) (sourceB2486 + difference 1 0) sourceC2486) = raw33142 := by
      apply Matrix.ext; unfold tripleCharges sourceA2486 sourceB2486 sourceC2486 difference raw33142; decide +kernel
    rw [ha]
    exact (canonical33142 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2486 + difference 0 2) (sourceB2486 + difference 2 0) sourceC2486) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5135) := by
    have ha : (tripleCharges (sourceA2486 + difference 0 2) (sourceB2486 + difference 2 0) sourceC2486) = raw32909 := by
      apply Matrix.ext; unfold tripleCharges sourceA2486 sourceB2486 sourceC2486 difference raw32909; decide +kernel
    rw [ha]
    exact (canonical32909 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2486 + difference 0 3) (sourceB2486 + difference 3 0) sourceC2486) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA2486 + difference 0 3) (sourceB2486 + difference 3 0) sourceC2486) = raw32254 := by
      apply Matrix.ext; unfold tripleCharges sourceA2486 sourceB2486 sourceC2486 difference raw32254; decide +kernel
    rw [ha]
    exact (canonical32254 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2486 + difference 0 4) (sourceB2486 + difference 4 0) sourceC2486) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5164) := by
    have ha : (tripleCharges (sourceA2486 + difference 0 4) (sourceB2486 + difference 4 0) sourceC2486) = raw32834 := by
      apply Matrix.ext; unfold tripleCharges sourceA2486 sourceB2486 sourceC2486 difference raw32834; decide +kernel
    rw [ha]
    exact (canonical32834 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2486 + difference 0 5) (sourceB2486 + difference 5 0) sourceC2486) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5170) := by
    have ha : (tripleCharges (sourceA2486 + difference 0 5) (sourceB2486 + difference 5 0) sourceC2486) = raw32243 := by
      apply Matrix.ext; unfold tripleCharges sourceA2486 sourceB2486 sourceC2486 difference raw32243; decide +kernel
    rw [ha]
    exact (canonical32243 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2486 + difference 1 0) (sourceB2486 + difference 0 1) sourceC2486) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4453) := by
    have ha : (tripleCharges (sourceA2486 + difference 1 0) (sourceB2486 + difference 0 1) sourceC2486) = raw33648 := by
      apply Matrix.ext; unfold tripleCharges sourceA2486 sourceB2486 sourceC2486 difference raw33648; decide +kernel
    rw [ha]
    exact (canonical33648 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2486 + difference 1 2) (sourceB2486 + difference 2 1) sourceC2486) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4799) := by
    have ha : (tripleCharges (sourceA2486 + difference 1 2) (sourceB2486 + difference 2 1) sourceC2486) = raw33650 := by
      apply Matrix.ext; unfold tripleCharges sourceA2486 sourceB2486 sourceC2486 difference raw33650; decide +kernel
    rw [ha]
    exact (canonical33650 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2486 + difference 1 3) (sourceB2486 + difference 3 1) sourceC2486) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA2486 + difference 1 3) (sourceB2486 + difference 3 1) sourceC2486) = raw33568 := by
      apply Matrix.ext; unfold tripleCharges sourceA2486 sourceB2486 sourceC2486 difference raw33568; decide +kernel
    rw [ha]
    exact (canonical33568 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2486 + difference 1 4) (sourceB2486 + difference 4 1) sourceC2486) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4861) := by
    have ha : (tripleCharges (sourceA2486 + difference 1 4) (sourceB2486 + difference 4 1) sourceC2486) = raw33651 := by
      apply Matrix.ext; unfold tripleCharges sourceA2486 sourceB2486 sourceC2486 difference raw33651; decide +kernel
    rw [ha]
    exact (canonical33651 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2486 + difference 1 5) (sourceB2486 + difference 5 1) sourceC2486) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4867) := by
    have ha : (tripleCharges (sourceA2486 + difference 1 5) (sourceB2486 + difference 5 1) sourceC2486) = raw33560 := by
      apply Matrix.ext; unfold tripleCharges sourceA2486 sourceB2486 sourceC2486 difference raw33560; decide +kernel
    rw [ha]
    exact (canonical33560 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2486 + difference 2 0) (sourceB2486 + difference 0 2) sourceC2486) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4397) := by
    have ha : (tripleCharges (sourceA2486 + difference 2 0) (sourceB2486 + difference 0 2) sourceC2486) = raw33986 := by
      apply Matrix.ext; unfold tripleCharges sourceA2486 sourceB2486 sourceC2486 difference raw33986; decide +kernel
    rw [ha]
    exact (canonical33986 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2486 + difference 2 1) (sourceB2486 + difference 1 2) sourceC2486) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4737) := by
    have ha : (tripleCharges (sourceA2486 + difference 2 1) (sourceB2486 + difference 1 2) sourceC2486) = raw33140 := by
      apply Matrix.ext; unfold tripleCharges sourceA2486 sourceB2486 sourceC2486 difference raw33140; decide +kernel
    rw [ha]
    exact (canonical33140 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2486 + difference 2 3) (sourceB2486 + difference 3 2) sourceC2486) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA2486 + difference 2 3) (sourceB2486 + difference 3 2) sourceC2486) = raw32327 := by
      apply Matrix.ext; unfold tripleCharges sourceA2486 sourceB2486 sourceC2486 difference raw32327; decide +kernel
    rw [ha]
    exact (canonical32327 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2486 + difference 2 4) (sourceB2486 + difference 4 2) sourceC2486) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4799) := by
    have ha : (tripleCharges (sourceA2486 + difference 2 4) (sourceB2486 + difference 4 2) sourceC2486) = raw33987 := by
      apply Matrix.ext; unfold tripleCharges sourceA2486 sourceB2486 sourceC2486 difference raw33987; decide +kernel
    rw [ha]
    exact (canonical33987 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2486 + difference 2 5) (sourceB2486 + difference 5 2) sourceC2486) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4803) := by
    have ha : (tripleCharges (sourceA2486 + difference 2 5) (sourceB2486 + difference 5 2) sourceC2486) = raw33868 := by
      apply Matrix.ext; unfold tripleCharges sourceA2486 sourceB2486 sourceC2486 difference raw33868; decide +kernel
    rw [ha]
    exact (canonical33868 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2486 + difference 3 0) (sourceB2486 + difference 0 3) sourceC2486) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4402) := by
    have ha : (tripleCharges (sourceA2486 + difference 3 0) (sourceB2486 + difference 0 3) sourceC2486) = raw34264 := by
      apply Matrix.ext; unfold tripleCharges sourceA2486 sourceB2486 sourceC2486 difference raw34264; decide +kernel
    rw [ha]
    exact (canonical34264 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2486 + difference 3 1) (sourceB2486 + difference 1 3) sourceC2486) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4742) := by
    have ha : (tripleCharges (sourceA2486 + difference 3 1) (sourceB2486 + difference 1 3) sourceC2486) = raw34265 := by
      apply Matrix.ext; unfold tripleCharges sourceA2486 sourceB2486 sourceC2486 difference raw34265; decide +kernel
    rw [ha]
    exact (canonical34265 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2486 + difference 3 2) (sourceB2486 + difference 2 3) sourceC2486) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4780) := by
    have ha : (tripleCharges (sourceA2486 + difference 3 2) (sourceB2486 + difference 2 3) sourceC2486) = raw34266 := by
      apply Matrix.ext; unfold tripleCharges sourceA2486 sourceB2486 sourceC2486 difference raw34266; decide +kernel
    rw [ha]
    exact (canonical34266 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2486 + difference 3 4) (sourceB2486 + difference 4 3) sourceC2486) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4829) := by
    have ha : (tripleCharges (sourceA2486 + difference 3 4) (sourceB2486 + difference 4 3) sourceC2486) = raw34267 := by
      apply Matrix.ext; unfold tripleCharges sourceA2486 sourceB2486 sourceC2486 difference raw34267; decide +kernel
    rw [ha]
    exact (canonical34267 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2486 + difference 3 5) (sourceB2486 + difference 5 3) sourceC2486) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4836) := by
    have ha : (tripleCharges (sourceA2486 + difference 3 5) (sourceB2486 + difference 5 3) sourceC2486) = raw34188 := by
      apply Matrix.ext; unfold tripleCharges sourceA2486 sourceB2486 sourceC2486 difference raw34188; decide +kernel
    rw [ha]
    exact (canonical34188 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2486 + difference 4 0) (sourceB2486 + difference 0 4) sourceC2486) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4424) := by
    have ha : (tripleCharges (sourceA2486 + difference 4 0) (sourceB2486 + difference 0 4) sourceC2486) = raw34194 := by
      apply Matrix.ext; unfold tripleCharges sourceA2486 sourceB2486 sourceC2486 difference raw34194; decide +kernel
    rw [ha]
    exact (canonical34194 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2486 + difference 4 1) (sourceB2486 + difference 1 4) sourceC2486) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4752) := by
    have ha : (tripleCharges (sourceA2486 + difference 4 1) (sourceB2486 + difference 1 4) sourceC2486) = raw34195 := by
      apply Matrix.ext; unfold tripleCharges sourceA2486 sourceB2486 sourceC2486 difference raw34195; decide +kernel
    rw [ha]
    exact (canonical34195 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2486 + difference 4 2) (sourceB2486 + difference 2 4) sourceC2486) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4787) := by
    have ha : (tripleCharges (sourceA2486 + difference 4 2) (sourceB2486 + difference 2 4) sourceC2486) = raw32906 := by
      apply Matrix.ext; unfold tripleCharges sourceA2486 sourceB2486 sourceC2486 difference raw32906; decide +kernel
    rw [ha]
    exact (canonical32906 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2486 + difference 4 3) (sourceB2486 + difference 3 4) sourceC2486) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4838) := by
    have ha : (tripleCharges (sourceA2486 + difference 4 3) (sourceB2486 + difference 3 4) sourceC2486) = raw32250 := by
      apply Matrix.ext; unfold tripleCharges sourceA2486 sourceB2486 sourceC2486 difference raw32250; decide +kernel
    rw [ha]
    exact (canonical32250 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2486 + difference 4 5) (sourceB2486 + difference 5 4) sourceC2486) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4839) := by
    have ha : (tripleCharges (sourceA2486 + difference 4 5) (sourceB2486 + difference 5 4) sourceC2486) = raw32240 := by
      apply Matrix.ext; unfold tripleCharges sourceA2486 sourceB2486 sourceC2486 difference raw32240; decide +kernel
    rw [ha]
    exact (canonical32240 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2486 + difference 5 0) (sourceB2486 + difference 0 5) sourceC2486) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4404) := by
    have ha : (tripleCharges (sourceA2486 + difference 5 0) (sourceB2486 + difference 0 5) sourceC2486) = raw34268 := by
      apply Matrix.ext; unfold tripleCharges sourceA2486 sourceB2486 sourceC2486 difference raw34268; decide +kernel
    rw [ha]
    exact (canonical34268 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2486 + difference 5 1) (sourceB2486 + difference 1 5) sourceC2486) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4745) := by
    have ha : (tripleCharges (sourceA2486 + difference 5 1) (sourceB2486 + difference 1 5) sourceC2486) = raw34269 := by
      apply Matrix.ext; unfold tripleCharges sourceA2486 sourceB2486 sourceC2486 difference raw34269; decide +kernel
    rw [ha]
    exact (canonical34269 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2486 + difference 5 2) (sourceB2486 + difference 2 5) sourceC2486) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4782) := by
    have ha : (tripleCharges (sourceA2486 + difference 5 2) (sourceB2486 + difference 2 5) sourceC2486) = raw33003 := by
      apply Matrix.ext; unfold tripleCharges sourceA2486 sourceB2486 sourceC2486 difference raw33003; decide +kernel
    rw [ha]
    exact (canonical33003 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2486 + difference 5 3) (sourceB2486 + difference 3 5) sourceC2486) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4834) := by
    have ha : (tripleCharges (sourceA2486 + difference 5 3) (sourceB2486 + difference 3 5) sourceC2486) = raw32835 := by
      apply Matrix.ext; unfold tripleCharges sourceA2486 sourceB2486 sourceC2486 difference raw32835; decide +kernel
    rw [ha]
    exact (canonical32835 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2486 + difference 5 4) (sourceB2486 + difference 4 5) sourceC2486) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4828) := by
    have ha : (tripleCharges (sourceA2486 + difference 5 4) (sourceB2486 + difference 4 5) sourceC2486) = raw32830 := by
      apply Matrix.ext; unfold tripleCharges sourceA2486 sourceB2486 sourceC2486 difference raw32830; decide +kernel
    rw [ha]
    exact (canonical32830 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2486 sourceB2486 sourceC2486
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2486, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2487 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2487 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC2487 : Charge := ![3, 0, 0, -1, -1, -1]
def sourceForm2487 : Integer.Sparse Master := [(Sum.inr 4083, 1), (Sum.inr 4344, 1), (Sum.inr 4352, 1), (Sum.inr 4355, 2), (Sum.inr 4502, 1), (Sum.inr 4679, 1), (Sum.inr 4686, 1), (Sum.inr 4689, 2), (Sum.inr 4764, 1), (Sum.inr 4767, 2), (Sum.inr 4802, 2), (Sum.inr 4807, 2), (Sum.inr 4811, 2), (Sum.inr 4833, 1), (Sum.inr 4838, 3), (Sum.inr 4895, 2), (Sum.inr 5237, 1), (Sum.inr 5247, 1), (Sum.inr 5271, 2), (Sum.inr 5273, 1)]

theorem sourceEq2487 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2487 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2487 + difference 0 1) (sourceB2487 + difference 1 0) sourceC2487) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5237) := by
    have ha : (tripleCharges (sourceA2487 + difference 0 1) (sourceB2487 + difference 1 0) sourceC2487) = raw34270 := by
      apply Matrix.ext; unfold tripleCharges sourceA2487 sourceB2487 sourceC2487 difference raw34270; decide +kernel
    rw [ha]
    exact (canonical34270 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2487 + difference 0 2) (sourceB2487 + difference 2 0) sourceC2487) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5247) := by
    have ha : (tripleCharges (sourceA2487 + difference 0 2) (sourceB2487 + difference 2 0) sourceC2487) = raw34271 := by
      apply Matrix.ext; unfold tripleCharges sourceA2487 sourceB2487 sourceC2487 difference raw34271; decide +kernel
    rw [ha]
    exact (canonical34271 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2487 + difference 0 3) (sourceB2487 + difference 3 0) sourceC2487) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA2487 + difference 0 3) (sourceB2487 + difference 3 0) sourceC2487) = raw34272 := by
      apply Matrix.ext; unfold tripleCharges sourceA2487 sourceB2487 sourceC2487 difference raw34272; decide +kernel
    rw [ha]
    exact (canonical34272 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2487 + difference 0 4) (sourceB2487 + difference 4 0) sourceC2487) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA2487 + difference 0 4) (sourceB2487 + difference 4 0) sourceC2487) = raw34273 := by
      apply Matrix.ext; unfold tripleCharges sourceA2487 sourceB2487 sourceC2487 difference raw34273; decide +kernel
    rw [ha]
    exact (canonical34273 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2487 + difference 0 5) (sourceB2487 + difference 5 0) sourceC2487) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5273) := by
    have ha : (tripleCharges (sourceA2487 + difference 0 5) (sourceB2487 + difference 5 0) sourceC2487) = raw34274 := by
      apply Matrix.ext; unfold tripleCharges sourceA2487 sourceB2487 sourceC2487 difference raw34274; decide +kernel
    rw [ha]
    exact (canonical34274 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2487 + difference 1 0) (sourceB2487 + difference 0 1) sourceC2487) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4502) := by
    have ha : (tripleCharges (sourceA2487 + difference 1 0) (sourceB2487 + difference 0 1) sourceC2487) = raw34275 := by
      apply Matrix.ext; unfold tripleCharges sourceA2487 sourceB2487 sourceC2487 difference raw34275; decide +kernel
    rw [ha]
    exact (canonical34275 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2487 + difference 1 2) (sourceB2487 + difference 2 1) sourceC2487) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4838) := by
    have ha : (tripleCharges (sourceA2487 + difference 1 2) (sourceB2487 + difference 2 1) sourceC2487) = raw25856 := by
      apply Matrix.ext; unfold tripleCharges sourceA2487 sourceB2487 sourceC2487 difference raw25856; decide +kernel
    rw [ha]
    exact (canonical25856 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2487 + difference 1 3) (sourceB2487 + difference 3 1) sourceC2487) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA2487 + difference 1 3) (sourceB2487 + difference 3 1) sourceC2487) = raw25857 := by
      apply Matrix.ext; unfold tripleCharges sourceA2487 sourceB2487 sourceC2487 difference raw25857; decide +kernel
    rw [ha]
    exact (canonical25857 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2487 + difference 1 4) (sourceB2487 + difference 4 1) sourceC2487) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA2487 + difference 1 4) (sourceB2487 + difference 4 1) sourceC2487) = raw25858 := by
      apply Matrix.ext; unfold tripleCharges sourceA2487 sourceB2487 sourceC2487 difference raw25858; decide +kernel
    rw [ha]
    exact (canonical25858 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2487 + difference 1 5) (sourceB2487 + difference 5 1) sourceC2487) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (tripleCharges (sourceA2487 + difference 1 5) (sourceB2487 + difference 5 1) sourceC2487) = raw25859 := by
      apply Matrix.ext; unfold tripleCharges sourceA2487 sourceB2487 sourceC2487 difference raw25859; decide +kernel
    rw [ha]
    exact (canonical25859 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2487 + difference 2 0) (sourceB2487 + difference 0 2) sourceC2487) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4344) := by
    have ha : (tripleCharges (sourceA2487 + difference 2 0) (sourceB2487 + difference 0 2) sourceC2487) = raw25866 := by
      apply Matrix.ext; unfold tripleCharges sourceA2487 sourceB2487 sourceC2487 difference raw25866; decide +kernel
    rw [ha]
    exact (canonical25866 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2487 + difference 2 1) (sourceB2487 + difference 1 2) sourceC2487) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4679) := by
    have ha : (tripleCharges (sourceA2487 + difference 2 1) (sourceB2487 + difference 1 2) sourceC2487) = raw34276 := by
      apply Matrix.ext; unfold tripleCharges sourceA2487 sourceB2487 sourceC2487 difference raw34276; decide +kernel
    rw [ha]
    exact (canonical34276 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2487 + difference 2 3) (sourceB2487 + difference 3 2) sourceC2487) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA2487 + difference 2 3) (sourceB2487 + difference 3 2) sourceC2487) = raw34277 := by
      apply Matrix.ext; unfold tripleCharges sourceA2487 sourceB2487 sourceC2487 difference raw34277; decide +kernel
    rw [ha]
    exact (canonical34277 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2487 + difference 2 4) (sourceB2487 + difference 4 2) sourceC2487) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA2487 + difference 2 4) (sourceB2487 + difference 4 2) sourceC2487) = raw34278 := by
      apply Matrix.ext; unfold tripleCharges sourceA2487 sourceB2487 sourceC2487 difference raw34278; decide +kernel
    rw [ha]
    exact (canonical34278 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2487 + difference 2 5) (sourceB2487 + difference 5 2) sourceC2487) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4833) := by
    have ha : (tripleCharges (sourceA2487 + difference 2 5) (sourceB2487 + difference 5 2) sourceC2487) = raw34279 := by
      apply Matrix.ext; unfold tripleCharges sourceA2487 sourceB2487 sourceC2487 difference raw34279; decide +kernel
    rw [ha]
    exact (canonical34279 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2487 + difference 3 0) (sourceB2487 + difference 0 3) sourceC2487) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4355) := by
    have ha : (tripleCharges (sourceA2487 + difference 3 0) (sourceB2487 + difference 0 3) sourceC2487) = raw25871 := by
      apply Matrix.ext; unfold tripleCharges sourceA2487 sourceB2487 sourceC2487 difference raw25871; decide +kernel
    rw [ha]
    exact (canonical25871 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2487 + difference 3 1) (sourceB2487 + difference 1 3) sourceC2487) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4689) := by
    have ha : (tripleCharges (sourceA2487 + difference 3 1) (sourceB2487 + difference 1 3) sourceC2487) = raw34280 := by
      apply Matrix.ext; unfold tripleCharges sourceA2487 sourceB2487 sourceC2487 difference raw34280; decide +kernel
    rw [ha]
    exact (canonical34280 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2487 + difference 3 2) (sourceB2487 + difference 2 3) sourceC2487) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4767) := by
    have ha : (tripleCharges (sourceA2487 + difference 3 2) (sourceB2487 + difference 2 3) sourceC2487) = raw34281 := by
      apply Matrix.ext; unfold tripleCharges sourceA2487 sourceB2487 sourceC2487 difference raw34281; decide +kernel
    rw [ha]
    exact (canonical34281 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2487 + difference 3 4) (sourceB2487 + difference 4 3) sourceC2487) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4811) := by
    have ha : (tripleCharges (sourceA2487 + difference 3 4) (sourceB2487 + difference 4 3) sourceC2487) = raw34282 := by
      apply Matrix.ext; unfold tripleCharges sourceA2487 sourceB2487 sourceC2487 difference raw34282; decide +kernel
    rw [ha]
    exact (canonical34282 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2487 + difference 3 5) (sourceB2487 + difference 5 3) sourceC2487) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4838) := by
    have ha : (tripleCharges (sourceA2487 + difference 3 5) (sourceB2487 + difference 5 3) sourceC2487) = raw34283 := by
      apply Matrix.ext; unfold tripleCharges sourceA2487 sourceB2487 sourceC2487 difference raw34283; decide +kernel
    rw [ha]
    exact (canonical34283 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2487 + difference 4 0) (sourceB2487 + difference 0 4) sourceC2487) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4355) := by
    have ha : (tripleCharges (sourceA2487 + difference 4 0) (sourceB2487 + difference 0 4) sourceC2487) = raw25876 := by
      apply Matrix.ext; unfold tripleCharges sourceA2487 sourceB2487 sourceC2487 difference raw25876; decide +kernel
    rw [ha]
    exact (canonical25876 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2487 + difference 4 1) (sourceB2487 + difference 1 4) sourceC2487) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4689) := by
    have ha : (tripleCharges (sourceA2487 + difference 4 1) (sourceB2487 + difference 1 4) sourceC2487) = raw34284 := by
      apply Matrix.ext; unfold tripleCharges sourceA2487 sourceB2487 sourceC2487 difference raw34284; decide +kernel
    rw [ha]
    exact (canonical34284 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2487 + difference 4 2) (sourceB2487 + difference 2 4) sourceC2487) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4767) := by
    have ha : (tripleCharges (sourceA2487 + difference 4 2) (sourceB2487 + difference 2 4) sourceC2487) = raw34285 := by
      apply Matrix.ext; unfold tripleCharges sourceA2487 sourceB2487 sourceC2487 difference raw34285; decide +kernel
    rw [ha]
    exact (canonical34285 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2487 + difference 4 3) (sourceB2487 + difference 3 4) sourceC2487) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4811) := by
    have ha : (tripleCharges (sourceA2487 + difference 4 3) (sourceB2487 + difference 3 4) sourceC2487) = raw34286 := by
      apply Matrix.ext; unfold tripleCharges sourceA2487 sourceB2487 sourceC2487 difference raw34286; decide +kernel
    rw [ha]
    exact (canonical34286 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2487 + difference 4 5) (sourceB2487 + difference 5 4) sourceC2487) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4838) := by
    have ha : (tripleCharges (sourceA2487 + difference 4 5) (sourceB2487 + difference 5 4) sourceC2487) = raw34287 := by
      apply Matrix.ext; unfold tripleCharges sourceA2487 sourceB2487 sourceC2487 difference raw34287; decide +kernel
    rw [ha]
    exact (canonical34287 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2487 + difference 5 0) (sourceB2487 + difference 0 5) sourceC2487) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4352) := by
    have ha : (tripleCharges (sourceA2487 + difference 5 0) (sourceB2487 + difference 0 5) sourceC2487) = raw25881 := by
      apply Matrix.ext; unfold tripleCharges sourceA2487 sourceB2487 sourceC2487 difference raw25881; decide +kernel
    rw [ha]
    exact (canonical25881 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2487 + difference 5 1) (sourceB2487 + difference 1 5) sourceC2487) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4686) := by
    have ha : (tripleCharges (sourceA2487 + difference 5 1) (sourceB2487 + difference 1 5) sourceC2487) = raw34288 := by
      apply Matrix.ext; unfold tripleCharges sourceA2487 sourceB2487 sourceC2487 difference raw34288; decide +kernel
    rw [ha]
    exact (canonical34288 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2487 + difference 5 2) (sourceB2487 + difference 2 5) sourceC2487) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4764) := by
    have ha : (tripleCharges (sourceA2487 + difference 5 2) (sourceB2487 + difference 2 5) sourceC2487) = raw34289 := by
      apply Matrix.ext; unfold tripleCharges sourceA2487 sourceB2487 sourceC2487 difference raw34289; decide +kernel
    rw [ha]
    exact (canonical34289 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2487 + difference 5 3) (sourceB2487 + difference 3 5) sourceC2487) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA2487 + difference 5 3) (sourceB2487 + difference 3 5) sourceC2487) = raw34290 := by
      apply Matrix.ext; unfold tripleCharges sourceA2487 sourceB2487 sourceC2487 difference raw34290; decide +kernel
    rw [ha]
    exact (canonical34290 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2487 + difference 5 4) (sourceB2487 + difference 4 5) sourceC2487) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA2487 + difference 5 4) (sourceB2487 + difference 4 5) sourceC2487) = raw34291 := by
      apply Matrix.ext; unfold tripleCharges sourceA2487 sourceB2487 sourceC2487 difference raw34291; decide +kernel
    rw [ha]
    exact (canonical34291 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2487 sourceB2487 sourceC2487
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2487, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2488 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2488 : Charge := ![0, 1, 0, 0, -1, 0]
def sourceC2488 : Charge := ![3, 0, 0, -1, 0, -2]
def sourceForm2488 : Integer.Sparse Master := [(Sum.inr 4084, 1), (Sum.inr 4341, 1), (Sum.inr 4346, 1), (Sum.inr 4349, 1), (Sum.inr 4354, 1), (Sum.inr 4498, 1), (Sum.inr 4676, 1), (Sum.inr 4681, 1), (Sum.inr 4684, 1), (Sum.inr 4688, 1), (Sum.inr 4760, 1), (Sum.inr 4763, 1), (Sum.inr 4766, 1), (Sum.inr 4801, 1), (Sum.inr 4804, 1), (Sum.inr 4810, 1), (Sum.inr 4831, 1), (Sum.inr 4834, 2), (Sum.inr 4835, 1), (Sum.inr 4839, 1), (Sum.inr 4841, 1), (Sum.inr 4846, 1), (Sum.inr 4894, 1), (Sum.inr 4895, 1), (Sum.inr 5228, 1), (Sum.inr 5241, 1), (Sum.inr 5258, 1), (Sum.inr 5259, 1), (Sum.inr 5274, 1)]

theorem sourceEq2488 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2488 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2488 + difference 0 1) (sourceB2488 + difference 1 0) sourceC2488) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5228) := by
    have ha : (tripleCharges (sourceA2488 + difference 0 1) (sourceB2488 + difference 1 0) sourceC2488) = raw34292 := by
      apply Matrix.ext; unfold tripleCharges sourceA2488 sourceB2488 sourceC2488 difference raw34292; decide +kernel
    rw [ha]
    exact (canonical34292 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2488 + difference 0 2) (sourceB2488 + difference 2 0) sourceC2488) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5241) := by
    have ha : (tripleCharges (sourceA2488 + difference 0 2) (sourceB2488 + difference 2 0) sourceC2488) = raw34293 := by
      apply Matrix.ext; unfold tripleCharges sourceA2488 sourceB2488 sourceC2488 difference raw34293; decide +kernel
    rw [ha]
    exact (canonical34293 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2488 + difference 0 3) (sourceB2488 + difference 3 0) sourceC2488) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA2488 + difference 0 3) (sourceB2488 + difference 3 0) sourceC2488) = raw34294 := by
      apply Matrix.ext; unfold tripleCharges sourceA2488 sourceB2488 sourceC2488 difference raw34294; decide +kernel
    rw [ha]
    exact (canonical34294 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2488 + difference 0 4) (sourceB2488 + difference 4 0) sourceC2488) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5274) := by
    have ha : (tripleCharges (sourceA2488 + difference 0 4) (sourceB2488 + difference 4 0) sourceC2488) = raw34295 := by
      apply Matrix.ext; unfold tripleCharges sourceA2488 sourceB2488 sourceC2488 difference raw34295; decide +kernel
    rw [ha]
    exact (canonical34295 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2488 + difference 0 5) (sourceB2488 + difference 5 0) sourceC2488) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA2488 + difference 0 5) (sourceB2488 + difference 5 0) sourceC2488) = raw34296 := by
      apply Matrix.ext; unfold tripleCharges sourceA2488 sourceB2488 sourceC2488 difference raw34296; decide +kernel
    rw [ha]
    exact (canonical34296 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2488 + difference 1 0) (sourceB2488 + difference 0 1) sourceC2488) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4498) := by
    have ha : (tripleCharges (sourceA2488 + difference 1 0) (sourceB2488 + difference 0 1) sourceC2488) = raw34297 := by
      apply Matrix.ext; unfold tripleCharges sourceA2488 sourceB2488 sourceC2488 difference raw34297; decide +kernel
    rw [ha]
    exact (canonical34297 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2488 + difference 1 2) (sourceB2488 + difference 2 1) sourceC2488) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4834) := by
    have ha : (tripleCharges (sourceA2488 + difference 1 2) (sourceB2488 + difference 2 1) sourceC2488) = raw25886 := by
      apply Matrix.ext; unfold tripleCharges sourceA2488 sourceB2488 sourceC2488 difference raw25886; decide +kernel
    rw [ha]
    exact (canonical25886 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2488 + difference 1 3) (sourceB2488 + difference 3 1) sourceC2488) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4894) := by
    have ha : (tripleCharges (sourceA2488 + difference 1 3) (sourceB2488 + difference 3 1) sourceC2488) = raw25887 := by
      apply Matrix.ext; unfold tripleCharges sourceA2488 sourceB2488 sourceC2488 difference raw25887; decide +kernel
    rw [ha]
    exact (canonical25887 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2488 + difference 1 4) (sourceB2488 + difference 4 1) sourceC2488) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA2488 + difference 1 4) (sourceB2488 + difference 4 1) sourceC2488) = raw25888 := by
      apply Matrix.ext; unfold tripleCharges sourceA2488 sourceB2488 sourceC2488 difference raw25888; decide +kernel
    rw [ha]
    exact (canonical25888 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2488 + difference 1 5) (sourceB2488 + difference 5 1) sourceC2488) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA2488 + difference 1 5) (sourceB2488 + difference 5 1) sourceC2488) = raw25889 := by
      apply Matrix.ext; unfold tripleCharges sourceA2488 sourceB2488 sourceC2488 difference raw25889; decide +kernel
    rw [ha]
    exact (canonical25889 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2488 + difference 2 0) (sourceB2488 + difference 0 2) sourceC2488) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4341) := by
    have ha : (tripleCharges (sourceA2488 + difference 2 0) (sourceB2488 + difference 0 2) sourceC2488) = raw25896 := by
      apply Matrix.ext; unfold tripleCharges sourceA2488 sourceB2488 sourceC2488 difference raw25896; decide +kernel
    rw [ha]
    exact (canonical25896 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2488 + difference 2 1) (sourceB2488 + difference 1 2) sourceC2488) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4676) := by
    have ha : (tripleCharges (sourceA2488 + difference 2 1) (sourceB2488 + difference 1 2) sourceC2488) = raw34298 := by
      apply Matrix.ext; unfold tripleCharges sourceA2488 sourceB2488 sourceC2488 difference raw34298; decide +kernel
    rw [ha]
    exact (canonical34298 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2488 + difference 2 3) (sourceB2488 + difference 3 2) sourceC2488) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4801) := by
    have ha : (tripleCharges (sourceA2488 + difference 2 3) (sourceB2488 + difference 3 2) sourceC2488) = raw34299 := by
      apply Matrix.ext; unfold tripleCharges sourceA2488 sourceB2488 sourceC2488 difference raw34299; decide +kernel
    rw [ha]
    exact (canonical34299 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2488 + difference 2 4) (sourceB2488 + difference 4 2) sourceC2488) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4834) := by
    have ha : (tripleCharges (sourceA2488 + difference 2 4) (sourceB2488 + difference 4 2) sourceC2488) = raw34300 := by
      apply Matrix.ext; unfold tripleCharges sourceA2488 sourceB2488 sourceC2488 difference raw34300; decide +kernel
    rw [ha]
    exact (canonical34300 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2488 + difference 2 5) (sourceB2488 + difference 5 2) sourceC2488) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4831) := by
    have ha : (tripleCharges (sourceA2488 + difference 2 5) (sourceB2488 + difference 5 2) sourceC2488) = raw34301 := by
      apply Matrix.ext; unfold tripleCharges sourceA2488 sourceB2488 sourceC2488 difference raw34301; decide +kernel
    rw [ha]
    exact (canonical34301 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2488 + difference 3 0) (sourceB2488 + difference 0 3) sourceC2488) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4349) := by
    have ha : (tripleCharges (sourceA2488 + difference 3 0) (sourceB2488 + difference 0 3) sourceC2488) = raw25901 := by
      apply Matrix.ext; unfold tripleCharges sourceA2488 sourceB2488 sourceC2488 difference raw25901; decide +kernel
    rw [ha]
    exact (canonical25901 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2488 + difference 3 1) (sourceB2488 + difference 1 3) sourceC2488) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4684) := by
    have ha : (tripleCharges (sourceA2488 + difference 3 1) (sourceB2488 + difference 1 3) sourceC2488) = raw34302 := by
      apply Matrix.ext; unfold tripleCharges sourceA2488 sourceB2488 sourceC2488 difference raw34302; decide +kernel
    rw [ha]
    exact (canonical34302 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2488 + difference 3 2) (sourceB2488 + difference 2 3) sourceC2488) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4763) := by
    have ha : (tripleCharges (sourceA2488 + difference 3 2) (sourceB2488 + difference 2 3) sourceC2488) = raw34303 := by
      apply Matrix.ext; unfold tripleCharges sourceA2488 sourceB2488 sourceC2488 difference raw34303; decide +kernel
    rw [ha]
    exact (canonical34303 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2488 + difference 3 4) (sourceB2488 + difference 4 3) sourceC2488) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4846) := by
    have ha : (tripleCharges (sourceA2488 + difference 3 4) (sourceB2488 + difference 4 3) sourceC2488) = raw34304 := by
      apply Matrix.ext; unfold tripleCharges sourceA2488 sourceB2488 sourceC2488 difference raw34304; decide +kernel
    rw [ha]
    exact (canonical34304 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2488 + difference 3 5) (sourceB2488 + difference 5 3) sourceC2488) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4835) := by
    have ha : (tripleCharges (sourceA2488 + difference 3 5) (sourceB2488 + difference 5 3) sourceC2488) = raw34305 := by
      apply Matrix.ext; unfold tripleCharges sourceA2488 sourceB2488 sourceC2488 difference raw34305; decide +kernel
    rw [ha]
    exact (canonical34305 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2488 + difference 4 0) (sourceB2488 + difference 0 4) sourceC2488) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4354) := by
    have ha : (tripleCharges (sourceA2488 + difference 4 0) (sourceB2488 + difference 0 4) sourceC2488) = raw25906 := by
      apply Matrix.ext; unfold tripleCharges sourceA2488 sourceB2488 sourceC2488 difference raw25906; decide +kernel
    rw [ha]
    exact (canonical25906 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2488 + difference 4 1) (sourceB2488 + difference 1 4) sourceC2488) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4688) := by
    have ha : (tripleCharges (sourceA2488 + difference 4 1) (sourceB2488 + difference 1 4) sourceC2488) = raw34306 := by
      apply Matrix.ext; unfold tripleCharges sourceA2488 sourceB2488 sourceC2488 difference raw34306; decide +kernel
    rw [ha]
    exact (canonical34306 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2488 + difference 4 2) (sourceB2488 + difference 2 4) sourceC2488) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4766) := by
    have ha : (tripleCharges (sourceA2488 + difference 4 2) (sourceB2488 + difference 2 4) sourceC2488) = raw34307 := by
      apply Matrix.ext; unfold tripleCharges sourceA2488 sourceB2488 sourceC2488 difference raw34307; decide +kernel
    rw [ha]
    exact (canonical34307 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2488 + difference 4 3) (sourceB2488 + difference 3 4) sourceC2488) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4810) := by
    have ha : (tripleCharges (sourceA2488 + difference 4 3) (sourceB2488 + difference 3 4) sourceC2488) = raw34308 := by
      apply Matrix.ext; unfold tripleCharges sourceA2488 sourceB2488 sourceC2488 difference raw34308; decide +kernel
    rw [ha]
    exact (canonical34308 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2488 + difference 4 5) (sourceB2488 + difference 5 4) sourceC2488) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4839) := by
    have ha : (tripleCharges (sourceA2488 + difference 4 5) (sourceB2488 + difference 5 4) sourceC2488) = raw34309 := by
      apply Matrix.ext; unfold tripleCharges sourceA2488 sourceB2488 sourceC2488 difference raw34309; decide +kernel
    rw [ha]
    exact (canonical34309 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2488 + difference 5 0) (sourceB2488 + difference 0 5) sourceC2488) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4346) := by
    have ha : (tripleCharges (sourceA2488 + difference 5 0) (sourceB2488 + difference 0 5) sourceC2488) = raw25911 := by
      apply Matrix.ext; unfold tripleCharges sourceA2488 sourceB2488 sourceC2488 difference raw25911; decide +kernel
    rw [ha]
    exact (canonical25911 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2488 + difference 5 1) (sourceB2488 + difference 1 5) sourceC2488) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4681) := by
    have ha : (tripleCharges (sourceA2488 + difference 5 1) (sourceB2488 + difference 1 5) sourceC2488) = raw34310 := by
      apply Matrix.ext; unfold tripleCharges sourceA2488 sourceB2488 sourceC2488 difference raw34310; decide +kernel
    rw [ha]
    exact (canonical34310 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2488 + difference 5 2) (sourceB2488 + difference 2 5) sourceC2488) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4760) := by
    have ha : (tripleCharges (sourceA2488 + difference 5 2) (sourceB2488 + difference 2 5) sourceC2488) = raw34311 := by
      apply Matrix.ext; unfold tripleCharges sourceA2488 sourceB2488 sourceC2488 difference raw34311; decide +kernel
    rw [ha]
    exact (canonical34311 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2488 + difference 5 3) (sourceB2488 + difference 3 5) sourceC2488) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA2488 + difference 5 3) (sourceB2488 + difference 3 5) sourceC2488) = raw34312 := by
      apply Matrix.ext; unfold tripleCharges sourceA2488 sourceB2488 sourceC2488 difference raw34312; decide +kernel
    rw [ha]
    exact (canonical34312 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2488 + difference 5 4) (sourceB2488 + difference 4 5) sourceC2488) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4841) := by
    have ha : (tripleCharges (sourceA2488 + difference 5 4) (sourceB2488 + difference 4 5) sourceC2488) = raw34313 := by
      apply Matrix.ext; unfold tripleCharges sourceA2488 sourceB2488 sourceC2488 difference raw34313; decide +kernel
    rw [ha]
    exact (canonical34313 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2488 sourceB2488 sourceC2488
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2488, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2489 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2489 : Charge := ![0, 1, 0, -1, -1, 1]
def sourceC2489 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceForm2489 : Integer.Sparse Master := [(Sum.inr 4340, 1), (Sum.inr 4343, 1), (Sum.inr 4348, 2), (Sum.inr 4496, 1), (Sum.inr 4675, 1), (Sum.inr 4678, 1), (Sum.inr 4683, 2), (Sum.inr 4759, 1), (Sum.inr 4762, 2), (Sum.inr 4830, 1), (Sum.inr 4832, 3), (Sum.inr 4836, 2), (Sum.inr 4837, 2), (Sum.inr 4845, 2), (Sum.inr 4890, 1), (Sum.inr 4897, 2), (Sum.inr 5222, 1), (Sum.inr 5239, 1), (Sum.inr 5252, 1), (Sum.inr 5261, 2)]

theorem sourceEq2489 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2489 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2489 + difference 0 1) (sourceB2489 + difference 1 0) sourceC2489) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5222) := by
    have ha : (tripleCharges (sourceA2489 + difference 0 1) (sourceB2489 + difference 1 0) sourceC2489) = raw34314 := by
      apply Matrix.ext; unfold tripleCharges sourceA2489 sourceB2489 sourceC2489 difference raw34314; decide +kernel
    rw [ha]
    exact (canonical34314 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2489 + difference 0 2) (sourceB2489 + difference 2 0) sourceC2489) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5239) := by
    have ha : (tripleCharges (sourceA2489 + difference 0 2) (sourceB2489 + difference 2 0) sourceC2489) = raw34315 := by
      apply Matrix.ext; unfold tripleCharges sourceA2489 sourceB2489 sourceC2489 difference raw34315; decide +kernel
    rw [ha]
    exact (canonical34315 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2489 + difference 0 3) (sourceB2489 + difference 3 0) sourceC2489) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5261) := by
    have ha : (tripleCharges (sourceA2489 + difference 0 3) (sourceB2489 + difference 3 0) sourceC2489) = raw29233 := by
      apply Matrix.ext; unfold tripleCharges sourceA2489 sourceB2489 sourceC2489 difference raw29233; decide +kernel
    rw [ha]
    exact (canonical29233 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2489 + difference 0 4) (sourceB2489 + difference 4 0) sourceC2489) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5261) := by
    have ha : (tripleCharges (sourceA2489 + difference 0 4) (sourceB2489 + difference 4 0) sourceC2489) = raw34316 := by
      apply Matrix.ext; unfold tripleCharges sourceA2489 sourceB2489 sourceC2489 difference raw34316; decide +kernel
    rw [ha]
    exact (canonical34316 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2489 + difference 0 5) (sourceB2489 + difference 5 0) sourceC2489) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5252) := by
    have ha : (tripleCharges (sourceA2489 + difference 0 5) (sourceB2489 + difference 5 0) sourceC2489) = raw34317 := by
      apply Matrix.ext; unfold tripleCharges sourceA2489 sourceB2489 sourceC2489 difference raw34317; decide +kernel
    rw [ha]
    exact (canonical34317 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2489 + difference 1 0) (sourceB2489 + difference 0 1) sourceC2489) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4496) := by
    have ha : (tripleCharges (sourceA2489 + difference 1 0) (sourceB2489 + difference 0 1) sourceC2489) = raw21846 := by
      apply Matrix.ext; unfold tripleCharges sourceA2489 sourceB2489 sourceC2489 difference raw21846; decide +kernel
    rw [ha]
    exact (canonical21846 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2489 + difference 1 2) (sourceB2489 + difference 2 1) sourceC2489) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4832) := by
    have ha : (tripleCharges (sourceA2489 + difference 1 2) (sourceB2489 + difference 2 1) sourceC2489) = raw25923 := by
      apply Matrix.ext; unfold tripleCharges sourceA2489 sourceB2489 sourceC2489 difference raw25923; decide +kernel
    rw [ha]
    exact (canonical25923 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2489 + difference 1 3) (sourceB2489 + difference 3 1) sourceC2489) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4897) := by
    have ha : (tripleCharges (sourceA2489 + difference 1 3) (sourceB2489 + difference 3 1) sourceC2489) = raw21834 := by
      apply Matrix.ext; unfold tripleCharges sourceA2489 sourceB2489 sourceC2489 difference raw21834; decide +kernel
    rw [ha]
    exact (canonical21834 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2489 + difference 1 4) (sourceB2489 + difference 4 1) sourceC2489) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4897) := by
    have ha : (tripleCharges (sourceA2489 + difference 1 4) (sourceB2489 + difference 4 1) sourceC2489) = raw25924 := by
      apply Matrix.ext; unfold tripleCharges sourceA2489 sourceB2489 sourceC2489 difference raw25924; decide +kernel
    rw [ha]
    exact (canonical25924 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2489 + difference 1 5) (sourceB2489 + difference 5 1) sourceC2489) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4890) := by
    have ha : (tripleCharges (sourceA2489 + difference 1 5) (sourceB2489 + difference 5 1) sourceC2489) = raw25925 := by
      apply Matrix.ext; unfold tripleCharges sourceA2489 sourceB2489 sourceC2489 difference raw25925; decide +kernel
    rw [ha]
    exact (canonical25925 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2489 + difference 2 0) (sourceB2489 + difference 0 2) sourceC2489) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4340) := by
    have ha : (tripleCharges (sourceA2489 + difference 2 0) (sourceB2489 + difference 0 2) sourceC2489) = raw25931 := by
      apply Matrix.ext; unfold tripleCharges sourceA2489 sourceB2489 sourceC2489 difference raw25931; decide +kernel
    rw [ha]
    exact (canonical25931 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2489 + difference 2 1) (sourceB2489 + difference 1 2) sourceC2489) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4675) := by
    have ha : (tripleCharges (sourceA2489 + difference 2 1) (sourceB2489 + difference 1 2) sourceC2489) = raw34318 := by
      apply Matrix.ext; unfold tripleCharges sourceA2489 sourceB2489 sourceC2489 difference raw34318; decide +kernel
    rw [ha]
    exact (canonical34318 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2489 + difference 2 3) (sourceB2489 + difference 3 2) sourceC2489) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4832) := by
    have ha : (tripleCharges (sourceA2489 + difference 2 3) (sourceB2489 + difference 3 2) sourceC2489) = raw29237 := by
      apply Matrix.ext; unfold tripleCharges sourceA2489 sourceB2489 sourceC2489 difference raw29237; decide +kernel
    rw [ha]
    exact (canonical29237 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2489 + difference 2 4) (sourceB2489 + difference 4 2) sourceC2489) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4832) := by
    have ha : (tripleCharges (sourceA2489 + difference 2 4) (sourceB2489 + difference 4 2) sourceC2489) = raw34319 := by
      apply Matrix.ext; unfold tripleCharges sourceA2489 sourceB2489 sourceC2489 difference raw34319; decide +kernel
    rw [ha]
    exact (canonical34319 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2489 + difference 2 5) (sourceB2489 + difference 5 2) sourceC2489) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4830) := by
    have ha : (tripleCharges (sourceA2489 + difference 2 5) (sourceB2489 + difference 5 2) sourceC2489) = raw34320 := by
      apply Matrix.ext; unfold tripleCharges sourceA2489 sourceB2489 sourceC2489 difference raw34320; decide +kernel
    rw [ha]
    exact (canonical34320 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2489 + difference 3 0) (sourceB2489 + difference 0 3) sourceC2489) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4348) := by
    have ha : (tripleCharges (sourceA2489 + difference 3 0) (sourceB2489 + difference 0 3) sourceC2489) = raw25935 := by
      apply Matrix.ext; unfold tripleCharges sourceA2489 sourceB2489 sourceC2489 difference raw25935; decide +kernel
    rw [ha]
    exact (canonical25935 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2489 + difference 3 1) (sourceB2489 + difference 1 3) sourceC2489) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4683) := by
    have ha : (tripleCharges (sourceA2489 + difference 3 1) (sourceB2489 + difference 1 3) sourceC2489) = raw34321 := by
      apply Matrix.ext; unfold tripleCharges sourceA2489 sourceB2489 sourceC2489 difference raw34321; decide +kernel
    rw [ha]
    exact (canonical34321 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2489 + difference 3 2) (sourceB2489 + difference 2 3) sourceC2489) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4762) := by
    have ha : (tripleCharges (sourceA2489 + difference 3 2) (sourceB2489 + difference 2 3) sourceC2489) = raw34322 := by
      apply Matrix.ext; unfold tripleCharges sourceA2489 sourceB2489 sourceC2489 difference raw34322; decide +kernel
    rw [ha]
    exact (canonical34322 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2489 + difference 3 4) (sourceB2489 + difference 4 3) sourceC2489) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4845) := by
    have ha : (tripleCharges (sourceA2489 + difference 3 4) (sourceB2489 + difference 4 3) sourceC2489) = raw34323 := by
      apply Matrix.ext; unfold tripleCharges sourceA2489 sourceB2489 sourceC2489 difference raw34323; decide +kernel
    rw [ha]
    exact (canonical34323 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2489 + difference 3 5) (sourceB2489 + difference 5 3) sourceC2489) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4836) := by
    have ha : (tripleCharges (sourceA2489 + difference 3 5) (sourceB2489 + difference 5 3) sourceC2489) = raw34324 := by
      apply Matrix.ext; unfold tripleCharges sourceA2489 sourceB2489 sourceC2489 difference raw34324; decide +kernel
    rw [ha]
    exact (canonical34324 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2489 + difference 4 0) (sourceB2489 + difference 0 4) sourceC2489) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4348) := by
    have ha : (tripleCharges (sourceA2489 + difference 4 0) (sourceB2489 + difference 0 4) sourceC2489) = raw25940 := by
      apply Matrix.ext; unfold tripleCharges sourceA2489 sourceB2489 sourceC2489 difference raw25940; decide +kernel
    rw [ha]
    exact (canonical25940 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2489 + difference 4 1) (sourceB2489 + difference 1 4) sourceC2489) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4683) := by
    have ha : (tripleCharges (sourceA2489 + difference 4 1) (sourceB2489 + difference 1 4) sourceC2489) = raw34325 := by
      apply Matrix.ext; unfold tripleCharges sourceA2489 sourceB2489 sourceC2489 difference raw34325; decide +kernel
    rw [ha]
    exact (canonical34325 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2489 + difference 4 2) (sourceB2489 + difference 2 4) sourceC2489) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4762) := by
    have ha : (tripleCharges (sourceA2489 + difference 4 2) (sourceB2489 + difference 2 4) sourceC2489) = raw34326 := by
      apply Matrix.ext; unfold tripleCharges sourceA2489 sourceB2489 sourceC2489 difference raw34326; decide +kernel
    rw [ha]
    exact (canonical34326 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2489 + difference 4 3) (sourceB2489 + difference 3 4) sourceC2489) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4845) := by
    have ha : (tripleCharges (sourceA2489 + difference 4 3) (sourceB2489 + difference 3 4) sourceC2489) = raw29244 := by
      apply Matrix.ext; unfold tripleCharges sourceA2489 sourceB2489 sourceC2489 difference raw29244; decide +kernel
    rw [ha]
    exact (canonical29244 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2489 + difference 4 5) (sourceB2489 + difference 5 4) sourceC2489) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4836) := by
    have ha : (tripleCharges (sourceA2489 + difference 4 5) (sourceB2489 + difference 5 4) sourceC2489) = raw34327 := by
      apply Matrix.ext; unfold tripleCharges sourceA2489 sourceB2489 sourceC2489 difference raw34327; decide +kernel
    rw [ha]
    exact (canonical34327 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2489 + difference 5 0) (sourceB2489 + difference 0 5) sourceC2489) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4343) := by
    have ha : (tripleCharges (sourceA2489 + difference 5 0) (sourceB2489 + difference 0 5) sourceC2489) = raw21844 := by
      apply Matrix.ext; unfold tripleCharges sourceA2489 sourceB2489 sourceC2489 difference raw21844; decide +kernel
    rw [ha]
    exact (canonical21844 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2489 + difference 5 1) (sourceB2489 + difference 1 5) sourceC2489) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4678) := by
    have ha : (tripleCharges (sourceA2489 + difference 5 1) (sourceB2489 + difference 1 5) sourceC2489) = raw29238 := by
      apply Matrix.ext; unfold tripleCharges sourceA2489 sourceB2489 sourceC2489 difference raw29238; decide +kernel
    rw [ha]
    exact (canonical29238 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2489 + difference 5 2) (sourceB2489 + difference 2 5) sourceC2489) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4759) := by
    have ha : (tripleCharges (sourceA2489 + difference 5 2) (sourceB2489 + difference 2 5) sourceC2489) = raw29239 := by
      apply Matrix.ext; unfold tripleCharges sourceA2489 sourceB2489 sourceC2489 difference raw29239; decide +kernel
    rw [ha]
    exact (canonical29239 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2489 + difference 5 3) (sourceB2489 + difference 3 5) sourceC2489) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4837) := by
    have ha : (tripleCharges (sourceA2489 + difference 5 3) (sourceB2489 + difference 3 5) sourceC2489) = raw21831 := by
      apply Matrix.ext; unfold tripleCharges sourceA2489 sourceB2489 sourceC2489 difference raw21831; decide +kernel
    rw [ha]
    exact (canonical21831 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2489 + difference 5 4) (sourceB2489 + difference 4 5) sourceC2489) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4837) := by
    have ha : (tripleCharges (sourceA2489 + difference 5 4) (sourceB2489 + difference 4 5) sourceC2489) = raw29240 := by
      apply Matrix.ext; unfold tripleCharges sourceA2489 sourceB2489 sourceC2489 difference raw29240; decide +kernel
    rw [ha]
    exact (canonical29240 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2489 sourceB2489 sourceC2489
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2489, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2490 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2490 : Charge := ![0, 1, 0, -1, -1, 1]
def sourceC2490 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceForm2490 : Integer.Sparse Master := [(Sum.inr 1345, 1), (Sum.inr 1346, 1), (Sum.inr 1347, 2), (Sum.inr 1451, 1), (Sum.inr 2707, 1), (Sum.inr 2712, 1), (Sum.inr 2716, 2), (Sum.inr 2755, 1), (Sum.inr 3027, 1), (Sum.inr 3031, 1), (Sum.inr 3033, 2), (Sum.inr 3061, 1), (Sum.inr 3062, 2), (Sum.inr 3082, 3), (Sum.inr 3090, 2), (Sum.inr 3095, 2), (Sum.inr 3114, 2), (Sum.inr 3143, 1), (Sum.inr 3192, 1), (Sum.inr 3215, 2)]

theorem sourceEq2490 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2490 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2490 + difference 0 1) (sourceB2490 + difference 1 0) sourceC2490) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3031) := by
    have ha : (tripleCharges (sourceA2490 + difference 0 1) (sourceB2490 + difference 1 0) sourceC2490) = raw34328 := by
      apply Matrix.ext; unfold tripleCharges sourceA2490 sourceB2490 sourceC2490 difference raw34328; decide +kernel
    rw [ha]
    exact (canonical34328 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2490 + difference 0 2) (sourceB2490 + difference 2 0) sourceC2490) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3061) := by
    have ha : (tripleCharges (sourceA2490 + difference 0 2) (sourceB2490 + difference 2 0) sourceC2490) = raw34329 := by
      apply Matrix.ext; unfold tripleCharges sourceA2490 sourceB2490 sourceC2490 difference raw34329; decide +kernel
    rw [ha]
    exact (canonical34329 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2490 + difference 0 3) (sourceB2490 + difference 3 0) sourceC2490) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3090) := by
    have ha : (tripleCharges (sourceA2490 + difference 0 3) (sourceB2490 + difference 3 0) sourceC2490) = raw34330 := by
      apply Matrix.ext; unfold tripleCharges sourceA2490 sourceB2490 sourceC2490 difference raw34330; decide +kernel
    rw [ha]
    exact (canonical34330 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2490 + difference 0 4) (sourceB2490 + difference 4 0) sourceC2490) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3090) := by
    have ha : (tripleCharges (sourceA2490 + difference 0 4) (sourceB2490 + difference 4 0) sourceC2490) = raw34331 := by
      apply Matrix.ext; unfold tripleCharges sourceA2490 sourceB2490 sourceC2490 difference raw34331; decide +kernel
    rw [ha]
    exact (canonical34331 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2490 + difference 0 5) (sourceB2490 + difference 5 0) sourceC2490) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2712) := by
    have ha : (tripleCharges (sourceA2490 + difference 0 5) (sourceB2490 + difference 5 0) sourceC2490) = raw34332 := by
      apply Matrix.ext; unfold tripleCharges sourceA2490 sourceB2490 sourceC2490 difference raw34332; decide +kernel
    rw [ha]
    exact (canonical34332 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2490 + difference 1 0) (sourceB2490 + difference 0 1) sourceC2490) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1451) := by
    have ha : (tripleCharges (sourceA2490 + difference 1 0) (sourceB2490 + difference 0 1) sourceC2490) = raw34333 := by
      apply Matrix.ext; unfold tripleCharges sourceA2490 sourceB2490 sourceC2490 difference raw34333; decide +kernel
    rw [ha]
    exact (canonical34333 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2490 + difference 1 2) (sourceB2490 + difference 2 1) sourceC2490) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3082) := by
    have ha : (tripleCharges (sourceA2490 + difference 1 2) (sourceB2490 + difference 2 1) sourceC2490) = raw25944 := by
      apply Matrix.ext; unfold tripleCharges sourceA2490 sourceB2490 sourceC2490 difference raw25944; decide +kernel
    rw [ha]
    exact (canonical25944 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2490 + difference 1 3) (sourceB2490 + difference 3 1) sourceC2490) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3114) := by
    have ha : (tripleCharges (sourceA2490 + difference 1 3) (sourceB2490 + difference 3 1) sourceC2490) = raw25945 := by
      apply Matrix.ext; unfold tripleCharges sourceA2490 sourceB2490 sourceC2490 difference raw25945; decide +kernel
    rw [ha]
    exact (canonical25945 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2490 + difference 1 4) (sourceB2490 + difference 4 1) sourceC2490) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3114) := by
    have ha : (tripleCharges (sourceA2490 + difference 1 4) (sourceB2490 + difference 4 1) sourceC2490) = raw25946 := by
      apply Matrix.ext; unfold tripleCharges sourceA2490 sourceB2490 sourceC2490 difference raw25946; decide +kernel
    rw [ha]
    exact (canonical25946 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2490 + difference 1 5) (sourceB2490 + difference 5 1) sourceC2490) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2755) := by
    have ha : (tripleCharges (sourceA2490 + difference 1 5) (sourceB2490 + difference 5 1) sourceC2490) = raw25947 := by
      apply Matrix.ext; unfold tripleCharges sourceA2490 sourceB2490 sourceC2490 difference raw25947; decide +kernel
    rw [ha]
    exact (canonical25947 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2490 + difference 2 0) (sourceB2490 + difference 0 2) sourceC2490) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1345) := by
    have ha : (tripleCharges (sourceA2490 + difference 2 0) (sourceB2490 + difference 0 2) sourceC2490) = raw25954 := by
      apply Matrix.ext; unfold tripleCharges sourceA2490 sourceB2490 sourceC2490 difference raw25954; decide +kernel
    rw [ha]
    exact (canonical25954 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2490 + difference 2 1) (sourceB2490 + difference 1 2) sourceC2490) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3027) := by
    have ha : (tripleCharges (sourceA2490 + difference 2 1) (sourceB2490 + difference 1 2) sourceC2490) = raw34334 := by
      apply Matrix.ext; unfold tripleCharges sourceA2490 sourceB2490 sourceC2490 difference raw34334; decide +kernel
    rw [ha]
    exact (canonical34334 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2490 + difference 2 3) (sourceB2490 + difference 3 2) sourceC2490) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3082) := by
    have ha : (tripleCharges (sourceA2490 + difference 2 3) (sourceB2490 + difference 3 2) sourceC2490) = raw34335 := by
      apply Matrix.ext; unfold tripleCharges sourceA2490 sourceB2490 sourceC2490 difference raw34335; decide +kernel
    rw [ha]
    exact (canonical34335 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2490 + difference 2 4) (sourceB2490 + difference 4 2) sourceC2490) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3082) := by
    have ha : (tripleCharges (sourceA2490 + difference 2 4) (sourceB2490 + difference 4 2) sourceC2490) = raw34336 := by
      apply Matrix.ext; unfold tripleCharges sourceA2490 sourceB2490 sourceC2490 difference raw34336; decide +kernel
    rw [ha]
    exact (canonical34336 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2490 + difference 2 5) (sourceB2490 + difference 5 2) sourceC2490) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2707) := by
    have ha : (tripleCharges (sourceA2490 + difference 2 5) (sourceB2490 + difference 5 2) sourceC2490) = raw34337 := by
      apply Matrix.ext; unfold tripleCharges sourceA2490 sourceB2490 sourceC2490 difference raw34337; decide +kernel
    rw [ha]
    exact (canonical34337 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2490 + difference 3 0) (sourceB2490 + difference 0 3) sourceC2490) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1347) := by
    have ha : (tripleCharges (sourceA2490 + difference 3 0) (sourceB2490 + difference 0 3) sourceC2490) = raw25959 := by
      apply Matrix.ext; unfold tripleCharges sourceA2490 sourceB2490 sourceC2490 difference raw25959; decide +kernel
    rw [ha]
    exact (canonical25959 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2490 + difference 3 1) (sourceB2490 + difference 1 3) sourceC2490) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3033) := by
    have ha : (tripleCharges (sourceA2490 + difference 3 1) (sourceB2490 + difference 1 3) sourceC2490) = raw34338 := by
      apply Matrix.ext; unfold tripleCharges sourceA2490 sourceB2490 sourceC2490 difference raw34338; decide +kernel
    rw [ha]
    exact (canonical34338 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2490 + difference 3 2) (sourceB2490 + difference 2 3) sourceC2490) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3062) := by
    have ha : (tripleCharges (sourceA2490 + difference 3 2) (sourceB2490 + difference 2 3) sourceC2490) = raw34339 := by
      apply Matrix.ext; unfold tripleCharges sourceA2490 sourceB2490 sourceC2490 difference raw34339; decide +kernel
    rw [ha]
    exact (canonical34339 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2490 + difference 3 4) (sourceB2490 + difference 4 3) sourceC2490) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3095) := by
    have ha : (tripleCharges (sourceA2490 + difference 3 4) (sourceB2490 + difference 4 3) sourceC2490) = raw34340 := by
      apply Matrix.ext; unfold tripleCharges sourceA2490 sourceB2490 sourceC2490 difference raw34340; decide +kernel
    rw [ha]
    exact (canonical34340 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2490 + difference 3 5) (sourceB2490 + difference 5 3) sourceC2490) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2716) := by
    have ha : (tripleCharges (sourceA2490 + difference 3 5) (sourceB2490 + difference 5 3) sourceC2490) = raw34341 := by
      apply Matrix.ext; unfold tripleCharges sourceA2490 sourceB2490 sourceC2490 difference raw34341; decide +kernel
    rw [ha]
    exact (canonical34341 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2490 + difference 4 0) (sourceB2490 + difference 0 4) sourceC2490) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1347) := by
    have ha : (tripleCharges (sourceA2490 + difference 4 0) (sourceB2490 + difference 0 4) sourceC2490) = raw25964 := by
      apply Matrix.ext; unfold tripleCharges sourceA2490 sourceB2490 sourceC2490 difference raw25964; decide +kernel
    rw [ha]
    exact (canonical25964 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2490 + difference 4 1) (sourceB2490 + difference 1 4) sourceC2490) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3033) := by
    have ha : (tripleCharges (sourceA2490 + difference 4 1) (sourceB2490 + difference 1 4) sourceC2490) = raw34342 := by
      apply Matrix.ext; unfold tripleCharges sourceA2490 sourceB2490 sourceC2490 difference raw34342; decide +kernel
    rw [ha]
    exact (canonical34342 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2490 + difference 4 2) (sourceB2490 + difference 2 4) sourceC2490) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3062) := by
    have ha : (tripleCharges (sourceA2490 + difference 4 2) (sourceB2490 + difference 2 4) sourceC2490) = raw34343 := by
      apply Matrix.ext; unfold tripleCharges sourceA2490 sourceB2490 sourceC2490 difference raw34343; decide +kernel
    rw [ha]
    exact (canonical34343 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2490 + difference 4 3) (sourceB2490 + difference 3 4) sourceC2490) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3095) := by
    have ha : (tripleCharges (sourceA2490 + difference 4 3) (sourceB2490 + difference 3 4) sourceC2490) = raw34344 := by
      apply Matrix.ext; unfold tripleCharges sourceA2490 sourceB2490 sourceC2490 difference raw34344; decide +kernel
    rw [ha]
    exact (canonical34344 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2490 + difference 4 5) (sourceB2490 + difference 5 4) sourceC2490) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2716) := by
    have ha : (tripleCharges (sourceA2490 + difference 4 5) (sourceB2490 + difference 5 4) sourceC2490) = raw34345 := by
      apply Matrix.ext; unfold tripleCharges sourceA2490 sourceB2490 sourceC2490 difference raw34345; decide +kernel
    rw [ha]
    exact (canonical34345 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2490 + difference 5 0) (sourceB2490 + difference 0 5) sourceC2490) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1346) := by
    have ha : (tripleCharges (sourceA2490 + difference 5 0) (sourceB2490 + difference 0 5) sourceC2490) = raw25969 := by
      apply Matrix.ext; unfold tripleCharges sourceA2490 sourceB2490 sourceC2490 difference raw25969; decide +kernel
    rw [ha]
    exact (canonical25969 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2490 + difference 5 1) (sourceB2490 + difference 1 5) sourceC2490) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3143) := by
    have ha : (tripleCharges (sourceA2490 + difference 5 1) (sourceB2490 + difference 1 5) sourceC2490) = raw34346 := by
      apply Matrix.ext; unfold tripleCharges sourceA2490 sourceB2490 sourceC2490 difference raw34346; decide +kernel
    rw [ha]
    exact (canonical34346 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2490 + difference 5 2) (sourceB2490 + difference 2 5) sourceC2490) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3192) := by
    have ha : (tripleCharges (sourceA2490 + difference 5 2) (sourceB2490 + difference 2 5) sourceC2490) = raw34347 := by
      apply Matrix.ext; unfold tripleCharges sourceA2490 sourceB2490 sourceC2490 difference raw34347; decide +kernel
    rw [ha]
    exact (canonical34347 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2490 + difference 5 3) (sourceB2490 + difference 3 5) sourceC2490) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3215) := by
    have ha : (tripleCharges (sourceA2490 + difference 5 3) (sourceB2490 + difference 3 5) sourceC2490) = raw34348 := by
      apply Matrix.ext; unfold tripleCharges sourceA2490 sourceB2490 sourceC2490 difference raw34348; decide +kernel
    rw [ha]
    exact (canonical34348 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2490 + difference 5 4) (sourceB2490 + difference 4 5) sourceC2490) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3215) := by
    have ha : (tripleCharges (sourceA2490 + difference 5 4) (sourceB2490 + difference 4 5) sourceC2490) = raw34349 := by
      apply Matrix.ext; unfold tripleCharges sourceA2490 sourceB2490 sourceC2490 difference raw34349; decide +kernel
    rw [ha]
    exact (canonical34349 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2490 sourceB2490 sourceC2490
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2490, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2491 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2491 : Charge := ![0, 1, 0, -1, -1, 1]
def sourceC2491 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceForm2491 : Integer.Sparse Master := [(Sum.inr 1662, 1), (Sum.inr 1666, 1), (Sum.inr 1669, 2), (Sum.inr 1710, 1), (Sum.inr 2139, 1), (Sum.inr 2143, 1), (Sum.inr 2146, 2), (Sum.inr 2170, 1), (Sum.inr 2171, 2), (Sum.inr 2187, 1), (Sum.inr 2193, 3), (Sum.inr 2197, 2), (Sum.inr 2208, 2), (Sum.inr 2218, 2), (Sum.inr 2247, 1), (Sum.inr 2268, 2), (Sum.inr 2664, 1), (Sum.inr 2691, 1), (Sum.inr 2712, 1), (Sum.inr 2726, 2)]

theorem sourceEq2491 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2491 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2491 + difference 0 1) (sourceB2491 + difference 1 0) sourceC2491) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2664) := by
    have ha : (tripleCharges (sourceA2491 + difference 0 1) (sourceB2491 + difference 1 0) sourceC2491) = raw34350 := by
      apply Matrix.ext; unfold tripleCharges sourceA2491 sourceB2491 sourceC2491 difference raw34350; decide +kernel
    rw [ha]
    exact (canonical34350 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2491 + difference 0 2) (sourceB2491 + difference 2 0) sourceC2491) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2691) := by
    have ha : (tripleCharges (sourceA2491 + difference 0 2) (sourceB2491 + difference 2 0) sourceC2491) = raw34351 := by
      apply Matrix.ext; unfold tripleCharges sourceA2491 sourceB2491 sourceC2491 difference raw34351; decide +kernel
    rw [ha]
    exact (canonical34351 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2491 + difference 0 3) (sourceB2491 + difference 3 0) sourceC2491) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2726) := by
    have ha : (tripleCharges (sourceA2491 + difference 0 3) (sourceB2491 + difference 3 0) sourceC2491) = raw29252 := by
      apply Matrix.ext; unfold tripleCharges sourceA2491 sourceB2491 sourceC2491 difference raw29252; decide +kernel
    rw [ha]
    exact (canonical29252 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2491 + difference 0 4) (sourceB2491 + difference 4 0) sourceC2491) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2726) := by
    have ha : (tripleCharges (sourceA2491 + difference 0 4) (sourceB2491 + difference 4 0) sourceC2491) = raw34352 := by
      apply Matrix.ext; unfold tripleCharges sourceA2491 sourceB2491 sourceC2491 difference raw34352; decide +kernel
    rw [ha]
    exact (canonical34352 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2491 + difference 0 5) (sourceB2491 + difference 5 0) sourceC2491) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2712) := by
    have ha : (tripleCharges (sourceA2491 + difference 0 5) (sourceB2491 + difference 5 0) sourceC2491) = raw34353 := by
      apply Matrix.ext; unfold tripleCharges sourceA2491 sourceB2491 sourceC2491 difference raw34353; decide +kernel
    rw [ha]
    exact (canonical34353 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2491 + difference 1 0) (sourceB2491 + difference 0 1) sourceC2491) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1710) := by
    have ha : (tripleCharges (sourceA2491 + difference 1 0) (sourceB2491 + difference 0 1) sourceC2491) = raw21868 := by
      apply Matrix.ext; unfold tripleCharges sourceA2491 sourceB2491 sourceC2491 difference raw21868; decide +kernel
    rw [ha]
    exact (canonical21868 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2491 + difference 1 2) (sourceB2491 + difference 2 1) sourceC2491) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2193) := by
    have ha : (tripleCharges (sourceA2491 + difference 1 2) (sourceB2491 + difference 2 1) sourceC2491) = raw25974 := by
      apply Matrix.ext; unfold tripleCharges sourceA2491 sourceB2491 sourceC2491 difference raw25974; decide +kernel
    rw [ha]
    exact (canonical25974 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2491 + difference 1 3) (sourceB2491 + difference 3 1) sourceC2491) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2268) := by
    have ha : (tripleCharges (sourceA2491 + difference 1 3) (sourceB2491 + difference 3 1) sourceC2491) = raw21856 := by
      apply Matrix.ext; unfold tripleCharges sourceA2491 sourceB2491 sourceC2491 difference raw21856; decide +kernel
    rw [ha]
    exact (canonical21856 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2491 + difference 1 4) (sourceB2491 + difference 4 1) sourceC2491) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2268) := by
    have ha : (tripleCharges (sourceA2491 + difference 1 4) (sourceB2491 + difference 4 1) sourceC2491) = raw25975 := by
      apply Matrix.ext; unfold tripleCharges sourceA2491 sourceB2491 sourceC2491 difference raw25975; decide +kernel
    rw [ha]
    exact (canonical25975 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2491 + difference 1 5) (sourceB2491 + difference 5 1) sourceC2491) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2247) := by
    have ha : (tripleCharges (sourceA2491 + difference 1 5) (sourceB2491 + difference 5 1) sourceC2491) = raw25976 := by
      apply Matrix.ext; unfold tripleCharges sourceA2491 sourceB2491 sourceC2491 difference raw25976; decide +kernel
    rw [ha]
    exact (canonical25976 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2491 + difference 2 0) (sourceB2491 + difference 0 2) sourceC2491) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1662) := by
    have ha : (tripleCharges (sourceA2491 + difference 2 0) (sourceB2491 + difference 0 2) sourceC2491) = raw25982 := by
      apply Matrix.ext; unfold tripleCharges sourceA2491 sourceB2491 sourceC2491 difference raw25982; decide +kernel
    rw [ha]
    exact (canonical25982 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2491 + difference 2 1) (sourceB2491 + difference 1 2) sourceC2491) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2139) := by
    have ha : (tripleCharges (sourceA2491 + difference 2 1) (sourceB2491 + difference 1 2) sourceC2491) = raw34354 := by
      apply Matrix.ext; unfold tripleCharges sourceA2491 sourceB2491 sourceC2491 difference raw34354; decide +kernel
    rw [ha]
    exact (canonical34354 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2491 + difference 2 3) (sourceB2491 + difference 3 2) sourceC2491) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2193) := by
    have ha : (tripleCharges (sourceA2491 + difference 2 3) (sourceB2491 + difference 3 2) sourceC2491) = raw29256 := by
      apply Matrix.ext; unfold tripleCharges sourceA2491 sourceB2491 sourceC2491 difference raw29256; decide +kernel
    rw [ha]
    exact (canonical29256 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2491 + difference 2 4) (sourceB2491 + difference 4 2) sourceC2491) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2193) := by
    have ha : (tripleCharges (sourceA2491 + difference 2 4) (sourceB2491 + difference 4 2) sourceC2491) = raw34355 := by
      apply Matrix.ext; unfold tripleCharges sourceA2491 sourceB2491 sourceC2491 difference raw34355; decide +kernel
    rw [ha]
    exact (canonical34355 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2491 + difference 2 5) (sourceB2491 + difference 5 2) sourceC2491) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2187) := by
    have ha : (tripleCharges (sourceA2491 + difference 2 5) (sourceB2491 + difference 5 2) sourceC2491) = raw34356 := by
      apply Matrix.ext; unfold tripleCharges sourceA2491 sourceB2491 sourceC2491 difference raw34356; decide +kernel
    rw [ha]
    exact (canonical34356 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2491 + difference 3 0) (sourceB2491 + difference 0 3) sourceC2491) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1669) := by
    have ha : (tripleCharges (sourceA2491 + difference 3 0) (sourceB2491 + difference 0 3) sourceC2491) = raw25986 := by
      apply Matrix.ext; unfold tripleCharges sourceA2491 sourceB2491 sourceC2491 difference raw25986; decide +kernel
    rw [ha]
    exact (canonical25986 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2491 + difference 3 1) (sourceB2491 + difference 1 3) sourceC2491) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2146) := by
    have ha : (tripleCharges (sourceA2491 + difference 3 1) (sourceB2491 + difference 1 3) sourceC2491) = raw34357 := by
      apply Matrix.ext; unfold tripleCharges sourceA2491 sourceB2491 sourceC2491 difference raw34357; decide +kernel
    rw [ha]
    exact (canonical34357 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2491 + difference 3 2) (sourceB2491 + difference 2 3) sourceC2491) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2171) := by
    have ha : (tripleCharges (sourceA2491 + difference 3 2) (sourceB2491 + difference 2 3) sourceC2491) = raw34358 := by
      apply Matrix.ext; unfold tripleCharges sourceA2491 sourceB2491 sourceC2491 difference raw34358; decide +kernel
    rw [ha]
    exact (canonical34358 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2491 + difference 3 4) (sourceB2491 + difference 4 3) sourceC2491) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2218) := by
    have ha : (tripleCharges (sourceA2491 + difference 3 4) (sourceB2491 + difference 4 3) sourceC2491) = raw34359 := by
      apply Matrix.ext; unfold tripleCharges sourceA2491 sourceB2491 sourceC2491 difference raw34359; decide +kernel
    rw [ha]
    exact (canonical34359 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2491 + difference 3 5) (sourceB2491 + difference 5 3) sourceC2491) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2197) := by
    have ha : (tripleCharges (sourceA2491 + difference 3 5) (sourceB2491 + difference 5 3) sourceC2491) = raw34360 := by
      apply Matrix.ext; unfold tripleCharges sourceA2491 sourceB2491 sourceC2491 difference raw34360; decide +kernel
    rw [ha]
    exact (canonical34360 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2491 + difference 4 0) (sourceB2491 + difference 0 4) sourceC2491) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1669) := by
    have ha : (tripleCharges (sourceA2491 + difference 4 0) (sourceB2491 + difference 0 4) sourceC2491) = raw25991 := by
      apply Matrix.ext; unfold tripleCharges sourceA2491 sourceB2491 sourceC2491 difference raw25991; decide +kernel
    rw [ha]
    exact (canonical25991 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2491 + difference 4 1) (sourceB2491 + difference 1 4) sourceC2491) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2146) := by
    have ha : (tripleCharges (sourceA2491 + difference 4 1) (sourceB2491 + difference 1 4) sourceC2491) = raw34361 := by
      apply Matrix.ext; unfold tripleCharges sourceA2491 sourceB2491 sourceC2491 difference raw34361; decide +kernel
    rw [ha]
    exact (canonical34361 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2491 + difference 4 2) (sourceB2491 + difference 2 4) sourceC2491) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2171) := by
    have ha : (tripleCharges (sourceA2491 + difference 4 2) (sourceB2491 + difference 2 4) sourceC2491) = raw34362 := by
      apply Matrix.ext; unfold tripleCharges sourceA2491 sourceB2491 sourceC2491 difference raw34362; decide +kernel
    rw [ha]
    exact (canonical34362 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2491 + difference 4 3) (sourceB2491 + difference 3 4) sourceC2491) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2218) := by
    have ha : (tripleCharges (sourceA2491 + difference 4 3) (sourceB2491 + difference 3 4) sourceC2491) = raw29263 := by
      apply Matrix.ext; unfold tripleCharges sourceA2491 sourceB2491 sourceC2491 difference raw29263; decide +kernel
    rw [ha]
    exact (canonical29263 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2491 + difference 4 5) (sourceB2491 + difference 5 4) sourceC2491) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2197) := by
    have ha : (tripleCharges (sourceA2491 + difference 4 5) (sourceB2491 + difference 5 4) sourceC2491) = raw34363 := by
      apply Matrix.ext; unfold tripleCharges sourceA2491 sourceB2491 sourceC2491 difference raw34363; decide +kernel
    rw [ha]
    exact (canonical34363 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2491 + difference 5 0) (sourceB2491 + difference 0 5) sourceC2491) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1666) := by
    have ha : (tripleCharges (sourceA2491 + difference 5 0) (sourceB2491 + difference 0 5) sourceC2491) = raw21866 := by
      apply Matrix.ext; unfold tripleCharges sourceA2491 sourceB2491 sourceC2491 difference raw21866; decide +kernel
    rw [ha]
    exact (canonical21866 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2491 + difference 5 1) (sourceB2491 + difference 1 5) sourceC2491) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2143) := by
    have ha : (tripleCharges (sourceA2491 + difference 5 1) (sourceB2491 + difference 1 5) sourceC2491) = raw29257 := by
      apply Matrix.ext; unfold tripleCharges sourceA2491 sourceB2491 sourceC2491 difference raw29257; decide +kernel
    rw [ha]
    exact (canonical29257 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2491 + difference 5 2) (sourceB2491 + difference 2 5) sourceC2491) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2170) := by
    have ha : (tripleCharges (sourceA2491 + difference 5 2) (sourceB2491 + difference 2 5) sourceC2491) = raw29258 := by
      apply Matrix.ext; unfold tripleCharges sourceA2491 sourceB2491 sourceC2491 difference raw29258; decide +kernel
    rw [ha]
    exact (canonical29258 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2491 + difference 5 3) (sourceB2491 + difference 3 5) sourceC2491) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2208) := by
    have ha : (tripleCharges (sourceA2491 + difference 5 3) (sourceB2491 + difference 3 5) sourceC2491) = raw21853 := by
      apply Matrix.ext; unfold tripleCharges sourceA2491 sourceB2491 sourceC2491 difference raw21853; decide +kernel
    rw [ha]
    exact (canonical21853 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2491 + difference 5 4) (sourceB2491 + difference 4 5) sourceC2491) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2208) := by
    have ha : (tripleCharges (sourceA2491 + difference 5 4) (sourceB2491 + difference 4 5) sourceC2491) = raw29259 := by
      apply Matrix.ext; unfold tripleCharges sourceA2491 sourceB2491 sourceC2491 difference raw29259; decide +kernel
    rw [ha]
    exact (canonical29259 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2491 sourceB2491 sourceC2491
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2491, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2492 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2492 : Charge := ![0, 1, 0, -1, -1, 1]
def sourceC2492 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceForm2492 : Integer.Sparse Master := [(Sum.inr 1801, 1), (Sum.inr 1804, 1), (Sum.inr 1809, 2), (Sum.inr 2052, 1), (Sum.inr 3389, 1), (Sum.inr 4085, -1)]

theorem sourceEq2492 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2492 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2492 + difference 0 1) (sourceB2492 + difference 1 0) sourceC2492) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3389) := by
    have ha : (tripleCharges (sourceA2492 + difference 0 1) (sourceB2492 + difference 1 0) sourceC2492) = raw34364 := by
      apply Matrix.ext; unfold tripleCharges sourceA2492 sourceB2492 sourceC2492 difference raw34364; decide +kernel
    rw [ha]
    exact (canonical34364 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2492 + difference 1 1) (sourceB2492 + difference 1 1) sourceC2492) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2052) := by
    have ha : (tripleCharges (sourceA2492 + difference 1 1) (sourceB2492 + difference 1 1) sourceC2492) = raw34365 := by
      apply Matrix.ext; unfold tripleCharges sourceA2492 sourceB2492 sourceC2492 difference raw34365; decide +kernel
    rw [ha]
    exact (canonical34365 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2492 + difference 2 1) (sourceB2492 + difference 1 2) sourceC2492) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1801) := by
    have ha : (tripleCharges (sourceA2492 + difference 2 1) (sourceB2492 + difference 1 2) sourceC2492) = raw34366 := by
      apply Matrix.ext; unfold tripleCharges sourceA2492 sourceB2492 sourceC2492 difference raw34366; decide +kernel
    rw [ha]
    exact (canonical34366 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2492 + difference 3 1) (sourceB2492 + difference 1 3) sourceC2492) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1809) := by
    have ha : (tripleCharges (sourceA2492 + difference 3 1) (sourceB2492 + difference 1 3) sourceC2492) = raw34367 := by
      apply Matrix.ext; unfold tripleCharges sourceA2492 sourceB2492 sourceC2492 difference raw34367; decide +kernel
    rw [ha]
    exact (canonical34367 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2492 + difference 4 1) (sourceB2492 + difference 1 4) sourceC2492) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1809) := by
    have ha : (tripleCharges (sourceA2492 + difference 4 1) (sourceB2492 + difference 1 4) sourceC2492) = raw34368 := by
      apply Matrix.ext; unfold tripleCharges sourceA2492 sourceB2492 sourceC2492 difference raw34368; decide +kernel
    rw [ha]
    exact (canonical34368 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2492 + difference 5 1) (sourceB2492 + difference 1 5) sourceC2492) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1804) := by
    have ha : (tripleCharges (sourceA2492 + difference 5 1) (sourceB2492 + difference 1 5) sourceC2492) = raw29270 := by
      apply Matrix.ext; unfold tripleCharges sourceA2492 sourceB2492 sourceC2492 difference raw29270; decide +kernel
    rw [ha]
    exact (canonical29270 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2492 + sourceB2492) sourceC2492) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA2492 + sourceB2492) sourceC2492) = raw19953 := by
      apply Matrix.ext; unfold doubleCharges sourceA2492 sourceB2492 sourceC2492 raw19953; decide +kernel
    rw [ha]
    exact (canonical19953 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2492 sourceB2492 sourceC2492
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2492, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2493 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2493 : Charge := ![0, 1, 0, -1, -1, 1]
def sourceC2493 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceForm2493 : Integer.Sparse Master := [(Sum.inr 918, 1), (Sum.inr 1801, 1), (Sum.inr 2050, 1), (Sum.inr 2052, 3), (Sum.inr 4085, -1)]

theorem sourceEq2493 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2493 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2493 + difference 2 0) (sourceB2493 + difference 0 2) sourceC2493) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 918) := by
    have ha : (tripleCharges (sourceA2493 + difference 2 0) (sourceB2493 + difference 0 2) sourceC2493) = raw34369 := by
      apply Matrix.ext; unfold tripleCharges sourceA2493 sourceB2493 sourceC2493 difference raw34369; decide +kernel
    rw [ha]
    exact (canonical34369 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2493 + difference 2 1) (sourceB2493 + difference 1 2) sourceC2493) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1801) := by
    have ha : (tripleCharges (sourceA2493 + difference 2 1) (sourceB2493 + difference 1 2) sourceC2493) = raw34366 := by
      apply Matrix.ext; unfold tripleCharges sourceA2493 sourceB2493 sourceC2493 difference raw34366; decide +kernel
    rw [ha]
    exact (canonical34366 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2493 + difference 2 2) (sourceB2493 + difference 2 2) sourceC2493) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2052) := by
    have ha : (tripleCharges (sourceA2493 + difference 2 2) (sourceB2493 + difference 2 2) sourceC2493) = raw34365 := by
      apply Matrix.ext; unfold tripleCharges sourceA2493 sourceB2493 sourceC2493 difference raw34365; decide +kernel
    rw [ha]
    exact (canonical34365 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2493 + difference 2 3) (sourceB2493 + difference 3 2) sourceC2493) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2052) := by
    have ha : (tripleCharges (sourceA2493 + difference 2 3) (sourceB2493 + difference 3 2) sourceC2493) = raw34370 := by
      apply Matrix.ext; unfold tripleCharges sourceA2493 sourceB2493 sourceC2493 difference raw34370; decide +kernel
    rw [ha]
    exact (canonical34370 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2493 + difference 2 4) (sourceB2493 + difference 4 2) sourceC2493) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2052) := by
    have ha : (tripleCharges (sourceA2493 + difference 2 4) (sourceB2493 + difference 4 2) sourceC2493) = raw34371 := by
      apply Matrix.ext; unfold tripleCharges sourceA2493 sourceB2493 sourceC2493 difference raw34371; decide +kernel
    rw [ha]
    exact (canonical34371 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2493 + difference 2 5) (sourceB2493 + difference 5 2) sourceC2493) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2050) := by
    have ha : (tripleCharges (sourceA2493 + difference 2 5) (sourceB2493 + difference 5 2) sourceC2493) = raw34372 := by
      apply Matrix.ext; unfold tripleCharges sourceA2493 sourceB2493 sourceC2493 difference raw34372; decide +kernel
    rw [ha]
    exact (canonical34372 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2493 + sourceB2493) sourceC2493) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA2493 + sourceB2493) sourceC2493) = raw19953 := by
      apply Matrix.ext; unfold doubleCharges sourceA2493 sourceB2493 sourceC2493 raw19953; decide +kernel
    rw [ha]
    exact (canonical19953 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2493 sourceB2493 sourceC2493
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2493, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2494 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceB2494 : Charge := ![0, 1, -1, 0, 0, 0]
def sourceC2494 : Charge := ![3, 0, 1, -1, -1, -2]
def sourceForm2494 : Integer.Sparse Master := [(Sum.inr 4080, 1), (Sum.inr 4322, 1), (Sum.inr 4323, 2), (Sum.inr 4337, 1), (Sum.inr 4423, 1), (Sum.inr 4660, 1), (Sum.inr 4661, 2), (Sum.inr 4672, 1), (Sum.inr 4712, 1), (Sum.inr 4715, 2), (Sum.inr 4779, 2), (Sum.inr 4782, 2), (Sum.inr 4787, 2), (Sum.inr 4798, 2), (Sum.inr 4826, 1), (Sum.inr 4834, 2), (Sum.inr 4838, 1), (Sum.inr 5058, 1), (Sum.inr 5123, 1), (Sum.inr 5134, 2), (Sum.inr 5137, 1)]

theorem sourceEq2494 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2494 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2494 + difference 0 1) (sourceB2494 + difference 1 0) sourceC2494) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5123) := by
    have ha : (tripleCharges (sourceA2494 + difference 0 1) (sourceB2494 + difference 1 0) sourceC2494) = raw34373 := by
      apply Matrix.ext; unfold tripleCharges sourceA2494 sourceB2494 sourceC2494 difference raw34373; decide +kernel
    rw [ha]
    exact (canonical34373 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2494 + difference 0 2) (sourceB2494 + difference 2 0) sourceC2494) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5058) := by
    have ha : (tripleCharges (sourceA2494 + difference 0 2) (sourceB2494 + difference 2 0) sourceC2494) = raw34374 := by
      apply Matrix.ext; unfold tripleCharges sourceA2494 sourceB2494 sourceC2494 difference raw34374; decide +kernel
    rw [ha]
    exact (canonical34374 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2494 + difference 0 3) (sourceB2494 + difference 3 0) sourceC2494) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5134) := by
    have ha : (tripleCharges (sourceA2494 + difference 0 3) (sourceB2494 + difference 3 0) sourceC2494) = raw34375 := by
      apply Matrix.ext; unfold tripleCharges sourceA2494 sourceB2494 sourceC2494 difference raw34375; decide +kernel
    rw [ha]
    exact (canonical34375 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2494 + difference 0 4) (sourceB2494 + difference 4 0) sourceC2494) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5134) := by
    have ha : (tripleCharges (sourceA2494 + difference 0 4) (sourceB2494 + difference 4 0) sourceC2494) = raw34376 := by
      apply Matrix.ext; unfold tripleCharges sourceA2494 sourceB2494 sourceC2494 difference raw34376; decide +kernel
    rw [ha]
    exact (canonical34376 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2494 + difference 0 5) (sourceB2494 + difference 5 0) sourceC2494) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5137) := by
    have ha : (tripleCharges (sourceA2494 + difference 0 5) (sourceB2494 + difference 5 0) sourceC2494) = raw34377 := by
      apply Matrix.ext; unfold tripleCharges sourceA2494 sourceB2494 sourceC2494 difference raw34377; decide +kernel
    rw [ha]
    exact (canonical34377 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2494 + difference 1 0) (sourceB2494 + difference 0 1) sourceC2494) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4423) := by
    have ha : (tripleCharges (sourceA2494 + difference 1 0) (sourceB2494 + difference 0 1) sourceC2494) = raw34378 := by
      apply Matrix.ext; unfold tripleCharges sourceA2494 sourceB2494 sourceC2494 difference raw34378; decide +kernel
    rw [ha]
    exact (canonical34378 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2494 + difference 1 2) (sourceB2494 + difference 2 1) sourceC2494) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA2494 + difference 1 2) (sourceB2494 + difference 2 1) sourceC2494) = raw26136 := by
      apply Matrix.ext; unfold tripleCharges sourceA2494 sourceB2494 sourceC2494 difference raw26136; decide +kernel
    rw [ha]
    exact (canonical26136 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2494 + difference 1 3) (sourceB2494 + difference 3 1) sourceC2494) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4834) := by
    have ha : (tripleCharges (sourceA2494 + difference 1 3) (sourceB2494 + difference 3 1) sourceC2494) = raw26137 := by
      apply Matrix.ext; unfold tripleCharges sourceA2494 sourceB2494 sourceC2494 difference raw26137; decide +kernel
    rw [ha]
    exact (canonical26137 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2494 + difference 1 4) (sourceB2494 + difference 4 1) sourceC2494) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4834) := by
    have ha : (tripleCharges (sourceA2494 + difference 1 4) (sourceB2494 + difference 4 1) sourceC2494) = raw26138 := by
      apply Matrix.ext; unfold tripleCharges sourceA2494 sourceB2494 sourceC2494 difference raw26138; decide +kernel
    rw [ha]
    exact (canonical26138 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2494 + difference 1 5) (sourceB2494 + difference 5 1) sourceC2494) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4838) := by
    have ha : (tripleCharges (sourceA2494 + difference 1 5) (sourceB2494 + difference 5 1) sourceC2494) = raw26139 := by
      apply Matrix.ext; unfold tripleCharges sourceA2494 sourceB2494 sourceC2494 difference raw26139; decide +kernel
    rw [ha]
    exact (canonical26139 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2494 + difference 2 0) (sourceB2494 + difference 0 2) sourceC2494) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4337) := by
    have ha : (tripleCharges (sourceA2494 + difference 2 0) (sourceB2494 + difference 0 2) sourceC2494) = raw26146 := by
      apply Matrix.ext; unfold tripleCharges sourceA2494 sourceB2494 sourceC2494 difference raw26146; decide +kernel
    rw [ha]
    exact (canonical26146 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2494 + difference 2 1) (sourceB2494 + difference 1 2) sourceC2494) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4672) := by
    have ha : (tripleCharges (sourceA2494 + difference 2 1) (sourceB2494 + difference 1 2) sourceC2494) = raw34379 := by
      apply Matrix.ext; unfold tripleCharges sourceA2494 sourceB2494 sourceC2494 difference raw34379; decide +kernel
    rw [ha]
    exact (canonical34379 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2494 + difference 2 3) (sourceB2494 + difference 3 2) sourceC2494) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4798) := by
    have ha : (tripleCharges (sourceA2494 + difference 2 3) (sourceB2494 + difference 3 2) sourceC2494) = raw34380 := by
      apply Matrix.ext; unfold tripleCharges sourceA2494 sourceB2494 sourceC2494 difference raw34380; decide +kernel
    rw [ha]
    exact (canonical34380 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2494 + difference 2 4) (sourceB2494 + difference 4 2) sourceC2494) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4798) := by
    have ha : (tripleCharges (sourceA2494 + difference 2 4) (sourceB2494 + difference 4 2) sourceC2494) = raw34381 := by
      apply Matrix.ext; unfold tripleCharges sourceA2494 sourceB2494 sourceC2494 difference raw34381; decide +kernel
    rw [ha]
    exact (canonical34381 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2494 + difference 2 5) (sourceB2494 + difference 5 2) sourceC2494) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4826) := by
    have ha : (tripleCharges (sourceA2494 + difference 2 5) (sourceB2494 + difference 5 2) sourceC2494) = raw34382 := by
      apply Matrix.ext; unfold tripleCharges sourceA2494 sourceB2494 sourceC2494 difference raw34382; decide +kernel
    rw [ha]
    exact (canonical34382 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2494 + difference 3 0) (sourceB2494 + difference 0 3) sourceC2494) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4323) := by
    have ha : (tripleCharges (sourceA2494 + difference 3 0) (sourceB2494 + difference 0 3) sourceC2494) = raw26151 := by
      apply Matrix.ext; unfold tripleCharges sourceA2494 sourceB2494 sourceC2494 difference raw26151; decide +kernel
    rw [ha]
    exact (canonical26151 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2494 + difference 3 1) (sourceB2494 + difference 1 3) sourceC2494) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4661) := by
    have ha : (tripleCharges (sourceA2494 + difference 3 1) (sourceB2494 + difference 1 3) sourceC2494) = raw34383 := by
      apply Matrix.ext; unfold tripleCharges sourceA2494 sourceB2494 sourceC2494 difference raw34383; decide +kernel
    rw [ha]
    exact (canonical34383 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2494 + difference 3 2) (sourceB2494 + difference 2 3) sourceC2494) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4715) := by
    have ha : (tripleCharges (sourceA2494 + difference 3 2) (sourceB2494 + difference 2 3) sourceC2494) = raw34384 := by
      apply Matrix.ext; unfold tripleCharges sourceA2494 sourceB2494 sourceC2494 difference raw34384; decide +kernel
    rw [ha]
    exact (canonical34384 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2494 + difference 3 4) (sourceB2494 + difference 4 3) sourceC2494) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4782) := by
    have ha : (tripleCharges (sourceA2494 + difference 3 4) (sourceB2494 + difference 4 3) sourceC2494) = raw34385 := by
      apply Matrix.ext; unfold tripleCharges sourceA2494 sourceB2494 sourceC2494 difference raw34385; decide +kernel
    rw [ha]
    exact (canonical34385 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2494 + difference 3 5) (sourceB2494 + difference 5 3) sourceC2494) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4787) := by
    have ha : (tripleCharges (sourceA2494 + difference 3 5) (sourceB2494 + difference 5 3) sourceC2494) = raw34386 := by
      apply Matrix.ext; unfold tripleCharges sourceA2494 sourceB2494 sourceC2494 difference raw34386; decide +kernel
    rw [ha]
    exact (canonical34386 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2494 + difference 4 0) (sourceB2494 + difference 0 4) sourceC2494) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4323) := by
    have ha : (tripleCharges (sourceA2494 + difference 4 0) (sourceB2494 + difference 0 4) sourceC2494) = raw26156 := by
      apply Matrix.ext; unfold tripleCharges sourceA2494 sourceB2494 sourceC2494 difference raw26156; decide +kernel
    rw [ha]
    exact (canonical26156 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2494 + difference 4 1) (sourceB2494 + difference 1 4) sourceC2494) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4661) := by
    have ha : (tripleCharges (sourceA2494 + difference 4 1) (sourceB2494 + difference 1 4) sourceC2494) = raw34387 := by
      apply Matrix.ext; unfold tripleCharges sourceA2494 sourceB2494 sourceC2494 difference raw34387; decide +kernel
    rw [ha]
    exact (canonical34387 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2494 + difference 4 2) (sourceB2494 + difference 2 4) sourceC2494) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4715) := by
    have ha : (tripleCharges (sourceA2494 + difference 4 2) (sourceB2494 + difference 2 4) sourceC2494) = raw34388 := by
      apply Matrix.ext; unfold tripleCharges sourceA2494 sourceB2494 sourceC2494 difference raw34388; decide +kernel
    rw [ha]
    exact (canonical34388 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2494 + difference 4 3) (sourceB2494 + difference 3 4) sourceC2494) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4782) := by
    have ha : (tripleCharges (sourceA2494 + difference 4 3) (sourceB2494 + difference 3 4) sourceC2494) = raw34389 := by
      apply Matrix.ext; unfold tripleCharges sourceA2494 sourceB2494 sourceC2494 difference raw34389; decide +kernel
    rw [ha]
    exact (canonical34389 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2494 + difference 4 5) (sourceB2494 + difference 5 4) sourceC2494) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4787) := by
    have ha : (tripleCharges (sourceA2494 + difference 4 5) (sourceB2494 + difference 5 4) sourceC2494) = raw34390 := by
      apply Matrix.ext; unfold tripleCharges sourceA2494 sourceB2494 sourceC2494 difference raw34390; decide +kernel
    rw [ha]
    exact (canonical34390 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2494 + difference 5 0) (sourceB2494 + difference 0 5) sourceC2494) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4322) := by
    have ha : (tripleCharges (sourceA2494 + difference 5 0) (sourceB2494 + difference 0 5) sourceC2494) = raw26161 := by
      apply Matrix.ext; unfold tripleCharges sourceA2494 sourceB2494 sourceC2494 difference raw26161; decide +kernel
    rw [ha]
    exact (canonical26161 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2494 + difference 5 1) (sourceB2494 + difference 1 5) sourceC2494) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4660) := by
    have ha : (tripleCharges (sourceA2494 + difference 5 1) (sourceB2494 + difference 1 5) sourceC2494) = raw34391 := by
      apply Matrix.ext; unfold tripleCharges sourceA2494 sourceB2494 sourceC2494 difference raw34391; decide +kernel
    rw [ha]
    exact (canonical34391 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2494 + difference 5 2) (sourceB2494 + difference 2 5) sourceC2494) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4712) := by
    have ha : (tripleCharges (sourceA2494 + difference 5 2) (sourceB2494 + difference 2 5) sourceC2494) = raw34392 := by
      apply Matrix.ext; unfold tripleCharges sourceA2494 sourceB2494 sourceC2494 difference raw34392; decide +kernel
    rw [ha]
    exact (canonical34392 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2494 + difference 5 3) (sourceB2494 + difference 3 5) sourceC2494) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4779) := by
    have ha : (tripleCharges (sourceA2494 + difference 5 3) (sourceB2494 + difference 3 5) sourceC2494) = raw34393 := by
      apply Matrix.ext; unfold tripleCharges sourceA2494 sourceB2494 sourceC2494 difference raw34393; decide +kernel
    rw [ha]
    exact (canonical34393 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2494 + difference 5 4) (sourceB2494 + difference 4 5) sourceC2494) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4779) := by
    have ha : (tripleCharges (sourceA2494 + difference 5 4) (sourceB2494 + difference 4 5) sourceC2494) = raw34394 := by
      apply Matrix.ext; unfold tripleCharges sourceA2494 sourceB2494 sourceC2494 difference raw34394; decide +kernel
    rw [ha]
    exact (canonical34394 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2494 sourceB2494 sourceC2494
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2494, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2495 : Charge := ![0, 0, 1, 0, 0, -1]
def sourceB2495 : Charge := ![3, 1, -1, -1, -1, -1]
def sourceC2495 : Charge := ![-3, -1, 0, 1, 1, 2]
def sourceForm2495 : Integer.Sparse Master := [(Sum.inr 4080, 1), (Sum.inr 4300, 1), (Sum.inr 4301, 2), (Sum.inr 4307, 1), (Sum.inr 4417, 1), (Sum.inr 4641, 1), (Sum.inr 4642, 2), (Sum.inr 4648, 1), (Sum.inr 4736, 2), (Sum.inr 4737, 2), (Sum.inr 4740, 4), (Sum.inr 4746, 1), (Sum.inr 4752, 2), (Sum.inr 4802, 2), (Sum.inr 4805, 1), (Sum.inr 4838, 1), (Sum.inr 4998, 1), (Sum.inr 5073, 2), (Sum.inr 5076, 1), (Sum.inr 5104, 1)]

theorem sourceEq2495 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2495 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2495 + difference 0 1) (sourceB2495 + difference 1 0) sourceC2495) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4998) := by
    have ha : (tripleCharges (sourceA2495 + difference 0 1) (sourceB2495 + difference 1 0) sourceC2495) = raw33146 := by
      apply Matrix.ext; unfold tripleCharges sourceA2495 sourceB2495 sourceC2495 difference raw33146; decide +kernel
    rw [ha]
    exact (canonical33146 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2495 + difference 0 2) (sourceB2495 + difference 2 0) sourceC2495) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5104) := by
    have ha : (tripleCharges (sourceA2495 + difference 0 2) (sourceB2495 + difference 2 0) sourceC2495) = raw32251 := by
      apply Matrix.ext; unfold tripleCharges sourceA2495 sourceB2495 sourceC2495 difference raw32251; decide +kernel
    rw [ha]
    exact (canonical32251 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2495 + difference 0 3) (sourceB2495 + difference 3 0) sourceC2495) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5073) := by
    have ha : (tripleCharges (sourceA2495 + difference 0 3) (sourceB2495 + difference 3 0) sourceC2495) = raw32331 := by
      apply Matrix.ext; unfold tripleCharges sourceA2495 sourceB2495 sourceC2495 difference raw32331; decide +kernel
    rw [ha]
    exact (canonical32331 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2495 + difference 0 4) (sourceB2495 + difference 4 0) sourceC2495) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5073) := by
    have ha : (tripleCharges (sourceA2495 + difference 0 4) (sourceB2495 + difference 4 0) sourceC2495) = raw32328 := by
      apply Matrix.ext; unfold tripleCharges sourceA2495 sourceB2495 sourceC2495 difference raw32328; decide +kernel
    rw [ha]
    exact (canonical32328 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2495 + difference 0 5) (sourceB2495 + difference 5 0) sourceC2495) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5076) := by
    have ha : (tripleCharges (sourceA2495 + difference 0 5) (sourceB2495 + difference 5 0) sourceC2495) = raw32236 := by
      apply Matrix.ext; unfold tripleCharges sourceA2495 sourceB2495 sourceC2495 difference raw32236; decide +kernel
    rw [ha]
    exact (canonical32236 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2495 + difference 1 0) (sourceB2495 + difference 0 1) sourceC2495) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4417) := by
    have ha : (tripleCharges (sourceA2495 + difference 1 0) (sourceB2495 + difference 0 1) sourceC2495) = raw33873 := by
      apply Matrix.ext; unfold tripleCharges sourceA2495 sourceB2495 sourceC2495 difference raw33873; decide +kernel
    rw [ha]
    exact (canonical33873 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2495 + difference 1 2) (sourceB2495 + difference 2 1) sourceC2495) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4838) := by
    have ha : (tripleCharges (sourceA2495 + difference 1 2) (sourceB2495 + difference 2 1) sourceC2495) = raw32250 := by
      apply Matrix.ext; unfold tripleCharges sourceA2495 sourceB2495 sourceC2495 difference raw32250; decide +kernel
    rw [ha]
    exact (canonical32250 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2495 + difference 1 3) (sourceB2495 + difference 3 1) sourceC2495) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA2495 + difference 1 3) (sourceB2495 + difference 3 1) sourceC2495) = raw32330 := by
      apply Matrix.ext; unfold tripleCharges sourceA2495 sourceB2495 sourceC2495 difference raw32330; decide +kernel
    rw [ha]
    exact (canonical32330 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2495 + difference 1 4) (sourceB2495 + difference 4 1) sourceC2495) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA2495 + difference 1 4) (sourceB2495 + difference 4 1) sourceC2495) = raw32327 := by
      apply Matrix.ext; unfold tripleCharges sourceA2495 sourceB2495 sourceC2495 difference raw32327; decide +kernel
    rw [ha]
    exact (canonical32327 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2495 + difference 1 5) (sourceB2495 + difference 5 1) sourceC2495) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4805) := by
    have ha : (tripleCharges (sourceA2495 + difference 1 5) (sourceB2495 + difference 5 1) sourceC2495) = raw32235 := by
      apply Matrix.ext; unfold tripleCharges sourceA2495 sourceB2495 sourceC2495 difference raw32235; decide +kernel
    rw [ha]
    exact (canonical32235 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2495 + difference 2 0) (sourceB2495 + difference 0 2) sourceC2495) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4307) := by
    have ha : (tripleCharges (sourceA2495 + difference 2 0) (sourceB2495 + difference 0 2) sourceC2495) = raw34395 := by
      apply Matrix.ext; unfold tripleCharges sourceA2495 sourceB2495 sourceC2495 difference raw34395; decide +kernel
    rw [ha]
    exact (canonical34395 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2495 + difference 2 1) (sourceB2495 + difference 1 2) sourceC2495) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4648) := by
    have ha : (tripleCharges (sourceA2495 + difference 2 1) (sourceB2495 + difference 1 2) sourceC2495) = raw34396 := by
      apply Matrix.ext; unfold tripleCharges sourceA2495 sourceB2495 sourceC2495 difference raw34396; decide +kernel
    rw [ha]
    exact (canonical34396 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2495 + difference 2 3) (sourceB2495 + difference 3 2) sourceC2495) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4740) := by
    have ha : (tripleCharges (sourceA2495 + difference 2 3) (sourceB2495 + difference 3 2) sourceC2495) = raw34397 := by
      apply Matrix.ext; unfold tripleCharges sourceA2495 sourceB2495 sourceC2495 difference raw34397; decide +kernel
    rw [ha]
    exact (canonical34397 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2495 + difference 2 4) (sourceB2495 + difference 4 2) sourceC2495) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4740) := by
    have ha : (tripleCharges (sourceA2495 + difference 2 4) (sourceB2495 + difference 4 2) sourceC2495) = raw33136 := by
      apply Matrix.ext; unfold tripleCharges sourceA2495 sourceB2495 sourceC2495 difference raw33136; decide +kernel
    rw [ha]
    exact (canonical33136 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2495 + difference 2 5) (sourceB2495 + difference 5 2) sourceC2495) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4746) := by
    have ha : (tripleCharges (sourceA2495 + difference 2 5) (sourceB2495 + difference 5 2) sourceC2495) = raw33863 := by
      apply Matrix.ext; unfold tripleCharges sourceA2495 sourceB2495 sourceC2495 difference raw33863; decide +kernel
    rw [ha]
    exact (canonical33863 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2495 + difference 3 0) (sourceB2495 + difference 0 3) sourceC2495) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4301) := by
    have ha : (tripleCharges (sourceA2495 + difference 3 0) (sourceB2495 + difference 0 3) sourceC2495) = raw34398 := by
      apply Matrix.ext; unfold tripleCharges sourceA2495 sourceB2495 sourceC2495 difference raw34398; decide +kernel
    rw [ha]
    exact (canonical34398 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2495 + difference 3 1) (sourceB2495 + difference 1 3) sourceC2495) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4642) := by
    have ha : (tripleCharges (sourceA2495 + difference 3 1) (sourceB2495 + difference 1 3) sourceC2495) = raw34399 := by
      apply Matrix.ext; unfold tripleCharges sourceA2495 sourceB2495 sourceC2495 difference raw34399; decide +kernel
    rw [ha]
    exact (canonical34399 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2495 + difference 3 2) (sourceB2495 + difference 2 3) sourceC2495) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4752) := by
    have ha : (tripleCharges (sourceA2495 + difference 3 2) (sourceB2495 + difference 2 3) sourceC2495) = raw34195 := by
      apply Matrix.ext; unfold tripleCharges sourceA2495 sourceB2495 sourceC2495 difference raw34195; decide +kernel
    rw [ha]
    exact (canonical34195 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2495 + difference 3 4) (sourceB2495 + difference 4 3) sourceC2495) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4737) := by
    have ha : (tripleCharges (sourceA2495 + difference 3 4) (sourceB2495 + difference 4 3) sourceC2495) = raw33140 := by
      apply Matrix.ext; unfold tripleCharges sourceA2495 sourceB2495 sourceC2495 difference raw33140; decide +kernel
    rw [ha]
    exact (canonical33140 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2495 + difference 3 5) (sourceB2495 + difference 5 3) sourceC2495) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4740) := by
    have ha : (tripleCharges (sourceA2495 + difference 3 5) (sourceB2495 + difference 5 3) sourceC2495) = raw33867 := by
      apply Matrix.ext; unfold tripleCharges sourceA2495 sourceB2495 sourceC2495 difference raw33867; decide +kernel
    rw [ha]
    exact (canonical33867 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2495 + difference 4 0) (sourceB2495 + difference 0 4) sourceC2495) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4301) := by
    have ha : (tripleCharges (sourceA2495 + difference 4 0) (sourceB2495 + difference 0 4) sourceC2495) = raw34400 := by
      apply Matrix.ext; unfold tripleCharges sourceA2495 sourceB2495 sourceC2495 difference raw34400; decide +kernel
    rw [ha]
    exact (canonical34400 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2495 + difference 4 1) (sourceB2495 + difference 1 4) sourceC2495) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4642) := by
    have ha : (tripleCharges (sourceA2495 + difference 4 1) (sourceB2495 + difference 1 4) sourceC2495) = raw34401 := by
      apply Matrix.ext; unfold tripleCharges sourceA2495 sourceB2495 sourceC2495 difference raw34401; decide +kernel
    rw [ha]
    exact (canonical34401 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2495 + difference 4 2) (sourceB2495 + difference 2 4) sourceC2495) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4752) := by
    have ha : (tripleCharges (sourceA2495 + difference 4 2) (sourceB2495 + difference 2 4) sourceC2495) = raw34402 := by
      apply Matrix.ext; unfold tripleCharges sourceA2495 sourceB2495 sourceC2495 difference raw34402; decide +kernel
    rw [ha]
    exact (canonical34402 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2495 + difference 4 3) (sourceB2495 + difference 3 4) sourceC2495) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4737) := by
    have ha : (tripleCharges (sourceA2495 + difference 4 3) (sourceB2495 + difference 3 4) sourceC2495) = raw34403 := by
      apply Matrix.ext; unfold tripleCharges sourceA2495 sourceB2495 sourceC2495 difference raw34403; decide +kernel
    rw [ha]
    exact (canonical34403 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2495 + difference 4 5) (sourceB2495 + difference 5 4) sourceC2495) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4740) := by
    have ha : (tripleCharges (sourceA2495 + difference 4 5) (sourceB2495 + difference 5 4) sourceC2495) = raw33871 := by
      apply Matrix.ext; unfold tripleCharges sourceA2495 sourceB2495 sourceC2495 difference raw33871; decide +kernel
    rw [ha]
    exact (canonical33871 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2495 + difference 5 0) (sourceB2495 + difference 0 5) sourceC2495) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4300) := by
    have ha : (tripleCharges (sourceA2495 + difference 5 0) (sourceB2495 + difference 0 5) sourceC2495) = raw34404 := by
      apply Matrix.ext; unfold tripleCharges sourceA2495 sourceB2495 sourceC2495 difference raw34404; decide +kernel
    rw [ha]
    exact (canonical34404 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2495 + difference 5 1) (sourceB2495 + difference 1 5) sourceC2495) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4641) := by
    have ha : (tripleCharges (sourceA2495 + difference 5 1) (sourceB2495 + difference 1 5) sourceC2495) = raw33458 := by
      apply Matrix.ext; unfold tripleCharges sourceA2495 sourceB2495 sourceC2495 difference raw33458; decide +kernel
    rw [ha]
    exact (canonical33458 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2495 + difference 5 2) (sourceB2495 + difference 2 5) sourceC2495) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA2495 + difference 5 2) (sourceB2495 + difference 2 5) sourceC2495) = raw33420 := by
      apply Matrix.ext; unfold tripleCharges sourceA2495 sourceB2495 sourceC2495 difference raw33420; decide +kernel
    rw [ha]
    exact (canonical33420 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2495 + difference 5 3) (sourceB2495 + difference 3 5) sourceC2495) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4736) := by
    have ha : (tripleCharges (sourceA2495 + difference 5 3) (sourceB2495 + difference 3 5) sourceC2495) = raw33237 := by
      apply Matrix.ext; unfold tripleCharges sourceA2495 sourceB2495 sourceC2495 difference raw33237; decide +kernel
    rw [ha]
    exact (canonical33237 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2495 + difference 5 4) (sourceB2495 + difference 4 5) sourceC2495) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4736) := by
    have ha : (tripleCharges (sourceA2495 + difference 5 4) (sourceB2495 + difference 4 5) sourceC2495) = raw33147 := by
      apply Matrix.ext; unfold tripleCharges sourceA2495 sourceB2495 sourceC2495 difference raw33147; decide +kernel
    rw [ha]
    exact (canonical33147 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2495 sourceB2495 sourceC2495
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2495, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
