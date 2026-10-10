import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical42

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA160 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceB160 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceC160 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceForm160 : Integer.Sparse Master := [(Sum.inr 2193, 4), (Sum.inr 2208, 1), (Sum.inr 2218, 2), (Sum.inr 2268, 2), (Sum.inr 2664, 4), (Sum.inr 2680, 1), (Sum.inr 2691, 2), (Sum.inr 2712, 4), (Sum.inr 2726, 4), (Sum.inr 2734, 2), (Sum.inr 2770, 2), (Sum.inr 2790, 1), (Sum.inr 3090, 1)]

theorem sourceEq160 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm160 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA160 + difference 0 1) (sourceB160 + difference 1 0) sourceC160) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2770) := by
    have ha : (tripleCharges (sourceA160 + difference 0 1) (sourceB160 + difference 1 0) sourceC160) = raw4994 := by
      apply Matrix.ext; unfold tripleCharges sourceA160 sourceB160 sourceC160 difference raw4994; decide +kernel
    rw [ha]
    exact (canonical4994 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA160 + difference 0 2) (sourceB160 + difference 2 0) sourceC160) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2712) := by
    have ha : (tripleCharges (sourceA160 + difference 0 2) (sourceB160 + difference 2 0) sourceC160) = raw4995 := by
      apply Matrix.ext; unfold tripleCharges sourceA160 sourceB160 sourceC160 difference raw4995; decide +kernel
    rw [ha]
    exact (canonical4995 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA160 + difference 0 3) (sourceB160 + difference 3 0) sourceC160) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2712) := by
    have ha : (tripleCharges (sourceA160 + difference 0 3) (sourceB160 + difference 3 0) sourceC160) = raw4996 := by
      apply Matrix.ext; unfold tripleCharges sourceA160 sourceB160 sourceC160 difference raw4996; decide +kernel
    rw [ha]
    exact (canonical4996 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA160 + difference 0 4) (sourceB160 + difference 4 0) sourceC160) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2734) := by
    have ha : (tripleCharges (sourceA160 + difference 0 4) (sourceB160 + difference 4 0) sourceC160) = raw4997 := by
      apply Matrix.ext; unfold tripleCharges sourceA160 sourceB160 sourceC160 difference raw4997; decide +kernel
    rw [ha]
    exact (canonical4997 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA160 + difference 0 5) (sourceB160 + difference 5 0) sourceC160) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3090) := by
    have ha : (tripleCharges (sourceA160 + difference 0 5) (sourceB160 + difference 5 0) sourceC160) = raw4998 := by
      apply Matrix.ext; unfold tripleCharges sourceA160 sourceB160 sourceC160 difference raw4998; decide +kernel
    rw [ha]
    exact (canonical4998 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA160 + difference 1 0) (sourceB160 + difference 0 1) sourceC160) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2218) := by
    have ha : (tripleCharges (sourceA160 + difference 1 0) (sourceB160 + difference 0 1) sourceC160) = raw4999 := by
      apply Matrix.ext; unfold tripleCharges sourceA160 sourceB160 sourceC160 difference raw4999; decide +kernel
    rw [ha]
    exact (canonical4999 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA160 + difference 1 2) (sourceB160 + difference 2 1) sourceC160) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2664) := by
    have ha : (tripleCharges (sourceA160 + difference 1 2) (sourceB160 + difference 2 1) sourceC160) = raw5000 := by
      apply Matrix.ext; unfold tripleCharges sourceA160 sourceB160 sourceC160 difference raw5000; decide +kernel
    rw [ha]
    exact (canonical5000 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA160 + difference 1 3) (sourceB160 + difference 3 1) sourceC160) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2664) := by
    have ha : (tripleCharges (sourceA160 + difference 1 3) (sourceB160 + difference 3 1) sourceC160) = raw5001 := by
      apply Matrix.ext; unfold tripleCharges sourceA160 sourceB160 sourceC160 difference raw5001; decide +kernel
    rw [ha]
    exact (canonical5001 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA160 + difference 1 4) (sourceB160 + difference 4 1) sourceC160) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2680) := by
    have ha : (tripleCharges (sourceA160 + difference 1 4) (sourceB160 + difference 4 1) sourceC160) = raw5002 := by
      apply Matrix.ext; unfold tripleCharges sourceA160 sourceB160 sourceC160 difference raw5002; decide +kernel
    rw [ha]
    exact (canonical5002 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA160 + difference 1 5) (sourceB160 + difference 5 1) sourceC160) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2734) := by
    have ha : (tripleCharges (sourceA160 + difference 1 5) (sourceB160 + difference 5 1) sourceC160) = raw5003 := by
      apply Matrix.ext; unfold tripleCharges sourceA160 sourceB160 sourceC160 difference raw5003; decide +kernel
    rw [ha]
    exact (canonical5003 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA160 + difference 2 0) (sourceB160 + difference 0 2) sourceC160) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2193) := by
    have ha : (tripleCharges (sourceA160 + difference 2 0) (sourceB160 + difference 0 2) sourceC160) = raw5004 := by
      apply Matrix.ext; unfold tripleCharges sourceA160 sourceB160 sourceC160 difference raw5004; decide +kernel
    rw [ha]
    exact (canonical5004 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA160 + difference 2 1) (sourceB160 + difference 1 2) sourceC160) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2726) := by
    have ha : (tripleCharges (sourceA160 + difference 2 1) (sourceB160 + difference 1 2) sourceC160) = raw5005 := by
      apply Matrix.ext; unfold tripleCharges sourceA160 sourceB160 sourceC160 difference raw5005; decide +kernel
    rw [ha]
    exact (canonical5005 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA160 + difference 2 3) (sourceB160 + difference 3 2) sourceC160) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2691) := by
    have ha : (tripleCharges (sourceA160 + difference 2 3) (sourceB160 + difference 3 2) sourceC160) = raw5006 := by
      apply Matrix.ext; unfold tripleCharges sourceA160 sourceB160 sourceC160 difference raw5006; decide +kernel
    rw [ha]
    exact (canonical5006 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA160 + difference 2 4) (sourceB160 + difference 4 2) sourceC160) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2664) := by
    have ha : (tripleCharges (sourceA160 + difference 2 4) (sourceB160 + difference 4 2) sourceC160) = raw5007 := by
      apply Matrix.ext; unfold tripleCharges sourceA160 sourceB160 sourceC160 difference raw5007; decide +kernel
    rw [ha]
    exact (canonical5007 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA160 + difference 2 5) (sourceB160 + difference 5 2) sourceC160) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2712) := by
    have ha : (tripleCharges (sourceA160 + difference 2 5) (sourceB160 + difference 5 2) sourceC160) = raw5008 := by
      apply Matrix.ext; unfold tripleCharges sourceA160 sourceB160 sourceC160 difference raw5008; decide +kernel
    rw [ha]
    exact (canonical5008 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA160 + difference 3 0) (sourceB160 + difference 0 3) sourceC160) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2193) := by
    have ha : (tripleCharges (sourceA160 + difference 3 0) (sourceB160 + difference 0 3) sourceC160) = raw5009 := by
      apply Matrix.ext; unfold tripleCharges sourceA160 sourceB160 sourceC160 difference raw5009; decide +kernel
    rw [ha]
    exact (canonical5009 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA160 + difference 3 1) (sourceB160 + difference 1 3) sourceC160) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2726) := by
    have ha : (tripleCharges (sourceA160 + difference 3 1) (sourceB160 + difference 1 3) sourceC160) = raw5010 := by
      apply Matrix.ext; unfold tripleCharges sourceA160 sourceB160 sourceC160 difference raw5010; decide +kernel
    rw [ha]
    exact (canonical5010 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA160 + difference 3 2) (sourceB160 + difference 2 3) sourceC160) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2691) := by
    have ha : (tripleCharges (sourceA160 + difference 3 2) (sourceB160 + difference 2 3) sourceC160) = raw5011 := by
      apply Matrix.ext; unfold tripleCharges sourceA160 sourceB160 sourceC160 difference raw5011; decide +kernel
    rw [ha]
    exact (canonical5011 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA160 + difference 3 4) (sourceB160 + difference 4 3) sourceC160) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2664) := by
    have ha : (tripleCharges (sourceA160 + difference 3 4) (sourceB160 + difference 4 3) sourceC160) = raw5012 := by
      apply Matrix.ext; unfold tripleCharges sourceA160 sourceB160 sourceC160 difference raw5012; decide +kernel
    rw [ha]
    exact (canonical5012 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA160 + difference 3 5) (sourceB160 + difference 5 3) sourceC160) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2712) := by
    have ha : (tripleCharges (sourceA160 + difference 3 5) (sourceB160 + difference 5 3) sourceC160) = raw5013 := by
      apply Matrix.ext; unfold tripleCharges sourceA160 sourceB160 sourceC160 difference raw5013; decide +kernel
    rw [ha]
    exact (canonical5013 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA160 + difference 4 0) (sourceB160 + difference 0 4) sourceC160) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2268) := by
    have ha : (tripleCharges (sourceA160 + difference 4 0) (sourceB160 + difference 0 4) sourceC160) = raw5014 := by
      apply Matrix.ext; unfold tripleCharges sourceA160 sourceB160 sourceC160 difference raw5014; decide +kernel
    rw [ha]
    exact (canonical5014 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA160 + difference 4 1) (sourceB160 + difference 1 4) sourceC160) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2790) := by
    have ha : (tripleCharges (sourceA160 + difference 4 1) (sourceB160 + difference 1 4) sourceC160) = raw4371 := by
      apply Matrix.ext; unfold tripleCharges sourceA160 sourceB160 sourceC160 difference raw4371; decide +kernel
    rw [ha]
    exact (canonical4371 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA160 + difference 4 2) (sourceB160 + difference 2 4) sourceC160) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2726) := by
    have ha : (tripleCharges (sourceA160 + difference 4 2) (sourceB160 + difference 2 4) sourceC160) = raw5015 := by
      apply Matrix.ext; unfold tripleCharges sourceA160 sourceB160 sourceC160 difference raw5015; decide +kernel
    rw [ha]
    exact (canonical5015 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA160 + difference 4 3) (sourceB160 + difference 3 4) sourceC160) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2726) := by
    have ha : (tripleCharges (sourceA160 + difference 4 3) (sourceB160 + difference 3 4) sourceC160) = raw5016 := by
      apply Matrix.ext; unfold tripleCharges sourceA160 sourceB160 sourceC160 difference raw5016; decide +kernel
    rw [ha]
    exact (canonical5016 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA160 + difference 4 5) (sourceB160 + difference 5 4) sourceC160) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2770) := by
    have ha : (tripleCharges (sourceA160 + difference 4 5) (sourceB160 + difference 5 4) sourceC160) = raw4364 := by
      apply Matrix.ext; unfold tripleCharges sourceA160 sourceB160 sourceC160 difference raw4364; decide +kernel
    rw [ha]
    exact (canonical4364 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA160 + difference 5 0) (sourceB160 + difference 0 5) sourceC160) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2208) := by
    have ha : (tripleCharges (sourceA160 + difference 5 0) (sourceB160 + difference 0 5) sourceC160) = raw5017 := by
      apply Matrix.ext; unfold tripleCharges sourceA160 sourceB160 sourceC160 difference raw5017; decide +kernel
    rw [ha]
    exact (canonical5017 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA160 + difference 5 1) (sourceB160 + difference 1 5) sourceC160) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2268) := by
    have ha : (tripleCharges (sourceA160 + difference 5 1) (sourceB160 + difference 1 5) sourceC160) = raw5018 := by
      apply Matrix.ext; unfold tripleCharges sourceA160 sourceB160 sourceC160 difference raw5018; decide +kernel
    rw [ha]
    exact (canonical5018 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA160 + difference 5 2) (sourceB160 + difference 2 5) sourceC160) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2193) := by
    have ha : (tripleCharges (sourceA160 + difference 5 2) (sourceB160 + difference 2 5) sourceC160) = raw5019 := by
      apply Matrix.ext; unfold tripleCharges sourceA160 sourceB160 sourceC160 difference raw5019; decide +kernel
    rw [ha]
    exact (canonical5019 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA160 + difference 5 3) (sourceB160 + difference 3 5) sourceC160) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2193) := by
    have ha : (tripleCharges (sourceA160 + difference 5 3) (sourceB160 + difference 3 5) sourceC160) = raw5020 := by
      apply Matrix.ext; unfold tripleCharges sourceA160 sourceB160 sourceC160 difference raw5020; decide +kernel
    rw [ha]
    exact (canonical5020 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA160 + difference 5 4) (sourceB160 + difference 4 5) sourceC160) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2218) := by
    have ha : (tripleCharges (sourceA160 + difference 5 4) (sourceB160 + difference 4 5) sourceC160) = raw5021 := by
      apply Matrix.ext; unfold tripleCharges sourceA160 sourceB160 sourceC160 difference raw5021; decide +kernel
    rw [ha]
    exact (canonical5021 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA160 sourceB160 sourceC160
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm160, Integer.Sparse.eval]
  linarith only [hs]

def sourceA161 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceB161 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceC161 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceForm161 : Integer.Sparse Master := [(Sum.inr 2712, 4), (Sum.inr 2726, 1), (Sum.inr 2734, 2), (Sum.inr 2770, 2), (Sum.inr 3031, 4), (Sum.inr 3046, 1), (Sum.inr 3061, 2), (Sum.inr 3082, 4), (Sum.inr 3090, 4), (Sum.inr 3095, 2), (Sum.inr 3114, 2), (Sum.inr 3126, 1), (Sum.inr 3215, 1)]

theorem sourceEq161 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm161 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA161 + difference 0 1) (sourceB161 + difference 1 0) sourceC161) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2770) := by
    have ha : (tripleCharges (sourceA161 + difference 0 1) (sourceB161 + difference 1 0) sourceC161) = raw5022 := by
      apply Matrix.ext; unfold tripleCharges sourceA161 sourceB161 sourceC161 difference raw5022; decide +kernel
    rw [ha]
    exact (canonical5022 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA161 + difference 0 2) (sourceB161 + difference 2 0) sourceC161) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2712) := by
    have ha : (tripleCharges (sourceA161 + difference 0 2) (sourceB161 + difference 2 0) sourceC161) = raw5023 := by
      apply Matrix.ext; unfold tripleCharges sourceA161 sourceB161 sourceC161 difference raw5023; decide +kernel
    rw [ha]
    exact (canonical5023 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA161 + difference 0 3) (sourceB161 + difference 3 0) sourceC161) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2712) := by
    have ha : (tripleCharges (sourceA161 + difference 0 3) (sourceB161 + difference 3 0) sourceC161) = raw5024 := by
      apply Matrix.ext; unfold tripleCharges sourceA161 sourceB161 sourceC161 difference raw5024; decide +kernel
    rw [ha]
    exact (canonical5024 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA161 + difference 0 4) (sourceB161 + difference 4 0) sourceC161) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2734) := by
    have ha : (tripleCharges (sourceA161 + difference 0 4) (sourceB161 + difference 4 0) sourceC161) = raw5025 := by
      apply Matrix.ext; unfold tripleCharges sourceA161 sourceB161 sourceC161 difference raw5025; decide +kernel
    rw [ha]
    exact (canonical5025 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA161 + difference 0 5) (sourceB161 + difference 5 0) sourceC161) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2726) := by
    have ha : (tripleCharges (sourceA161 + difference 0 5) (sourceB161 + difference 5 0) sourceC161) = raw5026 := by
      apply Matrix.ext; unfold tripleCharges sourceA161 sourceB161 sourceC161 difference raw5026; decide +kernel
    rw [ha]
    exact (canonical5026 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA161 + difference 1 0) (sourceB161 + difference 0 1) sourceC161) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3095) := by
    have ha : (tripleCharges (sourceA161 + difference 1 0) (sourceB161 + difference 0 1) sourceC161) = raw5027 := by
      apply Matrix.ext; unfold tripleCharges sourceA161 sourceB161 sourceC161 difference raw5027; decide +kernel
    rw [ha]
    exact (canonical5027 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA161 + difference 1 2) (sourceB161 + difference 2 1) sourceC161) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3031) := by
    have ha : (tripleCharges (sourceA161 + difference 1 2) (sourceB161 + difference 2 1) sourceC161) = raw5028 := by
      apply Matrix.ext; unfold tripleCharges sourceA161 sourceB161 sourceC161 difference raw5028; decide +kernel
    rw [ha]
    exact (canonical5028 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA161 + difference 1 3) (sourceB161 + difference 3 1) sourceC161) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3031) := by
    have ha : (tripleCharges (sourceA161 + difference 1 3) (sourceB161 + difference 3 1) sourceC161) = raw5029 := by
      apply Matrix.ext; unfold tripleCharges sourceA161 sourceB161 sourceC161 difference raw5029; decide +kernel
    rw [ha]
    exact (canonical5029 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA161 + difference 1 4) (sourceB161 + difference 4 1) sourceC161) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3046) := by
    have ha : (tripleCharges (sourceA161 + difference 1 4) (sourceB161 + difference 4 1) sourceC161) = raw5030 := by
      apply Matrix.ext; unfold tripleCharges sourceA161 sourceB161 sourceC161 difference raw5030; decide +kernel
    rw [ha]
    exact (canonical5030 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA161 + difference 1 5) (sourceB161 + difference 5 1) sourceC161) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2734) := by
    have ha : (tripleCharges (sourceA161 + difference 1 5) (sourceB161 + difference 5 1) sourceC161) = raw5031 := by
      apply Matrix.ext; unfold tripleCharges sourceA161 sourceB161 sourceC161 difference raw5031; decide +kernel
    rw [ha]
    exact (canonical5031 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA161 + difference 2 0) (sourceB161 + difference 0 2) sourceC161) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3082) := by
    have ha : (tripleCharges (sourceA161 + difference 2 0) (sourceB161 + difference 0 2) sourceC161) = raw5032 := by
      apply Matrix.ext; unfold tripleCharges sourceA161 sourceB161 sourceC161 difference raw5032; decide +kernel
    rw [ha]
    exact (canonical5032 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA161 + difference 2 1) (sourceB161 + difference 1 2) sourceC161) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3090) := by
    have ha : (tripleCharges (sourceA161 + difference 2 1) (sourceB161 + difference 1 2) sourceC161) = raw5033 := by
      apply Matrix.ext; unfold tripleCharges sourceA161 sourceB161 sourceC161 difference raw5033; decide +kernel
    rw [ha]
    exact (canonical5033 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA161 + difference 2 3) (sourceB161 + difference 3 2) sourceC161) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3061) := by
    have ha : (tripleCharges (sourceA161 + difference 2 3) (sourceB161 + difference 3 2) sourceC161) = raw5034 := by
      apply Matrix.ext; unfold tripleCharges sourceA161 sourceB161 sourceC161 difference raw5034; decide +kernel
    rw [ha]
    exact (canonical5034 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA161 + difference 2 4) (sourceB161 + difference 4 2) sourceC161) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3031) := by
    have ha : (tripleCharges (sourceA161 + difference 2 4) (sourceB161 + difference 4 2) sourceC161) = raw5035 := by
      apply Matrix.ext; unfold tripleCharges sourceA161 sourceB161 sourceC161 difference raw5035; decide +kernel
    rw [ha]
    exact (canonical5035 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA161 + difference 2 5) (sourceB161 + difference 5 2) sourceC161) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2712) := by
    have ha : (tripleCharges (sourceA161 + difference 2 5) (sourceB161 + difference 5 2) sourceC161) = raw5036 := by
      apply Matrix.ext; unfold tripleCharges sourceA161 sourceB161 sourceC161 difference raw5036; decide +kernel
    rw [ha]
    exact (canonical5036 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA161 + difference 3 0) (sourceB161 + difference 0 3) sourceC161) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3082) := by
    have ha : (tripleCharges (sourceA161 + difference 3 0) (sourceB161 + difference 0 3) sourceC161) = raw5037 := by
      apply Matrix.ext; unfold tripleCharges sourceA161 sourceB161 sourceC161 difference raw5037; decide +kernel
    rw [ha]
    exact (canonical5037 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA161 + difference 3 1) (sourceB161 + difference 1 3) sourceC161) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3090) := by
    have ha : (tripleCharges (sourceA161 + difference 3 1) (sourceB161 + difference 1 3) sourceC161) = raw5038 := by
      apply Matrix.ext; unfold tripleCharges sourceA161 sourceB161 sourceC161 difference raw5038; decide +kernel
    rw [ha]
    exact (canonical5038 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA161 + difference 3 2) (sourceB161 + difference 2 3) sourceC161) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3061) := by
    have ha : (tripleCharges (sourceA161 + difference 3 2) (sourceB161 + difference 2 3) sourceC161) = raw5039 := by
      apply Matrix.ext; unfold tripleCharges sourceA161 sourceB161 sourceC161 difference raw5039; decide +kernel
    rw [ha]
    exact (canonical5039 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA161 + difference 3 4) (sourceB161 + difference 4 3) sourceC161) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3031) := by
    have ha : (tripleCharges (sourceA161 + difference 3 4) (sourceB161 + difference 4 3) sourceC161) = raw5040 := by
      apply Matrix.ext; unfold tripleCharges sourceA161 sourceB161 sourceC161 difference raw5040; decide +kernel
    rw [ha]
    exact (canonical5040 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA161 + difference 3 5) (sourceB161 + difference 5 3) sourceC161) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2712) := by
    have ha : (tripleCharges (sourceA161 + difference 3 5) (sourceB161 + difference 5 3) sourceC161) = raw5041 := by
      apply Matrix.ext; unfold tripleCharges sourceA161 sourceB161 sourceC161 difference raw5041; decide +kernel
    rw [ha]
    exact (canonical5041 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA161 + difference 4 0) (sourceB161 + difference 0 4) sourceC161) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3114) := by
    have ha : (tripleCharges (sourceA161 + difference 4 0) (sourceB161 + difference 0 4) sourceC161) = raw5042 := by
      apply Matrix.ext; unfold tripleCharges sourceA161 sourceB161 sourceC161 difference raw5042; decide +kernel
    rw [ha]
    exact (canonical5042 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA161 + difference 4 1) (sourceB161 + difference 1 4) sourceC161) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3126) := by
    have ha : (tripleCharges (sourceA161 + difference 4 1) (sourceB161 + difference 1 4) sourceC161) = raw5043 := by
      apply Matrix.ext; unfold tripleCharges sourceA161 sourceB161 sourceC161 difference raw5043; decide +kernel
    rw [ha]
    exact (canonical5043 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA161 + difference 4 2) (sourceB161 + difference 2 4) sourceC161) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3090) := by
    have ha : (tripleCharges (sourceA161 + difference 4 2) (sourceB161 + difference 2 4) sourceC161) = raw5044 := by
      apply Matrix.ext; unfold tripleCharges sourceA161 sourceB161 sourceC161 difference raw5044; decide +kernel
    rw [ha]
    exact (canonical5044 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA161 + difference 4 3) (sourceB161 + difference 3 4) sourceC161) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3090) := by
    have ha : (tripleCharges (sourceA161 + difference 4 3) (sourceB161 + difference 3 4) sourceC161) = raw5045 := by
      apply Matrix.ext; unfold tripleCharges sourceA161 sourceB161 sourceC161 difference raw5045; decide +kernel
    rw [ha]
    exact (canonical5045 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA161 + difference 4 5) (sourceB161 + difference 5 4) sourceC161) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2770) := by
    have ha : (tripleCharges (sourceA161 + difference 4 5) (sourceB161 + difference 5 4) sourceC161) = raw5046 := by
      apply Matrix.ext; unfold tripleCharges sourceA161 sourceB161 sourceC161 difference raw5046; decide +kernel
    rw [ha]
    exact (canonical5046 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA161 + difference 5 0) (sourceB161 + difference 0 5) sourceC161) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3215) := by
    have ha : (tripleCharges (sourceA161 + difference 5 0) (sourceB161 + difference 0 5) sourceC161) = raw5047 := by
      apply Matrix.ext; unfold tripleCharges sourceA161 sourceB161 sourceC161 difference raw5047; decide +kernel
    rw [ha]
    exact (canonical5047 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA161 + difference 5 1) (sourceB161 + difference 1 5) sourceC161) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3114) := by
    have ha : (tripleCharges (sourceA161 + difference 5 1) (sourceB161 + difference 1 5) sourceC161) = raw5048 := by
      apply Matrix.ext; unfold tripleCharges sourceA161 sourceB161 sourceC161 difference raw5048; decide +kernel
    rw [ha]
    exact (canonical5048 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA161 + difference 5 2) (sourceB161 + difference 2 5) sourceC161) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3082) := by
    have ha : (tripleCharges (sourceA161 + difference 5 2) (sourceB161 + difference 2 5) sourceC161) = raw5049 := by
      apply Matrix.ext; unfold tripleCharges sourceA161 sourceB161 sourceC161 difference raw5049; decide +kernel
    rw [ha]
    exact (canonical5049 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA161 + difference 5 3) (sourceB161 + difference 3 5) sourceC161) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3082) := by
    have ha : (tripleCharges (sourceA161 + difference 5 3) (sourceB161 + difference 3 5) sourceC161) = raw5050 := by
      apply Matrix.ext; unfold tripleCharges sourceA161 sourceB161 sourceC161 difference raw5050; decide +kernel
    rw [ha]
    exact (canonical5050 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA161 + difference 5 4) (sourceB161 + difference 4 5) sourceC161) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3095) := by
    have ha : (tripleCharges (sourceA161 + difference 5 4) (sourceB161 + difference 4 5) sourceC161) = raw5051 := by
      apply Matrix.ext; unfold tripleCharges sourceA161 sourceB161 sourceC161 difference raw5051; decide +kernel
    rw [ha]
    exact (canonical5051 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA161 sourceB161 sourceC161
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm161, Integer.Sparse.eval]
  linarith only [hs]

def sourceA162 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceB162 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceC162 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceForm162 : Integer.Sparse Master := [(Sum.inr 2052, 2), (Sum.inr 2056, 1), (Sum.inr 2065, 1), (Sum.inr 2292, 1), (Sum.inr 3545, 1), (Sum.inr 4085, -1)]

theorem sourceEq162 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm162 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA162 + difference 0 0) (sourceB162 + difference 0 0) sourceC162) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3545) := by
    have ha : (tripleCharges (sourceA162 + difference 0 0) (sourceB162 + difference 0 0) sourceC162) = raw5052 := by
      apply Matrix.ext; unfold tripleCharges sourceA162 sourceB162 sourceC162 difference raw5052; decide +kernel
    rw [ha]
    exact (canonical5052 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA162 + difference 1 0) (sourceB162 + difference 0 1) sourceC162) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2065) := by
    have ha : (tripleCharges (sourceA162 + difference 1 0) (sourceB162 + difference 0 1) sourceC162) = raw5053 := by
      apply Matrix.ext; unfold tripleCharges sourceA162 sourceB162 sourceC162 difference raw5053; decide +kernel
    rw [ha]
    exact (canonical5053 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA162 + difference 2 0) (sourceB162 + difference 0 2) sourceC162) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2052) := by
    have ha : (tripleCharges (sourceA162 + difference 2 0) (sourceB162 + difference 0 2) sourceC162) = raw5054 := by
      apply Matrix.ext; unfold tripleCharges sourceA162 sourceB162 sourceC162 difference raw5054; decide +kernel
    rw [ha]
    exact (canonical5054 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA162 + difference 3 0) (sourceB162 + difference 0 3) sourceC162) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2052) := by
    have ha : (tripleCharges (sourceA162 + difference 3 0) (sourceB162 + difference 0 3) sourceC162) = raw5055 := by
      apply Matrix.ext; unfold tripleCharges sourceA162 sourceB162 sourceC162 difference raw5055; decide +kernel
    rw [ha]
    exact (canonical5055 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA162 + difference 4 0) (sourceB162 + difference 0 4) sourceC162) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2292) := by
    have ha : (tripleCharges (sourceA162 + difference 4 0) (sourceB162 + difference 0 4) sourceC162) = raw5056 := by
      apply Matrix.ext; unfold tripleCharges sourceA162 sourceB162 sourceC162 difference raw5056; decide +kernel
    rw [ha]
    exact (canonical5056 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA162 + difference 5 0) (sourceB162 + difference 0 5) sourceC162) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2056) := by
    have ha : (tripleCharges (sourceA162 + difference 5 0) (sourceB162 + difference 0 5) sourceC162) = raw5057 := by
      apply Matrix.ext; unfold tripleCharges sourceA162 sourceB162 sourceC162 difference raw5057; decide +kernel
    rw [ha]
    exact (canonical5057 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA162 + sourceB162) sourceC162) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA162 + sourceB162) sourceC162) = raw3721 := by
      apply Matrix.ext; unfold doubleCharges sourceA162 sourceB162 sourceC162 raw3721; decide +kernel
    rw [ha]
    exact (canonical3721 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA162 sourceB162 sourceC162
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm162, Integer.Sparse.eval]
  linarith only [hs]

def sourceA163 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB163 : Charge := ![1, 0, 0, 0, 0, -1]
def sourceC163 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceForm163 : Integer.Sparse Master := [(Sum.inr 4094, 1), (Sum.inr 4625, 8), (Sum.inr 4629, 1), (Sum.inr 5171, 12), (Sum.inr 5308, 8)]

theorem sourceEq163 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm163 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA163 + difference 0 1) (sourceB163 + difference 1 0) sourceC163) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5308) := by
    have ha : (tripleCharges (sourceA163 + difference 0 1) (sourceB163 + difference 1 0) sourceC163) = raw5058 := by
      apply Matrix.ext; unfold tripleCharges sourceA163 sourceB163 sourceC163 difference raw5058; decide +kernel
    rw [ha]
    exact (canonical5058 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA163 + difference 0 2) (sourceB163 + difference 2 0) sourceC163) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5308) := by
    have ha : (tripleCharges (sourceA163 + difference 0 2) (sourceB163 + difference 2 0) sourceC163) = raw5059 := by
      apply Matrix.ext; unfold tripleCharges sourceA163 sourceB163 sourceC163 difference raw5059; decide +kernel
    rw [ha]
    exact (canonical5059 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA163 + difference 0 3) (sourceB163 + difference 3 0) sourceC163) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5308) := by
    have ha : (tripleCharges (sourceA163 + difference 0 3) (sourceB163 + difference 3 0) sourceC163) = raw5060 := by
      apply Matrix.ext; unfold tripleCharges sourceA163 sourceB163 sourceC163 difference raw5060; decide +kernel
    rw [ha]
    exact (canonical5060 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA163 + difference 0 4) (sourceB163 + difference 4 0) sourceC163) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5308) := by
    have ha : (tripleCharges (sourceA163 + difference 0 4) (sourceB163 + difference 4 0) sourceC163) = raw5061 := by
      apply Matrix.ext; unfold tripleCharges sourceA163 sourceB163 sourceC163 difference raw5061; decide +kernel
    rw [ha]
    exact (canonical5061 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA163 + difference 0 5) (sourceB163 + difference 5 0) sourceC163) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4094) := by
    have ha : (tripleCharges (sourceA163 + difference 0 5) (sourceB163 + difference 5 0) sourceC163) = raw5062 := by
      apply Matrix.ext; unfold tripleCharges sourceA163 sourceB163 sourceC163 difference raw5062; decide +kernel
    rw [ha]
    exact (canonical5062 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA163 + difference 1 0) (sourceB163 + difference 0 1) sourceC163) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4625) := by
    have ha : (tripleCharges (sourceA163 + difference 1 0) (sourceB163 + difference 0 1) sourceC163) = raw5063 := by
      apply Matrix.ext; unfold tripleCharges sourceA163 sourceB163 sourceC163 difference raw5063; decide +kernel
    rw [ha]
    exact (canonical5063 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA163 + difference 1 2) (sourceB163 + difference 2 1) sourceC163) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5171) := by
    have ha : (tripleCharges (sourceA163 + difference 1 2) (sourceB163 + difference 2 1) sourceC163) = raw5064 := by
      apply Matrix.ext; unfold tripleCharges sourceA163 sourceB163 sourceC163 difference raw5064; decide +kernel
    rw [ha]
    exact (canonical5064 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA163 + difference 1 3) (sourceB163 + difference 3 1) sourceC163) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5171) := by
    have ha : (tripleCharges (sourceA163 + difference 1 3) (sourceB163 + difference 3 1) sourceC163) = raw5065 := by
      apply Matrix.ext; unfold tripleCharges sourceA163 sourceB163 sourceC163 difference raw5065; decide +kernel
    rw [ha]
    exact (canonical5065 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA163 + difference 1 4) (sourceB163 + difference 4 1) sourceC163) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5171) := by
    have ha : (tripleCharges (sourceA163 + difference 1 4) (sourceB163 + difference 4 1) sourceC163) = raw5066 := by
      apply Matrix.ext; unfold tripleCharges sourceA163 sourceB163 sourceC163 difference raw5066; decide +kernel
    rw [ha]
    exact (canonical5066 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA163 + difference 1 5) (sourceB163 + difference 5 1) sourceC163) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5308) := by
    have ha : (tripleCharges (sourceA163 + difference 1 5) (sourceB163 + difference 5 1) sourceC163) = raw5067 := by
      apply Matrix.ext; unfold tripleCharges sourceA163 sourceB163 sourceC163 difference raw5067; decide +kernel
    rw [ha]
    exact (canonical5067 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA163 + difference 2 0) (sourceB163 + difference 0 2) sourceC163) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4625) := by
    have ha : (tripleCharges (sourceA163 + difference 2 0) (sourceB163 + difference 0 2) sourceC163) = raw5068 := by
      apply Matrix.ext; unfold tripleCharges sourceA163 sourceB163 sourceC163 difference raw5068; decide +kernel
    rw [ha]
    exact (canonical5068 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA163 + difference 2 1) (sourceB163 + difference 1 2) sourceC163) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5171) := by
    have ha : (tripleCharges (sourceA163 + difference 2 1) (sourceB163 + difference 1 2) sourceC163) = raw5069 := by
      apply Matrix.ext; unfold tripleCharges sourceA163 sourceB163 sourceC163 difference raw5069; decide +kernel
    rw [ha]
    exact (canonical5069 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA163 + difference 2 3) (sourceB163 + difference 3 2) sourceC163) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5171) := by
    have ha : (tripleCharges (sourceA163 + difference 2 3) (sourceB163 + difference 3 2) sourceC163) = raw5070 := by
      apply Matrix.ext; unfold tripleCharges sourceA163 sourceB163 sourceC163 difference raw5070; decide +kernel
    rw [ha]
    exact (canonical5070 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA163 + difference 2 4) (sourceB163 + difference 4 2) sourceC163) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5171) := by
    have ha : (tripleCharges (sourceA163 + difference 2 4) (sourceB163 + difference 4 2) sourceC163) = raw5071 := by
      apply Matrix.ext; unfold tripleCharges sourceA163 sourceB163 sourceC163 difference raw5071; decide +kernel
    rw [ha]
    exact (canonical5071 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA163 + difference 2 5) (sourceB163 + difference 5 2) sourceC163) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5308) := by
    have ha : (tripleCharges (sourceA163 + difference 2 5) (sourceB163 + difference 5 2) sourceC163) = raw5072 := by
      apply Matrix.ext; unfold tripleCharges sourceA163 sourceB163 sourceC163 difference raw5072; decide +kernel
    rw [ha]
    exact (canonical5072 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA163 + difference 3 0) (sourceB163 + difference 0 3) sourceC163) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4625) := by
    have ha : (tripleCharges (sourceA163 + difference 3 0) (sourceB163 + difference 0 3) sourceC163) = raw5073 := by
      apply Matrix.ext; unfold tripleCharges sourceA163 sourceB163 sourceC163 difference raw5073; decide +kernel
    rw [ha]
    exact (canonical5073 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA163 + difference 3 1) (sourceB163 + difference 1 3) sourceC163) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5171) := by
    have ha : (tripleCharges (sourceA163 + difference 3 1) (sourceB163 + difference 1 3) sourceC163) = raw5074 := by
      apply Matrix.ext; unfold tripleCharges sourceA163 sourceB163 sourceC163 difference raw5074; decide +kernel
    rw [ha]
    exact (canonical5074 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA163 + difference 3 2) (sourceB163 + difference 2 3) sourceC163) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5171) := by
    have ha : (tripleCharges (sourceA163 + difference 3 2) (sourceB163 + difference 2 3) sourceC163) = raw5075 := by
      apply Matrix.ext; unfold tripleCharges sourceA163 sourceB163 sourceC163 difference raw5075; decide +kernel
    rw [ha]
    exact (canonical5075 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA163 + difference 3 4) (sourceB163 + difference 4 3) sourceC163) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5171) := by
    have ha : (tripleCharges (sourceA163 + difference 3 4) (sourceB163 + difference 4 3) sourceC163) = raw5076 := by
      apply Matrix.ext; unfold tripleCharges sourceA163 sourceB163 sourceC163 difference raw5076; decide +kernel
    rw [ha]
    exact (canonical5076 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA163 + difference 3 5) (sourceB163 + difference 5 3) sourceC163) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5308) := by
    have ha : (tripleCharges (sourceA163 + difference 3 5) (sourceB163 + difference 5 3) sourceC163) = raw5077 := by
      apply Matrix.ext; unfold tripleCharges sourceA163 sourceB163 sourceC163 difference raw5077; decide +kernel
    rw [ha]
    exact (canonical5077 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA163 + difference 4 0) (sourceB163 + difference 0 4) sourceC163) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4625) := by
    have ha : (tripleCharges (sourceA163 + difference 4 0) (sourceB163 + difference 0 4) sourceC163) = raw5078 := by
      apply Matrix.ext; unfold tripleCharges sourceA163 sourceB163 sourceC163 difference raw5078; decide +kernel
    rw [ha]
    exact (canonical5078 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA163 + difference 4 1) (sourceB163 + difference 1 4) sourceC163) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5171) := by
    have ha : (tripleCharges (sourceA163 + difference 4 1) (sourceB163 + difference 1 4) sourceC163) = raw5079 := by
      apply Matrix.ext; unfold tripleCharges sourceA163 sourceB163 sourceC163 difference raw5079; decide +kernel
    rw [ha]
    exact (canonical5079 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA163 + difference 4 2) (sourceB163 + difference 2 4) sourceC163) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5171) := by
    have ha : (tripleCharges (sourceA163 + difference 4 2) (sourceB163 + difference 2 4) sourceC163) = raw5080 := by
      apply Matrix.ext; unfold tripleCharges sourceA163 sourceB163 sourceC163 difference raw5080; decide +kernel
    rw [ha]
    exact (canonical5080 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA163 + difference 4 3) (sourceB163 + difference 3 4) sourceC163) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5171) := by
    have ha : (tripleCharges (sourceA163 + difference 4 3) (sourceB163 + difference 3 4) sourceC163) = raw5081 := by
      apply Matrix.ext; unfold tripleCharges sourceA163 sourceB163 sourceC163 difference raw5081; decide +kernel
    rw [ha]
    exact (canonical5081 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA163 + difference 4 5) (sourceB163 + difference 5 4) sourceC163) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5308) := by
    have ha : (tripleCharges (sourceA163 + difference 4 5) (sourceB163 + difference 5 4) sourceC163) = raw5082 := by
      apply Matrix.ext; unfold tripleCharges sourceA163 sourceB163 sourceC163 difference raw5082; decide +kernel
    rw [ha]
    exact (canonical5082 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA163 + difference 5 0) (sourceB163 + difference 0 5) sourceC163) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4629) := by
    have ha : (tripleCharges (sourceA163 + difference 5 0) (sourceB163 + difference 0 5) sourceC163) = raw5083 := by
      apply Matrix.ext; unfold tripleCharges sourceA163 sourceB163 sourceC163 difference raw5083; decide +kernel
    rw [ha]
    exact (canonical5083 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA163 + difference 5 1) (sourceB163 + difference 1 5) sourceC163) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4625) := by
    have ha : (tripleCharges (sourceA163 + difference 5 1) (sourceB163 + difference 1 5) sourceC163) = raw5084 := by
      apply Matrix.ext; unfold tripleCharges sourceA163 sourceB163 sourceC163 difference raw5084; decide +kernel
    rw [ha]
    exact (canonical5084 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA163 + difference 5 2) (sourceB163 + difference 2 5) sourceC163) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4625) := by
    have ha : (tripleCharges (sourceA163 + difference 5 2) (sourceB163 + difference 2 5) sourceC163) = raw5085 := by
      apply Matrix.ext; unfold tripleCharges sourceA163 sourceB163 sourceC163 difference raw5085; decide +kernel
    rw [ha]
    exact (canonical5085 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA163 + difference 5 3) (sourceB163 + difference 3 5) sourceC163) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4625) := by
    have ha : (tripleCharges (sourceA163 + difference 5 3) (sourceB163 + difference 3 5) sourceC163) = raw5086 := by
      apply Matrix.ext; unfold tripleCharges sourceA163 sourceB163 sourceC163 difference raw5086; decide +kernel
    rw [ha]
    exact (canonical5086 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA163 + difference 5 4) (sourceB163 + difference 4 5) sourceC163) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4625) := by
    have ha : (tripleCharges (sourceA163 + difference 5 4) (sourceB163 + difference 4 5) sourceC163) = raw5087 := by
      apply Matrix.ext; unfold tripleCharges sourceA163 sourceB163 sourceC163 difference raw5087; decide +kernel
    rw [ha]
    exact (canonical5087 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA163 sourceB163 sourceC163
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm163, Integer.Sparse.eval]
  linarith only [hs]

def sourceA164 : Charge := ![1, 0, 0, 0, 0, -1]
def sourceB164 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC164 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceForm164 : Integer.Sparse Master := [(Sum.inr 4085, 1), (Sum.inr 4897, 8), (Sum.inr 5261, 12), (Sum.inr 5296, 8), (Sum.inr 5312, 1)]

theorem sourceEq164 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm164 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA164 + difference 0 1) (sourceB164 + difference 1 0) sourceC164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5296) := by
    have ha : (tripleCharges (sourceA164 + difference 0 1) (sourceB164 + difference 1 0) sourceC164) = raw5088 := by
      apply Matrix.ext; unfold tripleCharges sourceA164 sourceB164 sourceC164 difference raw5088; decide +kernel
    rw [ha]
    exact (canonical5088 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA164 + difference 0 2) (sourceB164 + difference 2 0) sourceC164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5296) := by
    have ha : (tripleCharges (sourceA164 + difference 0 2) (sourceB164 + difference 2 0) sourceC164) = raw5089 := by
      apply Matrix.ext; unfold tripleCharges sourceA164 sourceB164 sourceC164 difference raw5089; decide +kernel
    rw [ha]
    exact (canonical5089 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA164 + difference 0 3) (sourceB164 + difference 3 0) sourceC164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5296) := by
    have ha : (tripleCharges (sourceA164 + difference 0 3) (sourceB164 + difference 3 0) sourceC164) = raw5090 := by
      apply Matrix.ext; unfold tripleCharges sourceA164 sourceB164 sourceC164 difference raw5090; decide +kernel
    rw [ha]
    exact (canonical5090 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA164 + difference 0 4) (sourceB164 + difference 4 0) sourceC164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5296) := by
    have ha : (tripleCharges (sourceA164 + difference 0 4) (sourceB164 + difference 4 0) sourceC164) = raw4966 := by
      apply Matrix.ext; unfold tripleCharges sourceA164 sourceB164 sourceC164 difference raw4966; decide +kernel
    rw [ha]
    exact (canonical4966 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA164 + difference 0 5) (sourceB164 + difference 5 0) sourceC164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5312) := by
    have ha : (tripleCharges (sourceA164 + difference 0 5) (sourceB164 + difference 5 0) sourceC164) = raw4344 := by
      apply Matrix.ext; unfold tripleCharges sourceA164 sourceB164 sourceC164 difference raw4344; decide +kernel
    rw [ha]
    exact (canonical4344 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA164 + difference 1 0) (sourceB164 + difference 0 1) sourceC164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4897) := by
    have ha : (tripleCharges (sourceA164 + difference 1 0) (sourceB164 + difference 0 1) sourceC164) = raw4986 := by
      apply Matrix.ext; unfold tripleCharges sourceA164 sourceB164 sourceC164 difference raw4986; decide +kernel
    rw [ha]
    exact (canonical4986 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA164 + difference 1 2) (sourceB164 + difference 2 1) sourceC164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5261) := by
    have ha : (tripleCharges (sourceA164 + difference 1 2) (sourceB164 + difference 2 1) sourceC164) = raw4987 := by
      apply Matrix.ext; unfold tripleCharges sourceA164 sourceB164 sourceC164 difference raw4987; decide +kernel
    rw [ha]
    exact (canonical4987 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA164 + difference 1 3) (sourceB164 + difference 3 1) sourceC164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5261) := by
    have ha : (tripleCharges (sourceA164 + difference 1 3) (sourceB164 + difference 3 1) sourceC164) = raw4988 := by
      apply Matrix.ext; unfold tripleCharges sourceA164 sourceB164 sourceC164 difference raw4988; decide +kernel
    rw [ha]
    exact (canonical4988 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA164 + difference 1 4) (sourceB164 + difference 4 1) sourceC164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5261) := by
    have ha : (tripleCharges (sourceA164 + difference 1 4) (sourceB164 + difference 4 1) sourceC164) = raw5091 := by
      apply Matrix.ext; unfold tripleCharges sourceA164 sourceB164 sourceC164 difference raw5091; decide +kernel
    rw [ha]
    exact (canonical5091 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA164 + difference 1 5) (sourceB164 + difference 5 1) sourceC164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5296) := by
    have ha : (tripleCharges (sourceA164 + difference 1 5) (sourceB164 + difference 5 1) sourceC164) = raw4349 := by
      apply Matrix.ext; unfold tripleCharges sourceA164 sourceB164 sourceC164 difference raw4349; decide +kernel
    rw [ha]
    exact (canonical4349 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA164 + difference 2 0) (sourceB164 + difference 0 2) sourceC164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4897) := by
    have ha : (tripleCharges (sourceA164 + difference 2 0) (sourceB164 + difference 0 2) sourceC164) = raw5092 := by
      apply Matrix.ext; unfold tripleCharges sourceA164 sourceB164 sourceC164 difference raw5092; decide +kernel
    rw [ha]
    exact (canonical5092 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA164 + difference 2 1) (sourceB164 + difference 1 2) sourceC164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5261) := by
    have ha : (tripleCharges (sourceA164 + difference 2 1) (sourceB164 + difference 1 2) sourceC164) = raw5093 := by
      apply Matrix.ext; unfold tripleCharges sourceA164 sourceB164 sourceC164 difference raw5093; decide +kernel
    rw [ha]
    exact (canonical5093 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA164 + difference 2 3) (sourceB164 + difference 3 2) sourceC164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5261) := by
    have ha : (tripleCharges (sourceA164 + difference 2 3) (sourceB164 + difference 3 2) sourceC164) = raw5094 := by
      apply Matrix.ext; unfold tripleCharges sourceA164 sourceB164 sourceC164 difference raw5094; decide +kernel
    rw [ha]
    exact (canonical5094 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA164 + difference 2 4) (sourceB164 + difference 4 2) sourceC164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5261) := by
    have ha : (tripleCharges (sourceA164 + difference 2 4) (sourceB164 + difference 4 2) sourceC164) = raw4977 := by
      apply Matrix.ext; unfold tripleCharges sourceA164 sourceB164 sourceC164 difference raw4977; decide +kernel
    rw [ha]
    exact (canonical4977 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA164 + difference 2 5) (sourceB164 + difference 5 2) sourceC164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5296) := by
    have ha : (tripleCharges (sourceA164 + difference 2 5) (sourceB164 + difference 5 2) sourceC164) = raw4352 := by
      apply Matrix.ext; unfold tripleCharges sourceA164 sourceB164 sourceC164 difference raw4352; decide +kernel
    rw [ha]
    exact (canonical4352 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA164 + difference 3 0) (sourceB164 + difference 0 3) sourceC164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4897) := by
    have ha : (tripleCharges (sourceA164 + difference 3 0) (sourceB164 + difference 0 3) sourceC164) = raw5095 := by
      apply Matrix.ext; unfold tripleCharges sourceA164 sourceB164 sourceC164 difference raw5095; decide +kernel
    rw [ha]
    exact (canonical5095 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA164 + difference 3 1) (sourceB164 + difference 1 3) sourceC164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5261) := by
    have ha : (tripleCharges (sourceA164 + difference 3 1) (sourceB164 + difference 1 3) sourceC164) = raw4248 := by
      apply Matrix.ext; unfold tripleCharges sourceA164 sourceB164 sourceC164 difference raw4248; decide +kernel
    rw [ha]
    exact (canonical4248 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA164 + difference 3 2) (sourceB164 + difference 2 3) sourceC164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5261) := by
    have ha : (tripleCharges (sourceA164 + difference 3 2) (sourceB164 + difference 2 3) sourceC164) = raw5096 := by
      apply Matrix.ext; unfold tripleCharges sourceA164 sourceB164 sourceC164 difference raw5096; decide +kernel
    rw [ha]
    exact (canonical5096 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA164 + difference 3 4) (sourceB164 + difference 4 3) sourceC164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5261) := by
    have ha : (tripleCharges (sourceA164 + difference 3 4) (sourceB164 + difference 4 3) sourceC164) = raw4982 := by
      apply Matrix.ext; unfold tripleCharges sourceA164 sourceB164 sourceC164 difference raw4982; decide +kernel
    rw [ha]
    exact (canonical4982 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA164 + difference 3 5) (sourceB164 + difference 5 3) sourceC164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5296) := by
    have ha : (tripleCharges (sourceA164 + difference 3 5) (sourceB164 + difference 5 3) sourceC164) = raw4236 := by
      apply Matrix.ext; unfold tripleCharges sourceA164 sourceB164 sourceC164 difference raw4236; decide +kernel
    rw [ha]
    exact (canonical4236 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA164 + difference 4 0) (sourceB164 + difference 0 4) sourceC164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4897) := by
    have ha : (tripleCharges (sourceA164 + difference 4 0) (sourceB164 + difference 0 4) sourceC164) = raw4353 := by
      apply Matrix.ext; unfold tripleCharges sourceA164 sourceB164 sourceC164 difference raw4353; decide +kernel
    rw [ha]
    exact (canonical4353 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA164 + difference 4 1) (sourceB164 + difference 1 4) sourceC164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5261) := by
    have ha : (tripleCharges (sourceA164 + difference 4 1) (sourceB164 + difference 1 4) sourceC164) = raw4058 := by
      apply Matrix.ext; unfold tripleCharges sourceA164 sourceB164 sourceC164 difference raw4058; decide +kernel
    rw [ha]
    exact (canonical4058 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA164 + difference 4 2) (sourceB164 + difference 2 4) sourceC164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5261) := by
    have ha : (tripleCharges (sourceA164 + difference 4 2) (sourceB164 + difference 2 4) sourceC164) = raw4354 := by
      apply Matrix.ext; unfold tripleCharges sourceA164 sourceB164 sourceC164 difference raw4354; decide +kernel
    rw [ha]
    exact (canonical4354 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA164 + difference 4 3) (sourceB164 + difference 3 4) sourceC164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5261) := by
    have ha : (tripleCharges (sourceA164 + difference 4 3) (sourceB164 + difference 3 4) sourceC164) = raw4355 := by
      apply Matrix.ext; unfold tripleCharges sourceA164 sourceB164 sourceC164 difference raw4355; decide +kernel
    rw [ha]
    exact (canonical4355 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA164 + difference 4 5) (sourceB164 + difference 5 4) sourceC164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5296) := by
    have ha : (tripleCharges (sourceA164 + difference 4 5) (sourceB164 + difference 5 4) sourceC164) = raw4040 := by
      apply Matrix.ext; unfold tripleCharges sourceA164 sourceB164 sourceC164 difference raw4040; decide +kernel
    rw [ha]
    exact (canonical4040 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA164 + difference 5 0) (sourceB164 + difference 0 5) sourceC164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (tripleCharges (sourceA164 + difference 5 0) (sourceB164 + difference 0 5) sourceC164) = raw5097 := by
      apply Matrix.ext; unfold tripleCharges sourceA164 sourceB164 sourceC164 difference raw5097; decide +kernel
    rw [ha]
    exact (canonical5097 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA164 + difference 5 1) (sourceB164 + difference 1 5) sourceC164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4897) := by
    have ha : (tripleCharges (sourceA164 + difference 5 1) (sourceB164 + difference 1 5) sourceC164) = raw5098 := by
      apply Matrix.ext; unfold tripleCharges sourceA164 sourceB164 sourceC164 difference raw5098; decide +kernel
    rw [ha]
    exact (canonical5098 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA164 + difference 5 2) (sourceB164 + difference 2 5) sourceC164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4897) := by
    have ha : (tripleCharges (sourceA164 + difference 5 2) (sourceB164 + difference 2 5) sourceC164) = raw5099 := by
      apply Matrix.ext; unfold tripleCharges sourceA164 sourceB164 sourceC164 difference raw5099; decide +kernel
    rw [ha]
    exact (canonical5099 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA164 + difference 5 3) (sourceB164 + difference 3 5) sourceC164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4897) := by
    have ha : (tripleCharges (sourceA164 + difference 5 3) (sourceB164 + difference 3 5) sourceC164) = raw5100 := by
      apply Matrix.ext; unfold tripleCharges sourceA164 sourceB164 sourceC164 difference raw5100; decide +kernel
    rw [ha]
    exact (canonical5100 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA164 + difference 5 4) (sourceB164 + difference 4 5) sourceC164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4897) := by
    have ha : (tripleCharges (sourceA164 + difference 5 4) (sourceB164 + difference 4 5) sourceC164) = raw4990 := by
      apply Matrix.ext; unfold tripleCharges sourceA164 sourceB164 sourceC164 difference raw4990; decide +kernel
    rw [ha]
    exact (canonical4990 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA164 sourceB164 sourceC164
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm164, Integer.Sparse.eval]
  linarith only [hs]

def sourceA165 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB165 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceC165 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceForm165 : Integer.Sparse Master := [(Sum.inr 4084, 1), (Sum.inr 4460, 3), (Sum.inr 4468, 1), (Sum.inr 4505, 1), (Sum.inr 4605, 3), (Sum.inr 4621, 1), (Sum.inr 4804, 6), (Sum.inr 4841, 3), (Sum.inr 4868, 3), (Sum.inr 4894, 3), (Sum.inr 5272, 3), (Sum.inr 5305, 1), (Sum.inr 5308, 1)]

theorem sourceEq165 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm165 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA165 + difference 0 1) (sourceB165 + difference 1 0) sourceC165) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4894) := by
    have ha : (tripleCharges (sourceA165 + difference 0 1) (sourceB165 + difference 1 0) sourceC165) = raw5101 := by
      apply Matrix.ext; unfold tripleCharges sourceA165 sourceB165 sourceC165 difference raw5101; decide +kernel
    rw [ha]
    exact (canonical5101 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA165 + difference 0 2) (sourceB165 + difference 2 0) sourceC165) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4894) := by
    have ha : (tripleCharges (sourceA165 + difference 0 2) (sourceB165 + difference 2 0) sourceC165) = raw5102 := by
      apply Matrix.ext; unfold tripleCharges sourceA165 sourceB165 sourceC165 difference raw5102; decide +kernel
    rw [ha]
    exact (canonical5102 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA165 + difference 0 3) (sourceB165 + difference 3 0) sourceC165) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4894) := by
    have ha : (tripleCharges (sourceA165 + difference 0 3) (sourceB165 + difference 3 0) sourceC165) = raw5103 := by
      apply Matrix.ext; unfold tripleCharges sourceA165 sourceB165 sourceC165 difference raw5103; decide +kernel
    rw [ha]
    exact (canonical5103 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA165 + difference 0 4) (sourceB165 + difference 4 0) sourceC165) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA165 + difference 0 4) (sourceB165 + difference 4 0) sourceC165) = raw5104 := by
      apply Matrix.ext; unfold tripleCharges sourceA165 sourceB165 sourceC165 difference raw5104; decide +kernel
    rw [ha]
    exact (canonical5104 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA165 + difference 0 5) (sourceB165 + difference 5 0) sourceC165) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5308) := by
    have ha : (tripleCharges (sourceA165 + difference 0 5) (sourceB165 + difference 5 0) sourceC165) = raw5105 := by
      apply Matrix.ext; unfold tripleCharges sourceA165 sourceB165 sourceC165 difference raw5105; decide +kernel
    rw [ha]
    exact (canonical5105 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA165 + difference 1 0) (sourceB165 + difference 0 1) sourceC165) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4605) := by
    have ha : (tripleCharges (sourceA165 + difference 1 0) (sourceB165 + difference 0 1) sourceC165) = raw5106 := by
      apply Matrix.ext; unfold tripleCharges sourceA165 sourceB165 sourceC165 difference raw5106; decide +kernel
    rw [ha]
    exact (canonical5106 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA165 + difference 1 2) (sourceB165 + difference 2 1) sourceC165) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA165 + difference 1 2) (sourceB165 + difference 2 1) sourceC165) = raw5107 := by
      apply Matrix.ext; unfold tripleCharges sourceA165 sourceB165 sourceC165 difference raw5107; decide +kernel
    rw [ha]
    exact (canonical5107 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA165 + difference 1 3) (sourceB165 + difference 3 1) sourceC165) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA165 + difference 1 3) (sourceB165 + difference 3 1) sourceC165) = raw5108 := by
      apply Matrix.ext; unfold tripleCharges sourceA165 sourceB165 sourceC165 difference raw5108; decide +kernel
    rw [ha]
    exact (canonical5108 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA165 + difference 1 4) (sourceB165 + difference 4 1) sourceC165) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4841) := by
    have ha : (tripleCharges (sourceA165 + difference 1 4) (sourceB165 + difference 4 1) sourceC165) = raw5109 := by
      apply Matrix.ext; unfold tripleCharges sourceA165 sourceB165 sourceC165 difference raw5109; decide +kernel
    rw [ha]
    exact (canonical5109 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA165 + difference 1 5) (sourceB165 + difference 5 1) sourceC165) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5272) := by
    have ha : (tripleCharges (sourceA165 + difference 1 5) (sourceB165 + difference 5 1) sourceC165) = raw5110 := by
      apply Matrix.ext; unfold tripleCharges sourceA165 sourceB165 sourceC165 difference raw5110; decide +kernel
    rw [ha]
    exact (canonical5110 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA165 + difference 2 0) (sourceB165 + difference 0 2) sourceC165) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4605) := by
    have ha : (tripleCharges (sourceA165 + difference 2 0) (sourceB165 + difference 0 2) sourceC165) = raw5111 := by
      apply Matrix.ext; unfold tripleCharges sourceA165 sourceB165 sourceC165 difference raw5111; decide +kernel
    rw [ha]
    exact (canonical5111 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA165 + difference 2 1) (sourceB165 + difference 1 2) sourceC165) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA165 + difference 2 1) (sourceB165 + difference 1 2) sourceC165) = raw5112 := by
      apply Matrix.ext; unfold tripleCharges sourceA165 sourceB165 sourceC165 difference raw5112; decide +kernel
    rw [ha]
    exact (canonical5112 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA165 + difference 2 3) (sourceB165 + difference 3 2) sourceC165) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA165 + difference 2 3) (sourceB165 + difference 3 2) sourceC165) = raw5113 := by
      apply Matrix.ext; unfold tripleCharges sourceA165 sourceB165 sourceC165 difference raw5113; decide +kernel
    rw [ha]
    exact (canonical5113 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA165 + difference 2 4) (sourceB165 + difference 4 2) sourceC165) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4841) := by
    have ha : (tripleCharges (sourceA165 + difference 2 4) (sourceB165 + difference 4 2) sourceC165) = raw5114 := by
      apply Matrix.ext; unfold tripleCharges sourceA165 sourceB165 sourceC165 difference raw5114; decide +kernel
    rw [ha]
    exact (canonical5114 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA165 + difference 2 5) (sourceB165 + difference 5 2) sourceC165) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5272) := by
    have ha : (tripleCharges (sourceA165 + difference 2 5) (sourceB165 + difference 5 2) sourceC165) = raw5115 := by
      apply Matrix.ext; unfold tripleCharges sourceA165 sourceB165 sourceC165 difference raw5115; decide +kernel
    rw [ha]
    exact (canonical5115 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA165 + difference 3 0) (sourceB165 + difference 0 3) sourceC165) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4605) := by
    have ha : (tripleCharges (sourceA165 + difference 3 0) (sourceB165 + difference 0 3) sourceC165) = raw5116 := by
      apply Matrix.ext; unfold tripleCharges sourceA165 sourceB165 sourceC165 difference raw5116; decide +kernel
    rw [ha]
    exact (canonical5116 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA165 + difference 3 1) (sourceB165 + difference 1 3) sourceC165) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA165 + difference 3 1) (sourceB165 + difference 1 3) sourceC165) = raw5117 := by
      apply Matrix.ext; unfold tripleCharges sourceA165 sourceB165 sourceC165 difference raw5117; decide +kernel
    rw [ha]
    exact (canonical5117 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA165 + difference 3 2) (sourceB165 + difference 2 3) sourceC165) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA165 + difference 3 2) (sourceB165 + difference 2 3) sourceC165) = raw5118 := by
      apply Matrix.ext; unfold tripleCharges sourceA165 sourceB165 sourceC165 difference raw5118; decide +kernel
    rw [ha]
    exact (canonical5118 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA165 + difference 3 4) (sourceB165 + difference 4 3) sourceC165) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4841) := by
    have ha : (tripleCharges (sourceA165 + difference 3 4) (sourceB165 + difference 4 3) sourceC165) = raw5119 := by
      apply Matrix.ext; unfold tripleCharges sourceA165 sourceB165 sourceC165 difference raw5119; decide +kernel
    rw [ha]
    exact (canonical5119 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA165 + difference 3 5) (sourceB165 + difference 5 3) sourceC165) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5272) := by
    have ha : (tripleCharges (sourceA165 + difference 3 5) (sourceB165 + difference 5 3) sourceC165) = raw5120 := by
      apply Matrix.ext; unfold tripleCharges sourceA165 sourceB165 sourceC165 difference raw5120; decide +kernel
    rw [ha]
    exact (canonical5120 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA165 + difference 4 0) (sourceB165 + difference 0 4) sourceC165) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4621) := by
    have ha : (tripleCharges (sourceA165 + difference 4 0) (sourceB165 + difference 0 4) sourceC165) = raw5121 := by
      apply Matrix.ext; unfold tripleCharges sourceA165 sourceB165 sourceC165 difference raw5121; decide +kernel
    rw [ha]
    exact (canonical5121 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA165 + difference 4 1) (sourceB165 + difference 1 4) sourceC165) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4868) := by
    have ha : (tripleCharges (sourceA165 + difference 4 1) (sourceB165 + difference 1 4) sourceC165) = raw5122 := by
      apply Matrix.ext; unfold tripleCharges sourceA165 sourceB165 sourceC165 difference raw5122; decide +kernel
    rw [ha]
    exact (canonical5122 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA165 + difference 4 2) (sourceB165 + difference 2 4) sourceC165) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4868) := by
    have ha : (tripleCharges (sourceA165 + difference 4 2) (sourceB165 + difference 2 4) sourceC165) = raw5123 := by
      apply Matrix.ext; unfold tripleCharges sourceA165 sourceB165 sourceC165 difference raw5123; decide +kernel
    rw [ha]
    exact (canonical5123 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA165 + difference 4 3) (sourceB165 + difference 3 4) sourceC165) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4868) := by
    have ha : (tripleCharges (sourceA165 + difference 4 3) (sourceB165 + difference 3 4) sourceC165) = raw5124 := by
      apply Matrix.ext; unfold tripleCharges sourceA165 sourceB165 sourceC165 difference raw5124; decide +kernel
    rw [ha]
    exact (canonical5124 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA165 + difference 4 5) (sourceB165 + difference 5 4) sourceC165) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5305) := by
    have ha : (tripleCharges (sourceA165 + difference 4 5) (sourceB165 + difference 5 4) sourceC165) = raw5125 := by
      apply Matrix.ext; unfold tripleCharges sourceA165 sourceB165 sourceC165 difference raw5125; decide +kernel
    rw [ha]
    exact (canonical5125 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA165 + difference 5 0) (sourceB165 + difference 0 5) sourceC165) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4468) := by
    have ha : (tripleCharges (sourceA165 + difference 5 0) (sourceB165 + difference 0 5) sourceC165) = raw5126 := by
      apply Matrix.ext; unfold tripleCharges sourceA165 sourceB165 sourceC165 difference raw5126; decide +kernel
    rw [ha]
    exact (canonical5126 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA165 + difference 5 1) (sourceB165 + difference 1 5) sourceC165) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4460) := by
    have ha : (tripleCharges (sourceA165 + difference 5 1) (sourceB165 + difference 1 5) sourceC165) = raw5127 := by
      apply Matrix.ext; unfold tripleCharges sourceA165 sourceB165 sourceC165 difference raw5127; decide +kernel
    rw [ha]
    exact (canonical5127 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA165 + difference 5 2) (sourceB165 + difference 2 5) sourceC165) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4460) := by
    have ha : (tripleCharges (sourceA165 + difference 5 2) (sourceB165 + difference 2 5) sourceC165) = raw5128 := by
      apply Matrix.ext; unfold tripleCharges sourceA165 sourceB165 sourceC165 difference raw5128; decide +kernel
    rw [ha]
    exact (canonical5128 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA165 + difference 5 3) (sourceB165 + difference 3 5) sourceC165) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4460) := by
    have ha : (tripleCharges (sourceA165 + difference 5 3) (sourceB165 + difference 3 5) sourceC165) = raw5129 := by
      apply Matrix.ext; unfold tripleCharges sourceA165 sourceB165 sourceC165 difference raw5129; decide +kernel
    rw [ha]
    exact (canonical5129 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA165 + difference 5 4) (sourceB165 + difference 4 5) sourceC165) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4505) := by
    have ha : (tripleCharges (sourceA165 + difference 5 4) (sourceB165 + difference 4 5) sourceC165) = raw5130 := by
      apply Matrix.ext; unfold tripleCharges sourceA165 sourceB165 sourceC165 difference raw5130; decide +kernel
    rw [ha]
    exact (canonical5130 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA165 sourceB165 sourceC165
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm165, Integer.Sparse.eval]
  linarith only [hs]

def sourceA166 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB166 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceC166 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceForm166 : Integer.Sparse Master := [(Sum.inr 1725, 3), (Sum.inr 1752, 1), (Sum.inr 1754, 1), (Sum.inr 2203, 6), (Sum.inr 2226, 3), (Sum.inr 2228, 3), (Sum.inr 2261, 3), (Sum.inr 2264, 3), (Sum.inr 2289, 1), (Sum.inr 2740, 3), (Sum.inr 2783, 1), (Sum.inr 2786, 1), (Sum.inr 4084, 1)]

theorem sourceEq166 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm166 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA166 + difference 0 1) (sourceB166 + difference 1 0) sourceC166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2264) := by
    have ha : (tripleCharges (sourceA166 + difference 0 1) (sourceB166 + difference 1 0) sourceC166) = raw5131 := by
      apply Matrix.ext; unfold tripleCharges sourceA166 sourceB166 sourceC166 difference raw5131; decide +kernel
    rw [ha]
    exact (canonical5131 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA166 + difference 0 2) (sourceB166 + difference 2 0) sourceC166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2264) := by
    have ha : (tripleCharges (sourceA166 + difference 0 2) (sourceB166 + difference 2 0) sourceC166) = raw5132 := by
      apply Matrix.ext; unfold tripleCharges sourceA166 sourceB166 sourceC166 difference raw5132; decide +kernel
    rw [ha]
    exact (canonical5132 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA166 + difference 0 3) (sourceB166 + difference 3 0) sourceC166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2264) := by
    have ha : (tripleCharges (sourceA166 + difference 0 3) (sourceB166 + difference 3 0) sourceC166) = raw5133 := by
      apply Matrix.ext; unfold tripleCharges sourceA166 sourceB166 sourceC166 difference raw5133; decide +kernel
    rw [ha]
    exact (canonical5133 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA166 + difference 0 4) (sourceB166 + difference 4 0) sourceC166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA166 + difference 0 4) (sourceB166 + difference 4 0) sourceC166) = raw5134 := by
      apply Matrix.ext; unfold tripleCharges sourceA166 sourceB166 sourceC166 difference raw5134; decide +kernel
    rw [ha]
    exact (canonical5134 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA166 + difference 0 5) (sourceB166 + difference 5 0) sourceC166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2786) := by
    have ha : (tripleCharges (sourceA166 + difference 0 5) (sourceB166 + difference 5 0) sourceC166) = raw5135 := by
      apply Matrix.ext; unfold tripleCharges sourceA166 sourceB166 sourceC166 difference raw5135; decide +kernel
    rw [ha]
    exact (canonical5135 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA166 + difference 1 0) (sourceB166 + difference 0 1) sourceC166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2226) := by
    have ha : (tripleCharges (sourceA166 + difference 1 0) (sourceB166 + difference 0 1) sourceC166) = raw5136 := by
      apply Matrix.ext; unfold tripleCharges sourceA166 sourceB166 sourceC166 difference raw5136; decide +kernel
    rw [ha]
    exact (canonical5136 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA166 + difference 1 2) (sourceB166 + difference 2 1) sourceC166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2203) := by
    have ha : (tripleCharges (sourceA166 + difference 1 2) (sourceB166 + difference 2 1) sourceC166) = raw5137 := by
      apply Matrix.ext; unfold tripleCharges sourceA166 sourceB166 sourceC166 difference raw5137; decide +kernel
    rw [ha]
    exact (canonical5137 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA166 + difference 1 3) (sourceB166 + difference 3 1) sourceC166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2203) := by
    have ha : (tripleCharges (sourceA166 + difference 1 3) (sourceB166 + difference 3 1) sourceC166) = raw5138 := by
      apply Matrix.ext; unfold tripleCharges sourceA166 sourceB166 sourceC166 difference raw5138; decide +kernel
    rw [ha]
    exact (canonical5138 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA166 + difference 1 4) (sourceB166 + difference 4 1) sourceC166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2228) := by
    have ha : (tripleCharges (sourceA166 + difference 1 4) (sourceB166 + difference 4 1) sourceC166) = raw5139 := by
      apply Matrix.ext; unfold tripleCharges sourceA166 sourceB166 sourceC166 difference raw5139; decide +kernel
    rw [ha]
    exact (canonical5139 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA166 + difference 1 5) (sourceB166 + difference 5 1) sourceC166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2740) := by
    have ha : (tripleCharges (sourceA166 + difference 1 5) (sourceB166 + difference 5 1) sourceC166) = raw5140 := by
      apply Matrix.ext; unfold tripleCharges sourceA166 sourceB166 sourceC166 difference raw5140; decide +kernel
    rw [ha]
    exact (canonical5140 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA166 + difference 2 0) (sourceB166 + difference 0 2) sourceC166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2226) := by
    have ha : (tripleCharges (sourceA166 + difference 2 0) (sourceB166 + difference 0 2) sourceC166) = raw5141 := by
      apply Matrix.ext; unfold tripleCharges sourceA166 sourceB166 sourceC166 difference raw5141; decide +kernel
    rw [ha]
    exact (canonical5141 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA166 + difference 2 1) (sourceB166 + difference 1 2) sourceC166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2203) := by
    have ha : (tripleCharges (sourceA166 + difference 2 1) (sourceB166 + difference 1 2) sourceC166) = raw5142 := by
      apply Matrix.ext; unfold tripleCharges sourceA166 sourceB166 sourceC166 difference raw5142; decide +kernel
    rw [ha]
    exact (canonical5142 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA166 + difference 2 3) (sourceB166 + difference 3 2) sourceC166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2203) := by
    have ha : (tripleCharges (sourceA166 + difference 2 3) (sourceB166 + difference 3 2) sourceC166) = raw5143 := by
      apply Matrix.ext; unfold tripleCharges sourceA166 sourceB166 sourceC166 difference raw5143; decide +kernel
    rw [ha]
    exact (canonical5143 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA166 + difference 2 4) (sourceB166 + difference 4 2) sourceC166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2228) := by
    have ha : (tripleCharges (sourceA166 + difference 2 4) (sourceB166 + difference 4 2) sourceC166) = raw5144 := by
      apply Matrix.ext; unfold tripleCharges sourceA166 sourceB166 sourceC166 difference raw5144; decide +kernel
    rw [ha]
    exact (canonical5144 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA166 + difference 2 5) (sourceB166 + difference 5 2) sourceC166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2740) := by
    have ha : (tripleCharges (sourceA166 + difference 2 5) (sourceB166 + difference 5 2) sourceC166) = raw5145 := by
      apply Matrix.ext; unfold tripleCharges sourceA166 sourceB166 sourceC166 difference raw5145; decide +kernel
    rw [ha]
    exact (canonical5145 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA166 + difference 3 0) (sourceB166 + difference 0 3) sourceC166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2226) := by
    have ha : (tripleCharges (sourceA166 + difference 3 0) (sourceB166 + difference 0 3) sourceC166) = raw5146 := by
      apply Matrix.ext; unfold tripleCharges sourceA166 sourceB166 sourceC166 difference raw5146; decide +kernel
    rw [ha]
    exact (canonical5146 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA166 + difference 3 1) (sourceB166 + difference 1 3) sourceC166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2203) := by
    have ha : (tripleCharges (sourceA166 + difference 3 1) (sourceB166 + difference 1 3) sourceC166) = raw5147 := by
      apply Matrix.ext; unfold tripleCharges sourceA166 sourceB166 sourceC166 difference raw5147; decide +kernel
    rw [ha]
    exact (canonical5147 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA166 + difference 3 2) (sourceB166 + difference 2 3) sourceC166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2203) := by
    have ha : (tripleCharges (sourceA166 + difference 3 2) (sourceB166 + difference 2 3) sourceC166) = raw5148 := by
      apply Matrix.ext; unfold tripleCharges sourceA166 sourceB166 sourceC166 difference raw5148; decide +kernel
    rw [ha]
    exact (canonical5148 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA166 + difference 3 4) (sourceB166 + difference 4 3) sourceC166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2228) := by
    have ha : (tripleCharges (sourceA166 + difference 3 4) (sourceB166 + difference 4 3) sourceC166) = raw5149 := by
      apply Matrix.ext; unfold tripleCharges sourceA166 sourceB166 sourceC166 difference raw5149; decide +kernel
    rw [ha]
    exact (canonical5149 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA166 + difference 3 5) (sourceB166 + difference 5 3) sourceC166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2740) := by
    have ha : (tripleCharges (sourceA166 + difference 3 5) (sourceB166 + difference 5 3) sourceC166) = raw5150 := by
      apply Matrix.ext; unfold tripleCharges sourceA166 sourceB166 sourceC166 difference raw5150; decide +kernel
    rw [ha]
    exact (canonical5150 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA166 + difference 4 0) (sourceB166 + difference 0 4) sourceC166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2289) := by
    have ha : (tripleCharges (sourceA166 + difference 4 0) (sourceB166 + difference 0 4) sourceC166) = raw5151 := by
      apply Matrix.ext; unfold tripleCharges sourceA166 sourceB166 sourceC166 difference raw5151; decide +kernel
    rw [ha]
    exact (canonical5151 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA166 + difference 4 1) (sourceB166 + difference 1 4) sourceC166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2261) := by
    have ha : (tripleCharges (sourceA166 + difference 4 1) (sourceB166 + difference 1 4) sourceC166) = raw5152 := by
      apply Matrix.ext; unfold tripleCharges sourceA166 sourceB166 sourceC166 difference raw5152; decide +kernel
    rw [ha]
    exact (canonical5152 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA166 + difference 4 2) (sourceB166 + difference 2 4) sourceC166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2261) := by
    have ha : (tripleCharges (sourceA166 + difference 4 2) (sourceB166 + difference 2 4) sourceC166) = raw5153 := by
      apply Matrix.ext; unfold tripleCharges sourceA166 sourceB166 sourceC166 difference raw5153; decide +kernel
    rw [ha]
    exact (canonical5153 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA166 + difference 4 3) (sourceB166 + difference 3 4) sourceC166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2261) := by
    have ha : (tripleCharges (sourceA166 + difference 4 3) (sourceB166 + difference 3 4) sourceC166) = raw5154 := by
      apply Matrix.ext; unfold tripleCharges sourceA166 sourceB166 sourceC166 difference raw5154; decide +kernel
    rw [ha]
    exact (canonical5154 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA166 + difference 4 5) (sourceB166 + difference 5 4) sourceC166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2783) := by
    have ha : (tripleCharges (sourceA166 + difference 4 5) (sourceB166 + difference 5 4) sourceC166) = raw5155 := by
      apply Matrix.ext; unfold tripleCharges sourceA166 sourceB166 sourceC166 difference raw5155; decide +kernel
    rw [ha]
    exact (canonical5155 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA166 + difference 5 0) (sourceB166 + difference 0 5) sourceC166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1752) := by
    have ha : (tripleCharges (sourceA166 + difference 5 0) (sourceB166 + difference 0 5) sourceC166) = raw5156 := by
      apply Matrix.ext; unfold tripleCharges sourceA166 sourceB166 sourceC166 difference raw5156; decide +kernel
    rw [ha]
    exact (canonical5156 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA166 + difference 5 1) (sourceB166 + difference 1 5) sourceC166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1725) := by
    have ha : (tripleCharges (sourceA166 + difference 5 1) (sourceB166 + difference 1 5) sourceC166) = raw5157 := by
      apply Matrix.ext; unfold tripleCharges sourceA166 sourceB166 sourceC166 difference raw5157; decide +kernel
    rw [ha]
    exact (canonical5157 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA166 + difference 5 2) (sourceB166 + difference 2 5) sourceC166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1725) := by
    have ha : (tripleCharges (sourceA166 + difference 5 2) (sourceB166 + difference 2 5) sourceC166) = raw5158 := by
      apply Matrix.ext; unfold tripleCharges sourceA166 sourceB166 sourceC166 difference raw5158; decide +kernel
    rw [ha]
    exact (canonical5158 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA166 + difference 5 3) (sourceB166 + difference 3 5) sourceC166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1725) := by
    have ha : (tripleCharges (sourceA166 + difference 5 3) (sourceB166 + difference 3 5) sourceC166) = raw5159 := by
      apply Matrix.ext; unfold tripleCharges sourceA166 sourceB166 sourceC166 difference raw5159; decide +kernel
    rw [ha]
    exact (canonical5159 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA166 + difference 5 4) (sourceB166 + difference 4 5) sourceC166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1754) := by
    have ha : (tripleCharges (sourceA166 + difference 5 4) (sourceB166 + difference 4 5) sourceC166) = raw5160 := by
      apply Matrix.ext; unfold tripleCharges sourceA166 sourceB166 sourceC166 difference raw5160; decide +kernel
    rw [ha]
    exact (canonical5160 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA166 sourceB166 sourceC166
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm166, Integer.Sparse.eval]
  linarith only [hs]

def sourceA167 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB167 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceC167 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceForm167 : Integer.Sparse Master := [(Sum.inr 1051, 1), (Sum.inr 1239, 3), (Sum.inr 1297, 1), (Sum.inr 2268, 1), (Sum.inr 4084, -1)]

theorem sourceEq167 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm167 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA167 + difference 0 0) (sourceB167 + difference 0 0) sourceC167) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2268) := by
    have ha : (tripleCharges (sourceA167 + difference 0 0) (sourceB167 + difference 0 0) sourceC167) = raw5161 := by
      apply Matrix.ext; unfold tripleCharges sourceA167 sourceB167 sourceC167 difference raw5161; decide +kernel
    rw [ha]
    exact (canonical5161 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA167 + difference 1 0) (sourceB167 + difference 0 1) sourceC167) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1239) := by
    have ha : (tripleCharges (sourceA167 + difference 1 0) (sourceB167 + difference 0 1) sourceC167) = raw5162 := by
      apply Matrix.ext; unfold tripleCharges sourceA167 sourceB167 sourceC167 difference raw5162; decide +kernel
    rw [ha]
    exact (canonical5162 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA167 + difference 2 0) (sourceB167 + difference 0 2) sourceC167) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1239) := by
    have ha : (tripleCharges (sourceA167 + difference 2 0) (sourceB167 + difference 0 2) sourceC167) = raw5163 := by
      apply Matrix.ext; unfold tripleCharges sourceA167 sourceB167 sourceC167 difference raw5163; decide +kernel
    rw [ha]
    exact (canonical5163 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA167 + difference 3 0) (sourceB167 + difference 0 3) sourceC167) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1239) := by
    have ha : (tripleCharges (sourceA167 + difference 3 0) (sourceB167 + difference 0 3) sourceC167) = raw5164 := by
      apply Matrix.ext; unfold tripleCharges sourceA167 sourceB167 sourceC167 difference raw5164; decide +kernel
    rw [ha]
    exact (canonical5164 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA167 + difference 4 0) (sourceB167 + difference 0 4) sourceC167) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1297) := by
    have ha : (tripleCharges (sourceA167 + difference 4 0) (sourceB167 + difference 0 4) sourceC167) = raw5165 := by
      apply Matrix.ext; unfold tripleCharges sourceA167 sourceB167 sourceC167 difference raw5165; decide +kernel
    rw [ha]
    exact (canonical5165 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA167 + difference 5 0) (sourceB167 + difference 0 5) sourceC167) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1051) := by
    have ha : (tripleCharges (sourceA167 + difference 5 0) (sourceB167 + difference 0 5) sourceC167) = raw5166 := by
      apply Matrix.ext; unfold tripleCharges sourceA167 sourceB167 sourceC167 difference raw5166; decide +kernel
    rw [ha]
    exact (canonical5166 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA167 + sourceB167) sourceC167) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA167 + sourceB167) sourceC167) = raw5167 := by
      apply Matrix.ext; unfold doubleCharges sourceA167 sourceB167 sourceC167 raw5167; decide +kernel
    rw [ha]
    exact (canonical5167 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA167 sourceB167 sourceC167
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm167, Integer.Sparse.eval]
  linarith only [hs]

def sourceA168 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB168 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceC168 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceForm168 : Integer.Sparse Master := [(Sum.inr 1239, 1), (Sum.inr 2022, 2), (Sum.inr 2060, 1), (Sum.inr 2268, 1), (Sum.inr 2740, 1), (Sum.inr 4084, -1)]

theorem sourceEq168 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm168 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA168 + difference 1 0) (sourceB168 + difference 0 1) sourceC168) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1239) := by
    have ha : (tripleCharges (sourceA168 + difference 1 0) (sourceB168 + difference 0 1) sourceC168) = raw5162 := by
      apply Matrix.ext; unfold tripleCharges sourceA168 sourceB168 sourceC168 difference raw5162; decide +kernel
    rw [ha]
    exact (canonical5162 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA168 + difference 1 1) (sourceB168 + difference 1 1) sourceC168) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2268) := by
    have ha : (tripleCharges (sourceA168 + difference 1 1) (sourceB168 + difference 1 1) sourceC168) = raw5161 := by
      apply Matrix.ext; unfold tripleCharges sourceA168 sourceB168 sourceC168 difference raw5161; decide +kernel
    rw [ha]
    exact (canonical5161 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA168 + difference 1 2) (sourceB168 + difference 2 1) sourceC168) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2022) := by
    have ha : (tripleCharges (sourceA168 + difference 1 2) (sourceB168 + difference 2 1) sourceC168) = raw5168 := by
      apply Matrix.ext; unfold tripleCharges sourceA168 sourceB168 sourceC168 difference raw5168; decide +kernel
    rw [ha]
    exact (canonical5168 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA168 + difference 1 3) (sourceB168 + difference 3 1) sourceC168) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2022) := by
    have ha : (tripleCharges (sourceA168 + difference 1 3) (sourceB168 + difference 3 1) sourceC168) = raw5169 := by
      apply Matrix.ext; unfold tripleCharges sourceA168 sourceB168 sourceC168 difference raw5169; decide +kernel
    rw [ha]
    exact (canonical5169 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA168 + difference 1 4) (sourceB168 + difference 4 1) sourceC168) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2060) := by
    have ha : (tripleCharges (sourceA168 + difference 1 4) (sourceB168 + difference 4 1) sourceC168) = raw5170 := by
      apply Matrix.ext; unfold tripleCharges sourceA168 sourceB168 sourceC168 difference raw5170; decide +kernel
    rw [ha]
    exact (canonical5170 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA168 + difference 1 5) (sourceB168 + difference 5 1) sourceC168) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2740) := by
    have ha : (tripleCharges (sourceA168 + difference 1 5) (sourceB168 + difference 5 1) sourceC168) = raw5171 := by
      apply Matrix.ext; unfold tripleCharges sourceA168 sourceB168 sourceC168 difference raw5171; decide +kernel
    rw [ha]
    exact (canonical5171 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA168 + sourceB168) sourceC168) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA168 + sourceB168) sourceC168) = raw5167 := by
      apply Matrix.ext; unfold doubleCharges sourceA168 sourceB168 sourceC168 raw5167; decide +kernel
    rw [ha]
    exact (canonical5167 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA168 sourceB168 sourceC168
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm168, Integer.Sparse.eval]
  linarith only [hs]

def sourceA169 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB169 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceC169 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceForm169 : Integer.Sparse Master := [(Sum.inr 1043, 1), (Sum.inr 2022, 2), (Sum.inr 2109, 1), (Sum.inr 2264, 1), (Sum.inr 2268, 1), (Sum.inr 4084, -1)]

theorem sourceEq169 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm169 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA169 + difference 0 1) (sourceB169 + difference 1 0) sourceC169) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2264) := by
    have ha : (tripleCharges (sourceA169 + difference 0 1) (sourceB169 + difference 1 0) sourceC169) = raw5172 := by
      apply Matrix.ext; unfold tripleCharges sourceA169 sourceB169 sourceC169 difference raw5172; decide +kernel
    rw [ha]
    exact (canonical5172 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA169 + difference 1 1) (sourceB169 + difference 1 1) sourceC169) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2268) := by
    have ha : (tripleCharges (sourceA169 + difference 1 1) (sourceB169 + difference 1 1) sourceC169) = raw5161 := by
      apply Matrix.ext; unfold tripleCharges sourceA169 sourceB169 sourceC169 difference raw5161; decide +kernel
    rw [ha]
    exact (canonical5161 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA169 + difference 2 1) (sourceB169 + difference 1 2) sourceC169) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2022) := by
    have ha : (tripleCharges (sourceA169 + difference 2 1) (sourceB169 + difference 1 2) sourceC169) = raw5173 := by
      apply Matrix.ext; unfold tripleCharges sourceA169 sourceB169 sourceC169 difference raw5173; decide +kernel
    rw [ha]
    exact (canonical5173 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA169 + difference 3 1) (sourceB169 + difference 1 3) sourceC169) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2022) := by
    have ha : (tripleCharges (sourceA169 + difference 3 1) (sourceB169 + difference 1 3) sourceC169) = raw5174 := by
      apply Matrix.ext; unfold tripleCharges sourceA169 sourceB169 sourceC169 difference raw5174; decide +kernel
    rw [ha]
    exact (canonical5174 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA169 + difference 4 1) (sourceB169 + difference 1 4) sourceC169) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2109) := by
    have ha : (tripleCharges (sourceA169 + difference 4 1) (sourceB169 + difference 1 4) sourceC169) = raw5175 := by
      apply Matrix.ext; unfold tripleCharges sourceA169 sourceB169 sourceC169 difference raw5175; decide +kernel
    rw [ha]
    exact (canonical5175 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA169 + difference 5 1) (sourceB169 + difference 1 5) sourceC169) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1043) := by
    have ha : (tripleCharges (sourceA169 + difference 5 1) (sourceB169 + difference 1 5) sourceC169) = raw5176 := by
      apply Matrix.ext; unfold tripleCharges sourceA169 sourceB169 sourceC169 difference raw5176; decide +kernel
    rw [ha]
    exact (canonical5176 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA169 + sourceB169) sourceC169) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA169 + sourceB169) sourceC169) = raw5167 := by
      apply Matrix.ext; unfold doubleCharges sourceA169 sourceB169 sourceC169 raw5167; decide +kernel
    rw [ha]
    exact (canonical5167 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA169 sourceB169 sourceC169
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm169, Integer.Sparse.eval]
  linarith only [hs]

def sourceA170 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB170 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceC170 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceForm170 : Integer.Sparse Master := [(Sum.inr 1297, 1), (Sum.inr 2109, 3), (Sum.inr 2268, 1), (Sum.inr 2783, 1), (Sum.inr 4084, -1)]

theorem sourceEq170 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm170 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA170 + difference 4 0) (sourceB170 + difference 0 4) sourceC170) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1297) := by
    have ha : (tripleCharges (sourceA170 + difference 4 0) (sourceB170 + difference 0 4) sourceC170) = raw5165 := by
      apply Matrix.ext; unfold tripleCharges sourceA170 sourceB170 sourceC170 difference raw5165; decide +kernel
    rw [ha]
    exact (canonical5165 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA170 + difference 4 1) (sourceB170 + difference 1 4) sourceC170) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2109) := by
    have ha : (tripleCharges (sourceA170 + difference 4 1) (sourceB170 + difference 1 4) sourceC170) = raw5175 := by
      apply Matrix.ext; unfold tripleCharges sourceA170 sourceB170 sourceC170 difference raw5175; decide +kernel
    rw [ha]
    exact (canonical5175 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA170 + difference 4 2) (sourceB170 + difference 2 4) sourceC170) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2109) := by
    have ha : (tripleCharges (sourceA170 + difference 4 2) (sourceB170 + difference 2 4) sourceC170) = raw5177 := by
      apply Matrix.ext; unfold tripleCharges sourceA170 sourceB170 sourceC170 difference raw5177; decide +kernel
    rw [ha]
    exact (canonical5177 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA170 + difference 4 3) (sourceB170 + difference 3 4) sourceC170) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2109) := by
    have ha : (tripleCharges (sourceA170 + difference 4 3) (sourceB170 + difference 3 4) sourceC170) = raw5178 := by
      apply Matrix.ext; unfold tripleCharges sourceA170 sourceB170 sourceC170 difference raw5178; decide +kernel
    rw [ha]
    exact (canonical5178 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA170 + difference 4 4) (sourceB170 + difference 4 4) sourceC170) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2268) := by
    have ha : (tripleCharges (sourceA170 + difference 4 4) (sourceB170 + difference 4 4) sourceC170) = raw5161 := by
      apply Matrix.ext; unfold tripleCharges sourceA170 sourceB170 sourceC170 difference raw5161; decide +kernel
    rw [ha]
    exact (canonical5161 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA170 + difference 4 5) (sourceB170 + difference 5 4) sourceC170) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2783) := by
    have ha : (tripleCharges (sourceA170 + difference 4 5) (sourceB170 + difference 5 4) sourceC170) = raw5179 := by
      apply Matrix.ext; unfold tripleCharges sourceA170 sourceB170 sourceC170 difference raw5179; decide +kernel
    rw [ha]
    exact (canonical5179 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA170 + sourceB170) sourceC170) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA170 + sourceB170) sourceC170) = raw5167 := by
      apply Matrix.ext; unfold doubleCharges sourceA170 sourceB170 sourceC170 raw5167; decide +kernel
    rw [ha]
    exact (canonical5167 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA170 sourceB170 sourceC170
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm170, Integer.Sparse.eval]
  linarith only [hs]

def sourceA171 : Charge := ![1, 0, 0, 0, -1, 0]
def sourceB171 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceC171 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceForm171 : Integer.Sparse Master := [(Sum.inr 4085, 1), (Sum.inr 4496, 3), (Sum.inr 4501, 1), (Sum.inr 4510, 1), (Sum.inr 4832, 6), (Sum.inr 4837, 3), (Sum.inr 4845, 3), (Sum.inr 4890, 3), (Sum.inr 4897, 3), (Sum.inr 4899, 1), (Sum.inr 5261, 3), (Sum.inr 5296, 1), (Sum.inr 5312, 1)]

theorem sourceEq171 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm171 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA171 + difference 0 1) (sourceB171 + difference 1 0) sourceC171) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4890) := by
    have ha : (tripleCharges (sourceA171 + difference 0 1) (sourceB171 + difference 1 0) sourceC171) = raw5180 := by
      apply Matrix.ext; unfold tripleCharges sourceA171 sourceB171 sourceC171 difference raw5180; decide +kernel
    rw [ha]
    exact (canonical5180 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA171 + difference 0 2) (sourceB171 + difference 2 0) sourceC171) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4890) := by
    have ha : (tripleCharges (sourceA171 + difference 0 2) (sourceB171 + difference 2 0) sourceC171) = raw5181 := by
      apply Matrix.ext; unfold tripleCharges sourceA171 sourceB171 sourceC171 difference raw5181; decide +kernel
    rw [ha]
    exact (canonical5181 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA171 + difference 0 3) (sourceB171 + difference 3 0) sourceC171) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4890) := by
    have ha : (tripleCharges (sourceA171 + difference 0 3) (sourceB171 + difference 3 0) sourceC171) = raw5182 := by
      apply Matrix.ext; unfold tripleCharges sourceA171 sourceB171 sourceC171 difference raw5182; decide +kernel
    rw [ha]
    exact (canonical5182 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA171 + difference 0 4) (sourceB171 + difference 4 0) sourceC171) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4899) := by
    have ha : (tripleCharges (sourceA171 + difference 0 4) (sourceB171 + difference 4 0) sourceC171) = raw5183 := by
      apply Matrix.ext; unfold tripleCharges sourceA171 sourceB171 sourceC171 difference raw5183; decide +kernel
    rw [ha]
    exact (canonical5183 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA171 + difference 0 5) (sourceB171 + difference 5 0) sourceC171) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5296) := by
    have ha : (tripleCharges (sourceA171 + difference 0 5) (sourceB171 + difference 5 0) sourceC171) = raw4966 := by
      apply Matrix.ext; unfold tripleCharges sourceA171 sourceB171 sourceC171 difference raw4966; decide +kernel
    rw [ha]
    exact (canonical4966 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA171 + difference 1 0) (sourceB171 + difference 0 1) sourceC171) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4837) := by
    have ha : (tripleCharges (sourceA171 + difference 1 0) (sourceB171 + difference 0 1) sourceC171) = raw4989 := by
      apply Matrix.ext; unfold tripleCharges sourceA171 sourceB171 sourceC171 difference raw4989; decide +kernel
    rw [ha]
    exact (canonical4989 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA171 + difference 1 2) (sourceB171 + difference 2 1) sourceC171) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4832) := by
    have ha : (tripleCharges (sourceA171 + difference 1 2) (sourceB171 + difference 2 1) sourceC171) = raw4991 := by
      apply Matrix.ext; unfold tripleCharges sourceA171 sourceB171 sourceC171 difference raw4991; decide +kernel
    rw [ha]
    exact (canonical4991 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA171 + difference 1 3) (sourceB171 + difference 3 1) sourceC171) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4832) := by
    have ha : (tripleCharges (sourceA171 + difference 1 3) (sourceB171 + difference 3 1) sourceC171) = raw4992 := by
      apply Matrix.ext; unfold tripleCharges sourceA171 sourceB171 sourceC171 difference raw4992; decide +kernel
    rw [ha]
    exact (canonical4992 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA171 + difference 1 4) (sourceB171 + difference 4 1) sourceC171) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4845) := by
    have ha : (tripleCharges (sourceA171 + difference 1 4) (sourceB171 + difference 4 1) sourceC171) = raw4993 := by
      apply Matrix.ext; unfold tripleCharges sourceA171 sourceB171 sourceC171 difference raw4993; decide +kernel
    rw [ha]
    exact (canonical4993 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA171 + difference 1 5) (sourceB171 + difference 5 1) sourceC171) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5261) := by
    have ha : (tripleCharges (sourceA171 + difference 1 5) (sourceB171 + difference 5 1) sourceC171) = raw5091 := by
      apply Matrix.ext; unfold tripleCharges sourceA171 sourceB171 sourceC171 difference raw5091; decide +kernel
    rw [ha]
    exact (canonical5091 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA171 + difference 2 0) (sourceB171 + difference 0 2) sourceC171) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4837) := by
    have ha : (tripleCharges (sourceA171 + difference 2 0) (sourceB171 + difference 0 2) sourceC171) = raw5184 := by
      apply Matrix.ext; unfold tripleCharges sourceA171 sourceB171 sourceC171 difference raw5184; decide +kernel
    rw [ha]
    exact (canonical5184 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA171 + difference 2 1) (sourceB171 + difference 1 2) sourceC171) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4832) := by
    have ha : (tripleCharges (sourceA171 + difference 2 1) (sourceB171 + difference 1 2) sourceC171) = raw5185 := by
      apply Matrix.ext; unfold tripleCharges sourceA171 sourceB171 sourceC171 difference raw5185; decide +kernel
    rw [ha]
    exact (canonical5185 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA171 + difference 2 3) (sourceB171 + difference 3 2) sourceC171) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4832) := by
    have ha : (tripleCharges (sourceA171 + difference 2 3) (sourceB171 + difference 3 2) sourceC171) = raw5186 := by
      apply Matrix.ext; unfold tripleCharges sourceA171 sourceB171 sourceC171 difference raw5186; decide +kernel
    rw [ha]
    exact (canonical5186 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA171 + difference 2 4) (sourceB171 + difference 4 2) sourceC171) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4845) := by
    have ha : (tripleCharges (sourceA171 + difference 2 4) (sourceB171 + difference 4 2) sourceC171) = raw5187 := by
      apply Matrix.ext; unfold tripleCharges sourceA171 sourceB171 sourceC171 difference raw5187; decide +kernel
    rw [ha]
    exact (canonical5187 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA171 + difference 2 5) (sourceB171 + difference 5 2) sourceC171) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5261) := by
    have ha : (tripleCharges (sourceA171 + difference 2 5) (sourceB171 + difference 5 2) sourceC171) = raw4977 := by
      apply Matrix.ext; unfold tripleCharges sourceA171 sourceB171 sourceC171 difference raw4977; decide +kernel
    rw [ha]
    exact (canonical4977 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA171 + difference 3 0) (sourceB171 + difference 0 3) sourceC171) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4837) := by
    have ha : (tripleCharges (sourceA171 + difference 3 0) (sourceB171 + difference 0 3) sourceC171) = raw5188 := by
      apply Matrix.ext; unfold tripleCharges sourceA171 sourceB171 sourceC171 difference raw5188; decide +kernel
    rw [ha]
    exact (canonical5188 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA171 + difference 3 1) (sourceB171 + difference 1 3) sourceC171) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4832) := by
    have ha : (tripleCharges (sourceA171 + difference 3 1) (sourceB171 + difference 1 3) sourceC171) = raw5189 := by
      apply Matrix.ext; unfold tripleCharges sourceA171 sourceB171 sourceC171 difference raw5189; decide +kernel
    rw [ha]
    exact (canonical5189 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA171 + difference 3 2) (sourceB171 + difference 2 3) sourceC171) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4832) := by
    have ha : (tripleCharges (sourceA171 + difference 3 2) (sourceB171 + difference 2 3) sourceC171) = raw5190 := by
      apply Matrix.ext; unfold tripleCharges sourceA171 sourceB171 sourceC171 difference raw5190; decide +kernel
    rw [ha]
    exact (canonical5190 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA171 + difference 3 4) (sourceB171 + difference 4 3) sourceC171) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4845) := by
    have ha : (tripleCharges (sourceA171 + difference 3 4) (sourceB171 + difference 4 3) sourceC171) = raw5191 := by
      apply Matrix.ext; unfold tripleCharges sourceA171 sourceB171 sourceC171 difference raw5191; decide +kernel
    rw [ha]
    exact (canonical5191 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA171 + difference 3 5) (sourceB171 + difference 5 3) sourceC171) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5261) := by
    have ha : (tripleCharges (sourceA171 + difference 3 5) (sourceB171 + difference 5 3) sourceC171) = raw4982 := by
      apply Matrix.ext; unfold tripleCharges sourceA171 sourceB171 sourceC171 difference raw4982; decide +kernel
    rw [ha]
    exact (canonical4982 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA171 + difference 4 0) (sourceB171 + difference 0 4) sourceC171) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (tripleCharges (sourceA171 + difference 4 0) (sourceB171 + difference 0 4) sourceC171) = raw5097 := by
      apply Matrix.ext; unfold tripleCharges sourceA171 sourceB171 sourceC171 difference raw5097; decide +kernel
    rw [ha]
    exact (canonical5097 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA171 + difference 4 1) (sourceB171 + difference 1 4) sourceC171) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4897) := by
    have ha : (tripleCharges (sourceA171 + difference 4 1) (sourceB171 + difference 1 4) sourceC171) = raw5098 := by
      apply Matrix.ext; unfold tripleCharges sourceA171 sourceB171 sourceC171 difference raw5098; decide +kernel
    rw [ha]
    exact (canonical5098 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA171 + difference 4 2) (sourceB171 + difference 2 4) sourceC171) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4897) := by
    have ha : (tripleCharges (sourceA171 + difference 4 2) (sourceB171 + difference 2 4) sourceC171) = raw5099 := by
      apply Matrix.ext; unfold tripleCharges sourceA171 sourceB171 sourceC171 difference raw5099; decide +kernel
    rw [ha]
    exact (canonical5099 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA171 + difference 4 3) (sourceB171 + difference 3 4) sourceC171) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4897) := by
    have ha : (tripleCharges (sourceA171 + difference 4 3) (sourceB171 + difference 3 4) sourceC171) = raw5100 := by
      apply Matrix.ext; unfold tripleCharges sourceA171 sourceB171 sourceC171 difference raw5100; decide +kernel
    rw [ha]
    exact (canonical5100 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA171 + difference 4 5) (sourceB171 + difference 5 4) sourceC171) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5312) := by
    have ha : (tripleCharges (sourceA171 + difference 4 5) (sourceB171 + difference 5 4) sourceC171) = raw4356 := by
      apply Matrix.ext; unfold tripleCharges sourceA171 sourceB171 sourceC171 difference raw4356; decide +kernel
    rw [ha]
    exact (canonical4356 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA171 + difference 5 0) (sourceB171 + difference 0 5) sourceC171) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4501) := by
    have ha : (tripleCharges (sourceA171 + difference 5 0) (sourceB171 + difference 0 5) sourceC171) = raw5192 := by
      apply Matrix.ext; unfold tripleCharges sourceA171 sourceB171 sourceC171 difference raw5192; decide +kernel
    rw [ha]
    exact (canonical5192 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA171 + difference 5 1) (sourceB171 + difference 1 5) sourceC171) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4496) := by
    have ha : (tripleCharges (sourceA171 + difference 5 1) (sourceB171 + difference 1 5) sourceC171) = raw5193 := by
      apply Matrix.ext; unfold tripleCharges sourceA171 sourceB171 sourceC171 difference raw5193; decide +kernel
    rw [ha]
    exact (canonical5193 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA171 + difference 5 2) (sourceB171 + difference 2 5) sourceC171) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4496) := by
    have ha : (tripleCharges (sourceA171 + difference 5 2) (sourceB171 + difference 2 5) sourceC171) = raw5194 := by
      apply Matrix.ext; unfold tripleCharges sourceA171 sourceB171 sourceC171 difference raw5194; decide +kernel
    rw [ha]
    exact (canonical5194 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA171 + difference 5 3) (sourceB171 + difference 3 5) sourceC171) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4496) := by
    have ha : (tripleCharges (sourceA171 + difference 5 3) (sourceB171 + difference 3 5) sourceC171) = raw5195 := by
      apply Matrix.ext; unfold tripleCharges sourceA171 sourceB171 sourceC171 difference raw5195; decide +kernel
    rw [ha]
    exact (canonical5195 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA171 + difference 5 4) (sourceB171 + difference 4 5) sourceC171) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4510) := by
    have ha : (tripleCharges (sourceA171 + difference 5 4) (sourceB171 + difference 4 5) sourceC171) = raw5196 := by
      apply Matrix.ext; unfold tripleCharges sourceA171 sourceB171 sourceC171 difference raw5196; decide +kernel
    rw [ha]
    exact (canonical5196 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA171 sourceB171 sourceC171
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm171, Integer.Sparse.eval]
  linarith only [hs]

def sourceA172 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB172 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceC172 : Charge := ![0, 0, 0, 0, 0, 0]
def sourceForm172 : Integer.Sparse Master := [(Sum.inr 4070, 8), (Sum.inr 4072, 1), (Sum.inr 4081, 12), (Sum.inr 4084, 8), (Sum.inr 4094, 1)]

theorem sourceEq172 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm172 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA172 + difference 0 1) (sourceB172 + difference 1 0) sourceC172) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA172 + difference 0 1) (sourceB172 + difference 1 0) sourceC172) = raw2935 := by
      apply Matrix.ext; unfold tripleCharges sourceA172 sourceB172 sourceC172 difference raw2935; decide +kernel
    rw [ha]
    exact (canonical2935 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA172 + difference 0 2) (sourceB172 + difference 2 0) sourceC172) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA172 + difference 0 2) (sourceB172 + difference 2 0) sourceC172) = raw2936 := by
      apply Matrix.ext; unfold tripleCharges sourceA172 sourceB172 sourceC172 difference raw2936; decide +kernel
    rw [ha]
    exact (canonical2936 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA172 + difference 0 3) (sourceB172 + difference 3 0) sourceC172) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA172 + difference 0 3) (sourceB172 + difference 3 0) sourceC172) = raw2937 := by
      apply Matrix.ext; unfold tripleCharges sourceA172 sourceB172 sourceC172 difference raw2937; decide +kernel
    rw [ha]
    exact (canonical2937 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA172 + difference 0 4) (sourceB172 + difference 4 0) sourceC172) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA172 + difference 0 4) (sourceB172 + difference 4 0) sourceC172) = raw2938 := by
      apply Matrix.ext; unfold tripleCharges sourceA172 sourceB172 sourceC172 difference raw2938; decide +kernel
    rw [ha]
    exact (canonical2938 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA172 + difference 0 5) (sourceB172 + difference 5 0) sourceC172) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4094) := by
    have ha : (tripleCharges (sourceA172 + difference 0 5) (sourceB172 + difference 5 0) sourceC172) = raw3340 := by
      apply Matrix.ext; unfold tripleCharges sourceA172 sourceB172 sourceC172 difference raw3340; decide +kernel
    rw [ha]
    exact (canonical3340 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA172 + difference 1 0) (sourceB172 + difference 0 1) sourceC172) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (tripleCharges (sourceA172 + difference 1 0) (sourceB172 + difference 0 1) sourceC172) = raw5197 := by
      apply Matrix.ext; unfold tripleCharges sourceA172 sourceB172 sourceC172 difference raw5197; decide +kernel
    rw [ha]
    exact (canonical5197 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA172 + difference 1 2) (sourceB172 + difference 2 1) sourceC172) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (tripleCharges (sourceA172 + difference 1 2) (sourceB172 + difference 2 1) sourceC172) = raw5198 := by
      apply Matrix.ext; unfold tripleCharges sourceA172 sourceB172 sourceC172 difference raw5198; decide +kernel
    rw [ha]
    exact (canonical5198 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA172 + difference 1 3) (sourceB172 + difference 3 1) sourceC172) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (tripleCharges (sourceA172 + difference 1 3) (sourceB172 + difference 3 1) sourceC172) = raw5199 := by
      apply Matrix.ext; unfold tripleCharges sourceA172 sourceB172 sourceC172 difference raw5199; decide +kernel
    rw [ha]
    exact (canonical5199 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA172 + difference 1 4) (sourceB172 + difference 4 1) sourceC172) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (tripleCharges (sourceA172 + difference 1 4) (sourceB172 + difference 4 1) sourceC172) = raw5200 := by
      apply Matrix.ext; unfold tripleCharges sourceA172 sourceB172 sourceC172 difference raw5200; decide +kernel
    rw [ha]
    exact (canonical5200 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA172 + difference 1 5) (sourceB172 + difference 5 1) sourceC172) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA172 + difference 1 5) (sourceB172 + difference 5 1) sourceC172) = raw2914 := by
      apply Matrix.ext; unfold tripleCharges sourceA172 sourceB172 sourceC172 difference raw2914; decide +kernel
    rw [ha]
    exact (canonical2914 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA172 + difference 2 0) (sourceB172 + difference 0 2) sourceC172) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (tripleCharges (sourceA172 + difference 2 0) (sourceB172 + difference 0 2) sourceC172) = raw5201 := by
      apply Matrix.ext; unfold tripleCharges sourceA172 sourceB172 sourceC172 difference raw5201; decide +kernel
    rw [ha]
    exact (canonical5201 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA172 + difference 2 1) (sourceB172 + difference 1 2) sourceC172) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (tripleCharges (sourceA172 + difference 2 1) (sourceB172 + difference 1 2) sourceC172) = raw5202 := by
      apply Matrix.ext; unfold tripleCharges sourceA172 sourceB172 sourceC172 difference raw5202; decide +kernel
    rw [ha]
    exact (canonical5202 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA172 + difference 2 3) (sourceB172 + difference 3 2) sourceC172) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (tripleCharges (sourceA172 + difference 2 3) (sourceB172 + difference 3 2) sourceC172) = raw5203 := by
      apply Matrix.ext; unfold tripleCharges sourceA172 sourceB172 sourceC172 difference raw5203; decide +kernel
    rw [ha]
    exact (canonical5203 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA172 + difference 2 4) (sourceB172 + difference 4 2) sourceC172) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (tripleCharges (sourceA172 + difference 2 4) (sourceB172 + difference 4 2) sourceC172) = raw5204 := by
      apply Matrix.ext; unfold tripleCharges sourceA172 sourceB172 sourceC172 difference raw5204; decide +kernel
    rw [ha]
    exact (canonical5204 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA172 + difference 2 5) (sourceB172 + difference 5 2) sourceC172) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA172 + difference 2 5) (sourceB172 + difference 5 2) sourceC172) = raw2919 := by
      apply Matrix.ext; unfold tripleCharges sourceA172 sourceB172 sourceC172 difference raw2919; decide +kernel
    rw [ha]
    exact (canonical2919 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA172 + difference 3 0) (sourceB172 + difference 0 3) sourceC172) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (tripleCharges (sourceA172 + difference 3 0) (sourceB172 + difference 0 3) sourceC172) = raw5205 := by
      apply Matrix.ext; unfold tripleCharges sourceA172 sourceB172 sourceC172 difference raw5205; decide +kernel
    rw [ha]
    exact (canonical5205 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA172 + difference 3 1) (sourceB172 + difference 1 3) sourceC172) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (tripleCharges (sourceA172 + difference 3 1) (sourceB172 + difference 1 3) sourceC172) = raw5206 := by
      apply Matrix.ext; unfold tripleCharges sourceA172 sourceB172 sourceC172 difference raw5206; decide +kernel
    rw [ha]
    exact (canonical5206 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA172 + difference 3 2) (sourceB172 + difference 2 3) sourceC172) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (tripleCharges (sourceA172 + difference 3 2) (sourceB172 + difference 2 3) sourceC172) = raw5207 := by
      apply Matrix.ext; unfold tripleCharges sourceA172 sourceB172 sourceC172 difference raw5207; decide +kernel
    rw [ha]
    exact (canonical5207 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA172 + difference 3 4) (sourceB172 + difference 4 3) sourceC172) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (tripleCharges (sourceA172 + difference 3 4) (sourceB172 + difference 4 3) sourceC172) = raw5208 := by
      apply Matrix.ext; unfold tripleCharges sourceA172 sourceB172 sourceC172 difference raw5208; decide +kernel
    rw [ha]
    exact (canonical5208 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA172 + difference 3 5) (sourceB172 + difference 5 3) sourceC172) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA172 + difference 3 5) (sourceB172 + difference 5 3) sourceC172) = raw2924 := by
      apply Matrix.ext; unfold tripleCharges sourceA172 sourceB172 sourceC172 difference raw2924; decide +kernel
    rw [ha]
    exact (canonical2924 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA172 + difference 4 0) (sourceB172 + difference 0 4) sourceC172) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (tripleCharges (sourceA172 + difference 4 0) (sourceB172 + difference 0 4) sourceC172) = raw5209 := by
      apply Matrix.ext; unfold tripleCharges sourceA172 sourceB172 sourceC172 difference raw5209; decide +kernel
    rw [ha]
    exact (canonical5209 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA172 + difference 4 1) (sourceB172 + difference 1 4) sourceC172) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (tripleCharges (sourceA172 + difference 4 1) (sourceB172 + difference 1 4) sourceC172) = raw5210 := by
      apply Matrix.ext; unfold tripleCharges sourceA172 sourceB172 sourceC172 difference raw5210; decide +kernel
    rw [ha]
    exact (canonical5210 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA172 + difference 4 2) (sourceB172 + difference 2 4) sourceC172) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (tripleCharges (sourceA172 + difference 4 2) (sourceB172 + difference 2 4) sourceC172) = raw5211 := by
      apply Matrix.ext; unfold tripleCharges sourceA172 sourceB172 sourceC172 difference raw5211; decide +kernel
    rw [ha]
    exact (canonical5211 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA172 + difference 4 3) (sourceB172 + difference 3 4) sourceC172) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (tripleCharges (sourceA172 + difference 4 3) (sourceB172 + difference 3 4) sourceC172) = raw5212 := by
      apply Matrix.ext; unfold tripleCharges sourceA172 sourceB172 sourceC172 difference raw5212; decide +kernel
    rw [ha]
    exact (canonical5212 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA172 + difference 4 5) (sourceB172 + difference 5 4) sourceC172) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA172 + difference 4 5) (sourceB172 + difference 5 4) sourceC172) = raw2929 := by
      apply Matrix.ext; unfold tripleCharges sourceA172 sourceB172 sourceC172 difference raw2929; decide +kernel
    rw [ha]
    exact (canonical2929 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA172 + difference 5 0) (sourceB172 + difference 0 5) sourceC172) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4072) := by
    have ha : (tripleCharges (sourceA172 + difference 5 0) (sourceB172 + difference 0 5) sourceC172) = raw5213 := by
      apply Matrix.ext; unfold tripleCharges sourceA172 sourceB172 sourceC172 difference raw5213; decide +kernel
    rw [ha]
    exact (canonical5213 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA172 + difference 5 1) (sourceB172 + difference 1 5) sourceC172) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (tripleCharges (sourceA172 + difference 5 1) (sourceB172 + difference 1 5) sourceC172) = raw5214 := by
      apply Matrix.ext; unfold tripleCharges sourceA172 sourceB172 sourceC172 difference raw5214; decide +kernel
    rw [ha]
    exact (canonical5214 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA172 + difference 5 2) (sourceB172 + difference 2 5) sourceC172) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (tripleCharges (sourceA172 + difference 5 2) (sourceB172 + difference 2 5) sourceC172) = raw5215 := by
      apply Matrix.ext; unfold tripleCharges sourceA172 sourceB172 sourceC172 difference raw5215; decide +kernel
    rw [ha]
    exact (canonical5215 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA172 + difference 5 3) (sourceB172 + difference 3 5) sourceC172) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (tripleCharges (sourceA172 + difference 5 3) (sourceB172 + difference 3 5) sourceC172) = raw5216 := by
      apply Matrix.ext; unfold tripleCharges sourceA172 sourceB172 sourceC172 difference raw5216; decide +kernel
    rw [ha]
    exact (canonical5216 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA172 + difference 5 4) (sourceB172 + difference 4 5) sourceC172) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (tripleCharges (sourceA172 + difference 5 4) (sourceB172 + difference 4 5) sourceC172) = raw5217 := by
      apply Matrix.ext; unfold tripleCharges sourceA172 sourceB172 sourceC172 difference raw5217; decide +kernel
    rw [ha]
    exact (canonical5217 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA172 sourceB172 sourceC172
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm172, Integer.Sparse.eval]
  linarith only [hs]

def sourceA173 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB173 : Charge := ![0, 0, 1, 2, -1, -2]
def sourceC173 : Charge := ![3, 0, -1, -2, 0, 0]
def sourceForm173 : Integer.Sparse Master := [(Sum.inr 4446, 1), (Sum.inr 4447, 1), (Sum.inr 4448, 1), (Sum.inr 4459, 1), (Sum.inr 4475, 1), (Sum.inr 4734, 1), (Sum.inr 4743, 1), (Sum.inr 4748, 1), (Sum.inr 4796, 1), (Sum.inr 4803, 1), (Sum.inr 4816, 1), (Sum.inr 4857, 1), (Sum.inr 4858, 1), (Sum.inr 4867, 1), (Sum.inr 4876, 1), (Sum.inr 4877, 1), (Sum.inr 4880, 1), (Sum.inr 4885, 1), (Sum.inr 4888, 1), (Sum.inr 4889, 1), (Sum.inr 4891, 2), (Sum.inr 4892, 1), (Sum.inr 4896, 1), (Sum.inr 4898, 1), (Sum.inr 5103, 1), (Sum.inr 5254, 1), (Sum.inr 5284, 1), (Sum.inr 5287, 1), (Sum.inr 5302, 1)]

theorem sourceEq173 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm173 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA173 + difference 0 1) (sourceB173 + difference 1 0) sourceC173) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5254) := by
    have ha : (tripleCharges (sourceA173 + difference 0 1) (sourceB173 + difference 1 0) sourceC173) = raw5218 := by
      apply Matrix.ext; unfold tripleCharges sourceA173 sourceB173 sourceC173 difference raw5218; decide +kernel
    rw [ha]
    exact (canonical5218 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA173 + difference 0 2) (sourceB173 + difference 2 0) sourceC173) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5287) := by
    have ha : (tripleCharges (sourceA173 + difference 0 2) (sourceB173 + difference 2 0) sourceC173) = raw5219 := by
      apply Matrix.ext; unfold tripleCharges sourceA173 sourceB173 sourceC173 difference raw5219; decide +kernel
    rw [ha]
    exact (canonical5219 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA173 + difference 0 3) (sourceB173 + difference 3 0) sourceC173) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5103) := by
    have ha : (tripleCharges (sourceA173 + difference 0 3) (sourceB173 + difference 3 0) sourceC173) = raw5220 := by
      apply Matrix.ext; unfold tripleCharges sourceA173 sourceB173 sourceC173 difference raw5220; decide +kernel
    rw [ha]
    exact (canonical5220 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA173 + difference 0 4) (sourceB173 + difference 4 0) sourceC173) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA173 + difference 0 4) (sourceB173 + difference 4 0) sourceC173) = raw5221 := by
      apply Matrix.ext; unfold tripleCharges sourceA173 sourceB173 sourceC173 difference raw5221; decide +kernel
    rw [ha]
    exact (canonical5221 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA173 + difference 0 5) (sourceB173 + difference 5 0) sourceC173) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA173 + difference 0 5) (sourceB173 + difference 5 0) sourceC173) = raw5222 := by
      apply Matrix.ext; unfold tripleCharges sourceA173 sourceB173 sourceC173 difference raw5222; decide +kernel
    rw [ha]
    exact (canonical5222 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA173 + difference 1 0) (sourceB173 + difference 0 1) sourceC173) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4446) := by
    have ha : (tripleCharges (sourceA173 + difference 1 0) (sourceB173 + difference 0 1) sourceC173) = raw5223 := by
      apply Matrix.ext; unfold tripleCharges sourceA173 sourceB173 sourceC173 difference raw5223; decide +kernel
    rw [ha]
    exact (canonical5223 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA173 + difference 1 2) (sourceB173 + difference 2 1) sourceC173) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4857) := by
    have ha : (tripleCharges (sourceA173 + difference 1 2) (sourceB173 + difference 2 1) sourceC173) = raw5224 := by
      apply Matrix.ext; unfold tripleCharges sourceA173 sourceB173 sourceC173 difference raw5224; decide +kernel
    rw [ha]
    exact (canonical5224 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA173 + difference 1 3) (sourceB173 + difference 3 1) sourceC173) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4876) := by
    have ha : (tripleCharges (sourceA173 + difference 1 3) (sourceB173 + difference 3 1) sourceC173) = raw5225 := by
      apply Matrix.ext; unfold tripleCharges sourceA173 sourceB173 sourceC173 difference raw5225; decide +kernel
    rw [ha]
    exact (canonical5225 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA173 + difference 1 4) (sourceB173 + difference 4 1) sourceC173) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4891) := by
    have ha : (tripleCharges (sourceA173 + difference 1 4) (sourceB173 + difference 4 1) sourceC173) = raw5226 := by
      apply Matrix.ext; unfold tripleCharges sourceA173 sourceB173 sourceC173 difference raw5226; decide +kernel
    rw [ha]
    exact (canonical5226 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA173 + difference 1 5) (sourceB173 + difference 5 1) sourceC173) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4885) := by
    have ha : (tripleCharges (sourceA173 + difference 1 5) (sourceB173 + difference 5 1) sourceC173) = raw5227 := by
      apply Matrix.ext; unfold tripleCharges sourceA173 sourceB173 sourceC173 difference raw5227; decide +kernel
    rw [ha]
    exact (canonical5227 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA173 + difference 2 0) (sourceB173 + difference 0 2) sourceC173) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4475) := by
    have ha : (tripleCharges (sourceA173 + difference 2 0) (sourceB173 + difference 0 2) sourceC173) = raw5228 := by
      apply Matrix.ext; unfold tripleCharges sourceA173 sourceB173 sourceC173 difference raw5228; decide +kernel
    rw [ha]
    exact (canonical5228 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA173 + difference 2 1) (sourceB173 + difference 1 2) sourceC173) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4816) := by
    have ha : (tripleCharges (sourceA173 + difference 2 1) (sourceB173 + difference 1 2) sourceC173) = raw5229 := by
      apply Matrix.ext; unfold tripleCharges sourceA173 sourceB173 sourceC173 difference raw5229; decide +kernel
    rw [ha]
    exact (canonical5229 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA173 + difference 2 3) (sourceB173 + difference 3 2) sourceC173) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4880) := by
    have ha : (tripleCharges (sourceA173 + difference 2 3) (sourceB173 + difference 3 2) sourceC173) = raw5230 := by
      apply Matrix.ext; unfold tripleCharges sourceA173 sourceB173 sourceC173 difference raw5230; decide +kernel
    rw [ha]
    exact (canonical5230 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA173 + difference 2 4) (sourceB173 + difference 4 2) sourceC173) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4898) := by
    have ha : (tripleCharges (sourceA173 + difference 2 4) (sourceB173 + difference 4 2) sourceC173) = raw5231 := by
      apply Matrix.ext; unfold tripleCharges sourceA173 sourceB173 sourceC173 difference raw5231; decide +kernel
    rw [ha]
    exact (canonical5231 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA173 + difference 2 5) (sourceB173 + difference 5 2) sourceC173) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA173 + difference 2 5) (sourceB173 + difference 5 2) sourceC173) = raw5232 := by
      apply Matrix.ext; unfold tripleCharges sourceA173 sourceB173 sourceC173 difference raw5232; decide +kernel
    rw [ha]
    exact (canonical5232 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA173 + difference 3 0) (sourceB173 + difference 0 3) sourceC173) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4459) := by
    have ha : (tripleCharges (sourceA173 + difference 3 0) (sourceB173 + difference 0 3) sourceC173) = raw5233 := by
      apply Matrix.ext; unfold tripleCharges sourceA173 sourceB173 sourceC173 difference raw5233; decide +kernel
    rw [ha]
    exact (canonical5233 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA173 + difference 3 1) (sourceB173 + difference 1 3) sourceC173) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4803) := by
    have ha : (tripleCharges (sourceA173 + difference 3 1) (sourceB173 + difference 1 3) sourceC173) = raw5234 := by
      apply Matrix.ext; unfold tripleCharges sourceA173 sourceB173 sourceC173 difference raw5234; decide +kernel
    rw [ha]
    exact (canonical5234 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA173 + difference 3 2) (sourceB173 + difference 2 3) sourceC173) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4867) := by
    have ha : (tripleCharges (sourceA173 + difference 3 2) (sourceB173 + difference 2 3) sourceC173) = raw5235 := by
      apply Matrix.ext; unfold tripleCharges sourceA173 sourceB173 sourceC173 difference raw5235; decide +kernel
    rw [ha]
    exact (canonical5235 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA173 + difference 3 4) (sourceB173 + difference 4 3) sourceC173) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4896) := by
    have ha : (tripleCharges (sourceA173 + difference 3 4) (sourceB173 + difference 4 3) sourceC173) = raw5236 := by
      apply Matrix.ext; unfold tripleCharges sourceA173 sourceB173 sourceC173 difference raw5236; decide +kernel
    rw [ha]
    exact (canonical5236 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA173 + difference 3 5) (sourceB173 + difference 5 3) sourceC173) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA173 + difference 3 5) (sourceB173 + difference 5 3) sourceC173) = raw5237 := by
      apply Matrix.ext; unfold tripleCharges sourceA173 sourceB173 sourceC173 difference raw5237; decide +kernel
    rw [ha]
    exact (canonical5237 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA173 + difference 4 0) (sourceB173 + difference 0 4) sourceC173) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4448) := by
    have ha : (tripleCharges (sourceA173 + difference 4 0) (sourceB173 + difference 0 4) sourceC173) = raw5238 := by
      apply Matrix.ext; unfold tripleCharges sourceA173 sourceB173 sourceC173 difference raw5238; decide +kernel
    rw [ha]
    exact (canonical5238 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA173 + difference 4 1) (sourceB173 + difference 1 4) sourceC173) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4796) := by
    have ha : (tripleCharges (sourceA173 + difference 4 1) (sourceB173 + difference 1 4) sourceC173) = raw5239 := by
      apply Matrix.ext; unfold tripleCharges sourceA173 sourceB173 sourceC173 difference raw5239; decide +kernel
    rw [ha]
    exact (canonical5239 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA173 + difference 4 2) (sourceB173 + difference 2 4) sourceC173) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4858) := by
    have ha : (tripleCharges (sourceA173 + difference 4 2) (sourceB173 + difference 2 4) sourceC173) = raw5240 := by
      apply Matrix.ext; unfold tripleCharges sourceA173 sourceB173 sourceC173 difference raw5240; decide +kernel
    rw [ha]
    exact (canonical5240 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA173 + difference 4 3) (sourceB173 + difference 3 4) sourceC173) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4877) := by
    have ha : (tripleCharges (sourceA173 + difference 4 3) (sourceB173 + difference 3 4) sourceC173) = raw5241 := by
      apply Matrix.ext; unfold tripleCharges sourceA173 sourceB173 sourceC173 difference raw5241; decide +kernel
    rw [ha]
    exact (canonical5241 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA173 + difference 4 5) (sourceB173 + difference 5 4) sourceC173) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4891) := by
    have ha : (tripleCharges (sourceA173 + difference 4 5) (sourceB173 + difference 5 4) sourceC173) = raw5242 := by
      apply Matrix.ext; unfold tripleCharges sourceA173 sourceB173 sourceC173 difference raw5242; decide +kernel
    rw [ha]
    exact (canonical5242 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA173 + difference 5 0) (sourceB173 + difference 0 5) sourceC173) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4447) := by
    have ha : (tripleCharges (sourceA173 + difference 5 0) (sourceB173 + difference 0 5) sourceC173) = raw5243 := by
      apply Matrix.ext; unfold tripleCharges sourceA173 sourceB173 sourceC173 difference raw5243; decide +kernel
    rw [ha]
    exact (canonical5243 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA173 + difference 5 1) (sourceB173 + difference 1 5) sourceC173) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4734) := by
    have ha : (tripleCharges (sourceA173 + difference 5 1) (sourceB173 + difference 1 5) sourceC173) = raw5244 := by
      apply Matrix.ext; unfold tripleCharges sourceA173 sourceB173 sourceC173 difference raw5244; decide +kernel
    rw [ha]
    exact (canonical5244 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA173 + difference 5 2) (sourceB173 + difference 2 5) sourceC173) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4748) := by
    have ha : (tripleCharges (sourceA173 + difference 5 2) (sourceB173 + difference 2 5) sourceC173) = raw5245 := by
      apply Matrix.ext; unfold tripleCharges sourceA173 sourceB173 sourceC173 difference raw5245; decide +kernel
    rw [ha]
    exact (canonical5245 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA173 + difference 5 3) (sourceB173 + difference 3 5) sourceC173) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4743) := by
    have ha : (tripleCharges (sourceA173 + difference 5 3) (sourceB173 + difference 3 5) sourceC173) = raw5246 := by
      apply Matrix.ext; unfold tripleCharges sourceA173 sourceB173 sourceC173 difference raw5246; decide +kernel
    rw [ha]
    exact (canonical5246 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA173 + difference 5 4) (sourceB173 + difference 4 5) sourceC173) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4892) := by
    have ha : (tripleCharges (sourceA173 + difference 5 4) (sourceB173 + difference 4 5) sourceC173) = raw5247 := by
      apply Matrix.ext; unfold tripleCharges sourceA173 sourceB173 sourceC173 difference raw5247; decide +kernel
    rw [ha]
    exact (canonical5247 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA173 sourceB173 sourceC173
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm173, Integer.Sparse.eval]
  linarith only [hs]

def sourceA174 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB174 : Charge := ![0, 0, 1, 2, -1, -2]
def sourceC174 : Charge := ![3, 0, -1, -2, 0, 0]
def sourceForm174 : Integer.Sparse Master := [(Sum.inr 1354, 1), (Sum.inr 1355, 1), (Sum.inr 1356, 1), (Sum.inr 1367, 1), (Sum.inr 1406, 1), (Sum.inr 1903, 1), (Sum.inr 1916, 1), (Sum.inr 1927, 1), (Sum.inr 2255, 1), (Sum.inr 3016, 1), (Sum.inr 3024, 1), (Sum.inr 3025, 1), (Sum.inr 3054, 1), (Sum.inr 3077, 1), (Sum.inr 3146, 1), (Sum.inr 3147, 1), (Sum.inr 3156, 1), (Sum.inr 3165, 1), (Sum.inr 3166, 1), (Sum.inr 3180, 1), (Sum.inr 3193, 1), (Sum.inr 3196, 1), (Sum.inr 3202, 1), (Sum.inr 3221, 1), (Sum.inr 3222, 2), (Sum.inr 3223, 1), (Sum.inr 3224, 1), (Sum.inr 3225, 1), (Sum.inr 3227, 1)]

theorem sourceEq174 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm174 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA174 + difference 0 1) (sourceB174 + difference 1 0) sourceC174) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3016) := by
    have ha : (tripleCharges (sourceA174 + difference 0 1) (sourceB174 + difference 1 0) sourceC174) = raw5248 := by
      apply Matrix.ext; unfold tripleCharges sourceA174 sourceB174 sourceC174 difference raw5248; decide +kernel
    rw [ha]
    exact (canonical5248 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA174 + difference 0 2) (sourceB174 + difference 2 0) sourceC174) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3025) := by
    have ha : (tripleCharges (sourceA174 + difference 0 2) (sourceB174 + difference 2 0) sourceC174) = raw5249 := by
      apply Matrix.ext; unfold tripleCharges sourceA174 sourceB174 sourceC174 difference raw5249; decide +kernel
    rw [ha]
    exact (canonical5249 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA174 + difference 0 3) (sourceB174 + difference 3 0) sourceC174) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3024) := by
    have ha : (tripleCharges (sourceA174 + difference 0 3) (sourceB174 + difference 3 0) sourceC174) = raw5250 := by
      apply Matrix.ext; unfold tripleCharges sourceA174 sourceB174 sourceC174 difference raw5250; decide +kernel
    rw [ha]
    exact (canonical5250 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA174 + difference 0 4) (sourceB174 + difference 4 0) sourceC174) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3054) := by
    have ha : (tripleCharges (sourceA174 + difference 0 4) (sourceB174 + difference 4 0) sourceC174) = raw5251 := by
      apply Matrix.ext; unfold tripleCharges sourceA174 sourceB174 sourceC174 difference raw5251; decide +kernel
    rw [ha]
    exact (canonical5251 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA174 + difference 0 5) (sourceB174 + difference 5 0) sourceC174) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3077) := by
    have ha : (tripleCharges (sourceA174 + difference 0 5) (sourceB174 + difference 5 0) sourceC174) = raw5252 := by
      apply Matrix.ext; unfold tripleCharges sourceA174 sourceB174 sourceC174 difference raw5252; decide +kernel
    rw [ha]
    exact (canonical5252 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA174 + difference 1 0) (sourceB174 + difference 0 1) sourceC174) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1354) := by
    have ha : (tripleCharges (sourceA174 + difference 1 0) (sourceB174 + difference 0 1) sourceC174) = raw5253 := by
      apply Matrix.ext; unfold tripleCharges sourceA174 sourceB174 sourceC174 difference raw5253; decide +kernel
    rw [ha]
    exact (canonical5253 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA174 + difference 1 2) (sourceB174 + difference 2 1) sourceC174) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3165) := by
    have ha : (tripleCharges (sourceA174 + difference 1 2) (sourceB174 + difference 2 1) sourceC174) = raw5254 := by
      apply Matrix.ext; unfold tripleCharges sourceA174 sourceB174 sourceC174 difference raw5254; decide +kernel
    rw [ha]
    exact (canonical5254 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA174 + difference 1 3) (sourceB174 + difference 3 1) sourceC174) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3146) := by
    have ha : (tripleCharges (sourceA174 + difference 1 3) (sourceB174 + difference 3 1) sourceC174) = raw5255 := by
      apply Matrix.ext; unfold tripleCharges sourceA174 sourceB174 sourceC174 difference raw5255; decide +kernel
    rw [ha]
    exact (canonical5255 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA174 + difference 1 4) (sourceB174 + difference 4 1) sourceC174) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3222) := by
    have ha : (tripleCharges (sourceA174 + difference 1 4) (sourceB174 + difference 4 1) sourceC174) = raw5256 := by
      apply Matrix.ext; unfold tripleCharges sourceA174 sourceB174 sourceC174 difference raw5256; decide +kernel
    rw [ha]
    exact (canonical5256 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA174 + difference 1 5) (sourceB174 + difference 5 1) sourceC174) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3221) := by
    have ha : (tripleCharges (sourceA174 + difference 1 5) (sourceB174 + difference 5 1) sourceC174) = raw5257 := by
      apply Matrix.ext; unfold tripleCharges sourceA174 sourceB174 sourceC174 difference raw5257; decide +kernel
    rw [ha]
    exact (canonical5257 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA174 + difference 2 0) (sourceB174 + difference 0 2) sourceC174) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1367) := by
    have ha : (tripleCharges (sourceA174 + difference 2 0) (sourceB174 + difference 0 2) sourceC174) = raw5258 := by
      apply Matrix.ext; unfold tripleCharges sourceA174 sourceB174 sourceC174 difference raw5258; decide +kernel
    rw [ha]
    exact (canonical5258 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA174 + difference 2 1) (sourceB174 + difference 1 2) sourceC174) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3196) := by
    have ha : (tripleCharges (sourceA174 + difference 2 1) (sourceB174 + difference 1 2) sourceC174) = raw5259 := by
      apply Matrix.ext; unfold tripleCharges sourceA174 sourceB174 sourceC174 difference raw5259; decide +kernel
    rw [ha]
    exact (canonical5259 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA174 + difference 2 3) (sourceB174 + difference 3 2) sourceC174) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3156) := by
    have ha : (tripleCharges (sourceA174 + difference 2 3) (sourceB174 + difference 3 2) sourceC174) = raw5260 := by
      apply Matrix.ext; unfold tripleCharges sourceA174 sourceB174 sourceC174 difference raw5260; decide +kernel
    rw [ha]
    exact (canonical5260 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA174 + difference 2 4) (sourceB174 + difference 4 2) sourceC174) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3224) := by
    have ha : (tripleCharges (sourceA174 + difference 2 4) (sourceB174 + difference 4 2) sourceC174) = raw5261 := by
      apply Matrix.ext; unfold tripleCharges sourceA174 sourceB174 sourceC174 difference raw5261; decide +kernel
    rw [ha]
    exact (canonical5261 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA174 + difference 2 5) (sourceB174 + difference 5 2) sourceC174) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3223) := by
    have ha : (tripleCharges (sourceA174 + difference 2 5) (sourceB174 + difference 5 2) sourceC174) = raw5262 := by
      apply Matrix.ext; unfold tripleCharges sourceA174 sourceB174 sourceC174 difference raw5262; decide +kernel
    rw [ha]
    exact (canonical5262 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA174 + difference 3 0) (sourceB174 + difference 0 3) sourceC174) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1406) := by
    have ha : (tripleCharges (sourceA174 + difference 3 0) (sourceB174 + difference 0 3) sourceC174) = raw5263 := by
      apply Matrix.ext; unfold tripleCharges sourceA174 sourceB174 sourceC174 difference raw5263; decide +kernel
    rw [ha]
    exact (canonical5263 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA174 + difference 3 1) (sourceB174 + difference 1 3) sourceC174) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3202) := by
    have ha : (tripleCharges (sourceA174 + difference 3 1) (sourceB174 + difference 1 3) sourceC174) = raw5264 := by
      apply Matrix.ext; unfold tripleCharges sourceA174 sourceB174 sourceC174 difference raw5264; decide +kernel
    rw [ha]
    exact (canonical5264 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA174 + difference 3 2) (sourceB174 + difference 2 3) sourceC174) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3180) := by
    have ha : (tripleCharges (sourceA174 + difference 3 2) (sourceB174 + difference 2 3) sourceC174) = raw5265 := by
      apply Matrix.ext; unfold tripleCharges sourceA174 sourceB174 sourceC174 difference raw5265; decide +kernel
    rw [ha]
    exact (canonical5265 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA174 + difference 3 4) (sourceB174 + difference 4 3) sourceC174) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3225) := by
    have ha : (tripleCharges (sourceA174 + difference 3 4) (sourceB174 + difference 4 3) sourceC174) = raw5266 := by
      apply Matrix.ext; unfold tripleCharges sourceA174 sourceB174 sourceC174 difference raw5266; decide +kernel
    rw [ha]
    exact (canonical5266 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA174 + difference 3 5) (sourceB174 + difference 5 3) sourceC174) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3227) := by
    have ha : (tripleCharges (sourceA174 + difference 3 5) (sourceB174 + difference 5 3) sourceC174) = raw5267 := by
      apply Matrix.ext; unfold tripleCharges sourceA174 sourceB174 sourceC174 difference raw5267; decide +kernel
    rw [ha]
    exact (canonical5267 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA174 + difference 4 0) (sourceB174 + difference 0 4) sourceC174) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1356) := by
    have ha : (tripleCharges (sourceA174 + difference 4 0) (sourceB174 + difference 0 4) sourceC174) = raw5268 := by
      apply Matrix.ext; unfold tripleCharges sourceA174 sourceB174 sourceC174 difference raw5268; decide +kernel
    rw [ha]
    exact (canonical5268 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA174 + difference 4 1) (sourceB174 + difference 1 4) sourceC174) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3193) := by
    have ha : (tripleCharges (sourceA174 + difference 4 1) (sourceB174 + difference 1 4) sourceC174) = raw5269 := by
      apply Matrix.ext; unfold tripleCharges sourceA174 sourceB174 sourceC174 difference raw5269; decide +kernel
    rw [ha]
    exact (canonical5269 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA174 + difference 4 2) (sourceB174 + difference 2 4) sourceC174) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3166) := by
    have ha : (tripleCharges (sourceA174 + difference 4 2) (sourceB174 + difference 2 4) sourceC174) = raw5270 := by
      apply Matrix.ext; unfold tripleCharges sourceA174 sourceB174 sourceC174 difference raw5270; decide +kernel
    rw [ha]
    exact (canonical5270 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA174 + difference 4 3) (sourceB174 + difference 3 4) sourceC174) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3147) := by
    have ha : (tripleCharges (sourceA174 + difference 4 3) (sourceB174 + difference 3 4) sourceC174) = raw5271 := by
      apply Matrix.ext; unfold tripleCharges sourceA174 sourceB174 sourceC174 difference raw5271; decide +kernel
    rw [ha]
    exact (canonical5271 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA174 + difference 4 5) (sourceB174 + difference 5 4) sourceC174) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3222) := by
    have ha : (tripleCharges (sourceA174 + difference 4 5) (sourceB174 + difference 5 4) sourceC174) = raw5272 := by
      apply Matrix.ext; unfold tripleCharges sourceA174 sourceB174 sourceC174 difference raw5272; decide +kernel
    rw [ha]
    exact (canonical5272 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA174 + difference 5 0) (sourceB174 + difference 0 5) sourceC174) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1355) := by
    have ha : (tripleCharges (sourceA174 + difference 5 0) (sourceB174 + difference 0 5) sourceC174) = raw5273 := by
      apply Matrix.ext; unfold tripleCharges sourceA174 sourceB174 sourceC174 difference raw5273; decide +kernel
    rw [ha]
    exact (canonical5273 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA174 + difference 5 1) (sourceB174 + difference 1 5) sourceC174) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1903) := by
    have ha : (tripleCharges (sourceA174 + difference 5 1) (sourceB174 + difference 1 5) sourceC174) = raw5274 := by
      apply Matrix.ext; unfold tripleCharges sourceA174 sourceB174 sourceC174 difference raw5274; decide +kernel
    rw [ha]
    exact (canonical5274 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA174 + difference 5 2) (sourceB174 + difference 2 5) sourceC174) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1927) := by
    have ha : (tripleCharges (sourceA174 + difference 5 2) (sourceB174 + difference 2 5) sourceC174) = raw5275 := by
      apply Matrix.ext; unfold tripleCharges sourceA174 sourceB174 sourceC174 difference raw5275; decide +kernel
    rw [ha]
    exact (canonical5275 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA174 + difference 5 3) (sourceB174 + difference 3 5) sourceC174) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1916) := by
    have ha : (tripleCharges (sourceA174 + difference 5 3) (sourceB174 + difference 3 5) sourceC174) = raw5276 := by
      apply Matrix.ext; unfold tripleCharges sourceA174 sourceB174 sourceC174 difference raw5276; decide +kernel
    rw [ha]
    exact (canonical5276 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA174 + difference 5 4) (sourceB174 + difference 4 5) sourceC174) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2255) := by
    have ha : (tripleCharges (sourceA174 + difference 5 4) (sourceB174 + difference 4 5) sourceC174) = raw5277 := by
      apply Matrix.ext; unfold tripleCharges sourceA174 sourceB174 sourceC174 difference raw5277; decide +kernel
    rw [ha]
    exact (canonical5277 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA174 sourceB174 sourceC174
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm174, Integer.Sparse.eval]
  linarith only [hs]

def sourceA175 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB175 : Charge := ![0, 0, 1, 2, -1, -2]
def sourceC175 : Charge := ![3, 0, -1, -2, 0, 0]
def sourceForm175 : Integer.Sparse Master := [(Sum.inr 1701, 1), (Sum.inr 1714, 1), (Sum.inr 1715, 1), (Sum.inr 1718, 1), (Sum.inr 1732, 1), (Sum.inr 1931, 1), (Sum.inr 1932, 1), (Sum.inr 1934, 1), (Sum.inr 2195, 1), (Sum.inr 2196, 1), (Sum.inr 2209, 1), (Sum.inr 2233, 1), (Sum.inr 2236, 1), (Sum.inr 2237, 1), (Sum.inr 2244, 1), (Sum.inr 2245, 1), (Sum.inr 2251, 1), (Sum.inr 2253, 2), (Sum.inr 2254, 1), (Sum.inr 2270, 1), (Sum.inr 2271, 1), (Sum.inr 2278, 1), (Sum.inr 2279, 1), (Sum.inr 2284, 1), (Sum.inr 2714, 1), (Sum.inr 2753, 1), (Sum.inr 2758, 1), (Sum.inr 2759, 1), (Sum.inr 2776, 1)]

theorem sourceEq175 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm175 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA175 + difference 0 1) (sourceB175 + difference 1 0) sourceC175) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2714) := by
    have ha : (tripleCharges (sourceA175 + difference 0 1) (sourceB175 + difference 1 0) sourceC175) = raw5278 := by
      apply Matrix.ext; unfold tripleCharges sourceA175 sourceB175 sourceC175 difference raw5278; decide +kernel
    rw [ha]
    exact (canonical5278 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA175 + difference 0 2) (sourceB175 + difference 2 0) sourceC175) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2758) := by
    have ha : (tripleCharges (sourceA175 + difference 0 2) (sourceB175 + difference 2 0) sourceC175) = raw5279 := by
      apply Matrix.ext; unfold tripleCharges sourceA175 sourceB175 sourceC175 difference raw5279; decide +kernel
    rw [ha]
    exact (canonical5279 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA175 + difference 0 3) (sourceB175 + difference 3 0) sourceC175) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2759) := by
    have ha : (tripleCharges (sourceA175 + difference 0 3) (sourceB175 + difference 3 0) sourceC175) = raw5280 := by
      apply Matrix.ext; unfold tripleCharges sourceA175 sourceB175 sourceC175 difference raw5280; decide +kernel
    rw [ha]
    exact (canonical5280 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA175 + difference 0 4) (sourceB175 + difference 4 0) sourceC175) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2776) := by
    have ha : (tripleCharges (sourceA175 + difference 0 4) (sourceB175 + difference 4 0) sourceC175) = raw5281 := by
      apply Matrix.ext; unfold tripleCharges sourceA175 sourceB175 sourceC175 difference raw5281; decide +kernel
    rw [ha]
    exact (canonical5281 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA175 + difference 0 5) (sourceB175 + difference 5 0) sourceC175) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2753) := by
    have ha : (tripleCharges (sourceA175 + difference 0 5) (sourceB175 + difference 5 0) sourceC175) = raw5282 := by
      apply Matrix.ext; unfold tripleCharges sourceA175 sourceB175 sourceC175 difference raw5282; decide +kernel
    rw [ha]
    exact (canonical5282 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA175 + difference 1 0) (sourceB175 + difference 0 1) sourceC175) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1701) := by
    have ha : (tripleCharges (sourceA175 + difference 1 0) (sourceB175 + difference 0 1) sourceC175) = raw5283 := by
      apply Matrix.ext; unfold tripleCharges sourceA175 sourceB175 sourceC175 difference raw5283; decide +kernel
    rw [ha]
    exact (canonical5283 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA175 + difference 1 2) (sourceB175 + difference 2 1) sourceC175) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2236) := by
    have ha : (tripleCharges (sourceA175 + difference 1 2) (sourceB175 + difference 2 1) sourceC175) = raw5284 := by
      apply Matrix.ext; unfold tripleCharges sourceA175 sourceB175 sourceC175 difference raw5284; decide +kernel
    rw [ha]
    exact (canonical5284 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA175 + difference 1 3) (sourceB175 + difference 3 1) sourceC175) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2237) := by
    have ha : (tripleCharges (sourceA175 + difference 1 3) (sourceB175 + difference 3 1) sourceC175) = raw5285 := by
      apply Matrix.ext; unfold tripleCharges sourceA175 sourceB175 sourceC175 difference raw5285; decide +kernel
    rw [ha]
    exact (canonical5285 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA175 + difference 1 4) (sourceB175 + difference 4 1) sourceC175) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2253) := by
    have ha : (tripleCharges (sourceA175 + difference 1 4) (sourceB175 + difference 4 1) sourceC175) = raw5286 := by
      apply Matrix.ext; unfold tripleCharges sourceA175 sourceB175 sourceC175 difference raw5286; decide +kernel
    rw [ha]
    exact (canonical5286 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA175 + difference 1 5) (sourceB175 + difference 5 1) sourceC175) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2233) := by
    have ha : (tripleCharges (sourceA175 + difference 1 5) (sourceB175 + difference 5 1) sourceC175) = raw5287 := by
      apply Matrix.ext; unfold tripleCharges sourceA175 sourceB175 sourceC175 difference raw5287; decide +kernel
    rw [ha]
    exact (canonical5287 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA175 + difference 2 0) (sourceB175 + difference 0 2) sourceC175) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1715) := by
    have ha : (tripleCharges (sourceA175 + difference 2 0) (sourceB175 + difference 0 2) sourceC175) = raw5288 := by
      apply Matrix.ext; unfold tripleCharges sourceA175 sourceB175 sourceC175 difference raw5288; decide +kernel
    rw [ha]
    exact (canonical5288 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA175 + difference 2 1) (sourceB175 + difference 1 2) sourceC175) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2196) := by
    have ha : (tripleCharges (sourceA175 + difference 2 1) (sourceB175 + difference 1 2) sourceC175) = raw5289 := by
      apply Matrix.ext; unfold tripleCharges sourceA175 sourceB175 sourceC175 difference raw5289; decide +kernel
    rw [ha]
    exact (canonical5289 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA175 + difference 2 3) (sourceB175 + difference 3 2) sourceC175) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2254) := by
    have ha : (tripleCharges (sourceA175 + difference 2 3) (sourceB175 + difference 3 2) sourceC175) = raw5290 := by
      apply Matrix.ext; unfold tripleCharges sourceA175 sourceB175 sourceC175 difference raw5290; decide +kernel
    rw [ha]
    exact (canonical5290 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA175 + difference 2 4) (sourceB175 + difference 4 2) sourceC175) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2279) := by
    have ha : (tripleCharges (sourceA175 + difference 2 4) (sourceB175 + difference 4 2) sourceC175) = raw5291 := by
      apply Matrix.ext; unfold tripleCharges sourceA175 sourceB175 sourceC175 difference raw5291; decide +kernel
    rw [ha]
    exact (canonical5291 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA175 + difference 2 5) (sourceB175 + difference 5 2) sourceC175) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2245) := by
    have ha : (tripleCharges (sourceA175 + difference 2 5) (sourceB175 + difference 5 2) sourceC175) = raw5292 := by
      apply Matrix.ext; unfold tripleCharges sourceA175 sourceB175 sourceC175 difference raw5292; decide +kernel
    rw [ha]
    exact (canonical5292 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA175 + difference 3 0) (sourceB175 + difference 0 3) sourceC175) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1714) := by
    have ha : (tripleCharges (sourceA175 + difference 3 0) (sourceB175 + difference 0 3) sourceC175) = raw5293 := by
      apply Matrix.ext; unfold tripleCharges sourceA175 sourceB175 sourceC175 difference raw5293; decide +kernel
    rw [ha]
    exact (canonical5293 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA175 + difference 3 1) (sourceB175 + difference 1 3) sourceC175) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2195) := by
    have ha : (tripleCharges (sourceA175 + difference 3 1) (sourceB175 + difference 1 3) sourceC175) = raw5294 := by
      apply Matrix.ext; unfold tripleCharges sourceA175 sourceB175 sourceC175 difference raw5294; decide +kernel
    rw [ha]
    exact (canonical5294 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA175 + difference 3 2) (sourceB175 + difference 2 3) sourceC175) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2251) := by
    have ha : (tripleCharges (sourceA175 + difference 3 2) (sourceB175 + difference 2 3) sourceC175) = raw5295 := by
      apply Matrix.ext; unfold tripleCharges sourceA175 sourceB175 sourceC175 difference raw5295; decide +kernel
    rw [ha]
    exact (canonical5295 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA175 + difference 3 4) (sourceB175 + difference 4 3) sourceC175) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2278) := by
    have ha : (tripleCharges (sourceA175 + difference 3 4) (sourceB175 + difference 4 3) sourceC175) = raw5296 := by
      apply Matrix.ext; unfold tripleCharges sourceA175 sourceB175 sourceC175 difference raw5296; decide +kernel
    rw [ha]
    exact (canonical5296 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA175 + difference 3 5) (sourceB175 + difference 5 3) sourceC175) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2244) := by
    have ha : (tripleCharges (sourceA175 + difference 3 5) (sourceB175 + difference 5 3) sourceC175) = raw5297 := by
      apply Matrix.ext; unfold tripleCharges sourceA175 sourceB175 sourceC175 difference raw5297; decide +kernel
    rw [ha]
    exact (canonical5297 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA175 + difference 4 0) (sourceB175 + difference 0 4) sourceC175) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1732) := by
    have ha : (tripleCharges (sourceA175 + difference 4 0) (sourceB175 + difference 0 4) sourceC175) = raw5298 := by
      apply Matrix.ext; unfold tripleCharges sourceA175 sourceB175 sourceC175 difference raw5298; decide +kernel
    rw [ha]
    exact (canonical5298 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA175 + difference 4 1) (sourceB175 + difference 1 4) sourceC175) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2209) := by
    have ha : (tripleCharges (sourceA175 + difference 4 1) (sourceB175 + difference 1 4) sourceC175) = raw5299 := by
      apply Matrix.ext; unfold tripleCharges sourceA175 sourceB175 sourceC175 difference raw5299; decide +kernel
    rw [ha]
    exact (canonical5299 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA175 + difference 4 2) (sourceB175 + difference 2 4) sourceC175) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2270) := by
    have ha : (tripleCharges (sourceA175 + difference 4 2) (sourceB175 + difference 2 4) sourceC175) = raw5300 := by
      apply Matrix.ext; unfold tripleCharges sourceA175 sourceB175 sourceC175 difference raw5300; decide +kernel
    rw [ha]
    exact (canonical5300 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA175 + difference 4 3) (sourceB175 + difference 3 4) sourceC175) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2271) := by
    have ha : (tripleCharges (sourceA175 + difference 4 3) (sourceB175 + difference 3 4) sourceC175) = raw5301 := by
      apply Matrix.ext; unfold tripleCharges sourceA175 sourceB175 sourceC175 difference raw5301; decide +kernel
    rw [ha]
    exact (canonical5301 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA175 + difference 4 5) (sourceB175 + difference 5 4) sourceC175) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2253) := by
    have ha : (tripleCharges (sourceA175 + difference 4 5) (sourceB175 + difference 5 4) sourceC175) = raw5302 := by
      apply Matrix.ext; unfold tripleCharges sourceA175 sourceB175 sourceC175 difference raw5302; decide +kernel
    rw [ha]
    exact (canonical5302 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA175 + difference 5 0) (sourceB175 + difference 0 5) sourceC175) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1718) := by
    have ha : (tripleCharges (sourceA175 + difference 5 0) (sourceB175 + difference 0 5) sourceC175) = raw5303 := by
      apply Matrix.ext; unfold tripleCharges sourceA175 sourceB175 sourceC175 difference raw5303; decide +kernel
    rw [ha]
    exact (canonical5303 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA175 + difference 5 1) (sourceB175 + difference 1 5) sourceC175) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1931) := by
    have ha : (tripleCharges (sourceA175 + difference 5 1) (sourceB175 + difference 1 5) sourceC175) = raw5304 := by
      apply Matrix.ext; unfold tripleCharges sourceA175 sourceB175 sourceC175 difference raw5304; decide +kernel
    rw [ha]
    exact (canonical5304 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA175 + difference 5 2) (sourceB175 + difference 2 5) sourceC175) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1934) := by
    have ha : (tripleCharges (sourceA175 + difference 5 2) (sourceB175 + difference 2 5) sourceC175) = raw5305 := by
      apply Matrix.ext; unfold tripleCharges sourceA175 sourceB175 sourceC175 difference raw5305; decide +kernel
    rw [ha]
    exact (canonical5305 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA175 + difference 5 3) (sourceB175 + difference 3 5) sourceC175) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1932) := by
    have ha : (tripleCharges (sourceA175 + difference 5 3) (sourceB175 + difference 3 5) sourceC175) = raw5306 := by
      apply Matrix.ext; unfold tripleCharges sourceA175 sourceB175 sourceC175 difference raw5306; decide +kernel
    rw [ha]
    exact (canonical5306 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA175 + difference 5 4) (sourceB175 + difference 4 5) sourceC175) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2284) := by
    have ha : (tripleCharges (sourceA175 + difference 5 4) (sourceB175 + difference 4 5) sourceC175) = raw5307 := by
      apply Matrix.ext; unfold tripleCharges sourceA175 sourceB175 sourceC175 difference raw5307; decide +kernel
    rw [ha]
    exact (canonical5307 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA175 sourceB175 sourceC175
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm175, Integer.Sparse.eval]
  linarith only [hs]

def sourceA176 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB176 : Charge := ![0, 0, 1, 2, -1, -2]
def sourceC176 : Charge := ![3, 0, -1, -2, 0, 0]
def sourceForm176 : Integer.Sparse Master := [(Sum.inr 2253, 1), (Sum.inr 2513, 1), (Sum.inr 3528, 1), (Sum.inr 3577, 1), (Sum.inr 3625, 1), (Sum.inr 3626, 1), (Sum.inr 4084, -1)]

theorem sourceEq176 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm176 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA176 + difference 0 0) (sourceB176 + difference 0 0) sourceC176) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2253) := by
    have ha : (tripleCharges (sourceA176 + difference 0 0) (sourceB176 + difference 0 0) sourceC176) = raw5308 := by
      apply Matrix.ext; unfold tripleCharges sourceA176 sourceB176 sourceC176 difference raw5308; decide +kernel
    rw [ha]
    exact (canonical5308 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA176 + difference 0 1) (sourceB176 + difference 1 0) sourceC176) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3528) := by
    have ha : (tripleCharges (sourceA176 + difference 0 1) (sourceB176 + difference 1 0) sourceC176) = raw5309 := by
      apply Matrix.ext; unfold tripleCharges sourceA176 sourceB176 sourceC176 difference raw5309; decide +kernel
    rw [ha]
    exact (canonical5309 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA176 + difference 0 2) (sourceB176 + difference 2 0) sourceC176) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3577) := by
    have ha : (tripleCharges (sourceA176 + difference 0 2) (sourceB176 + difference 2 0) sourceC176) = raw5310 := by
      apply Matrix.ext; unfold tripleCharges sourceA176 sourceB176 sourceC176 difference raw5310; decide +kernel
    rw [ha]
    exact (canonical5310 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA176 + difference 0 3) (sourceB176 + difference 3 0) sourceC176) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2513) := by
    have ha : (tripleCharges (sourceA176 + difference 0 3) (sourceB176 + difference 3 0) sourceC176) = raw5311 := by
      apply Matrix.ext; unfold tripleCharges sourceA176 sourceB176 sourceC176 difference raw5311; decide +kernel
    rw [ha]
    exact (canonical5311 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA176 + difference 0 4) (sourceB176 + difference 4 0) sourceC176) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3626) := by
    have ha : (tripleCharges (sourceA176 + difference 0 4) (sourceB176 + difference 4 0) sourceC176) = raw5312 := by
      apply Matrix.ext; unfold tripleCharges sourceA176 sourceB176 sourceC176 difference raw5312; decide +kernel
    rw [ha]
    exact (canonical5312 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA176 + difference 0 5) (sourceB176 + difference 5 0) sourceC176) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3625) := by
    have ha : (tripleCharges (sourceA176 + difference 0 5) (sourceB176 + difference 5 0) sourceC176) = raw5313 := by
      apply Matrix.ext; unfold tripleCharges sourceA176 sourceB176 sourceC176 difference raw5313; decide +kernel
    rw [ha]
    exact (canonical5313 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA176 + sourceB176) sourceC176) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA176 + sourceB176) sourceC176) = raw5314 := by
      apply Matrix.ext; unfold doubleCharges sourceA176 sourceB176 sourceC176 raw5314; decide +kernel
    rw [ha]
    exact (canonical5314 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA176 sourceB176 sourceC176
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm176, Integer.Sparse.eval]
  linarith only [hs]

def sourceA177 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB177 : Charge := ![0, 0, 1, 2, -1, -2]
def sourceC177 : Charge := ![3, 0, -1, -2, 0, 0]
def sourceForm177 : Integer.Sparse Master := [(Sum.inr 1028, 1), (Sum.inr 1029, 1), (Sum.inr 1030, 1), (Sum.inr 1042, 1), (Sum.inr 1058, 1), (Sum.inr 2253, 1), (Sum.inr 4084, -1)]

theorem sourceEq177 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm177 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA177 + difference 0 0) (sourceB177 + difference 0 0) sourceC177) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2253) := by
    have ha : (tripleCharges (sourceA177 + difference 0 0) (sourceB177 + difference 0 0) sourceC177) = raw5308 := by
      apply Matrix.ext; unfold tripleCharges sourceA177 sourceB177 sourceC177 difference raw5308; decide +kernel
    rw [ha]
    exact (canonical5308 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA177 + difference 1 0) (sourceB177 + difference 0 1) sourceC177) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1028) := by
    have ha : (tripleCharges (sourceA177 + difference 1 0) (sourceB177 + difference 0 1) sourceC177) = raw5315 := by
      apply Matrix.ext; unfold tripleCharges sourceA177 sourceB177 sourceC177 difference raw5315; decide +kernel
    rw [ha]
    exact (canonical5315 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA177 + difference 2 0) (sourceB177 + difference 0 2) sourceC177) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1058) := by
    have ha : (tripleCharges (sourceA177 + difference 2 0) (sourceB177 + difference 0 2) sourceC177) = raw5316 := by
      apply Matrix.ext; unfold tripleCharges sourceA177 sourceB177 sourceC177 difference raw5316; decide +kernel
    rw [ha]
    exact (canonical5316 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA177 + difference 3 0) (sourceB177 + difference 0 3) sourceC177) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1042) := by
    have ha : (tripleCharges (sourceA177 + difference 3 0) (sourceB177 + difference 0 3) sourceC177) = raw5317 := by
      apply Matrix.ext; unfold tripleCharges sourceA177 sourceB177 sourceC177 difference raw5317; decide +kernel
    rw [ha]
    exact (canonical5317 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA177 + difference 4 0) (sourceB177 + difference 0 4) sourceC177) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1030) := by
    have ha : (tripleCharges (sourceA177 + difference 4 0) (sourceB177 + difference 0 4) sourceC177) = raw5318 := by
      apply Matrix.ext; unfold tripleCharges sourceA177 sourceB177 sourceC177 difference raw5318; decide +kernel
    rw [ha]
    exact (canonical5318 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA177 + difference 5 0) (sourceB177 + difference 0 5) sourceC177) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1029) := by
    have ha : (tripleCharges (sourceA177 + difference 5 0) (sourceB177 + difference 0 5) sourceC177) = raw5319 := by
      apply Matrix.ext; unfold tripleCharges sourceA177 sourceB177 sourceC177 difference raw5319; decide +kernel
    rw [ha]
    exact (canonical5319 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA177 + sourceB177) sourceC177) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA177 + sourceB177) sourceC177) = raw5314 := by
      apply Matrix.ext; unfold doubleCharges sourceA177 sourceB177 sourceC177 raw5314; decide +kernel
    rw [ha]
    exact (canonical5314 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA177 sourceB177 sourceC177
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm177, Integer.Sparse.eval]
  linarith only [hs]

def sourceA178 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB178 : Charge := ![0, 0, 1, 2, -1, -2]
def sourceC178 : Charge := ![3, 0, -1, -2, 0, 0]
def sourceForm178 : Integer.Sparse Master := [(Sum.inr 1028, 1), (Sum.inr 2095, 1), (Sum.inr 2124, 1), (Sum.inr 2252, 1), (Sum.inr 2253, 2), (Sum.inr 4084, -1)]

theorem sourceEq178 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm178 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA178 + difference 1 0) (sourceB178 + difference 0 1) sourceC178) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1028) := by
    have ha : (tripleCharges (sourceA178 + difference 1 0) (sourceB178 + difference 0 1) sourceC178) = raw5315 := by
      apply Matrix.ext; unfold tripleCharges sourceA178 sourceB178 sourceC178 difference raw5315; decide +kernel
    rw [ha]
    exact (canonical5315 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA178 + difference 1 1) (sourceB178 + difference 1 1) sourceC178) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2253) := by
    have ha : (tripleCharges (sourceA178 + difference 1 1) (sourceB178 + difference 1 1) sourceC178) = raw5308 := by
      apply Matrix.ext; unfold tripleCharges sourceA178 sourceB178 sourceC178 difference raw5308; decide +kernel
    rw [ha]
    exact (canonical5308 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA178 + difference 1 2) (sourceB178 + difference 2 1) sourceC178) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2095) := by
    have ha : (tripleCharges (sourceA178 + difference 1 2) (sourceB178 + difference 2 1) sourceC178) = raw5320 := by
      apply Matrix.ext; unfold tripleCharges sourceA178 sourceB178 sourceC178 difference raw5320; decide +kernel
    rw [ha]
    exact (canonical5320 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA178 + difference 1 3) (sourceB178 + difference 3 1) sourceC178) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2124) := by
    have ha : (tripleCharges (sourceA178 + difference 1 3) (sourceB178 + difference 3 1) sourceC178) = raw5321 := by
      apply Matrix.ext; unfold tripleCharges sourceA178 sourceB178 sourceC178 difference raw5321; decide +kernel
    rw [ha]
    exact (canonical5321 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA178 + difference 1 4) (sourceB178 + difference 4 1) sourceC178) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2253) := by
    have ha : (tripleCharges (sourceA178 + difference 1 4) (sourceB178 + difference 4 1) sourceC178) = raw5322 := by
      apply Matrix.ext; unfold tripleCharges sourceA178 sourceB178 sourceC178 difference raw5322; decide +kernel
    rw [ha]
    exact (canonical5322 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA178 + difference 1 5) (sourceB178 + difference 5 1) sourceC178) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2252) := by
    have ha : (tripleCharges (sourceA178 + difference 1 5) (sourceB178 + difference 5 1) sourceC178) = raw5323 := by
      apply Matrix.ext; unfold tripleCharges sourceA178 sourceB178 sourceC178 difference raw5323; decide +kernel
    rw [ha]
    exact (canonical5323 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA178 + sourceB178) sourceC178) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA178 + sourceB178) sourceC178) = raw5314 := by
      apply Matrix.ext; unfold doubleCharges sourceA178 sourceB178 sourceC178 raw5314; decide +kernel
    rw [ha]
    exact (canonical5314 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA178 sourceB178 sourceC178
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm178, Integer.Sparse.eval]
  linarith only [hs]

def sourceA179 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB179 : Charge := ![0, 0, 1, 2, -1, -2]
def sourceC179 : Charge := ![3, 0, -1, -2, 0, 0]
def sourceForm179 : Integer.Sparse Master := [(Sum.inr 2013, 1), (Sum.inr 2014, 1), (Sum.inr 2021, 1), (Sum.inr 2034, 1), (Sum.inr 2253, 1), (Sum.inr 3528, 1), (Sum.inr 4084, -1)]

theorem sourceEq179 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm179 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA179 + difference 0 1) (sourceB179 + difference 1 0) sourceC179) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3528) := by
    have ha : (tripleCharges (sourceA179 + difference 0 1) (sourceB179 + difference 1 0) sourceC179) = raw5309 := by
      apply Matrix.ext; unfold tripleCharges sourceA179 sourceB179 sourceC179 difference raw5309; decide +kernel
    rw [ha]
    exact (canonical5309 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA179 + difference 1 1) (sourceB179 + difference 1 1) sourceC179) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2253) := by
    have ha : (tripleCharges (sourceA179 + difference 1 1) (sourceB179 + difference 1 1) sourceC179) = raw5308 := by
      apply Matrix.ext; unfold tripleCharges sourceA179 sourceB179 sourceC179 difference raw5308; decide +kernel
    rw [ha]
    exact (canonical5308 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA179 + difference 2 1) (sourceB179 + difference 1 2) sourceC179) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2034) := by
    have ha : (tripleCharges (sourceA179 + difference 2 1) (sourceB179 + difference 1 2) sourceC179) = raw5324 := by
      apply Matrix.ext; unfold tripleCharges sourceA179 sourceB179 sourceC179 difference raw5324; decide +kernel
    rw [ha]
    exact (canonical5324 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA179 + difference 3 1) (sourceB179 + difference 1 3) sourceC179) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2021) := by
    have ha : (tripleCharges (sourceA179 + difference 3 1) (sourceB179 + difference 1 3) sourceC179) = raw5325 := by
      apply Matrix.ext; unfold tripleCharges sourceA179 sourceB179 sourceC179 difference raw5325; decide +kernel
    rw [ha]
    exact (canonical5325 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA179 + difference 4 1) (sourceB179 + difference 1 4) sourceC179) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2014) := by
    have ha : (tripleCharges (sourceA179 + difference 4 1) (sourceB179 + difference 1 4) sourceC179) = raw5326 := by
      apply Matrix.ext; unfold tripleCharges sourceA179 sourceB179 sourceC179 difference raw5326; decide +kernel
    rw [ha]
    exact (canonical5326 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA179 + difference 5 1) (sourceB179 + difference 1 5) sourceC179) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2013) := by
    have ha : (tripleCharges (sourceA179 + difference 5 1) (sourceB179 + difference 1 5) sourceC179) = raw5327 := by
      apply Matrix.ext; unfold tripleCharges sourceA179 sourceB179 sourceC179 difference raw5327; decide +kernel
    rw [ha]
    exact (canonical5327 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA179 + sourceB179) sourceC179) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA179 + sourceB179) sourceC179) = raw5314 := by
      apply Matrix.ext; unfold doubleCharges sourceA179 sourceB179 sourceC179 raw5314; decide +kernel
    rw [ha]
    exact (canonical5314 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA179 sourceB179 sourceC179
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm179, Integer.Sparse.eval]
  linarith only [hs]

def sourceA180 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB180 : Charge := ![0, 0, 1, 2, -1, -2]
def sourceC180 : Charge := ![3, 0, -1, -2, 0, 0]
def sourceForm180 : Integer.Sparse Master := [(Sum.inr 1058, 1), (Sum.inr 2034, 1), (Sum.inr 2133, 1), (Sum.inr 2253, 1), (Sum.inr 2277, 1), (Sum.inr 2279, 1), (Sum.inr 4084, -1)]

theorem sourceEq180 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm180 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA180 + difference 2 0) (sourceB180 + difference 0 2) sourceC180) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1058) := by
    have ha : (tripleCharges (sourceA180 + difference 2 0) (sourceB180 + difference 0 2) sourceC180) = raw5316 := by
      apply Matrix.ext; unfold tripleCharges sourceA180 sourceB180 sourceC180 difference raw5316; decide +kernel
    rw [ha]
    exact (canonical5316 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA180 + difference 2 1) (sourceB180 + difference 1 2) sourceC180) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2034) := by
    have ha : (tripleCharges (sourceA180 + difference 2 1) (sourceB180 + difference 1 2) sourceC180) = raw5324 := by
      apply Matrix.ext; unfold tripleCharges sourceA180 sourceB180 sourceC180 difference raw5324; decide +kernel
    rw [ha]
    exact (canonical5324 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA180 + difference 2 2) (sourceB180 + difference 2 2) sourceC180) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2253) := by
    have ha : (tripleCharges (sourceA180 + difference 2 2) (sourceB180 + difference 2 2) sourceC180) = raw5308 := by
      apply Matrix.ext; unfold tripleCharges sourceA180 sourceB180 sourceC180 difference raw5308; decide +kernel
    rw [ha]
    exact (canonical5308 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA180 + difference 2 3) (sourceB180 + difference 3 2) sourceC180) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2133) := by
    have ha : (tripleCharges (sourceA180 + difference 2 3) (sourceB180 + difference 3 2) sourceC180) = raw5328 := by
      apply Matrix.ext; unfold tripleCharges sourceA180 sourceB180 sourceC180 difference raw5328; decide +kernel
    rw [ha]
    exact (canonical5328 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA180 + difference 2 4) (sourceB180 + difference 4 2) sourceC180) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2279) := by
    have ha : (tripleCharges (sourceA180 + difference 2 4) (sourceB180 + difference 4 2) sourceC180) = raw5329 := by
      apply Matrix.ext; unfold tripleCharges sourceA180 sourceB180 sourceC180 difference raw5329; decide +kernel
    rw [ha]
    exact (canonical5329 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA180 + difference 2 5) (sourceB180 + difference 5 2) sourceC180) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2277) := by
    have ha : (tripleCharges (sourceA180 + difference 2 5) (sourceB180 + difference 5 2) sourceC180) = raw5330 := by
      apply Matrix.ext; unfold tripleCharges sourceA180 sourceB180 sourceC180 difference raw5330; decide +kernel
    rw [ha]
    exact (canonical5330 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA180 + sourceB180) sourceC180) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA180 + sourceB180) sourceC180) = raw5314 := by
      apply Matrix.ext; unfold doubleCharges sourceA180 sourceB180 sourceC180 raw5314; decide +kernel
    rw [ha]
    exact (canonical5314 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA180 sourceB180 sourceC180
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm180, Integer.Sparse.eval]
  linarith only [hs]

def sourceA181 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB181 : Charge := ![0, 0, 1, 2, -1, -2]
def sourceC181 : Charge := ![3, 0, -1, -2, 0, 0]
def sourceForm181 : Integer.Sparse Master := [(Sum.inr 2095, 1), (Sum.inr 2096, 1), (Sum.inr 2097, 1), (Sum.inr 2108, 1), (Sum.inr 2253, 1), (Sum.inr 3577, 1), (Sum.inr 4084, -1)]

theorem sourceEq181 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm181 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA181 + difference 0 2) (sourceB181 + difference 2 0) sourceC181) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3577) := by
    have ha : (tripleCharges (sourceA181 + difference 0 2) (sourceB181 + difference 2 0) sourceC181) = raw5310 := by
      apply Matrix.ext; unfold tripleCharges sourceA181 sourceB181 sourceC181 difference raw5310; decide +kernel
    rw [ha]
    exact (canonical5310 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA181 + difference 1 2) (sourceB181 + difference 2 1) sourceC181) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2095) := by
    have ha : (tripleCharges (sourceA181 + difference 1 2) (sourceB181 + difference 2 1) sourceC181) = raw5320 := by
      apply Matrix.ext; unfold tripleCharges sourceA181 sourceB181 sourceC181 difference raw5320; decide +kernel
    rw [ha]
    exact (canonical5320 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA181 + difference 2 2) (sourceB181 + difference 2 2) sourceC181) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2253) := by
    have ha : (tripleCharges (sourceA181 + difference 2 2) (sourceB181 + difference 2 2) sourceC181) = raw5308 := by
      apply Matrix.ext; unfold tripleCharges sourceA181 sourceB181 sourceC181 difference raw5308; decide +kernel
    rw [ha]
    exact (canonical5308 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA181 + difference 3 2) (sourceB181 + difference 2 3) sourceC181) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2108) := by
    have ha : (tripleCharges (sourceA181 + difference 3 2) (sourceB181 + difference 2 3) sourceC181) = raw5331 := by
      apply Matrix.ext; unfold tripleCharges sourceA181 sourceB181 sourceC181 difference raw5331; decide +kernel
    rw [ha]
    exact (canonical5331 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA181 + difference 4 2) (sourceB181 + difference 2 4) sourceC181) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2097) := by
    have ha : (tripleCharges (sourceA181 + difference 4 2) (sourceB181 + difference 2 4) sourceC181) = raw5332 := by
      apply Matrix.ext; unfold tripleCharges sourceA181 sourceB181 sourceC181 difference raw5332; decide +kernel
    rw [ha]
    exact (canonical5332 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA181 + difference 5 2) (sourceB181 + difference 2 5) sourceC181) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2096) := by
    have ha : (tripleCharges (sourceA181 + difference 5 2) (sourceB181 + difference 2 5) sourceC181) = raw5333 := by
      apply Matrix.ext; unfold tripleCharges sourceA181 sourceB181 sourceC181 difference raw5333; decide +kernel
    rw [ha]
    exact (canonical5333 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA181 + sourceB181) sourceC181) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA181 + sourceB181) sourceC181) = raw5314 := by
      apply Matrix.ext; unfold doubleCharges sourceA181 sourceB181 sourceC181 raw5314; decide +kernel
    rw [ha]
    exact (canonical5314 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA181 sourceB181 sourceC181
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm181, Integer.Sparse.eval]
  linarith only [hs]

def sourceA182 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB182 : Charge := ![0, 0, 1, 2, -1, -2]
def sourceC182 : Charge := ![3, 0, -1, -2, 0, 0]
def sourceForm182 : Integer.Sparse Master := [(Sum.inr 1042, 1), (Sum.inr 2021, 1), (Sum.inr 2108, 1), (Sum.inr 2253, 1), (Sum.inr 2262, 1), (Sum.inr 2266, 1), (Sum.inr 4084, -1)]

theorem sourceEq182 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm182 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA182 + difference 3 0) (sourceB182 + difference 0 3) sourceC182) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1042) := by
    have ha : (tripleCharges (sourceA182 + difference 3 0) (sourceB182 + difference 0 3) sourceC182) = raw5317 := by
      apply Matrix.ext; unfold tripleCharges sourceA182 sourceB182 sourceC182 difference raw5317; decide +kernel
    rw [ha]
    exact (canonical5317 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA182 + difference 3 1) (sourceB182 + difference 1 3) sourceC182) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2021) := by
    have ha : (tripleCharges (sourceA182 + difference 3 1) (sourceB182 + difference 1 3) sourceC182) = raw5325 := by
      apply Matrix.ext; unfold tripleCharges sourceA182 sourceB182 sourceC182 difference raw5325; decide +kernel
    rw [ha]
    exact (canonical5325 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA182 + difference 3 2) (sourceB182 + difference 2 3) sourceC182) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2108) := by
    have ha : (tripleCharges (sourceA182 + difference 3 2) (sourceB182 + difference 2 3) sourceC182) = raw5331 := by
      apply Matrix.ext; unfold tripleCharges sourceA182 sourceB182 sourceC182 difference raw5331; decide +kernel
    rw [ha]
    exact (canonical5331 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA182 + difference 3 3) (sourceB182 + difference 3 3) sourceC182) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2253) := by
    have ha : (tripleCharges (sourceA182 + difference 3 3) (sourceB182 + difference 3 3) sourceC182) = raw5308 := by
      apply Matrix.ext; unfold tripleCharges sourceA182 sourceB182 sourceC182 difference raw5308; decide +kernel
    rw [ha]
    exact (canonical5308 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA182 + difference 3 4) (sourceB182 + difference 4 3) sourceC182) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2266) := by
    have ha : (tripleCharges (sourceA182 + difference 3 4) (sourceB182 + difference 4 3) sourceC182) = raw5334 := by
      apply Matrix.ext; unfold tripleCharges sourceA182 sourceB182 sourceC182 difference raw5334; decide +kernel
    rw [ha]
    exact (canonical5334 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA182 + difference 3 5) (sourceB182 + difference 5 3) sourceC182) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2262) := by
    have ha : (tripleCharges (sourceA182 + difference 3 5) (sourceB182 + difference 5 3) sourceC182) = raw5335 := by
      apply Matrix.ext; unfold tripleCharges sourceA182 sourceB182 sourceC182 difference raw5335; decide +kernel
    rw [ha]
    exact (canonical5335 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA182 + sourceB182) sourceC182) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA182 + sourceB182) sourceC182) = raw5314 := by
      apply Matrix.ext; unfold doubleCharges sourceA182 sourceB182 sourceC182 raw5314; decide +kernel
    rw [ha]
    exact (canonical5314 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA182 sourceB182 sourceC182
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm182, Integer.Sparse.eval]
  linarith only [hs]

def sourceA183 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB183 : Charge := ![0, 0, 1, 2, -1, -2]
def sourceC183 : Charge := ![3, 0, -1, -2, 0, 0]
def sourceForm183 : Integer.Sparse Master := [(Sum.inr 2124, 1), (Sum.inr 2125, 1), (Sum.inr 2126, 1), (Sum.inr 2133, 1), (Sum.inr 2253, 1), (Sum.inr 2513, 1), (Sum.inr 4084, -1)]

theorem sourceEq183 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm183 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA183 + difference 0 3) (sourceB183 + difference 3 0) sourceC183) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2513) := by
    have ha : (tripleCharges (sourceA183 + difference 0 3) (sourceB183 + difference 3 0) sourceC183) = raw5311 := by
      apply Matrix.ext; unfold tripleCharges sourceA183 sourceB183 sourceC183 difference raw5311; decide +kernel
    rw [ha]
    exact (canonical5311 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA183 + difference 1 3) (sourceB183 + difference 3 1) sourceC183) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2124) := by
    have ha : (tripleCharges (sourceA183 + difference 1 3) (sourceB183 + difference 3 1) sourceC183) = raw5321 := by
      apply Matrix.ext; unfold tripleCharges sourceA183 sourceB183 sourceC183 difference raw5321; decide +kernel
    rw [ha]
    exact (canonical5321 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA183 + difference 2 3) (sourceB183 + difference 3 2) sourceC183) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2133) := by
    have ha : (tripleCharges (sourceA183 + difference 2 3) (sourceB183 + difference 3 2) sourceC183) = raw5328 := by
      apply Matrix.ext; unfold tripleCharges sourceA183 sourceB183 sourceC183 difference raw5328; decide +kernel
    rw [ha]
    exact (canonical5328 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA183 + difference 3 3) (sourceB183 + difference 3 3) sourceC183) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2253) := by
    have ha : (tripleCharges (sourceA183 + difference 3 3) (sourceB183 + difference 3 3) sourceC183) = raw5308 := by
      apply Matrix.ext; unfold tripleCharges sourceA183 sourceB183 sourceC183 difference raw5308; decide +kernel
    rw [ha]
    exact (canonical5308 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA183 + difference 4 3) (sourceB183 + difference 3 4) sourceC183) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2126) := by
    have ha : (tripleCharges (sourceA183 + difference 4 3) (sourceB183 + difference 3 4) sourceC183) = raw5336 := by
      apply Matrix.ext; unfold tripleCharges sourceA183 sourceB183 sourceC183 difference raw5336; decide +kernel
    rw [ha]
    exact (canonical5336 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA183 + difference 5 3) (sourceB183 + difference 3 5) sourceC183) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2125) := by
    have ha : (tripleCharges (sourceA183 + difference 5 3) (sourceB183 + difference 3 5) sourceC183) = raw5337 := by
      apply Matrix.ext; unfold tripleCharges sourceA183 sourceB183 sourceC183 difference raw5337; decide +kernel
    rw [ha]
    exact (canonical5337 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA183 + sourceB183) sourceC183) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA183 + sourceB183) sourceC183) = raw5314 := by
      apply Matrix.ext; unfold doubleCharges sourceA183 sourceB183 sourceC183 raw5314; decide +kernel
    rw [ha]
    exact (canonical5314 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA183 sourceB183 sourceC183
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm183, Integer.Sparse.eval]
  linarith only [hs]

def sourceA184 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB184 : Charge := ![0, 0, 1, 2, -1, -2]
def sourceC184 : Charge := ![3, 0, -1, -2, 0, 0]
def sourceForm184 : Integer.Sparse Master := [(Sum.inr 1030, 1), (Sum.inr 2014, 1), (Sum.inr 2097, 1), (Sum.inr 2126, 1), (Sum.inr 2253, 2), (Sum.inr 4084, -1)]

theorem sourceEq184 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm184 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA184 + difference 4 0) (sourceB184 + difference 0 4) sourceC184) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1030) := by
    have ha : (tripleCharges (sourceA184 + difference 4 0) (sourceB184 + difference 0 4) sourceC184) = raw5318 := by
      apply Matrix.ext; unfold tripleCharges sourceA184 sourceB184 sourceC184 difference raw5318; decide +kernel
    rw [ha]
    exact (canonical5318 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA184 + difference 4 1) (sourceB184 + difference 1 4) sourceC184) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2014) := by
    have ha : (tripleCharges (sourceA184 + difference 4 1) (sourceB184 + difference 1 4) sourceC184) = raw5326 := by
      apply Matrix.ext; unfold tripleCharges sourceA184 sourceB184 sourceC184 difference raw5326; decide +kernel
    rw [ha]
    exact (canonical5326 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA184 + difference 4 2) (sourceB184 + difference 2 4) sourceC184) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2097) := by
    have ha : (tripleCharges (sourceA184 + difference 4 2) (sourceB184 + difference 2 4) sourceC184) = raw5332 := by
      apply Matrix.ext; unfold tripleCharges sourceA184 sourceB184 sourceC184 difference raw5332; decide +kernel
    rw [ha]
    exact (canonical5332 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA184 + difference 4 3) (sourceB184 + difference 3 4) sourceC184) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2126) := by
    have ha : (tripleCharges (sourceA184 + difference 4 3) (sourceB184 + difference 3 4) sourceC184) = raw5336 := by
      apply Matrix.ext; unfold tripleCharges sourceA184 sourceB184 sourceC184 difference raw5336; decide +kernel
    rw [ha]
    exact (canonical5336 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA184 + difference 4 4) (sourceB184 + difference 4 4) sourceC184) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2253) := by
    have ha : (tripleCharges (sourceA184 + difference 4 4) (sourceB184 + difference 4 4) sourceC184) = raw5308 := by
      apply Matrix.ext; unfold tripleCharges sourceA184 sourceB184 sourceC184 difference raw5308; decide +kernel
    rw [ha]
    exact (canonical5308 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA184 + difference 4 5) (sourceB184 + difference 5 4) sourceC184) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2253) := by
    have ha : (tripleCharges (sourceA184 + difference 4 5) (sourceB184 + difference 5 4) sourceC184) = raw5338 := by
      apply Matrix.ext; unfold tripleCharges sourceA184 sourceB184 sourceC184 difference raw5338; decide +kernel
    rw [ha]
    exact (canonical5338 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA184 + sourceB184) sourceC184) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA184 + sourceB184) sourceC184) = raw5314 := by
      apply Matrix.ext; unfold doubleCharges sourceA184 sourceB184 sourceC184 raw5314; decide +kernel
    rw [ha]
    exact (canonical5314 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA184 sourceB184 sourceC184
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm184, Integer.Sparse.eval]
  linarith only [hs]

def sourceA185 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB185 : Charge := ![3, 0, -1, -2, 0, 0]
def sourceC185 : Charge := ![0, 0, 1, 2, -1, -2]
def sourceForm185 : Integer.Sparse Master := [(Sum.inr 4258, 1), (Sum.inr 4259, 2), (Sum.inr 4261, 2), (Sum.inr 4733, 2), (Sum.inr 4735, 2), (Sum.inr 4816, 2), (Sum.inr 4817, 2), (Sum.inr 4821, 2), (Sum.inr 4836, 2), (Sum.inr 4852, 2), (Sum.inr 4853, 2), (Sum.inr 4856, 2), (Sum.inr 4867, 2), (Sum.inr 5407, 1), (Sum.inr 5411, 2), (Sum.inr 5412, 2)]

theorem sourceEq185 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm185 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA185 + difference 0 1) (sourceB185 + difference 1 0) sourceC185) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5407) := by
    have ha : (tripleCharges (sourceA185 + difference 0 1) (sourceB185 + difference 1 0) sourceC185) = raw5339 := by
      apply Matrix.ext; unfold tripleCharges sourceA185 sourceB185 sourceC185 difference raw5339; decide +kernel
    rw [ha]
    exact (canonical5339 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA185 + difference 0 2) (sourceB185 + difference 2 0) sourceC185) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5412) := by
    have ha : (tripleCharges (sourceA185 + difference 0 2) (sourceB185 + difference 2 0) sourceC185) = raw5340 := by
      apply Matrix.ext; unfold tripleCharges sourceA185 sourceB185 sourceC185 difference raw5340; decide +kernel
    rw [ha]
    exact (canonical5340 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA185 + difference 0 3) (sourceB185 + difference 3 0) sourceC185) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA185 + difference 0 3) (sourceB185 + difference 3 0) sourceC185) = raw5341 := by
      apply Matrix.ext; unfold tripleCharges sourceA185 sourceB185 sourceC185 difference raw5341; decide +kernel
    rw [ha]
    exact (canonical5341 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA185 + difference 0 4) (sourceB185 + difference 4 0) sourceC185) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5412) := by
    have ha : (tripleCharges (sourceA185 + difference 0 4) (sourceB185 + difference 4 0) sourceC185) = raw5342 := by
      apply Matrix.ext; unfold tripleCharges sourceA185 sourceB185 sourceC185 difference raw5342; decide +kernel
    rw [ha]
    exact (canonical5342 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA185 + difference 0 5) (sourceB185 + difference 5 0) sourceC185) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA185 + difference 0 5) (sourceB185 + difference 5 0) sourceC185) = raw5343 := by
      apply Matrix.ext; unfold tripleCharges sourceA185 sourceB185 sourceC185 difference raw5343; decide +kernel
    rw [ha]
    exact (canonical5343 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA185 + difference 1 0) (sourceB185 + difference 0 1) sourceC185) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4258) := by
    have ha : (tripleCharges (sourceA185 + difference 1 0) (sourceB185 + difference 0 1) sourceC185) = raw5344 := by
      apply Matrix.ext; unfold tripleCharges sourceA185 sourceB185 sourceC185 difference raw5344; decide +kernel
    rw [ha]
    exact (canonical5344 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA185 + difference 1 2) (sourceB185 + difference 2 1) sourceC185) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4816) := by
    have ha : (tripleCharges (sourceA185 + difference 1 2) (sourceB185 + difference 2 1) sourceC185) = raw5345 := by
      apply Matrix.ext; unfold tripleCharges sourceA185 sourceB185 sourceC185 difference raw5345; decide +kernel
    rw [ha]
    exact (canonical5345 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA185 + difference 1 3) (sourceB185 + difference 3 1) sourceC185) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4852) := by
    have ha : (tripleCharges (sourceA185 + difference 1 3) (sourceB185 + difference 3 1) sourceC185) = raw5346 := by
      apply Matrix.ext; unfold tripleCharges sourceA185 sourceB185 sourceC185 difference raw5346; decide +kernel
    rw [ha]
    exact (canonical5346 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA185 + difference 1 4) (sourceB185 + difference 4 1) sourceC185) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4816) := by
    have ha : (tripleCharges (sourceA185 + difference 1 4) (sourceB185 + difference 4 1) sourceC185) = raw5347 := by
      apply Matrix.ext; unfold tripleCharges sourceA185 sourceB185 sourceC185 difference raw5347; decide +kernel
    rw [ha]
    exact (canonical5347 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA185 + difference 1 5) (sourceB185 + difference 5 1) sourceC185) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4852) := by
    have ha : (tripleCharges (sourceA185 + difference 1 5) (sourceB185 + difference 5 1) sourceC185) = raw5348 := by
      apply Matrix.ext; unfold tripleCharges sourceA185 sourceB185 sourceC185 difference raw5348; decide +kernel
    rw [ha]
    exact (canonical5348 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA185 + difference 2 0) (sourceB185 + difference 0 2) sourceC185) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4261) := by
    have ha : (tripleCharges (sourceA185 + difference 2 0) (sourceB185 + difference 0 2) sourceC185) = raw5349 := by
      apply Matrix.ext; unfold tripleCharges sourceA185 sourceB185 sourceC185 difference raw5349; decide +kernel
    rw [ha]
    exact (canonical5349 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA185 + difference 2 1) (sourceB185 + difference 1 2) sourceC185) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4735) := by
    have ha : (tripleCharges (sourceA185 + difference 2 1) (sourceB185 + difference 1 2) sourceC185) = raw5350 := by
      apply Matrix.ext; unfold tripleCharges sourceA185 sourceB185 sourceC185 difference raw5350; decide +kernel
    rw [ha]
    exact (canonical5350 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA185 + difference 2 3) (sourceB185 + difference 3 2) sourceC185) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4867) := by
    have ha : (tripleCharges (sourceA185 + difference 2 3) (sourceB185 + difference 3 2) sourceC185) = raw5351 := by
      apply Matrix.ext; unfold tripleCharges sourceA185 sourceB185 sourceC185 difference raw5351; decide +kernel
    rw [ha]
    exact (canonical5351 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA185 + difference 2 4) (sourceB185 + difference 4 2) sourceC185) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4821) := by
    have ha : (tripleCharges (sourceA185 + difference 2 4) (sourceB185 + difference 4 2) sourceC185) = raw5352 := by
      apply Matrix.ext; unfold tripleCharges sourceA185 sourceB185 sourceC185 difference raw5352; decide +kernel
    rw [ha]
    exact (canonical5352 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA185 + difference 2 5) (sourceB185 + difference 5 2) sourceC185) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4856) := by
    have ha : (tripleCharges (sourceA185 + difference 2 5) (sourceB185 + difference 5 2) sourceC185) = raw5353 := by
      apply Matrix.ext; unfold tripleCharges sourceA185 sourceB185 sourceC185 difference raw5353; decide +kernel
    rw [ha]
    exact (canonical5353 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA185 + difference 3 0) (sourceB185 + difference 0 3) sourceC185) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4259) := by
    have ha : (tripleCharges (sourceA185 + difference 3 0) (sourceB185 + difference 0 3) sourceC185) = raw5354 := by
      apply Matrix.ext; unfold tripleCharges sourceA185 sourceB185 sourceC185 difference raw5354; decide +kernel
    rw [ha]
    exact (canonical5354 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA185 + difference 3 1) (sourceB185 + difference 1 3) sourceC185) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4733) := by
    have ha : (tripleCharges (sourceA185 + difference 3 1) (sourceB185 + difference 1 3) sourceC185) = raw5355 := by
      apply Matrix.ext; unfold tripleCharges sourceA185 sourceB185 sourceC185 difference raw5355; decide +kernel
    rw [ha]
    exact (canonical5355 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA185 + difference 3 2) (sourceB185 + difference 2 3) sourceC185) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4836) := by
    have ha : (tripleCharges (sourceA185 + difference 3 2) (sourceB185 + difference 2 3) sourceC185) = raw5356 := by
      apply Matrix.ext; unfold tripleCharges sourceA185 sourceB185 sourceC185 difference raw5356; decide +kernel
    rw [ha]
    exact (canonical5356 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA185 + difference 3 4) (sourceB185 + difference 4 3) sourceC185) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4817) := by
    have ha : (tripleCharges (sourceA185 + difference 3 4) (sourceB185 + difference 4 3) sourceC185) = raw5357 := by
      apply Matrix.ext; unfold tripleCharges sourceA185 sourceB185 sourceC185 difference raw5357; decide +kernel
    rw [ha]
    exact (canonical5357 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA185 + difference 3 5) (sourceB185 + difference 5 3) sourceC185) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4853) := by
    have ha : (tripleCharges (sourceA185 + difference 3 5) (sourceB185 + difference 5 3) sourceC185) = raw5358 := by
      apply Matrix.ext; unfold tripleCharges sourceA185 sourceB185 sourceC185 difference raw5358; decide +kernel
    rw [ha]
    exact (canonical5358 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA185 + difference 4 0) (sourceB185 + difference 0 4) sourceC185) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4261) := by
    have ha : (tripleCharges (sourceA185 + difference 4 0) (sourceB185 + difference 0 4) sourceC185) = raw5359 := by
      apply Matrix.ext; unfold tripleCharges sourceA185 sourceB185 sourceC185 difference raw5359; decide +kernel
    rw [ha]
    exact (canonical5359 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA185 + difference 4 1) (sourceB185 + difference 1 4) sourceC185) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4735) := by
    have ha : (tripleCharges (sourceA185 + difference 4 1) (sourceB185 + difference 1 4) sourceC185) = raw5360 := by
      apply Matrix.ext; unfold tripleCharges sourceA185 sourceB185 sourceC185 difference raw5360; decide +kernel
    rw [ha]
    exact (canonical5360 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA185 + difference 4 2) (sourceB185 + difference 2 4) sourceC185) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4821) := by
    have ha : (tripleCharges (sourceA185 + difference 4 2) (sourceB185 + difference 2 4) sourceC185) = raw5361 := by
      apply Matrix.ext; unfold tripleCharges sourceA185 sourceB185 sourceC185 difference raw5361; decide +kernel
    rw [ha]
    exact (canonical5361 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA185 + difference 4 3) (sourceB185 + difference 3 4) sourceC185) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4856) := by
    have ha : (tripleCharges (sourceA185 + difference 4 3) (sourceB185 + difference 3 4) sourceC185) = raw5362 := by
      apply Matrix.ext; unfold tripleCharges sourceA185 sourceB185 sourceC185 difference raw5362; decide +kernel
    rw [ha]
    exact (canonical5362 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA185 + difference 4 5) (sourceB185 + difference 5 4) sourceC185) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4867) := by
    have ha : (tripleCharges (sourceA185 + difference 4 5) (sourceB185 + difference 5 4) sourceC185) = raw5363 := by
      apply Matrix.ext; unfold tripleCharges sourceA185 sourceB185 sourceC185 difference raw5363; decide +kernel
    rw [ha]
    exact (canonical5363 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA185 + difference 5 0) (sourceB185 + difference 0 5) sourceC185) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4259) := by
    have ha : (tripleCharges (sourceA185 + difference 5 0) (sourceB185 + difference 0 5) sourceC185) = raw5364 := by
      apply Matrix.ext; unfold tripleCharges sourceA185 sourceB185 sourceC185 difference raw5364; decide +kernel
    rw [ha]
    exact (canonical5364 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA185 + difference 5 1) (sourceB185 + difference 1 5) sourceC185) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4733) := by
    have ha : (tripleCharges (sourceA185 + difference 5 1) (sourceB185 + difference 1 5) sourceC185) = raw5365 := by
      apply Matrix.ext; unfold tripleCharges sourceA185 sourceB185 sourceC185 difference raw5365; decide +kernel
    rw [ha]
    exact (canonical5365 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA185 + difference 5 2) (sourceB185 + difference 2 5) sourceC185) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4817) := by
    have ha : (tripleCharges (sourceA185 + difference 5 2) (sourceB185 + difference 2 5) sourceC185) = raw5366 := by
      apply Matrix.ext; unfold tripleCharges sourceA185 sourceB185 sourceC185 difference raw5366; decide +kernel
    rw [ha]
    exact (canonical5366 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA185 + difference 5 3) (sourceB185 + difference 3 5) sourceC185) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4853) := by
    have ha : (tripleCharges (sourceA185 + difference 5 3) (sourceB185 + difference 3 5) sourceC185) = raw5367 := by
      apply Matrix.ext; unfold tripleCharges sourceA185 sourceB185 sourceC185 difference raw5367; decide +kernel
    rw [ha]
    exact (canonical5367 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA185 + difference 5 4) (sourceB185 + difference 4 5) sourceC185) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4836) := by
    have ha : (tripleCharges (sourceA185 + difference 5 4) (sourceB185 + difference 4 5) sourceC185) = raw5368 := by
      apply Matrix.ext; unfold tripleCharges sourceA185 sourceB185 sourceC185 difference raw5368; decide +kernel
    rw [ha]
    exact (canonical5368 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA185 sourceB185 sourceC185
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm185, Integer.Sparse.eval]
  linarith only [hs]

def sourceA186 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB186 : Charge := ![3, 0, -1, -2, 0, 0]
def sourceC186 : Charge := ![0, 0, 1, 2, -1, -2]
def sourceForm186 : Integer.Sparse Master := [(Sum.inr 793, 1), (Sum.inr 794, 1), (Sum.inr 796, 1), (Sum.inr 808, 1), (Sum.inr 825, 1), (Sum.inr 1902, 1), (Sum.inr 1904, 1), (Sum.inr 1910, 1), (Sum.inr 1923, 1), (Sum.inr 2034, 1), (Sum.inr 2035, 1), (Sum.inr 2039, 1), (Sum.inr 2055, 1), (Sum.inr 2089, 1), (Sum.inr 2090, 1), (Sum.inr 2094, 1), (Sum.inr 2108, 1), (Sum.inr 2196, 1), (Sum.inr 2197, 1), (Sum.inr 2207, 1), (Sum.inr 2217, 1), (Sum.inr 2250, 1), (Sum.inr 2251, 1), (Sum.inr 2259, 1), (Sum.inr 2274, 1), (Sum.inr 3803, 1), (Sum.inr 3813, 1), (Sum.inr 3814, 1), (Sum.inr 3856, 1), (Sum.inr 3883, 1)]

theorem sourceEq186 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm186 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA186 + difference 0 1) (sourceB186 + difference 1 0) sourceC186) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3803) := by
    have ha : (tripleCharges (sourceA186 + difference 0 1) (sourceB186 + difference 1 0) sourceC186) = raw5369 := by
      apply Matrix.ext; unfold tripleCharges sourceA186 sourceB186 sourceC186 difference raw5369; decide +kernel
    rw [ha]
    exact (canonical5369 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA186 + difference 0 2) (sourceB186 + difference 2 0) sourceC186) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3856) := by
    have ha : (tripleCharges (sourceA186 + difference 0 2) (sourceB186 + difference 2 0) sourceC186) = raw5370 := by
      apply Matrix.ext; unfold tripleCharges sourceA186 sourceB186 sourceC186 difference raw5370; decide +kernel
    rw [ha]
    exact (canonical5370 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA186 + difference 0 3) (sourceB186 + difference 3 0) sourceC186) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3883) := by
    have ha : (tripleCharges (sourceA186 + difference 0 3) (sourceB186 + difference 3 0) sourceC186) = raw5371 := by
      apply Matrix.ext; unfold tripleCharges sourceA186 sourceB186 sourceC186 difference raw5371; decide +kernel
    rw [ha]
    exact (canonical5371 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA186 + difference 0 4) (sourceB186 + difference 4 0) sourceC186) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3814) := by
    have ha : (tripleCharges (sourceA186 + difference 0 4) (sourceB186 + difference 4 0) sourceC186) = raw5372 := by
      apply Matrix.ext; unfold tripleCharges sourceA186 sourceB186 sourceC186 difference raw5372; decide +kernel
    rw [ha]
    exact (canonical5372 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA186 + difference 0 5) (sourceB186 + difference 5 0) sourceC186) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3813) := by
    have ha : (tripleCharges (sourceA186 + difference 0 5) (sourceB186 + difference 5 0) sourceC186) = raw5373 := by
      apply Matrix.ext; unfold tripleCharges sourceA186 sourceB186 sourceC186 difference raw5373; decide +kernel
    rw [ha]
    exact (canonical5373 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA186 + difference 1 0) (sourceB186 + difference 0 1) sourceC186) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 793) := by
    have ha : (tripleCharges (sourceA186 + difference 1 0) (sourceB186 + difference 0 1) sourceC186) = raw5374 := by
      apply Matrix.ext; unfold tripleCharges sourceA186 sourceB186 sourceC186 difference raw5374; decide +kernel
    rw [ha]
    exact (canonical5374 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA186 + difference 1 2) (sourceB186 + difference 2 1) sourceC186) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2034) := by
    have ha : (tripleCharges (sourceA186 + difference 1 2) (sourceB186 + difference 2 1) sourceC186) = raw5375 := by
      apply Matrix.ext; unfold tripleCharges sourceA186 sourceB186 sourceC186 difference raw5375; decide +kernel
    rw [ha]
    exact (canonical5375 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA186 + difference 1 3) (sourceB186 + difference 3 1) sourceC186) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2089) := by
    have ha : (tripleCharges (sourceA186 + difference 1 3) (sourceB186 + difference 3 1) sourceC186) = raw5376 := by
      apply Matrix.ext; unfold tripleCharges sourceA186 sourceB186 sourceC186 difference raw5376; decide +kernel
    rw [ha]
    exact (canonical5376 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA186 + difference 1 4) (sourceB186 + difference 4 1) sourceC186) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2196) := by
    have ha : (tripleCharges (sourceA186 + difference 1 4) (sourceB186 + difference 4 1) sourceC186) = raw5377 := by
      apply Matrix.ext; unfold tripleCharges sourceA186 sourceB186 sourceC186 difference raw5377; decide +kernel
    rw [ha]
    exact (canonical5377 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA186 + difference 1 5) (sourceB186 + difference 5 1) sourceC186) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2250) := by
    have ha : (tripleCharges (sourceA186 + difference 1 5) (sourceB186 + difference 5 1) sourceC186) = raw5378 := by
      apply Matrix.ext; unfold tripleCharges sourceA186 sourceB186 sourceC186 difference raw5378; decide +kernel
    rw [ha]
    exact (canonical5378 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA186 + difference 2 0) (sourceB186 + difference 0 2) sourceC186) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 825) := by
    have ha : (tripleCharges (sourceA186 + difference 2 0) (sourceB186 + difference 0 2) sourceC186) = raw5379 := by
      apply Matrix.ext; unfold tripleCharges sourceA186 sourceB186 sourceC186 difference raw5379; decide +kernel
    rw [ha]
    exact (canonical5379 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA186 + difference 2 1) (sourceB186 + difference 1 2) sourceC186) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1923) := by
    have ha : (tripleCharges (sourceA186 + difference 2 1) (sourceB186 + difference 1 2) sourceC186) = raw5380 := by
      apply Matrix.ext; unfold tripleCharges sourceA186 sourceB186 sourceC186 difference raw5380; decide +kernel
    rw [ha]
    exact (canonical5380 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA186 + difference 2 3) (sourceB186 + difference 3 2) sourceC186) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2108) := by
    have ha : (tripleCharges (sourceA186 + difference 2 3) (sourceB186 + difference 3 2) sourceC186) = raw5381 := by
      apply Matrix.ext; unfold tripleCharges sourceA186 sourceB186 sourceC186 difference raw5381; decide +kernel
    rw [ha]
    exact (canonical5381 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA186 + difference 2 4) (sourceB186 + difference 4 2) sourceC186) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2217) := by
    have ha : (tripleCharges (sourceA186 + difference 2 4) (sourceB186 + difference 4 2) sourceC186) = raw5382 := by
      apply Matrix.ext; unfold tripleCharges sourceA186 sourceB186 sourceC186 difference raw5382; decide +kernel
    rw [ha]
    exact (canonical5382 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA186 + difference 2 5) (sourceB186 + difference 5 2) sourceC186) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2274) := by
    have ha : (tripleCharges (sourceA186 + difference 2 5) (sourceB186 + difference 5 2) sourceC186) = raw5383 := by
      apply Matrix.ext; unfold tripleCharges sourceA186 sourceB186 sourceC186 difference raw5383; decide +kernel
    rw [ha]
    exact (canonical5383 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA186 + difference 3 0) (sourceB186 + difference 0 3) sourceC186) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 808) := by
    have ha : (tripleCharges (sourceA186 + difference 3 0) (sourceB186 + difference 0 3) sourceC186) = raw5384 := by
      apply Matrix.ext; unfold tripleCharges sourceA186 sourceB186 sourceC186 difference raw5384; decide +kernel
    rw [ha]
    exact (canonical5384 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA186 + difference 3 1) (sourceB186 + difference 1 3) sourceC186) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1910) := by
    have ha : (tripleCharges (sourceA186 + difference 3 1) (sourceB186 + difference 1 3) sourceC186) = raw5385 := by
      apply Matrix.ext; unfold tripleCharges sourceA186 sourceB186 sourceC186 difference raw5385; decide +kernel
    rw [ha]
    exact (canonical5385 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA186 + difference 3 2) (sourceB186 + difference 2 3) sourceC186) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2055) := by
    have ha : (tripleCharges (sourceA186 + difference 3 2) (sourceB186 + difference 2 3) sourceC186) = raw5386 := by
      apply Matrix.ext; unfold tripleCharges sourceA186 sourceB186 sourceC186 difference raw5386; decide +kernel
    rw [ha]
    exact (canonical5386 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA186 + difference 3 4) (sourceB186 + difference 4 3) sourceC186) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2207) := by
    have ha : (tripleCharges (sourceA186 + difference 3 4) (sourceB186 + difference 4 3) sourceC186) = raw5387 := by
      apply Matrix.ext; unfold tripleCharges sourceA186 sourceB186 sourceC186 difference raw5387; decide +kernel
    rw [ha]
    exact (canonical5387 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA186 + difference 3 5) (sourceB186 + difference 5 3) sourceC186) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2259) := by
    have ha : (tripleCharges (sourceA186 + difference 3 5) (sourceB186 + difference 5 3) sourceC186) = raw5388 := by
      apply Matrix.ext; unfold tripleCharges sourceA186 sourceB186 sourceC186 difference raw5388; decide +kernel
    rw [ha]
    exact (canonical5388 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA186 + difference 4 0) (sourceB186 + difference 0 4) sourceC186) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 796) := by
    have ha : (tripleCharges (sourceA186 + difference 4 0) (sourceB186 + difference 0 4) sourceC186) = raw5389 := by
      apply Matrix.ext; unfold tripleCharges sourceA186 sourceB186 sourceC186 difference raw5389; decide +kernel
    rw [ha]
    exact (canonical5389 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA186 + difference 4 1) (sourceB186 + difference 1 4) sourceC186) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1904) := by
    have ha : (tripleCharges (sourceA186 + difference 4 1) (sourceB186 + difference 1 4) sourceC186) = raw5390 := by
      apply Matrix.ext; unfold tripleCharges sourceA186 sourceB186 sourceC186 difference raw5390; decide +kernel
    rw [ha]
    exact (canonical5390 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA186 + difference 4 2) (sourceB186 + difference 2 4) sourceC186) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2039) := by
    have ha : (tripleCharges (sourceA186 + difference 4 2) (sourceB186 + difference 2 4) sourceC186) = raw5391 := by
      apply Matrix.ext; unfold tripleCharges sourceA186 sourceB186 sourceC186 difference raw5391; decide +kernel
    rw [ha]
    exact (canonical5391 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA186 + difference 4 3) (sourceB186 + difference 3 4) sourceC186) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2094) := by
    have ha : (tripleCharges (sourceA186 + difference 4 3) (sourceB186 + difference 3 4) sourceC186) = raw5392 := by
      apply Matrix.ext; unfold tripleCharges sourceA186 sourceB186 sourceC186 difference raw5392; decide +kernel
    rw [ha]
    exact (canonical5392 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA186 + difference 4 5) (sourceB186 + difference 5 4) sourceC186) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2251) := by
    have ha : (tripleCharges (sourceA186 + difference 4 5) (sourceB186 + difference 5 4) sourceC186) = raw5393 := by
      apply Matrix.ext; unfold tripleCharges sourceA186 sourceB186 sourceC186 difference raw5393; decide +kernel
    rw [ha]
    exact (canonical5393 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA186 + difference 5 0) (sourceB186 + difference 0 5) sourceC186) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 794) := by
    have ha : (tripleCharges (sourceA186 + difference 5 0) (sourceB186 + difference 0 5) sourceC186) = raw5394 := by
      apply Matrix.ext; unfold tripleCharges sourceA186 sourceB186 sourceC186 difference raw5394; decide +kernel
    rw [ha]
    exact (canonical5394 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA186 + difference 5 1) (sourceB186 + difference 1 5) sourceC186) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1902) := by
    have ha : (tripleCharges (sourceA186 + difference 5 1) (sourceB186 + difference 1 5) sourceC186) = raw5395 := by
      apply Matrix.ext; unfold tripleCharges sourceA186 sourceB186 sourceC186 difference raw5395; decide +kernel
    rw [ha]
    exact (canonical5395 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA186 + difference 5 2) (sourceB186 + difference 2 5) sourceC186) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2035) := by
    have ha : (tripleCharges (sourceA186 + difference 5 2) (sourceB186 + difference 2 5) sourceC186) = raw5396 := by
      apply Matrix.ext; unfold tripleCharges sourceA186 sourceB186 sourceC186 difference raw5396; decide +kernel
    rw [ha]
    exact (canonical5396 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA186 + difference 5 3) (sourceB186 + difference 3 5) sourceC186) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2090) := by
    have ha : (tripleCharges (sourceA186 + difference 5 3) (sourceB186 + difference 3 5) sourceC186) = raw5397 := by
      apply Matrix.ext; unfold tripleCharges sourceA186 sourceB186 sourceC186 difference raw5397; decide +kernel
    rw [ha]
    exact (canonical5397 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA186 + difference 5 4) (sourceB186 + difference 4 5) sourceC186) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2197) := by
    have ha : (tripleCharges (sourceA186 + difference 5 4) (sourceB186 + difference 4 5) sourceC186) = raw5398 := by
      apply Matrix.ext; unfold tripleCharges sourceA186 sourceB186 sourceC186 difference raw5398; decide +kernel
    rw [ha]
    exact (canonical5398 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA186 sourceB186 sourceC186
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm186, Integer.Sparse.eval]
  linarith only [hs]

def sourceA187 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB187 : Charge := ![3, 0, -1, -2, 0, 0]
def sourceC187 : Charge := ![0, 0, 1, 2, -1, -2]
def sourceForm187 : Integer.Sparse Master := [(Sum.inr 3222, 1), (Sum.inr 3803, 1), (Sum.inr 3809, 2), (Sum.inr 3814, 2), (Sum.inr 4092, -1)]

theorem sourceEq187 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm187 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA187 + difference 0 0) (sourceB187 + difference 0 0) sourceC187) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3222) := by
    have ha : (tripleCharges (sourceA187 + difference 0 0) (sourceB187 + difference 0 0) sourceC187) = raw5399 := by
      apply Matrix.ext; unfold tripleCharges sourceA187 sourceB187 sourceC187 difference raw5399; decide +kernel
    rw [ha]
    exact (canonical5399 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA187 + difference 0 1) (sourceB187 + difference 1 0) sourceC187) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3803) := by
    have ha : (tripleCharges (sourceA187 + difference 0 1) (sourceB187 + difference 1 0) sourceC187) = raw5400 := by
      apply Matrix.ext; unfold tripleCharges sourceA187 sourceB187 sourceC187 difference raw5400; decide +kernel
    rw [ha]
    exact (canonical5400 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA187 + difference 0 2) (sourceB187 + difference 2 0) sourceC187) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3814) := by
    have ha : (tripleCharges (sourceA187 + difference 0 2) (sourceB187 + difference 2 0) sourceC187) = raw5401 := by
      apply Matrix.ext; unfold tripleCharges sourceA187 sourceB187 sourceC187 difference raw5401; decide +kernel
    rw [ha]
    exact (canonical5401 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA187 + difference 0 3) (sourceB187 + difference 3 0) sourceC187) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3809) := by
    have ha : (tripleCharges (sourceA187 + difference 0 3) (sourceB187 + difference 3 0) sourceC187) = raw5402 := by
      apply Matrix.ext; unfold tripleCharges sourceA187 sourceB187 sourceC187 difference raw5402; decide +kernel
    rw [ha]
    exact (canonical5402 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA187 + difference 0 4) (sourceB187 + difference 4 0) sourceC187) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3814) := by
    have ha : (tripleCharges (sourceA187 + difference 0 4) (sourceB187 + difference 4 0) sourceC187) = raw5403 := by
      apply Matrix.ext; unfold tripleCharges sourceA187 sourceB187 sourceC187 difference raw5403; decide +kernel
    rw [ha]
    exact (canonical5403 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA187 + difference 0 5) (sourceB187 + difference 5 0) sourceC187) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3809) := by
    have ha : (tripleCharges (sourceA187 + difference 0 5) (sourceB187 + difference 5 0) sourceC187) = raw5404 := by
      apply Matrix.ext; unfold tripleCharges sourceA187 sourceB187 sourceC187 difference raw5404; decide +kernel
    rw [ha]
    exact (canonical5404 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA187 + sourceB187) sourceC187) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA187 + sourceB187) sourceC187) = raw5405 := by
      apply Matrix.ext; unfold doubleCharges sourceA187 sourceB187 sourceC187 raw5405; decide +kernel
    rw [ha]
    exact (canonical5405 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA187 sourceB187 sourceC187
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm187, Integer.Sparse.eval]
  linarith only [hs]

def sourceA188 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB188 : Charge := ![3, 0, -1, -2, 0, 0]
def sourceC188 : Charge := ![0, 0, 1, 2, -1, -2]
def sourceForm188 : Integer.Sparse Master := [(Sum.inr 1463, 1), (Sum.inr 1465, 2), (Sum.inr 1466, 2), (Sum.inr 3222, 1), (Sum.inr 4092, -1)]

theorem sourceEq188 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm188 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA188 + difference 0 0) (sourceB188 + difference 0 0) sourceC188) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3222) := by
    have ha : (tripleCharges (sourceA188 + difference 0 0) (sourceB188 + difference 0 0) sourceC188) = raw5399 := by
      apply Matrix.ext; unfold tripleCharges sourceA188 sourceB188 sourceC188 difference raw5399; decide +kernel
    rw [ha]
    exact (canonical5399 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA188 + difference 1 0) (sourceB188 + difference 0 1) sourceC188) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1463) := by
    have ha : (tripleCharges (sourceA188 + difference 1 0) (sourceB188 + difference 0 1) sourceC188) = raw5406 := by
      apply Matrix.ext; unfold tripleCharges sourceA188 sourceB188 sourceC188 difference raw5406; decide +kernel
    rw [ha]
    exact (canonical5406 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA188 + difference 2 0) (sourceB188 + difference 0 2) sourceC188) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1466) := by
    have ha : (tripleCharges (sourceA188 + difference 2 0) (sourceB188 + difference 0 2) sourceC188) = raw5407 := by
      apply Matrix.ext; unfold tripleCharges sourceA188 sourceB188 sourceC188 difference raw5407; decide +kernel
    rw [ha]
    exact (canonical5407 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA188 + difference 3 0) (sourceB188 + difference 0 3) sourceC188) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1465) := by
    have ha : (tripleCharges (sourceA188 + difference 3 0) (sourceB188 + difference 0 3) sourceC188) = raw5408 := by
      apply Matrix.ext; unfold tripleCharges sourceA188 sourceB188 sourceC188 difference raw5408; decide +kernel
    rw [ha]
    exact (canonical5408 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA188 + difference 4 0) (sourceB188 + difference 0 4) sourceC188) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1466) := by
    have ha : (tripleCharges (sourceA188 + difference 4 0) (sourceB188 + difference 0 4) sourceC188) = raw5409 := by
      apply Matrix.ext; unfold tripleCharges sourceA188 sourceB188 sourceC188 difference raw5409; decide +kernel
    rw [ha]
    exact (canonical5409 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA188 + difference 5 0) (sourceB188 + difference 0 5) sourceC188) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1465) := by
    have ha : (tripleCharges (sourceA188 + difference 5 0) (sourceB188 + difference 0 5) sourceC188) = raw5410 := by
      apply Matrix.ext; unfold tripleCharges sourceA188 sourceB188 sourceC188 difference raw5410; decide +kernel
    rw [ha]
    exact (canonical5410 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA188 + sourceB188) sourceC188) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA188 + sourceB188) sourceC188) = raw5405 := by
      apply Matrix.ext; unfold doubleCharges sourceA188 sourceB188 sourceC188 raw5405; decide +kernel
    rw [ha]
    exact (canonical5405 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA188 sourceB188 sourceC188
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm188, Integer.Sparse.eval]
  linarith only [hs]

def sourceA189 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB189 : Charge := ![3, 0, -1, -2, 0, 0]
def sourceC189 : Charge := ![0, 0, 1, 2, -1, -2]
def sourceForm189 : Integer.Sparse Master := [(Sum.inr 1463, 1), (Sum.inr 3170, 2), (Sum.inr 3196, 2), (Sum.inr 3222, 1), (Sum.inr 4092, -1)]

theorem sourceEq189 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm189 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA189 + difference 1 0) (sourceB189 + difference 0 1) sourceC189) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1463) := by
    have ha : (tripleCharges (sourceA189 + difference 1 0) (sourceB189 + difference 0 1) sourceC189) = raw5406 := by
      apply Matrix.ext; unfold tripleCharges sourceA189 sourceB189 sourceC189 difference raw5406; decide +kernel
    rw [ha]
    exact (canonical5406 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA189 + difference 1 1) (sourceB189 + difference 1 1) sourceC189) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3222) := by
    have ha : (tripleCharges (sourceA189 + difference 1 1) (sourceB189 + difference 1 1) sourceC189) = raw5399 := by
      apply Matrix.ext; unfold tripleCharges sourceA189 sourceB189 sourceC189 difference raw5399; decide +kernel
    rw [ha]
    exact (canonical5399 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA189 + difference 1 2) (sourceB189 + difference 2 1) sourceC189) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3196) := by
    have ha : (tripleCharges (sourceA189 + difference 1 2) (sourceB189 + difference 2 1) sourceC189) = raw5411 := by
      apply Matrix.ext; unfold tripleCharges sourceA189 sourceB189 sourceC189 difference raw5411; decide +kernel
    rw [ha]
    exact (canonical5411 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA189 + difference 1 3) (sourceB189 + difference 3 1) sourceC189) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3170) := by
    have ha : (tripleCharges (sourceA189 + difference 1 3) (sourceB189 + difference 3 1) sourceC189) = raw5412 := by
      apply Matrix.ext; unfold tripleCharges sourceA189 sourceB189 sourceC189 difference raw5412; decide +kernel
    rw [ha]
    exact (canonical5412 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA189 + difference 1 4) (sourceB189 + difference 4 1) sourceC189) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3196) := by
    have ha : (tripleCharges (sourceA189 + difference 1 4) (sourceB189 + difference 4 1) sourceC189) = raw5413 := by
      apply Matrix.ext; unfold tripleCharges sourceA189 sourceB189 sourceC189 difference raw5413; decide +kernel
    rw [ha]
    exact (canonical5413 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA189 + difference 1 5) (sourceB189 + difference 5 1) sourceC189) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3170) := by
    have ha : (tripleCharges (sourceA189 + difference 1 5) (sourceB189 + difference 5 1) sourceC189) = raw5414 := by
      apply Matrix.ext; unfold tripleCharges sourceA189 sourceB189 sourceC189 difference raw5414; decide +kernel
    rw [ha]
    exact (canonical5414 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA189 + sourceB189) sourceC189) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA189 + sourceB189) sourceC189) = raw5405 := by
      apply Matrix.ext; unfold doubleCharges sourceA189 sourceB189 sourceC189 raw5405; decide +kernel
    rw [ha]
    exact (canonical5405 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA189 sourceB189 sourceC189
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm189, Integer.Sparse.eval]
  linarith only [hs]

def sourceA190 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB190 : Charge := ![3, 0, -1, -2, 0, 0]
def sourceC190 : Charge := ![0, 0, 1, 2, -1, -2]
def sourceForm190 : Integer.Sparse Master := [(Sum.inr 2474, 2), (Sum.inr 3217, 2), (Sum.inr 3222, 1), (Sum.inr 3803, 1), (Sum.inr 4092, -1)]

theorem sourceEq190 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm190 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA190 + difference 0 1) (sourceB190 + difference 1 0) sourceC190) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3803) := by
    have ha : (tripleCharges (sourceA190 + difference 0 1) (sourceB190 + difference 1 0) sourceC190) = raw5400 := by
      apply Matrix.ext; unfold tripleCharges sourceA190 sourceB190 sourceC190 difference raw5400; decide +kernel
    rw [ha]
    exact (canonical5400 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA190 + difference 1 1) (sourceB190 + difference 1 1) sourceC190) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3222) := by
    have ha : (tripleCharges (sourceA190 + difference 1 1) (sourceB190 + difference 1 1) sourceC190) = raw5399 := by
      apply Matrix.ext; unfold tripleCharges sourceA190 sourceB190 sourceC190 difference raw5399; decide +kernel
    rw [ha]
    exact (canonical5399 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA190 + difference 2 1) (sourceB190 + difference 1 2) sourceC190) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3217) := by
    have ha : (tripleCharges (sourceA190 + difference 2 1) (sourceB190 + difference 1 2) sourceC190) = raw5415 := by
      apply Matrix.ext; unfold tripleCharges sourceA190 sourceB190 sourceC190 difference raw5415; decide +kernel
    rw [ha]
    exact (canonical5415 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA190 + difference 3 1) (sourceB190 + difference 1 3) sourceC190) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2474) := by
    have ha : (tripleCharges (sourceA190 + difference 3 1) (sourceB190 + difference 1 3) sourceC190) = raw5416 := by
      apply Matrix.ext; unfold tripleCharges sourceA190 sourceB190 sourceC190 difference raw5416; decide +kernel
    rw [ha]
    exact (canonical5416 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA190 + difference 4 1) (sourceB190 + difference 1 4) sourceC190) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3217) := by
    have ha : (tripleCharges (sourceA190 + difference 4 1) (sourceB190 + difference 1 4) sourceC190) = raw5417 := by
      apply Matrix.ext; unfold tripleCharges sourceA190 sourceB190 sourceC190 difference raw5417; decide +kernel
    rw [ha]
    exact (canonical5417 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA190 + difference 5 1) (sourceB190 + difference 1 5) sourceC190) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2474) := by
    have ha : (tripleCharges (sourceA190 + difference 5 1) (sourceB190 + difference 1 5) sourceC190) = raw5418 := by
      apply Matrix.ext; unfold tripleCharges sourceA190 sourceB190 sourceC190 difference raw5418; decide +kernel
    rw [ha]
    exact (canonical5418 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA190 + sourceB190) sourceC190) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA190 + sourceB190) sourceC190) = raw5405 := by
      apply Matrix.ext; unfold doubleCharges sourceA190 sourceB190 sourceC190 raw5405; decide +kernel
    rw [ha]
    exact (canonical5405 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA190 sourceB190 sourceC190
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm190, Integer.Sparse.eval]
  linarith only [hs]

def sourceA191 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB191 : Charge := ![3, 0, -1, -2, 0, 0]
def sourceC191 : Charge := ![0, 0, 1, 2, -1, -2]
def sourceForm191 : Integer.Sparse Master := [(Sum.inr 1466, 1), (Sum.inr 3174, 1), (Sum.inr 3180, 1), (Sum.inr 3198, 1), (Sum.inr 3217, 1), (Sum.inr 3222, 1), (Sum.inr 4092, -1)]

theorem sourceEq191 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm191 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA191 + difference 2 0) (sourceB191 + difference 0 2) sourceC191) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1466) := by
    have ha : (tripleCharges (sourceA191 + difference 2 0) (sourceB191 + difference 0 2) sourceC191) = raw5407 := by
      apply Matrix.ext; unfold tripleCharges sourceA191 sourceB191 sourceC191 difference raw5407; decide +kernel
    rw [ha]
    exact (canonical5407 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA191 + difference 2 1) (sourceB191 + difference 1 2) sourceC191) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3217) := by
    have ha : (tripleCharges (sourceA191 + difference 2 1) (sourceB191 + difference 1 2) sourceC191) = raw5415 := by
      apply Matrix.ext; unfold tripleCharges sourceA191 sourceB191 sourceC191 difference raw5415; decide +kernel
    rw [ha]
    exact (canonical5415 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA191 + difference 2 2) (sourceB191 + difference 2 2) sourceC191) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3222) := by
    have ha : (tripleCharges (sourceA191 + difference 2 2) (sourceB191 + difference 2 2) sourceC191) = raw5399 := by
      apply Matrix.ext; unfold tripleCharges sourceA191 sourceB191 sourceC191 difference raw5399; decide +kernel
    rw [ha]
    exact (canonical5399 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA191 + difference 2 3) (sourceB191 + difference 3 2) sourceC191) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3180) := by
    have ha : (tripleCharges (sourceA191 + difference 2 3) (sourceB191 + difference 3 2) sourceC191) = raw5419 := by
      apply Matrix.ext; unfold tripleCharges sourceA191 sourceB191 sourceC191 difference raw5419; decide +kernel
    rw [ha]
    exact (canonical5419 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA191 + difference 2 4) (sourceB191 + difference 4 2) sourceC191) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3198) := by
    have ha : (tripleCharges (sourceA191 + difference 2 4) (sourceB191 + difference 4 2) sourceC191) = raw5420 := by
      apply Matrix.ext; unfold tripleCharges sourceA191 sourceB191 sourceC191 difference raw5420; decide +kernel
    rw [ha]
    exact (canonical5420 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA191 + difference 2 5) (sourceB191 + difference 5 2) sourceC191) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3174) := by
    have ha : (tripleCharges (sourceA191 + difference 2 5) (sourceB191 + difference 5 2) sourceC191) = raw5421 := by
      apply Matrix.ext; unfold tripleCharges sourceA191 sourceB191 sourceC191 difference raw5421; decide +kernel
    rw [ha]
    exact (canonical5421 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA191 + sourceB191) sourceC191) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA191 + sourceB191) sourceC191) = raw5405 := by
      apply Matrix.ext; unfold doubleCharges sourceA191 sourceB191 sourceC191 raw5405; decide +kernel
    rw [ha]
    exact (canonical5405 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA191 sourceB191 sourceC191
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm191, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
