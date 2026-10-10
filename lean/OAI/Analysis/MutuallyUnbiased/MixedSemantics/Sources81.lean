import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical98
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical106
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical107
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical108
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical109
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical130
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical131
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical137
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical138
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical139
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical140
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical145
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical146
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical147
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical148
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical149
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical215
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical221
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical223
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical225
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical230
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical231
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical236
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical238
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical250
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical251
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical252
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical253
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical254
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical255
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical256
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical257
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical258
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical259
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical270
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical275
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical277
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical278
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical279
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical280
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical281
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical282
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical283
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical284
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical285
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical286

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA2592 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2592 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC2592 : Charge := ![0, 3, 0, -1, -1, -1]
def sourceForm2592 : Integer.Sparse Master := [(Sum.inr 2150, 1), (Sum.inr 2165, 1), (Sum.inr 2166, 2), (Sum.inr 2227, 1), (Sum.inr 2238, 1), (Sum.inr 2239, 1), (Sum.inr 2246, 1), (Sum.inr 2257, 2), (Sum.inr 2655, 1), (Sum.inr 2656, 2), (Sum.inr 2669, 2), (Sum.inr 2671, 1), (Sum.inr 2681, 2), (Sum.inr 2682, 2), (Sum.inr 2684, 2), (Sum.inr 2703, 1), (Sum.inr 2739, 2), (Sum.inr 2741, 1), (Sum.inr 3023, 1), (Sum.inr 3051, 2), (Sum.inr 3053, 1)]

theorem sourceEq2592 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2592 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2592 + difference 0 1) (sourceB2592 + difference 1 0) sourceC2592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2227) := by
    have ha : (tripleCharges (sourceA2592 + difference 0 1) (sourceB2592 + difference 1 0) sourceC2592) = raw35975 := by
      apply Matrix.ext; unfold tripleCharges sourceA2592 sourceB2592 sourceC2592 difference raw35975; decide +kernel
    rw [ha]
    exact (canonical35975 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2592 + difference 0 2) (sourceB2592 + difference 2 0) sourceC2592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2703) := by
    have ha : (tripleCharges (sourceA2592 + difference 0 2) (sourceB2592 + difference 2 0) sourceC2592) = raw35976 := by
      apply Matrix.ext; unfold tripleCharges sourceA2592 sourceB2592 sourceC2592 difference raw35976; decide +kernel
    rw [ha]
    exact (canonical35976 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2592 + difference 0 3) (sourceB2592 + difference 3 0) sourceC2592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2739) := by
    have ha : (tripleCharges (sourceA2592 + difference 0 3) (sourceB2592 + difference 3 0) sourceC2592) = raw35977 := by
      apply Matrix.ext; unfold tripleCharges sourceA2592 sourceB2592 sourceC2592 difference raw35977; decide +kernel
    rw [ha]
    exact (canonical35977 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2592 + difference 0 4) (sourceB2592 + difference 4 0) sourceC2592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2739) := by
    have ha : (tripleCharges (sourceA2592 + difference 0 4) (sourceB2592 + difference 4 0) sourceC2592) = raw35978 := by
      apply Matrix.ext; unfold tripleCharges sourceA2592 sourceB2592 sourceC2592 difference raw35978; decide +kernel
    rw [ha]
    exact (canonical35978 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2592 + difference 0 5) (sourceB2592 + difference 5 0) sourceC2592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2741) := by
    have ha : (tripleCharges (sourceA2592 + difference 0 5) (sourceB2592 + difference 5 0) sourceC2592) = raw35979 := by
      apply Matrix.ext; unfold tripleCharges sourceA2592 sourceB2592 sourceC2592 difference raw35979; decide +kernel
    rw [ha]
    exact (canonical35979 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2592 + difference 1 0) (sourceB2592 + difference 0 1) sourceC2592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2246) := by
    have ha : (tripleCharges (sourceA2592 + difference 1 0) (sourceB2592 + difference 0 1) sourceC2592) = raw35980 := by
      apply Matrix.ext; unfold tripleCharges sourceA2592 sourceB2592 sourceC2592 difference raw35980; decide +kernel
    rw [ha]
    exact (canonical35980 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2592 + difference 1 2) (sourceB2592 + difference 2 1) sourceC2592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3023) := by
    have ha : (tripleCharges (sourceA2592 + difference 1 2) (sourceB2592 + difference 2 1) sourceC2592) = raw35981 := by
      apply Matrix.ext; unfold tripleCharges sourceA2592 sourceB2592 sourceC2592 difference raw35981; decide +kernel
    rw [ha]
    exact (canonical35981 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2592 + difference 1 3) (sourceB2592 + difference 3 1) sourceC2592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3051) := by
    have ha : (tripleCharges (sourceA2592 + difference 1 3) (sourceB2592 + difference 3 1) sourceC2592) = raw35982 := by
      apply Matrix.ext; unfold tripleCharges sourceA2592 sourceB2592 sourceC2592 difference raw35982; decide +kernel
    rw [ha]
    exact (canonical35982 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2592 + difference 1 4) (sourceB2592 + difference 4 1) sourceC2592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3051) := by
    have ha : (tripleCharges (sourceA2592 + difference 1 4) (sourceB2592 + difference 4 1) sourceC2592) = raw35983 := by
      apply Matrix.ext; unfold tripleCharges sourceA2592 sourceB2592 sourceC2592 difference raw35983; decide +kernel
    rw [ha]
    exact (canonical35983 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2592 + difference 1 5) (sourceB2592 + difference 5 1) sourceC2592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3053) := by
    have ha : (tripleCharges (sourceA2592 + difference 1 5) (sourceB2592 + difference 5 1) sourceC2592) = raw35984 := by
      apply Matrix.ext; unfold tripleCharges sourceA2592 sourceB2592 sourceC2592 difference raw35984; decide +kernel
    rw [ha]
    exact (canonical35984 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2592 + difference 2 0) (sourceB2592 + difference 0 2) sourceC2592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2238) := by
    have ha : (tripleCharges (sourceA2592 + difference 2 0) (sourceB2592 + difference 0 2) sourceC2592) = raw35985 := by
      apply Matrix.ext; unfold tripleCharges sourceA2592 sourceB2592 sourceC2592 difference raw35985; decide +kernel
    rw [ha]
    exact (canonical35985 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2592 + difference 2 1) (sourceB2592 + difference 1 2) sourceC2592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2150) := by
    have ha : (tripleCharges (sourceA2592 + difference 2 1) (sourceB2592 + difference 1 2) sourceC2592) = raw35986 := by
      apply Matrix.ext; unfold tripleCharges sourceA2592 sourceB2592 sourceC2592 difference raw35986; decide +kernel
    rw [ha]
    exact (canonical35986 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2592 + difference 2 3) (sourceB2592 + difference 3 2) sourceC2592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2669) := by
    have ha : (tripleCharges (sourceA2592 + difference 2 3) (sourceB2592 + difference 3 2) sourceC2592) = raw35987 := by
      apply Matrix.ext; unfold tripleCharges sourceA2592 sourceB2592 sourceC2592 difference raw35987; decide +kernel
    rw [ha]
    exact (canonical35987 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2592 + difference 2 4) (sourceB2592 + difference 4 2) sourceC2592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2669) := by
    have ha : (tripleCharges (sourceA2592 + difference 2 4) (sourceB2592 + difference 4 2) sourceC2592) = raw35988 := by
      apply Matrix.ext; unfold tripleCharges sourceA2592 sourceB2592 sourceC2592 difference raw35988; decide +kernel
    rw [ha]
    exact (canonical35988 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2592 + difference 2 5) (sourceB2592 + difference 5 2) sourceC2592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2671) := by
    have ha : (tripleCharges (sourceA2592 + difference 2 5) (sourceB2592 + difference 5 2) sourceC2592) = raw35989 := by
      apply Matrix.ext; unfold tripleCharges sourceA2592 sourceB2592 sourceC2592 difference raw35989; decide +kernel
    rw [ha]
    exact (canonical35989 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2592 + difference 3 0) (sourceB2592 + difference 0 3) sourceC2592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2257) := by
    have ha : (tripleCharges (sourceA2592 + difference 3 0) (sourceB2592 + difference 0 3) sourceC2592) = raw35990 := by
      apply Matrix.ext; unfold tripleCharges sourceA2592 sourceB2592 sourceC2592 difference raw35990; decide +kernel
    rw [ha]
    exact (canonical35990 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2592 + difference 3 1) (sourceB2592 + difference 1 3) sourceC2592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2166) := by
    have ha : (tripleCharges (sourceA2592 + difference 3 1) (sourceB2592 + difference 1 3) sourceC2592) = raw35991 := by
      apply Matrix.ext; unfold tripleCharges sourceA2592 sourceB2592 sourceC2592 difference raw35991; decide +kernel
    rw [ha]
    exact (canonical35991 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2592 + difference 3 2) (sourceB2592 + difference 2 3) sourceC2592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2656) := by
    have ha : (tripleCharges (sourceA2592 + difference 3 2) (sourceB2592 + difference 2 3) sourceC2592) = raw35992 := by
      apply Matrix.ext; unfold tripleCharges sourceA2592 sourceB2592 sourceC2592 difference raw35992; decide +kernel
    rw [ha]
    exact (canonical35992 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2592 + difference 3 4) (sourceB2592 + difference 4 3) sourceC2592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2682) := by
    have ha : (tripleCharges (sourceA2592 + difference 3 4) (sourceB2592 + difference 4 3) sourceC2592) = raw35993 := by
      apply Matrix.ext; unfold tripleCharges sourceA2592 sourceB2592 sourceC2592 difference raw35993; decide +kernel
    rw [ha]
    exact (canonical35993 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2592 + difference 3 5) (sourceB2592 + difference 5 3) sourceC2592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2684) := by
    have ha : (tripleCharges (sourceA2592 + difference 3 5) (sourceB2592 + difference 5 3) sourceC2592) = raw35994 := by
      apply Matrix.ext; unfold tripleCharges sourceA2592 sourceB2592 sourceC2592 difference raw35994; decide +kernel
    rw [ha]
    exact (canonical35994 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2592 + difference 4 0) (sourceB2592 + difference 0 4) sourceC2592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2257) := by
    have ha : (tripleCharges (sourceA2592 + difference 4 0) (sourceB2592 + difference 0 4) sourceC2592) = raw35995 := by
      apply Matrix.ext; unfold tripleCharges sourceA2592 sourceB2592 sourceC2592 difference raw35995; decide +kernel
    rw [ha]
    exact (canonical35995 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2592 + difference 4 1) (sourceB2592 + difference 1 4) sourceC2592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2166) := by
    have ha : (tripleCharges (sourceA2592 + difference 4 1) (sourceB2592 + difference 1 4) sourceC2592) = raw35996 := by
      apply Matrix.ext; unfold tripleCharges sourceA2592 sourceB2592 sourceC2592 difference raw35996; decide +kernel
    rw [ha]
    exact (canonical35996 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2592 + difference 4 2) (sourceB2592 + difference 2 4) sourceC2592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2656) := by
    have ha : (tripleCharges (sourceA2592 + difference 4 2) (sourceB2592 + difference 2 4) sourceC2592) = raw35997 := by
      apply Matrix.ext; unfold tripleCharges sourceA2592 sourceB2592 sourceC2592 difference raw35997; decide +kernel
    rw [ha]
    exact (canonical35997 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2592 + difference 4 3) (sourceB2592 + difference 3 4) sourceC2592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2682) := by
    have ha : (tripleCharges (sourceA2592 + difference 4 3) (sourceB2592 + difference 3 4) sourceC2592) = raw35998 := by
      apply Matrix.ext; unfold tripleCharges sourceA2592 sourceB2592 sourceC2592 difference raw35998; decide +kernel
    rw [ha]
    exact (canonical35998 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2592 + difference 4 5) (sourceB2592 + difference 5 4) sourceC2592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2684) := by
    have ha : (tripleCharges (sourceA2592 + difference 4 5) (sourceB2592 + difference 5 4) sourceC2592) = raw35999 := by
      apply Matrix.ext; unfold tripleCharges sourceA2592 sourceB2592 sourceC2592 difference raw35999; decide +kernel
    rw [ha]
    exact (canonical35999 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2592 + difference 5 0) (sourceB2592 + difference 0 5) sourceC2592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2239) := by
    have ha : (tripleCharges (sourceA2592 + difference 5 0) (sourceB2592 + difference 0 5) sourceC2592) = raw36000 := by
      apply Matrix.ext; unfold tripleCharges sourceA2592 sourceB2592 sourceC2592 difference raw36000; decide +kernel
    rw [ha]
    exact (canonical36000 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2592 + difference 5 1) (sourceB2592 + difference 1 5) sourceC2592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2165) := by
    have ha : (tripleCharges (sourceA2592 + difference 5 1) (sourceB2592 + difference 1 5) sourceC2592) = raw36001 := by
      apply Matrix.ext; unfold tripleCharges sourceA2592 sourceB2592 sourceC2592 difference raw36001; decide +kernel
    rw [ha]
    exact (canonical36001 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2592 + difference 5 2) (sourceB2592 + difference 2 5) sourceC2592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2655) := by
    have ha : (tripleCharges (sourceA2592 + difference 5 2) (sourceB2592 + difference 2 5) sourceC2592) = raw36002 := by
      apply Matrix.ext; unfold tripleCharges sourceA2592 sourceB2592 sourceC2592 difference raw36002; decide +kernel
    rw [ha]
    exact (canonical36002 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2592 + difference 5 3) (sourceB2592 + difference 3 5) sourceC2592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2681) := by
    have ha : (tripleCharges (sourceA2592 + difference 5 3) (sourceB2592 + difference 3 5) sourceC2592) = raw36003 := by
      apply Matrix.ext; unfold tripleCharges sourceA2592 sourceB2592 sourceC2592 difference raw36003; decide +kernel
    rw [ha]
    exact (canonical36003 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2592 + difference 5 4) (sourceB2592 + difference 4 5) sourceC2592) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2681) := by
    have ha : (tripleCharges (sourceA2592 + difference 5 4) (sourceB2592 + difference 4 5) sourceC2592) = raw36004 := by
      apply Matrix.ext; unfold tripleCharges sourceA2592 sourceB2592 sourceC2592 difference raw36004; decide +kernel
    rw [ha]
    exact (canonical36004 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2592 sourceB2592 sourceC2592
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2592, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2593 : Charge := ![0, 3, 0, -1, -1, -1]
def sourceB2593 : Charge := ![2, -1, 0, 0, 0, -1]
def sourceC2593 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceForm2593 : Integer.Sparse Master := [(Sum.inr 4566, 1), (Sum.inr 4570, 1), (Sum.inr 4571, 2), (Sum.inr 4613, 1), (Sum.inr 5013, 1), (Sum.inr 5017, 1), (Sum.inr 5018, 2), (Sum.inr 5123, 1), (Sum.inr 5124, 2), (Sum.inr 5157, 1), (Sum.inr 5226, 2), (Sum.inr 5228, 2), (Sum.inr 5229, 2), (Sum.inr 5231, 1), (Sum.inr 5233, 2), (Sum.inr 5279, 1), (Sum.inr 5288, 2), (Sum.inr 5369, 1), (Sum.inr 5380, 1), (Sum.inr 5387, 1), (Sum.inr 5388, 2)]

theorem sourceEq2593 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2593 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2593 + difference 0 1) (sourceB2593 + difference 1 0) sourceC2593) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5369) := by
    have ha : (tripleCharges (sourceA2593 + difference 0 1) (sourceB2593 + difference 1 0) sourceC2593) = raw35576 := by
      apply Matrix.ext; unfold tripleCharges sourceA2593 sourceB2593 sourceC2593 difference raw35576; decide +kernel
    rw [ha]
    exact (canonical35576 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2593 + difference 0 2) (sourceB2593 + difference 2 0) sourceC2593) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5013) := by
    have ha : (tripleCharges (sourceA2593 + difference 0 2) (sourceB2593 + difference 2 0) sourceC2593) = raw36005 := by
      apply Matrix.ext; unfold tripleCharges sourceA2593 sourceB2593 sourceC2593 difference raw36005; decide +kernel
    rw [ha]
    exact (canonical36005 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2593 + difference 0 3) (sourceB2593 + difference 3 0) sourceC2593) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5018) := by
    have ha : (tripleCharges (sourceA2593 + difference 0 3) (sourceB2593 + difference 3 0) sourceC2593) = raw36006 := by
      apply Matrix.ext; unfold tripleCharges sourceA2593 sourceB2593 sourceC2593 difference raw36006; decide +kernel
    rw [ha]
    exact (canonical36006 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2593 + difference 0 4) (sourceB2593 + difference 4 0) sourceC2593) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5018) := by
    have ha : (tripleCharges (sourceA2593 + difference 0 4) (sourceB2593 + difference 4 0) sourceC2593) = raw36007 := by
      apply Matrix.ext; unfold tripleCharges sourceA2593 sourceB2593 sourceC2593 difference raw36007; decide +kernel
    rw [ha]
    exact (canonical36007 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2593 + difference 0 5) (sourceB2593 + difference 5 0) sourceC2593) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5017) := by
    have ha : (tripleCharges (sourceA2593 + difference 0 5) (sourceB2593 + difference 5 0) sourceC2593) = raw36008 := by
      apply Matrix.ext; unfold tripleCharges sourceA2593 sourceB2593 sourceC2593 difference raw36008; decide +kernel
    rw [ha]
    exact (canonical36008 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2593 + difference 1 0) (sourceB2593 + difference 0 1) sourceC2593) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4613) := by
    have ha : (tripleCharges (sourceA2593 + difference 1 0) (sourceB2593 + difference 0 1) sourceC2593) = raw36009 := by
      apply Matrix.ext; unfold tripleCharges sourceA2593 sourceB2593 sourceC2593 difference raw36009; decide +kernel
    rw [ha]
    exact (canonical36009 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2593 + difference 1 2) (sourceB2593 + difference 2 1) sourceC2593) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4566) := by
    have ha : (tripleCharges (sourceA2593 + difference 1 2) (sourceB2593 + difference 2 1) sourceC2593) = raw36010 := by
      apply Matrix.ext; unfold tripleCharges sourceA2593 sourceB2593 sourceC2593 difference raw36010; decide +kernel
    rw [ha]
    exact (canonical36010 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2593 + difference 1 3) (sourceB2593 + difference 3 1) sourceC2593) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4571) := by
    have ha : (tripleCharges (sourceA2593 + difference 1 3) (sourceB2593 + difference 3 1) sourceC2593) = raw36011 := by
      apply Matrix.ext; unfold tripleCharges sourceA2593 sourceB2593 sourceC2593 difference raw36011; decide +kernel
    rw [ha]
    exact (canonical36011 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2593 + difference 1 4) (sourceB2593 + difference 4 1) sourceC2593) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4571) := by
    have ha : (tripleCharges (sourceA2593 + difference 1 4) (sourceB2593 + difference 4 1) sourceC2593) = raw36012 := by
      apply Matrix.ext; unfold tripleCharges sourceA2593 sourceB2593 sourceC2593 difference raw36012; decide +kernel
    rw [ha]
    exact (canonical36012 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2593 + difference 1 5) (sourceB2593 + difference 5 1) sourceC2593) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4570) := by
    have ha : (tripleCharges (sourceA2593 + difference 1 5) (sourceB2593 + difference 5 1) sourceC2593) = raw36013 := by
      apply Matrix.ext; unfold tripleCharges sourceA2593 sourceB2593 sourceC2593 difference raw36013; decide +kernel
    rw [ha]
    exact (canonical36013 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2593 + difference 2 0) (sourceB2593 + difference 0 2) sourceC2593) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5157) := by
    have ha : (tripleCharges (sourceA2593 + difference 2 0) (sourceB2593 + difference 0 2) sourceC2593) = raw35825 := by
      apply Matrix.ext; unfold tripleCharges sourceA2593 sourceB2593 sourceC2593 difference raw35825; decide +kernel
    rw [ha]
    exact (canonical35825 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2593 + difference 2 1) (sourceB2593 + difference 1 2) sourceC2593) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5380) := by
    have ha : (tripleCharges (sourceA2593 + difference 2 1) (sourceB2593 + difference 1 2) sourceC2593) = raw35586 := by
      apply Matrix.ext; unfold tripleCharges sourceA2593 sourceB2593 sourceC2593 difference raw35586; decide +kernel
    rw [ha]
    exact (canonical35586 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2593 + difference 2 3) (sourceB2593 + difference 3 2) sourceC2593) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5124) := by
    have ha : (tripleCharges (sourceA2593 + difference 2 3) (sourceB2593 + difference 3 2) sourceC2593) = raw35826 := by
      apply Matrix.ext; unfold tripleCharges sourceA2593 sourceB2593 sourceC2593 difference raw35826; decide +kernel
    rw [ha]
    exact (canonical35826 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2593 + difference 2 4) (sourceB2593 + difference 4 2) sourceC2593) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5124) := by
    have ha : (tripleCharges (sourceA2593 + difference 2 4) (sourceB2593 + difference 4 2) sourceC2593) = raw35827 := by
      apply Matrix.ext; unfold tripleCharges sourceA2593 sourceB2593 sourceC2593 difference raw35827; decide +kernel
    rw [ha]
    exact (canonical35827 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2593 + difference 2 5) (sourceB2593 + difference 5 2) sourceC2593) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5123) := by
    have ha : (tripleCharges (sourceA2593 + difference 2 5) (sourceB2593 + difference 5 2) sourceC2593) = raw35828 := by
      apply Matrix.ext; unfold tripleCharges sourceA2593 sourceB2593 sourceC2593 difference raw35828; decide +kernel
    rw [ha]
    exact (canonical35828 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2593 + difference 3 0) (sourceB2593 + difference 0 3) sourceC2593) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5288) := by
    have ha : (tripleCharges (sourceA2593 + difference 3 0) (sourceB2593 + difference 0 3) sourceC2593) = raw36014 := by
      apply Matrix.ext; unfold tripleCharges sourceA2593 sourceB2593 sourceC2593 difference raw36014; decide +kernel
    rw [ha]
    exact (canonical36014 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2593 + difference 3 1) (sourceB2593 + difference 1 3) sourceC2593) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5388) := by
    have ha : (tripleCharges (sourceA2593 + difference 3 1) (sourceB2593 + difference 1 3) sourceC2593) = raw35591 := by
      apply Matrix.ext; unfold tripleCharges sourceA2593 sourceB2593 sourceC2593 difference raw35591; decide +kernel
    rw [ha]
    exact (canonical35591 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2593 + difference 3 2) (sourceB2593 + difference 2 3) sourceC2593) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5226) := by
    have ha : (tripleCharges (sourceA2593 + difference 3 2) (sourceB2593 + difference 2 3) sourceC2593) = raw36015 := by
      apply Matrix.ext; unfold tripleCharges sourceA2593 sourceB2593 sourceC2593 difference raw36015; decide +kernel
    rw [ha]
    exact (canonical36015 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2593 + difference 3 4) (sourceB2593 + difference 4 3) sourceC2593) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5229) := by
    have ha : (tripleCharges (sourceA2593 + difference 3 4) (sourceB2593 + difference 4 3) sourceC2593) = raw36016 := by
      apply Matrix.ext; unfold tripleCharges sourceA2593 sourceB2593 sourceC2593 difference raw36016; decide +kernel
    rw [ha]
    exact (canonical36016 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2593 + difference 3 5) (sourceB2593 + difference 5 3) sourceC2593) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5228) := by
    have ha : (tripleCharges (sourceA2593 + difference 3 5) (sourceB2593 + difference 5 3) sourceC2593) = raw36017 := by
      apply Matrix.ext; unfold tripleCharges sourceA2593 sourceB2593 sourceC2593 difference raw36017; decide +kernel
    rw [ha]
    exact (canonical36017 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2593 + difference 4 0) (sourceB2593 + difference 0 4) sourceC2593) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5288) := by
    have ha : (tripleCharges (sourceA2593 + difference 4 0) (sourceB2593 + difference 0 4) sourceC2593) = raw35619 := by
      apply Matrix.ext; unfold tripleCharges sourceA2593 sourceB2593 sourceC2593 difference raw35619; decide +kernel
    rw [ha]
    exact (canonical35619 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2593 + difference 4 1) (sourceB2593 + difference 1 4) sourceC2593) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5388) := by
    have ha : (tripleCharges (sourceA2593 + difference 4 1) (sourceB2593 + difference 1 4) sourceC2593) = raw35596 := by
      apply Matrix.ext; unfold tripleCharges sourceA2593 sourceB2593 sourceC2593 difference raw35596; decide +kernel
    rw [ha]
    exact (canonical35596 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2593 + difference 4 2) (sourceB2593 + difference 2 4) sourceC2593) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5226) := by
    have ha : (tripleCharges (sourceA2593 + difference 4 2) (sourceB2593 + difference 2 4) sourceC2593) = raw35620 := by
      apply Matrix.ext; unfold tripleCharges sourceA2593 sourceB2593 sourceC2593 difference raw35620; decide +kernel
    rw [ha]
    exact (canonical35620 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2593 + difference 4 3) (sourceB2593 + difference 3 4) sourceC2593) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5229) := by
    have ha : (tripleCharges (sourceA2593 + difference 4 3) (sourceB2593 + difference 3 4) sourceC2593) = raw35621 := by
      apply Matrix.ext; unfold tripleCharges sourceA2593 sourceB2593 sourceC2593 difference raw35621; decide +kernel
    rw [ha]
    exact (canonical35621 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2593 + difference 4 5) (sourceB2593 + difference 5 4) sourceC2593) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5228) := by
    have ha : (tripleCharges (sourceA2593 + difference 4 5) (sourceB2593 + difference 5 4) sourceC2593) = raw35622 := by
      apply Matrix.ext; unfold tripleCharges sourceA2593 sourceB2593 sourceC2593 difference raw35622; decide +kernel
    rw [ha]
    exact (canonical35622 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2593 + difference 5 0) (sourceB2593 + difference 0 5) sourceC2593) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5279) := by
    have ha : (tripleCharges (sourceA2593 + difference 5 0) (sourceB2593 + difference 0 5) sourceC2593) = raw35577 := by
      apply Matrix.ext; unfold tripleCharges sourceA2593 sourceB2593 sourceC2593 difference raw35577; decide +kernel
    rw [ha]
    exact (canonical35577 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2593 + difference 5 1) (sourceB2593 + difference 1 5) sourceC2593) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5387) := by
    have ha : (tripleCharges (sourceA2593 + difference 5 1) (sourceB2593 + difference 1 5) sourceC2593) = raw35636 := by
      apply Matrix.ext; unfold tripleCharges sourceA2593 sourceB2593 sourceC2593 difference raw35636; decide +kernel
    rw [ha]
    exact (canonical35636 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2593 + difference 5 2) (sourceB2593 + difference 2 5) sourceC2593) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5231) := by
    have ha : (tripleCharges (sourceA2593 + difference 5 2) (sourceB2593 + difference 2 5) sourceC2593) = raw35578 := by
      apply Matrix.ext; unfold tripleCharges sourceA2593 sourceB2593 sourceC2593 difference raw35578; decide +kernel
    rw [ha]
    exact (canonical35578 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2593 + difference 5 3) (sourceB2593 + difference 3 5) sourceC2593) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5233) := by
    have ha : (tripleCharges (sourceA2593 + difference 5 3) (sourceB2593 + difference 3 5) sourceC2593) = raw35579 := by
      apply Matrix.ext; unfold tripleCharges sourceA2593 sourceB2593 sourceC2593 difference raw35579; decide +kernel
    rw [ha]
    exact (canonical35579 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2593 + difference 5 4) (sourceB2593 + difference 4 5) sourceC2593) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5233) := by
    have ha : (tripleCharges (sourceA2593 + difference 5 4) (sourceB2593 + difference 4 5) sourceC2593) = raw35580 := by
      apply Matrix.ext; unfold tripleCharges sourceA2593 sourceB2593 sourceC2593 difference raw35580; decide +kernel
    rw [ha]
    exact (canonical35580 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2593 sourceB2593 sourceC2593
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2593, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2594 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2594 : Charge := ![0, 3, 0, -1, 0, -2]
def sourceC2594 : Charge := ![2, -1, 0, 0, -1, 0]
def sourceForm2594 : Integer.Sparse Master := [(Sum.inr 4376, 1), (Sum.inr 4377, 1), (Sum.inr 4378, 1), (Sum.inr 4381, 1), (Sum.inr 4452, 1), (Sum.inr 4714, 1), (Sum.inr 4719, 1), (Sum.inr 4744, 1), (Sum.inr 4845, 1), (Sum.inr 4981, 1), (Sum.inr 4983, 1), (Sum.inr 4984, 1), (Sum.inr 5045, 1), (Sum.inr 5046, 1), (Sum.inr 5070, 1), (Sum.inr 5123, 1), (Sum.inr 5125, 1), (Sum.inr 5163, 1), (Sum.inr 5204, 1), (Sum.inr 5227, 1), (Sum.inr 5228, 2), (Sum.inr 5237, 1), (Sum.inr 5238, 1), (Sum.inr 5290, 1), (Sum.inr 5291, 1), (Sum.inr 5397, 1), (Sum.inr 5411, 1), (Sum.inr 5443, 1), (Sum.inr 5450, 1)]

theorem sourceEq2594 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2594 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2594 + difference 0 1) (sourceB2594 + difference 1 0) sourceC2594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4452) := by
    have ha : (tripleCharges (sourceA2594 + difference 0 1) (sourceB2594 + difference 1 0) sourceC2594) = raw36018 := by
      apply Matrix.ext; unfold tripleCharges sourceA2594 sourceB2594 sourceC2594 difference raw36018; decide +kernel
    rw [ha]
    exact (canonical36018 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2594 + difference 0 2) (sourceB2594 + difference 2 0) sourceC2594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5070) := by
    have ha : (tripleCharges (sourceA2594 + difference 0 2) (sourceB2594 + difference 2 0) sourceC2594) = raw36019 := by
      apply Matrix.ext; unfold tripleCharges sourceA2594 sourceB2594 sourceC2594 difference raw36019; decide +kernel
    rw [ha]
    exact (canonical36019 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2594 + difference 0 3) (sourceB2594 + difference 3 0) sourceC2594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5291) := by
    have ha : (tripleCharges (sourceA2594 + difference 0 3) (sourceB2594 + difference 3 0) sourceC2594) = raw36020 := by
      apply Matrix.ext; unfold tripleCharges sourceA2594 sourceB2594 sourceC2594 difference raw36020; decide +kernel
    rw [ha]
    exact (canonical36020 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2594 + difference 0 4) (sourceB2594 + difference 4 0) sourceC2594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5163) := by
    have ha : (tripleCharges (sourceA2594 + difference 0 4) (sourceB2594 + difference 4 0) sourceC2594) = raw36021 := by
      apply Matrix.ext; unfold tripleCharges sourceA2594 sourceB2594 sourceC2594 difference raw36021; decide +kernel
    rw [ha]
    exact (canonical36021 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2594 + difference 0 5) (sourceB2594 + difference 5 0) sourceC2594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA2594 + difference 0 5) (sourceB2594 + difference 5 0) sourceC2594) = raw36022 := by
      apply Matrix.ext; unfold tripleCharges sourceA2594 sourceB2594 sourceC2594 difference raw36022; decide +kernel
    rw [ha]
    exact (canonical36022 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2594 + difference 1 0) (sourceB2594 + difference 0 1) sourceC2594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5204) := by
    have ha : (tripleCharges (sourceA2594 + difference 1 0) (sourceB2594 + difference 0 1) sourceC2594) = raw28354 := by
      apply Matrix.ext; unfold tripleCharges sourceA2594 sourceB2594 sourceC2594 difference raw28354; decide +kernel
    rw [ha]
    exact (canonical28354 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2594 + difference 1 2) (sourceB2594 + difference 2 1) sourceC2594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5397) := by
    have ha : (tripleCharges (sourceA2594 + difference 1 2) (sourceB2594 + difference 2 1) sourceC2594) = raw32628 := by
      apply Matrix.ext; unfold tripleCharges sourceA2594 sourceB2594 sourceC2594 difference raw32628; decide +kernel
    rw [ha]
    exact (canonical32628 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2594 + difference 1 3) (sourceB2594 + difference 3 1) sourceC2594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA2594 + difference 1 3) (sourceB2594 + difference 3 1) sourceC2594) = raw3315 := by
      apply Matrix.ext; unfold tripleCharges sourceA2594 sourceB2594 sourceC2594 difference raw3315; decide +kernel
    rw [ha]
    exact (canonical3315 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2594 + difference 1 4) (sourceB2594 + difference 4 1) sourceC2594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA2594 + difference 1 4) (sourceB2594 + difference 4 1) sourceC2594) = raw32629 := by
      apply Matrix.ext; unfold tripleCharges sourceA2594 sourceB2594 sourceC2594 difference raw32629; decide +kernel
    rw [ha]
    exact (canonical32629 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2594 + difference 1 5) (sourceB2594 + difference 5 1) sourceC2594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA2594 + difference 1 5) (sourceB2594 + difference 5 1) sourceC2594) = raw3305 := by
      apply Matrix.ext; unfold tripleCharges sourceA2594 sourceB2594 sourceC2594 difference raw3305; decide +kernel
    rw [ha]
    exact (canonical3305 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2594 + difference 2 0) (sourceB2594 + difference 0 2) sourceC2594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4981) := by
    have ha : (tripleCharges (sourceA2594 + difference 2 0) (sourceB2594 + difference 0 2) sourceC2594) = raw32634 := by
      apply Matrix.ext; unfold tripleCharges sourceA2594 sourceB2594 sourceC2594 difference raw32634; decide +kernel
    rw [ha]
    exact (canonical32634 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2594 + difference 2 1) (sourceB2594 + difference 1 2) sourceC2594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4376) := by
    have ha : (tripleCharges (sourceA2594 + difference 2 1) (sourceB2594 + difference 1 2) sourceC2594) = raw36023 := by
      apply Matrix.ext; unfold tripleCharges sourceA2594 sourceB2594 sourceC2594 difference raw36023; decide +kernel
    rw [ha]
    exact (canonical36023 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2594 + difference 2 3) (sourceB2594 + difference 3 2) sourceC2594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5228) := by
    have ha : (tripleCharges (sourceA2594 + difference 2 3) (sourceB2594 + difference 3 2) sourceC2594) = raw36024 := by
      apply Matrix.ext; unfold tripleCharges sourceA2594 sourceB2594 sourceC2594 difference raw36024; decide +kernel
    rw [ha]
    exact (canonical36024 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2594 + difference 2 4) (sourceB2594 + difference 4 2) sourceC2594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5123) := by
    have ha : (tripleCharges (sourceA2594 + difference 2 4) (sourceB2594 + difference 4 2) sourceC2594) = raw36025 := by
      apply Matrix.ext; unfold tripleCharges sourceA2594 sourceB2594 sourceC2594 difference raw36025; decide +kernel
    rw [ha]
    exact (canonical36025 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2594 + difference 2 5) (sourceB2594 + difference 5 2) sourceC2594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5227) := by
    have ha : (tripleCharges (sourceA2594 + difference 2 5) (sourceB2594 + difference 5 2) sourceC2594) = raw36026 := by
      apply Matrix.ext; unfold tripleCharges sourceA2594 sourceB2594 sourceC2594 difference raw36026; decide +kernel
    rw [ha]
    exact (canonical36026 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2594 + difference 3 0) (sourceB2594 + difference 0 3) sourceC2594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4984) := by
    have ha : (tripleCharges (sourceA2594 + difference 3 0) (sourceB2594 + difference 0 3) sourceC2594) = raw32638 := by
      apply Matrix.ext; unfold tripleCharges sourceA2594 sourceB2594 sourceC2594 difference raw32638; decide +kernel
    rw [ha]
    exact (canonical32638 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2594 + difference 3 1) (sourceB2594 + difference 1 3) sourceC2594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4378) := by
    have ha : (tripleCharges (sourceA2594 + difference 3 1) (sourceB2594 + difference 1 3) sourceC2594) = raw36027 := by
      apply Matrix.ext; unfold tripleCharges sourceA2594 sourceB2594 sourceC2594 difference raw36027; decide +kernel
    rw [ha]
    exact (canonical36027 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2594 + difference 3 2) (sourceB2594 + difference 2 3) sourceC2594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5045) := by
    have ha : (tripleCharges (sourceA2594 + difference 3 2) (sourceB2594 + difference 2 3) sourceC2594) = raw36028 := by
      apply Matrix.ext; unfold tripleCharges sourceA2594 sourceB2594 sourceC2594 difference raw36028; decide +kernel
    rw [ha]
    exact (canonical36028 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2594 + difference 3 4) (sourceB2594 + difference 4 3) sourceC2594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5125) := by
    have ha : (tripleCharges (sourceA2594 + difference 3 4) (sourceB2594 + difference 4 3) sourceC2594) = raw36029 := by
      apply Matrix.ext; unfold tripleCharges sourceA2594 sourceB2594 sourceC2594 difference raw36029; decide +kernel
    rw [ha]
    exact (canonical36029 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2594 + difference 3 5) (sourceB2594 + difference 5 3) sourceC2594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5228) := by
    have ha : (tripleCharges (sourceA2594 + difference 3 5) (sourceB2594 + difference 5 3) sourceC2594) = raw36030 := by
      apply Matrix.ext; unfold tripleCharges sourceA2594 sourceB2594 sourceC2594 difference raw36030; decide +kernel
    rw [ha]
    exact (canonical36030 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2594 + difference 4 0) (sourceB2594 + difference 0 4) sourceC2594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4983) := by
    have ha : (tripleCharges (sourceA2594 + difference 4 0) (sourceB2594 + difference 0 4) sourceC2594) = raw32643 := by
      apply Matrix.ext; unfold tripleCharges sourceA2594 sourceB2594 sourceC2594 difference raw32643; decide +kernel
    rw [ha]
    exact (canonical32643 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2594 + difference 4 1) (sourceB2594 + difference 1 4) sourceC2594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4381) := by
    have ha : (tripleCharges (sourceA2594 + difference 4 1) (sourceB2594 + difference 1 4) sourceC2594) = raw36031 := by
      apply Matrix.ext; unfold tripleCharges sourceA2594 sourceB2594 sourceC2594 difference raw36031; decide +kernel
    rw [ha]
    exact (canonical36031 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2594 + difference 4 2) (sourceB2594 + difference 2 4) sourceC2594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5046) := by
    have ha : (tripleCharges (sourceA2594 + difference 4 2) (sourceB2594 + difference 2 4) sourceC2594) = raw36032 := by
      apply Matrix.ext; unfold tripleCharges sourceA2594 sourceB2594 sourceC2594 difference raw36032; decide +kernel
    rw [ha]
    exact (canonical36032 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2594 + difference 4 3) (sourceB2594 + difference 3 4) sourceC2594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5238) := by
    have ha : (tripleCharges (sourceA2594 + difference 4 3) (sourceB2594 + difference 3 4) sourceC2594) = raw36033 := by
      apply Matrix.ext; unfold tripleCharges sourceA2594 sourceB2594 sourceC2594 difference raw36033; decide +kernel
    rw [ha]
    exact (canonical36033 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2594 + difference 4 5) (sourceB2594 + difference 5 4) sourceC2594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5237) := by
    have ha : (tripleCharges (sourceA2594 + difference 4 5) (sourceB2594 + difference 5 4) sourceC2594) = raw36034 := by
      apply Matrix.ext; unfold tripleCharges sourceA2594 sourceB2594 sourceC2594 difference raw36034; decide +kernel
    rw [ha]
    exact (canonical36034 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2594 + difference 5 0) (sourceB2594 + difference 0 5) sourceC2594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4719) := by
    have ha : (tripleCharges (sourceA2594 + difference 5 0) (sourceB2594 + difference 0 5) sourceC2594) = raw28351 := by
      apply Matrix.ext; unfold tripleCharges sourceA2594 sourceB2594 sourceC2594 difference raw28351; decide +kernel
    rw [ha]
    exact (canonical28351 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2594 + difference 5 1) (sourceB2594 + difference 1 5) sourceC2594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4377) := by
    have ha : (tripleCharges (sourceA2594 + difference 5 1) (sourceB2594 + difference 1 5) sourceC2594) = raw36035 := by
      apply Matrix.ext; unfold tripleCharges sourceA2594 sourceB2594 sourceC2594 difference raw36035; decide +kernel
    rw [ha]
    exact (canonical36035 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2594 + difference 5 2) (sourceB2594 + difference 2 5) sourceC2594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4714) := by
    have ha : (tripleCharges (sourceA2594 + difference 5 2) (sourceB2594 + difference 2 5) sourceC2594) = raw36036 := by
      apply Matrix.ext; unfold tripleCharges sourceA2594 sourceB2594 sourceC2594 difference raw36036; decide +kernel
    rw [ha]
    exact (canonical36036 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2594 + difference 5 3) (sourceB2594 + difference 3 5) sourceC2594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4845) := by
    have ha : (tripleCharges (sourceA2594 + difference 5 3) (sourceB2594 + difference 3 5) sourceC2594) = raw28337 := by
      apply Matrix.ext; unfold tripleCharges sourceA2594 sourceB2594 sourceC2594 difference raw28337; decide +kernel
    rw [ha]
    exact (canonical28337 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2594 + difference 5 4) (sourceB2594 + difference 4 5) sourceC2594) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4744) := by
    have ha : (tripleCharges (sourceA2594 + difference 5 4) (sourceB2594 + difference 4 5) sourceC2594) = raw36037 := by
      apply Matrix.ext; unfold tripleCharges sourceA2594 sourceB2594 sourceC2594 difference raw36037; decide +kernel
    rw [ha]
    exact (canonical36037 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2594 sourceB2594 sourceC2594
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2594, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2595 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2595 : Charge := ![2, -1, 0, 0, -1, 0]
def sourceC2595 : Charge := ![0, 3, 0, -1, 0, -2]
def sourceForm2595 : Integer.Sparse Master := [(Sum.inr 4676, 1), (Sum.inr 4681, 1), (Sum.inr 4684, 1), (Sum.inr 4688, 1), (Sum.inr 4698, 1), (Sum.inr 4699, 1), (Sum.inr 4700, 1), (Sum.inr 4703, 1), (Sum.inr 4834, 1), (Sum.inr 4880, 1), (Sum.inr 5035, 1), (Sum.inr 5110, 1), (Sum.inr 5140, 1), (Sum.inr 5215, 1), (Sum.inr 5216, 1), (Sum.inr 5219, 1), (Sum.inr 5220, 1), (Sum.inr 5228, 1), (Sum.inr 5229, 1), (Sum.inr 5232, 1), (Sum.inr 5233, 1), (Sum.inr 5238, 1), (Sum.inr 5241, 1), (Sum.inr 5254, 1), (Sum.inr 5258, 1), (Sum.inr 5259, 1), (Sum.inr 5266, 1), (Sum.inr 5267, 1), (Sum.inr 5274, 1), (Sum.inr 5302, 1)]

theorem sourceEq2595 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2595 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2595 + difference 0 1) (sourceB2595 + difference 1 0) sourceC2595) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4834) := by
    have ha : (tripleCharges (sourceA2595 + difference 0 1) (sourceB2595 + difference 1 0) sourceC2595) = raw36038 := by
      apply Matrix.ext; unfold tripleCharges sourceA2595 sourceB2595 sourceC2595 difference raw36038; decide +kernel
    rw [ha]
    exact (canonical36038 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2595 + difference 0 2) (sourceB2595 + difference 2 0) sourceC2595) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5241) := by
    have ha : (tripleCharges (sourceA2595 + difference 0 2) (sourceB2595 + difference 2 0) sourceC2595) = raw36039 := by
      apply Matrix.ext; unfold tripleCharges sourceA2595 sourceB2595 sourceC2595 difference raw36039; decide +kernel
    rw [ha]
    exact (canonical36039 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2595 + difference 0 3) (sourceB2595 + difference 3 0) sourceC2595) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA2595 + difference 0 3) (sourceB2595 + difference 3 0) sourceC2595) = raw36040 := by
      apply Matrix.ext; unfold tripleCharges sourceA2595 sourceB2595 sourceC2595 difference raw36040; decide +kernel
    rw [ha]
    exact (canonical36040 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2595 + difference 0 4) (sourceB2595 + difference 4 0) sourceC2595) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5274) := by
    have ha : (tripleCharges (sourceA2595 + difference 0 4) (sourceB2595 + difference 4 0) sourceC2595) = raw36041 := by
      apply Matrix.ext; unfold tripleCharges sourceA2595 sourceB2595 sourceC2595 difference raw36041; decide +kernel
    rw [ha]
    exact (canonical36041 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2595 + difference 0 5) (sourceB2595 + difference 5 0) sourceC2595) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA2595 + difference 0 5) (sourceB2595 + difference 5 0) sourceC2595) = raw36042 := by
      apply Matrix.ext; unfold tripleCharges sourceA2595 sourceB2595 sourceC2595 difference raw36042; decide +kernel
    rw [ha]
    exact (canonical36042 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2595 + difference 1 0) (sourceB2595 + difference 0 1) sourceC2595) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4880) := by
    have ha : (tripleCharges (sourceA2595 + difference 1 0) (sourceB2595 + difference 0 1) sourceC2595) = raw36043 := by
      apply Matrix.ext; unfold tripleCharges sourceA2595 sourceB2595 sourceC2595 difference raw36043; decide +kernel
    rw [ha]
    exact (canonical36043 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2595 + difference 1 2) (sourceB2595 + difference 2 1) sourceC2595) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5254) := by
    have ha : (tripleCharges (sourceA2595 + difference 1 2) (sourceB2595 + difference 2 1) sourceC2595) = raw36044 := by
      apply Matrix.ext; unfold tripleCharges sourceA2595 sourceB2595 sourceC2595 difference raw36044; decide +kernel
    rw [ha]
    exact (canonical36044 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2595 + difference 1 3) (sourceB2595 + difference 3 1) sourceC2595) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5267) := by
    have ha : (tripleCharges (sourceA2595 + difference 1 3) (sourceB2595 + difference 3 1) sourceC2595) = raw36045 := by
      apply Matrix.ext; unfold tripleCharges sourceA2595 sourceB2595 sourceC2595 difference raw36045; decide +kernel
    rw [ha]
    exact (canonical36045 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2595 + difference 1 4) (sourceB2595 + difference 4 1) sourceC2595) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA2595 + difference 1 4) (sourceB2595 + difference 4 1) sourceC2595) = raw36046 := by
      apply Matrix.ext; unfold tripleCharges sourceA2595 sourceB2595 sourceC2595 difference raw36046; decide +kernel
    rw [ha]
    exact (canonical36046 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2595 + difference 1 5) (sourceB2595 + difference 5 1) sourceC2595) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA2595 + difference 1 5) (sourceB2595 + difference 5 1) sourceC2595) = raw36047 := by
      apply Matrix.ext; unfold tripleCharges sourceA2595 sourceB2595 sourceC2595 difference raw36047; decide +kernel
    rw [ha]
    exact (canonical36047 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2595 + difference 2 0) (sourceB2595 + difference 0 2) sourceC2595) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4698) := by
    have ha : (tripleCharges (sourceA2595 + difference 2 0) (sourceB2595 + difference 0 2) sourceC2595) = raw36048 := by
      apply Matrix.ext; unfold tripleCharges sourceA2595 sourceB2595 sourceC2595 difference raw36048; decide +kernel
    rw [ha]
    exact (canonical36048 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2595 + difference 2 1) (sourceB2595 + difference 1 2) sourceC2595) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4676) := by
    have ha : (tripleCharges (sourceA2595 + difference 2 1) (sourceB2595 + difference 1 2) sourceC2595) = raw36049 := by
      apply Matrix.ext; unfold tripleCharges sourceA2595 sourceB2595 sourceC2595 difference raw36049; decide +kernel
    rw [ha]
    exact (canonical36049 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2595 + difference 2 3) (sourceB2595 + difference 3 2) sourceC2595) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5219) := by
    have ha : (tripleCharges (sourceA2595 + difference 2 3) (sourceB2595 + difference 3 2) sourceC2595) = raw36050 := by
      apply Matrix.ext; unfold tripleCharges sourceA2595 sourceB2595 sourceC2595 difference raw36050; decide +kernel
    rw [ha]
    exact (canonical36050 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2595 + difference 2 4) (sourceB2595 + difference 4 2) sourceC2595) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5228) := by
    have ha : (tripleCharges (sourceA2595 + difference 2 4) (sourceB2595 + difference 4 2) sourceC2595) = raw36051 := by
      apply Matrix.ext; unfold tripleCharges sourceA2595 sourceB2595 sourceC2595 difference raw36051; decide +kernel
    rw [ha]
    exact (canonical36051 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2595 + difference 2 5) (sourceB2595 + difference 5 2) sourceC2595) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5220) := by
    have ha : (tripleCharges (sourceA2595 + difference 2 5) (sourceB2595 + difference 5 2) sourceC2595) = raw36052 := by
      apply Matrix.ext; unfold tripleCharges sourceA2595 sourceB2595 sourceC2595 difference raw36052; decide +kernel
    rw [ha]
    exact (canonical36052 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2595 + difference 3 0) (sourceB2595 + difference 0 3) sourceC2595) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4703) := by
    have ha : (tripleCharges (sourceA2595 + difference 3 0) (sourceB2595 + difference 0 3) sourceC2595) = raw36053 := by
      apply Matrix.ext; unfold tripleCharges sourceA2595 sourceB2595 sourceC2595 difference raw36053; decide +kernel
    rw [ha]
    exact (canonical36053 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2595 + difference 3 1) (sourceB2595 + difference 1 3) sourceC2595) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4684) := by
    have ha : (tripleCharges (sourceA2595 + difference 3 1) (sourceB2595 + difference 1 3) sourceC2595) = raw36054 := by
      apply Matrix.ext; unfold tripleCharges sourceA2595 sourceB2595 sourceC2595 difference raw36054; decide +kernel
    rw [ha]
    exact (canonical36054 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2595 + difference 3 2) (sourceB2595 + difference 2 3) sourceC2595) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5215) := by
    have ha : (tripleCharges (sourceA2595 + difference 3 2) (sourceB2595 + difference 2 3) sourceC2595) = raw36055 := by
      apply Matrix.ext; unfold tripleCharges sourceA2595 sourceB2595 sourceC2595 difference raw36055; decide +kernel
    rw [ha]
    exact (canonical36055 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2595 + difference 3 4) (sourceB2595 + difference 4 3) sourceC2595) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5238) := by
    have ha : (tripleCharges (sourceA2595 + difference 3 4) (sourceB2595 + difference 4 3) sourceC2595) = raw36056 := by
      apply Matrix.ext; unfold tripleCharges sourceA2595 sourceB2595 sourceC2595 difference raw36056; decide +kernel
    rw [ha]
    exact (canonical36056 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2595 + difference 3 5) (sourceB2595 + difference 5 3) sourceC2595) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5229) := by
    have ha : (tripleCharges (sourceA2595 + difference 3 5) (sourceB2595 + difference 5 3) sourceC2595) = raw36057 := by
      apply Matrix.ext; unfold tripleCharges sourceA2595 sourceB2595 sourceC2595 difference raw36057; decide +kernel
    rw [ha]
    exact (canonical36057 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2595 + difference 4 0) (sourceB2595 + difference 0 4) sourceC2595) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4700) := by
    have ha : (tripleCharges (sourceA2595 + difference 4 0) (sourceB2595 + difference 0 4) sourceC2595) = raw36058 := by
      apply Matrix.ext; unfold tripleCharges sourceA2595 sourceB2595 sourceC2595 difference raw36058; decide +kernel
    rw [ha]
    exact (canonical36058 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2595 + difference 4 1) (sourceB2595 + difference 1 4) sourceC2595) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4688) := by
    have ha : (tripleCharges (sourceA2595 + difference 4 1) (sourceB2595 + difference 1 4) sourceC2595) = raw36059 := by
      apply Matrix.ext; unfold tripleCharges sourceA2595 sourceB2595 sourceC2595 difference raw36059; decide +kernel
    rw [ha]
    exact (canonical36059 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2595 + difference 4 2) (sourceB2595 + difference 2 4) sourceC2595) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5216) := by
    have ha : (tripleCharges (sourceA2595 + difference 4 2) (sourceB2595 + difference 2 4) sourceC2595) = raw36060 := by
      apply Matrix.ext; unfold tripleCharges sourceA2595 sourceB2595 sourceC2595 difference raw36060; decide +kernel
    rw [ha]
    exact (canonical36060 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2595 + difference 4 3) (sourceB2595 + difference 3 4) sourceC2595) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5232) := by
    have ha : (tripleCharges (sourceA2595 + difference 4 3) (sourceB2595 + difference 3 4) sourceC2595) = raw36061 := by
      apply Matrix.ext; unfold tripleCharges sourceA2595 sourceB2595 sourceC2595 difference raw36061; decide +kernel
    rw [ha]
    exact (canonical36061 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2595 + difference 4 5) (sourceB2595 + difference 5 4) sourceC2595) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5233) := by
    have ha : (tripleCharges (sourceA2595 + difference 4 5) (sourceB2595 + difference 5 4) sourceC2595) = raw36062 := by
      apply Matrix.ext; unfold tripleCharges sourceA2595 sourceB2595 sourceC2595 difference raw36062; decide +kernel
    rw [ha]
    exact (canonical36062 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2595 + difference 5 0) (sourceB2595 + difference 0 5) sourceC2595) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4699) := by
    have ha : (tripleCharges (sourceA2595 + difference 5 0) (sourceB2595 + difference 0 5) sourceC2595) = raw36063 := by
      apply Matrix.ext; unfold tripleCharges sourceA2595 sourceB2595 sourceC2595 difference raw36063; decide +kernel
    rw [ha]
    exact (canonical36063 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2595 + difference 5 1) (sourceB2595 + difference 1 5) sourceC2595) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4681) := by
    have ha : (tripleCharges (sourceA2595 + difference 5 1) (sourceB2595 + difference 1 5) sourceC2595) = raw36064 := by
      apply Matrix.ext; unfold tripleCharges sourceA2595 sourceB2595 sourceC2595 difference raw36064; decide +kernel
    rw [ha]
    exact (canonical36064 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2595 + difference 5 2) (sourceB2595 + difference 2 5) sourceC2595) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5035) := by
    have ha : (tripleCharges (sourceA2595 + difference 5 2) (sourceB2595 + difference 2 5) sourceC2595) = raw36065 := by
      apply Matrix.ext; unfold tripleCharges sourceA2595 sourceB2595 sourceC2595 difference raw36065; decide +kernel
    rw [ha]
    exact (canonical36065 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2595 + difference 5 3) (sourceB2595 + difference 3 5) sourceC2595) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5140) := by
    have ha : (tripleCharges (sourceA2595 + difference 5 3) (sourceB2595 + difference 3 5) sourceC2595) = raw36066 := by
      apply Matrix.ext; unfold tripleCharges sourceA2595 sourceB2595 sourceC2595 difference raw36066; decide +kernel
    rw [ha]
    exact (canonical36066 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2595 + difference 5 4) (sourceB2595 + difference 4 5) sourceC2595) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5110) := by
    have ha : (tripleCharges (sourceA2595 + difference 5 4) (sourceB2595 + difference 4 5) sourceC2595) = raw36067 := by
      apply Matrix.ext; unfold tripleCharges sourceA2595 sourceB2595 sourceC2595 difference raw36067; decide +kernel
    rw [ha]
    exact (canonical36067 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2595 sourceB2595 sourceC2595
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2595, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2596 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2596 : Charge := ![2, -1, 0, 0, -1, 0]
def sourceC2596 : Charge := ![0, 3, 0, -1, 0, -2]
def sourceForm2596 : Integer.Sparse Master := [(Sum.inr 2141, 1), (Sum.inr 2151, 1), (Sum.inr 2152, 1), (Sum.inr 2157, 1), (Sum.inr 2205, 1), (Sum.inr 2248, 1), (Sum.inr 2249, 1), (Sum.inr 2254, 1), (Sum.inr 2256, 1), (Sum.inr 2272, 1), (Sum.inr 2652, 1), (Sum.inr 2653, 1), (Sum.inr 2654, 1), (Sum.inr 2661, 1), (Sum.inr 2662, 1), (Sum.inr 2670, 1), (Sum.inr 2672, 1), (Sum.inr 2673, 1), (Sum.inr 2677, 1), (Sum.inr 2678, 1), (Sum.inr 2685, 1), (Sum.inr 2686, 1), (Sum.inr 2694, 1), (Sum.inr 2722, 1), (Sum.inr 2723, 1), (Sum.inr 2742, 1), (Sum.inr 3016, 1), (Sum.inr 3038, 1), (Sum.inr 3039, 1), (Sum.inr 3054, 1)]

theorem sourceEq2596 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2596 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2596 + difference 0 1) (sourceB2596 + difference 1 0) sourceC2596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2205) := by
    have ha : (tripleCharges (sourceA2596 + difference 0 1) (sourceB2596 + difference 1 0) sourceC2596) = raw36068 := by
      apply Matrix.ext; unfold tripleCharges sourceA2596 sourceB2596 sourceC2596 difference raw36068; decide +kernel
    rw [ha]
    exact (canonical36068 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2596 + difference 0 2) (sourceB2596 + difference 2 0) sourceC2596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2694) := by
    have ha : (tripleCharges (sourceA2596 + difference 0 2) (sourceB2596 + difference 2 0) sourceC2596) = raw36069 := by
      apply Matrix.ext; unfold tripleCharges sourceA2596 sourceB2596 sourceC2596 difference raw36069; decide +kernel
    rw [ha]
    exact (canonical36069 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2596 + difference 0 3) (sourceB2596 + difference 3 0) sourceC2596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA2596 + difference 0 3) (sourceB2596 + difference 3 0) sourceC2596) = raw36070 := by
      apply Matrix.ext; unfold tripleCharges sourceA2596 sourceB2596 sourceC2596 difference raw36070; decide +kernel
    rw [ha]
    exact (canonical36070 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2596 + difference 0 4) (sourceB2596 + difference 4 0) sourceC2596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2742) := by
    have ha : (tripleCharges (sourceA2596 + difference 0 4) (sourceB2596 + difference 4 0) sourceC2596) = raw36071 := by
      apply Matrix.ext; unfold tripleCharges sourceA2596 sourceB2596 sourceC2596 difference raw36071; decide +kernel
    rw [ha]
    exact (canonical36071 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2596 + difference 0 5) (sourceB2596 + difference 5 0) sourceC2596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA2596 + difference 0 5) (sourceB2596 + difference 5 0) sourceC2596) = raw36072 := by
      apply Matrix.ext; unfold tripleCharges sourceA2596 sourceB2596 sourceC2596 difference raw36072; decide +kernel
    rw [ha]
    exact (canonical36072 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2596 + difference 1 0) (sourceB2596 + difference 0 1) sourceC2596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2254) := by
    have ha : (tripleCharges (sourceA2596 + difference 1 0) (sourceB2596 + difference 0 1) sourceC2596) = raw36073 := by
      apply Matrix.ext; unfold tripleCharges sourceA2596 sourceB2596 sourceC2596 difference raw36073; decide +kernel
    rw [ha]
    exact (canonical36073 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2596 + difference 1 2) (sourceB2596 + difference 2 1) sourceC2596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3016) := by
    have ha : (tripleCharges (sourceA2596 + difference 1 2) (sourceB2596 + difference 2 1) sourceC2596) = raw36074 := by
      apply Matrix.ext; unfold tripleCharges sourceA2596 sourceB2596 sourceC2596 difference raw36074; decide +kernel
    rw [ha]
    exact (canonical36074 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2596 + difference 1 3) (sourceB2596 + difference 3 1) sourceC2596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3038) := by
    have ha : (tripleCharges (sourceA2596 + difference 1 3) (sourceB2596 + difference 3 1) sourceC2596) = raw36075 := by
      apply Matrix.ext; unfold tripleCharges sourceA2596 sourceB2596 sourceC2596 difference raw36075; decide +kernel
    rw [ha]
    exact (canonical36075 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2596 + difference 1 4) (sourceB2596 + difference 4 1) sourceC2596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3054) := by
    have ha : (tripleCharges (sourceA2596 + difference 1 4) (sourceB2596 + difference 4 1) sourceC2596) = raw36076 := by
      apply Matrix.ext; unfold tripleCharges sourceA2596 sourceB2596 sourceC2596 difference raw36076; decide +kernel
    rw [ha]
    exact (canonical36076 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2596 + difference 1 5) (sourceB2596 + difference 5 1) sourceC2596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3039) := by
    have ha : (tripleCharges (sourceA2596 + difference 1 5) (sourceB2596 + difference 5 1) sourceC2596) = raw36077 := by
      apply Matrix.ext; unfold tripleCharges sourceA2596 sourceB2596 sourceC2596 difference raw36077; decide +kernel
    rw [ha]
    exact (canonical36077 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2596 + difference 2 0) (sourceB2596 + difference 0 2) sourceC2596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2248) := by
    have ha : (tripleCharges (sourceA2596 + difference 2 0) (sourceB2596 + difference 0 2) sourceC2596) = raw36078 := by
      apply Matrix.ext; unfold tripleCharges sourceA2596 sourceB2596 sourceC2596 difference raw36078; decide +kernel
    rw [ha]
    exact (canonical36078 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2596 + difference 2 1) (sourceB2596 + difference 1 2) sourceC2596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2141) := by
    have ha : (tripleCharges (sourceA2596 + difference 2 1) (sourceB2596 + difference 1 2) sourceC2596) = raw36079 := by
      apply Matrix.ext; unfold tripleCharges sourceA2596 sourceB2596 sourceC2596 difference raw36079; decide +kernel
    rw [ha]
    exact (canonical36079 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2596 + difference 2 3) (sourceB2596 + difference 3 2) sourceC2596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2661) := by
    have ha : (tripleCharges (sourceA2596 + difference 2 3) (sourceB2596 + difference 3 2) sourceC2596) = raw36080 := by
      apply Matrix.ext; unfold tripleCharges sourceA2596 sourceB2596 sourceC2596 difference raw36080; decide +kernel
    rw [ha]
    exact (canonical36080 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2596 + difference 2 4) (sourceB2596 + difference 4 2) sourceC2596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2672) := by
    have ha : (tripleCharges (sourceA2596 + difference 2 4) (sourceB2596 + difference 4 2) sourceC2596) = raw36081 := by
      apply Matrix.ext; unfold tripleCharges sourceA2596 sourceB2596 sourceC2596 difference raw36081; decide +kernel
    rw [ha]
    exact (canonical36081 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2596 + difference 2 5) (sourceB2596 + difference 5 2) sourceC2596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2662) := by
    have ha : (tripleCharges (sourceA2596 + difference 2 5) (sourceB2596 + difference 5 2) sourceC2596) = raw36082 := by
      apply Matrix.ext; unfold tripleCharges sourceA2596 sourceB2596 sourceC2596 difference raw36082; decide +kernel
    rw [ha]
    exact (canonical36082 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2596 + difference 3 0) (sourceB2596 + difference 0 3) sourceC2596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2272) := by
    have ha : (tripleCharges (sourceA2596 + difference 3 0) (sourceB2596 + difference 0 3) sourceC2596) = raw36083 := by
      apply Matrix.ext; unfold tripleCharges sourceA2596 sourceB2596 sourceC2596 difference raw36083; decide +kernel
    rw [ha]
    exact (canonical36083 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2596 + difference 3 1) (sourceB2596 + difference 1 3) sourceC2596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2152) := by
    have ha : (tripleCharges (sourceA2596 + difference 3 1) (sourceB2596 + difference 1 3) sourceC2596) = raw36084 := by
      apply Matrix.ext; unfold tripleCharges sourceA2596 sourceB2596 sourceC2596 difference raw36084; decide +kernel
    rw [ha]
    exact (canonical36084 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2596 + difference 3 2) (sourceB2596 + difference 2 3) sourceC2596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2653) := by
    have ha : (tripleCharges (sourceA2596 + difference 3 2) (sourceB2596 + difference 2 3) sourceC2596) = raw36085 := by
      apply Matrix.ext; unfold tripleCharges sourceA2596 sourceB2596 sourceC2596 difference raw36085; decide +kernel
    rw [ha]
    exact (canonical36085 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2596 + difference 3 4) (sourceB2596 + difference 4 3) sourceC2596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2686) := by
    have ha : (tripleCharges (sourceA2596 + difference 3 4) (sourceB2596 + difference 4 3) sourceC2596) = raw36086 := by
      apply Matrix.ext; unfold tripleCharges sourceA2596 sourceB2596 sourceC2596 difference raw36086; decide +kernel
    rw [ha]
    exact (canonical36086 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2596 + difference 3 5) (sourceB2596 + difference 5 3) sourceC2596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2673) := by
    have ha : (tripleCharges (sourceA2596 + difference 3 5) (sourceB2596 + difference 5 3) sourceC2596) = raw36087 := by
      apply Matrix.ext; unfold tripleCharges sourceA2596 sourceB2596 sourceC2596 difference raw36087; decide +kernel
    rw [ha]
    exact (canonical36087 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2596 + difference 4 0) (sourceB2596 + difference 0 4) sourceC2596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2249) := by
    have ha : (tripleCharges (sourceA2596 + difference 4 0) (sourceB2596 + difference 0 4) sourceC2596) = raw36088 := by
      apply Matrix.ext; unfold tripleCharges sourceA2596 sourceB2596 sourceC2596 difference raw36088; decide +kernel
    rw [ha]
    exact (canonical36088 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2596 + difference 4 1) (sourceB2596 + difference 1 4) sourceC2596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2157) := by
    have ha : (tripleCharges (sourceA2596 + difference 4 1) (sourceB2596 + difference 1 4) sourceC2596) = raw36089 := by
      apply Matrix.ext; unfold tripleCharges sourceA2596 sourceB2596 sourceC2596 difference raw36089; decide +kernel
    rw [ha]
    exact (canonical36089 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2596 + difference 4 2) (sourceB2596 + difference 2 4) sourceC2596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2654) := by
    have ha : (tripleCharges (sourceA2596 + difference 4 2) (sourceB2596 + difference 2 4) sourceC2596) = raw36090 := by
      apply Matrix.ext; unfold tripleCharges sourceA2596 sourceB2596 sourceC2596 difference raw36090; decide +kernel
    rw [ha]
    exact (canonical36090 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2596 + difference 4 3) (sourceB2596 + difference 3 4) sourceC2596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2677) := by
    have ha : (tripleCharges (sourceA2596 + difference 4 3) (sourceB2596 + difference 3 4) sourceC2596) = raw36091 := by
      apply Matrix.ext; unfold tripleCharges sourceA2596 sourceB2596 sourceC2596 difference raw36091; decide +kernel
    rw [ha]
    exact (canonical36091 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2596 + difference 4 5) (sourceB2596 + difference 5 4) sourceC2596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2678) := by
    have ha : (tripleCharges (sourceA2596 + difference 4 5) (sourceB2596 + difference 5 4) sourceC2596) = raw36092 := by
      apply Matrix.ext; unfold tripleCharges sourceA2596 sourceB2596 sourceC2596 difference raw36092; decide +kernel
    rw [ha]
    exact (canonical36092 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2596 + difference 5 0) (sourceB2596 + difference 0 5) sourceC2596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2256) := by
    have ha : (tripleCharges (sourceA2596 + difference 5 0) (sourceB2596 + difference 0 5) sourceC2596) = raw36093 := by
      apply Matrix.ext; unfold tripleCharges sourceA2596 sourceB2596 sourceC2596 difference raw36093; decide +kernel
    rw [ha]
    exact (canonical36093 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2596 + difference 5 1) (sourceB2596 + difference 1 5) sourceC2596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2151) := by
    have ha : (tripleCharges (sourceA2596 + difference 5 1) (sourceB2596 + difference 1 5) sourceC2596) = raw36094 := by
      apply Matrix.ext; unfold tripleCharges sourceA2596 sourceB2596 sourceC2596 difference raw36094; decide +kernel
    rw [ha]
    exact (canonical36094 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2596 + difference 5 2) (sourceB2596 + difference 2 5) sourceC2596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2652) := by
    have ha : (tripleCharges (sourceA2596 + difference 5 2) (sourceB2596 + difference 2 5) sourceC2596) = raw36095 := by
      apply Matrix.ext; unfold tripleCharges sourceA2596 sourceB2596 sourceC2596 difference raw36095; decide +kernel
    rw [ha]
    exact (canonical36095 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2596 + difference 5 3) (sourceB2596 + difference 3 5) sourceC2596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2670) := by
    have ha : (tripleCharges (sourceA2596 + difference 5 3) (sourceB2596 + difference 3 5) sourceC2596) = raw36096 := by
      apply Matrix.ext; unfold tripleCharges sourceA2596 sourceB2596 sourceC2596 difference raw36096; decide +kernel
    rw [ha]
    exact (canonical36096 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2596 + difference 5 4) (sourceB2596 + difference 4 5) sourceC2596) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2685) := by
    have ha : (tripleCharges (sourceA2596 + difference 5 4) (sourceB2596 + difference 4 5) sourceC2596) = raw36097 := by
      apply Matrix.ext; unfold tripleCharges sourceA2596 sourceB2596 sourceC2596 difference raw36097; decide +kernel
    rw [ha]
    exact (canonical36097 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2596 sourceB2596 sourceC2596
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2596, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2597 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2597 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC2597 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceForm2597 : Integer.Sparse Master := [(Sum.inr 4947, 2), (Sum.inr 4948, 2), (Sum.inr 4949, 4), (Sum.inr 5115, 1), (Sum.inr 5172, 2), (Sum.inr 5177, 2), (Sum.inr 5373, 2), (Sum.inr 5390, 2), (Sum.inr 5404, 2), (Sum.inr 5416, 2), (Sum.inr 5418, 2), (Sum.inr 5442, 4), (Sum.inr 5462, 1), (Sum.inr 5485, 2)]

theorem sourceEq2597 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2597 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2597 + difference 0 1) (sourceB2597 + difference 1 0) sourceC2597) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5172) := by
    have ha : (tripleCharges (sourceA2597 + difference 0 1) (sourceB2597 + difference 1 0) sourceC2597) = raw36098 := by
      apply Matrix.ext; unfold tripleCharges sourceA2597 sourceB2597 sourceC2597 difference raw36098; decide +kernel
    rw [ha]
    exact (canonical36098 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2597 + difference 0 2) (sourceB2597 + difference 2 0) sourceC2597) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5416) := by
    have ha : (tripleCharges (sourceA2597 + difference 0 2) (sourceB2597 + difference 2 0) sourceC2597) = raw36099 := by
      apply Matrix.ext; unfold tripleCharges sourceA2597 sourceB2597 sourceC2597 difference raw36099; decide +kernel
    rw [ha]
    exact (canonical36099 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2597 + difference 0 3) (sourceB2597 + difference 3 0) sourceC2597) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5442) := by
    have ha : (tripleCharges (sourceA2597 + difference 0 3) (sourceB2597 + difference 3 0) sourceC2597) = raw17683 := by
      apply Matrix.ext; unfold tripleCharges sourceA2597 sourceB2597 sourceC2597 difference raw17683; decide +kernel
    rw [ha]
    exact (canonical17683 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2597 + difference 0 4) (sourceB2597 + difference 4 0) sourceC2597) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5442) := by
    have ha : (tripleCharges (sourceA2597 + difference 0 4) (sourceB2597 + difference 4 0) sourceC2597) = raw36100 := by
      apply Matrix.ext; unfold tripleCharges sourceA2597 sourceB2597 sourceC2597 difference raw36100; decide +kernel
    rw [ha]
    exact (canonical36100 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2597 + difference 0 5) (sourceB2597 + difference 5 0) sourceC2597) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA2597 + difference 0 5) (sourceB2597 + difference 5 0) sourceC2597) = raw18650 := by
      apply Matrix.ext; unfold tripleCharges sourceA2597 sourceB2597 sourceC2597 difference raw18650; decide +kernel
    rw [ha]
    exact (canonical18650 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2597 + difference 1 0) (sourceB2597 + difference 0 1) sourceC2597) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5172) := by
    have ha : (tripleCharges (sourceA2597 + difference 1 0) (sourceB2597 + difference 0 1) sourceC2597) = raw13592 := by
      apply Matrix.ext; unfold tripleCharges sourceA2597 sourceB2597 sourceC2597 difference raw13592; decide +kernel
    rw [ha]
    exact (canonical13592 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2597 + difference 1 2) (sourceB2597 + difference 2 1) sourceC2597) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5416) := by
    have ha : (tripleCharges (sourceA2597 + difference 1 2) (sourceB2597 + difference 2 1) sourceC2597) = raw17692 := by
      apply Matrix.ext; unfold tripleCharges sourceA2597 sourceB2597 sourceC2597 difference raw17692; decide +kernel
    rw [ha]
    exact (canonical17692 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2597 + difference 1 3) (sourceB2597 + difference 3 1) sourceC2597) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5442) := by
    have ha : (tripleCharges (sourceA2597 + difference 1 3) (sourceB2597 + difference 3 1) sourceC2597) = raw3055 := by
      apply Matrix.ext; unfold tripleCharges sourceA2597 sourceB2597 sourceC2597 difference raw3055; decide +kernel
    rw [ha]
    exact (canonical3055 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2597 + difference 1 4) (sourceB2597 + difference 4 1) sourceC2597) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5442) := by
    have ha : (tripleCharges (sourceA2597 + difference 1 4) (sourceB2597 + difference 4 1) sourceC2597) = raw17693 := by
      apply Matrix.ext; unfold tripleCharges sourceA2597 sourceB2597 sourceC2597 difference raw17693; decide +kernel
    rw [ha]
    exact (canonical17693 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2597 + difference 1 5) (sourceB2597 + difference 5 1) sourceC2597) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA2597 + difference 1 5) (sourceB2597 + difference 5 1) sourceC2597) = raw3045 := by
      apply Matrix.ext; unfold tripleCharges sourceA2597 sourceB2597 sourceC2597 difference raw3045; decide +kernel
    rw [ha]
    exact (canonical3045 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2597 + difference 2 0) (sourceB2597 + difference 0 2) sourceC2597) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4947) := by
    have ha : (tripleCharges (sourceA2597 + difference 2 0) (sourceB2597 + difference 0 2) sourceC2597) = raw32201 := by
      apply Matrix.ext; unfold tripleCharges sourceA2597 sourceB2597 sourceC2597 difference raw32201; decide +kernel
    rw [ha]
    exact (canonical32201 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2597 + difference 2 1) (sourceB2597 + difference 1 2) sourceC2597) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4947) := by
    have ha : (tripleCharges (sourceA2597 + difference 2 1) (sourceB2597 + difference 1 2) sourceC2597) = raw36101 := by
      apply Matrix.ext; unfold tripleCharges sourceA2597 sourceB2597 sourceC2597 difference raw36101; decide +kernel
    rw [ha]
    exact (canonical36101 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2597 + difference 2 3) (sourceB2597 + difference 3 2) sourceC2597) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5418) := by
    have ha : (tripleCharges (sourceA2597 + difference 2 3) (sourceB2597 + difference 3 2) sourceC2597) = raw17688 := by
      apply Matrix.ext; unfold tripleCharges sourceA2597 sourceB2597 sourceC2597 difference raw17688; decide +kernel
    rw [ha]
    exact (canonical17688 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2597 + difference 2 4) (sourceB2597 + difference 4 2) sourceC2597) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5418) := by
    have ha : (tripleCharges (sourceA2597 + difference 2 4) (sourceB2597 + difference 4 2) sourceC2597) = raw36102 := by
      apply Matrix.ext; unfold tripleCharges sourceA2597 sourceB2597 sourceC2597 difference raw36102; decide +kernel
    rw [ha]
    exact (canonical36102 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2597 + difference 2 5) (sourceB2597 + difference 5 2) sourceC2597) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5462) := by
    have ha : (tripleCharges (sourceA2597 + difference 2 5) (sourceB2597 + difference 5 2) sourceC2597) = raw18654 := by
      apply Matrix.ext; unfold tripleCharges sourceA2597 sourceB2597 sourceC2597 difference raw18654; decide +kernel
    rw [ha]
    exact (canonical18654 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2597 + difference 3 0) (sourceB2597 + difference 0 3) sourceC2597) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4949) := by
    have ha : (tripleCharges (sourceA2597 + difference 3 0) (sourceB2597 + difference 0 3) sourceC2597) = raw32203 := by
      apply Matrix.ext; unfold tripleCharges sourceA2597 sourceB2597 sourceC2597 difference raw32203; decide +kernel
    rw [ha]
    exact (canonical32203 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2597 + difference 3 1) (sourceB2597 + difference 1 3) sourceC2597) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4949) := by
    have ha : (tripleCharges (sourceA2597 + difference 3 1) (sourceB2597 + difference 1 3) sourceC2597) = raw36103 := by
      apply Matrix.ext; unfold tripleCharges sourceA2597 sourceB2597 sourceC2597 difference raw36103; decide +kernel
    rw [ha]
    exact (canonical36103 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2597 + difference 3 2) (sourceB2597 + difference 2 3) sourceC2597) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5373) := by
    have ha : (tripleCharges (sourceA2597 + difference 3 2) (sourceB2597 + difference 2 3) sourceC2597) = raw36104 := by
      apply Matrix.ext; unfold tripleCharges sourceA2597 sourceB2597 sourceC2597 difference raw36104; decide +kernel
    rw [ha]
    exact (canonical36104 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2597 + difference 3 4) (sourceB2597 + difference 4 3) sourceC2597) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5390) := by
    have ha : (tripleCharges (sourceA2597 + difference 3 4) (sourceB2597 + difference 4 3) sourceC2597) = raw36105 := by
      apply Matrix.ext; unfold tripleCharges sourceA2597 sourceB2597 sourceC2597 difference raw36105; decide +kernel
    rw [ha]
    exact (canonical36105 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2597 + difference 3 5) (sourceB2597 + difference 5 3) sourceC2597) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5404) := by
    have ha : (tripleCharges (sourceA2597 + difference 3 5) (sourceB2597 + difference 5 3) sourceC2597) = raw18657 := by
      apply Matrix.ext; unfold tripleCharges sourceA2597 sourceB2597 sourceC2597 difference raw18657; decide +kernel
    rw [ha]
    exact (canonical18657 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2597 + difference 4 0) (sourceB2597 + difference 0 4) sourceC2597) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4949) := by
    have ha : (tripleCharges (sourceA2597 + difference 4 0) (sourceB2597 + difference 0 4) sourceC2597) = raw32206 := by
      apply Matrix.ext; unfold tripleCharges sourceA2597 sourceB2597 sourceC2597 difference raw32206; decide +kernel
    rw [ha]
    exact (canonical32206 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2597 + difference 4 1) (sourceB2597 + difference 1 4) sourceC2597) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4949) := by
    have ha : (tripleCharges (sourceA2597 + difference 4 1) (sourceB2597 + difference 1 4) sourceC2597) = raw36106 := by
      apply Matrix.ext; unfold tripleCharges sourceA2597 sourceB2597 sourceC2597 difference raw36106; decide +kernel
    rw [ha]
    exact (canonical36106 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2597 + difference 4 2) (sourceB2597 + difference 2 4) sourceC2597) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5373) := by
    have ha : (tripleCharges (sourceA2597 + difference 4 2) (sourceB2597 + difference 2 4) sourceC2597) = raw36107 := by
      apply Matrix.ext; unfold tripleCharges sourceA2597 sourceB2597 sourceC2597 difference raw36107; decide +kernel
    rw [ha]
    exact (canonical36107 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2597 + difference 4 3) (sourceB2597 + difference 3 4) sourceC2597) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5390) := by
    have ha : (tripleCharges (sourceA2597 + difference 4 3) (sourceB2597 + difference 3 4) sourceC2597) = raw17695 := by
      apply Matrix.ext; unfold tripleCharges sourceA2597 sourceB2597 sourceC2597 difference raw17695; decide +kernel
    rw [ha]
    exact (canonical17695 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2597 + difference 4 5) (sourceB2597 + difference 5 4) sourceC2597) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5404) := by
    have ha : (tripleCharges (sourceA2597 + difference 4 5) (sourceB2597 + difference 5 4) sourceC2597) = raw18661 := by
      apply Matrix.ext; unfold tripleCharges sourceA2597 sourceB2597 sourceC2597 difference raw18661; decide +kernel
    rw [ha]
    exact (canonical18661 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2597 + difference 5 0) (sourceB2597 + difference 0 5) sourceC2597) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4948) := by
    have ha : (tripleCharges (sourceA2597 + difference 5 0) (sourceB2597 + difference 0 5) sourceC2597) = raw32208 := by
      apply Matrix.ext; unfold tripleCharges sourceA2597 sourceB2597 sourceC2597 difference raw32208; decide +kernel
    rw [ha]
    exact (canonical32208 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2597 + difference 5 1) (sourceB2597 + difference 1 5) sourceC2597) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4948) := by
    have ha : (tripleCharges (sourceA2597 + difference 5 1) (sourceB2597 + difference 1 5) sourceC2597) = raw36108 := by
      apply Matrix.ext; unfold tripleCharges sourceA2597 sourceB2597 sourceC2597 difference raw36108; decide +kernel
    rw [ha]
    exact (canonical36108 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2597 + difference 5 2) (sourceB2597 + difference 2 5) sourceC2597) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5115) := by
    have ha : (tripleCharges (sourceA2597 + difference 5 2) (sourceB2597 + difference 2 5) sourceC2597) = raw36109 := by
      apply Matrix.ext; unfold tripleCharges sourceA2597 sourceB2597 sourceC2597 difference raw36109; decide +kernel
    rw [ha]
    exact (canonical36109 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2597 + difference 5 3) (sourceB2597 + difference 3 5) sourceC2597) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5177) := by
    have ha : (tripleCharges (sourceA2597 + difference 5 3) (sourceB2597 + difference 3 5) sourceC2597) = raw17699 := by
      apply Matrix.ext; unfold tripleCharges sourceA2597 sourceB2597 sourceC2597 difference raw17699; decide +kernel
    rw [ha]
    exact (canonical17699 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2597 + difference 5 4) (sourceB2597 + difference 4 5) sourceC2597) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5177) := by
    have ha : (tripleCharges (sourceA2597 + difference 5 4) (sourceB2597 + difference 4 5) sourceC2597) = raw36110 := by
      apply Matrix.ext; unfold tripleCharges sourceA2597 sourceB2597 sourceC2597 difference raw36110; decide +kernel
    rw [ha]
    exact (canonical36110 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2597 sourceB2597 sourceC2597
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2597, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2598 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2598 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC2598 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceForm2598 : Integer.Sparse Master := [(Sum.inr 4767, 1), (Sum.inr 4769, 2), (Sum.inr 4811, 2), (Sum.inr 4939, 2), (Sum.inr 4946, 4), (Sum.inr 5168, 2), (Sum.inr 5337, 2), (Sum.inr 5356, 2), (Sum.inr 5393, 2), (Sum.inr 5416, 2), (Sum.inr 5434, 4), (Sum.inr 5464, 1), (Sum.inr 5465, 2), (Sum.inr 5486, 2)]

theorem sourceEq2598 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2598 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2598 + difference 0 1) (sourceB2598 + difference 1 0) sourceC2598) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5168) := by
    have ha : (tripleCharges (sourceA2598 + difference 0 1) (sourceB2598 + difference 1 0) sourceC2598) = raw36111 := by
      apply Matrix.ext; unfold tripleCharges sourceA2598 sourceB2598 sourceC2598 difference raw36111; decide +kernel
    rw [ha]
    exact (canonical36111 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2598 + difference 0 2) (sourceB2598 + difference 2 0) sourceC2598) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5416) := by
    have ha : (tripleCharges (sourceA2598 + difference 0 2) (sourceB2598 + difference 2 0) sourceC2598) = raw36112 := by
      apply Matrix.ext; unfold tripleCharges sourceA2598 sourceB2598 sourceC2598 difference raw36112; decide +kernel
    rw [ha]
    exact (canonical36112 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2598 + difference 0 3) (sourceB2598 + difference 3 0) sourceC2598) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA2598 + difference 0 3) (sourceB2598 + difference 3 0) sourceC2598) = raw36113 := by
      apply Matrix.ext; unfold tripleCharges sourceA2598 sourceB2598 sourceC2598 difference raw36113; decide +kernel
    rw [ha]
    exact (canonical36113 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2598 + difference 0 4) (sourceB2598 + difference 4 0) sourceC2598) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA2598 + difference 0 4) (sourceB2598 + difference 4 0) sourceC2598) = raw36114 := by
      apply Matrix.ext; unfold tripleCharges sourceA2598 sourceB2598 sourceC2598 difference raw36114; decide +kernel
    rw [ha]
    exact (canonical36114 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2598 + difference 0 5) (sourceB2598 + difference 5 0) sourceC2598) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5486) := by
    have ha : (tripleCharges (sourceA2598 + difference 0 5) (sourceB2598 + difference 5 0) sourceC2598) = raw19003 := by
      apply Matrix.ext; unfold tripleCharges sourceA2598 sourceB2598 sourceC2598 difference raw19003; decide +kernel
    rw [ha]
    exact (canonical19003 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2598 + difference 1 0) (sourceB2598 + difference 0 1) sourceC2598) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5168) := by
    have ha : (tripleCharges (sourceA2598 + difference 1 0) (sourceB2598 + difference 0 1) sourceC2598) = raw10101 := by
      apply Matrix.ext; unfold tripleCharges sourceA2598 sourceB2598 sourceC2598 difference raw10101; decide +kernel
    rw [ha]
    exact (canonical10101 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2598 + difference 1 2) (sourceB2598 + difference 2 1) sourceC2598) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5416) := by
    have ha : (tripleCharges (sourceA2598 + difference 1 2) (sourceB2598 + difference 2 1) sourceC2598) = raw19027 := by
      apply Matrix.ext; unfold tripleCharges sourceA2598 sourceB2598 sourceC2598 difference raw19027; decide +kernel
    rw [ha]
    exact (canonical19027 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2598 + difference 1 3) (sourceB2598 + difference 3 1) sourceC2598) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA2598 + difference 1 3) (sourceB2598 + difference 3 1) sourceC2598) = raw10085 := by
      apply Matrix.ext; unfold tripleCharges sourceA2598 sourceB2598 sourceC2598 difference raw10085; decide +kernel
    rw [ha]
    exact (canonical10085 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2598 + difference 1 4) (sourceB2598 + difference 4 1) sourceC2598) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA2598 + difference 1 4) (sourceB2598 + difference 4 1) sourceC2598) = raw19028 := by
      apply Matrix.ext; unfold tripleCharges sourceA2598 sourceB2598 sourceC2598 difference raw19028; decide +kernel
    rw [ha]
    exact (canonical19028 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2598 + difference 1 5) (sourceB2598 + difference 5 1) sourceC2598) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5486) := by
    have ha : (tripleCharges (sourceA2598 + difference 1 5) (sourceB2598 + difference 5 1) sourceC2598) = raw32044 := by
      apply Matrix.ext; unfold tripleCharges sourceA2598 sourceB2598 sourceC2598 difference raw32044; decide +kernel
    rw [ha]
    exact (canonical32044 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2598 + difference 2 0) (sourceB2598 + difference 0 2) sourceC2598) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4939) := by
    have ha : (tripleCharges (sourceA2598 + difference 2 0) (sourceB2598 + difference 0 2) sourceC2598) = raw32045 := by
      apply Matrix.ext; unfold tripleCharges sourceA2598 sourceB2598 sourceC2598 difference raw32045; decide +kernel
    rw [ha]
    exact (canonical32045 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2598 + difference 2 1) (sourceB2598 + difference 1 2) sourceC2598) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4939) := by
    have ha : (tripleCharges (sourceA2598 + difference 2 1) (sourceB2598 + difference 1 2) sourceC2598) = raw36115 := by
      apply Matrix.ext; unfold tripleCharges sourceA2598 sourceB2598 sourceC2598 difference raw36115; decide +kernel
    rw [ha]
    exact (canonical36115 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2598 + difference 2 3) (sourceB2598 + difference 3 2) sourceC2598) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5393) := by
    have ha : (tripleCharges (sourceA2598 + difference 2 3) (sourceB2598 + difference 3 2) sourceC2598) = raw36116 := by
      apply Matrix.ext; unfold tripleCharges sourceA2598 sourceB2598 sourceC2598 difference raw36116; decide +kernel
    rw [ha]
    exact (canonical36116 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2598 + difference 2 4) (sourceB2598 + difference 4 2) sourceC2598) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5393) := by
    have ha : (tripleCharges (sourceA2598 + difference 2 4) (sourceB2598 + difference 4 2) sourceC2598) = raw36117 := by
      apply Matrix.ext; unfold tripleCharges sourceA2598 sourceB2598 sourceC2598 difference raw36117; decide +kernel
    rw [ha]
    exact (canonical36117 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2598 + difference 2 5) (sourceB2598 + difference 5 2) sourceC2598) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5464) := by
    have ha : (tripleCharges (sourceA2598 + difference 2 5) (sourceB2598 + difference 5 2) sourceC2598) = raw19012 := by
      apply Matrix.ext; unfold tripleCharges sourceA2598 sourceB2598 sourceC2598 difference raw19012; decide +kernel
    rw [ha]
    exact (canonical19012 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2598 + difference 3 0) (sourceB2598 + difference 0 3) sourceC2598) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4946) := by
    have ha : (tripleCharges (sourceA2598 + difference 3 0) (sourceB2598 + difference 0 3) sourceC2598) = raw32047 := by
      apply Matrix.ext; unfold tripleCharges sourceA2598 sourceB2598 sourceC2598 difference raw32047; decide +kernel
    rw [ha]
    exact (canonical32047 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2598 + difference 3 1) (sourceB2598 + difference 1 3) sourceC2598) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4946) := by
    have ha : (tripleCharges (sourceA2598 + difference 3 1) (sourceB2598 + difference 1 3) sourceC2598) = raw36118 := by
      apply Matrix.ext; unfold tripleCharges sourceA2598 sourceB2598 sourceC2598 difference raw36118; decide +kernel
    rw [ha]
    exact (canonical36118 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2598 + difference 3 2) (sourceB2598 + difference 2 3) sourceC2598) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5337) := by
    have ha : (tripleCharges (sourceA2598 + difference 3 2) (sourceB2598 + difference 2 3) sourceC2598) = raw36119 := by
      apply Matrix.ext; unfold tripleCharges sourceA2598 sourceB2598 sourceC2598 difference raw36119; decide +kernel
    rw [ha]
    exact (canonical36119 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2598 + difference 3 4) (sourceB2598 + difference 4 3) sourceC2598) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5356) := by
    have ha : (tripleCharges (sourceA2598 + difference 3 4) (sourceB2598 + difference 4 3) sourceC2598) = raw36120 := by
      apply Matrix.ext; unfold tripleCharges sourceA2598 sourceB2598 sourceC2598 difference raw36120; decide +kernel
    rw [ha]
    exact (canonical36120 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2598 + difference 3 5) (sourceB2598 + difference 5 3) sourceC2598) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5465) := by
    have ha : (tripleCharges (sourceA2598 + difference 3 5) (sourceB2598 + difference 5 3) sourceC2598) = raw19017 := by
      apply Matrix.ext; unfold tripleCharges sourceA2598 sourceB2598 sourceC2598 difference raw19017; decide +kernel
    rw [ha]
    exact (canonical19017 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2598 + difference 4 0) (sourceB2598 + difference 0 4) sourceC2598) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4946) := by
    have ha : (tripleCharges (sourceA2598 + difference 4 0) (sourceB2598 + difference 0 4) sourceC2598) = raw32050 := by
      apply Matrix.ext; unfold tripleCharges sourceA2598 sourceB2598 sourceC2598 difference raw32050; decide +kernel
    rw [ha]
    exact (canonical32050 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2598 + difference 4 1) (sourceB2598 + difference 1 4) sourceC2598) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4946) := by
    have ha : (tripleCharges (sourceA2598 + difference 4 1) (sourceB2598 + difference 1 4) sourceC2598) = raw36121 := by
      apply Matrix.ext; unfold tripleCharges sourceA2598 sourceB2598 sourceC2598 difference raw36121; decide +kernel
    rw [ha]
    exact (canonical36121 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2598 + difference 4 2) (sourceB2598 + difference 2 4) sourceC2598) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5337) := by
    have ha : (tripleCharges (sourceA2598 + difference 4 2) (sourceB2598 + difference 2 4) sourceC2598) = raw36122 := by
      apply Matrix.ext; unfold tripleCharges sourceA2598 sourceB2598 sourceC2598 difference raw36122; decide +kernel
    rw [ha]
    exact (canonical36122 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2598 + difference 4 3) (sourceB2598 + difference 3 4) sourceC2598) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5356) := by
    have ha : (tripleCharges (sourceA2598 + difference 4 3) (sourceB2598 + difference 3 4) sourceC2598) = raw36123 := by
      apply Matrix.ext; unfold tripleCharges sourceA2598 sourceB2598 sourceC2598 difference raw36123; decide +kernel
    rw [ha]
    exact (canonical36123 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2598 + difference 4 5) (sourceB2598 + difference 5 4) sourceC2598) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5465) := by
    have ha : (tripleCharges (sourceA2598 + difference 4 5) (sourceB2598 + difference 5 4) sourceC2598) = raw19022 := by
      apply Matrix.ext; unfold tripleCharges sourceA2598 sourceB2598 sourceC2598 difference raw19022; decide +kernel
    rw [ha]
    exact (canonical19022 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2598 + difference 5 0) (sourceB2598 + difference 0 5) sourceC2598) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4769) := by
    have ha : (tripleCharges (sourceA2598 + difference 5 0) (sourceB2598 + difference 0 5) sourceC2598) = raw28893 := by
      apply Matrix.ext; unfold tripleCharges sourceA2598 sourceB2598 sourceC2598 difference raw28893; decide +kernel
    rw [ha]
    exact (canonical28893 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2598 + difference 5 1) (sourceB2598 + difference 1 5) sourceC2598) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4769) := by
    have ha : (tripleCharges (sourceA2598 + difference 5 1) (sourceB2598 + difference 1 5) sourceC2598) = raw36124 := by
      apply Matrix.ext; unfold tripleCharges sourceA2598 sourceB2598 sourceC2598 difference raw36124; decide +kernel
    rw [ha]
    exact (canonical36124 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2598 + difference 5 2) (sourceB2598 + difference 2 5) sourceC2598) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4767) := by
    have ha : (tripleCharges (sourceA2598 + difference 5 2) (sourceB2598 + difference 2 5) sourceC2598) = raw36125 := by
      apply Matrix.ext; unfold tripleCharges sourceA2598 sourceB2598 sourceC2598 difference raw36125; decide +kernel
    rw [ha]
    exact (canonical36125 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2598 + difference 5 3) (sourceB2598 + difference 3 5) sourceC2598) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4811) := by
    have ha : (tripleCharges (sourceA2598 + difference 5 3) (sourceB2598 + difference 3 5) sourceC2598) = raw28885 := by
      apply Matrix.ext; unfold tripleCharges sourceA2598 sourceB2598 sourceC2598 difference raw28885; decide +kernel
    rw [ha]
    exact (canonical28885 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2598 + difference 5 4) (sourceB2598 + difference 4 5) sourceC2598) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4811) := by
    have ha : (tripleCharges (sourceA2598 + difference 5 4) (sourceB2598 + difference 4 5) sourceC2598) = raw36126 := by
      apply Matrix.ext; unfold tripleCharges sourceA2598 sourceB2598 sourceC2598 difference raw36126; decide +kernel
    rw [ha]
    exact (canonical36126 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2598 sourceB2598 sourceC2598
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2598, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2599 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2599 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC2599 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceForm2599 : Integer.Sparse Master := [(Sum.inr 4941, 2), (Sum.inr 4943, 2), (Sum.inr 4946, 2), (Sum.inr 4950, 2), (Sum.inr 5039, 1), (Sum.inr 5081, 1), (Sum.inr 5169, 2), (Sum.inr 5177, 1), (Sum.inr 5337, 1), (Sum.inr 5356, 1), (Sum.inr 5418, 1), (Sum.inr 5457, 1), (Sum.inr 5460, 1), (Sum.inr 5464, 1), (Sum.inr 5465, 2), (Sum.inr 5466, 1), (Sum.inr 5476, 2), (Sum.inr 5483, 2), (Sum.inr 5486, 2), (Sum.inr 5487, 2)]

theorem sourceEq2599 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2599 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2599 + difference 0 1) (sourceB2599 + difference 1 0) sourceC2599) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA2599 + difference 0 1) (sourceB2599 + difference 1 0) sourceC2599) = raw36127 := by
      apply Matrix.ext; unfold tripleCharges sourceA2599 sourceB2599 sourceC2599 difference raw36127; decide +kernel
    rw [ha]
    exact (canonical36127 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2599 + difference 0 2) (sourceB2599 + difference 2 0) sourceC2599) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5476) := by
    have ha : (tripleCharges (sourceA2599 + difference 0 2) (sourceB2599 + difference 2 0) sourceC2599) = raw36128 := by
      apply Matrix.ext; unfold tripleCharges sourceA2599 sourceB2599 sourceC2599 difference raw36128; decide +kernel
    rw [ha]
    exact (canonical36128 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2599 + difference 0 3) (sourceB2599 + difference 3 0) sourceC2599) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5487) := by
    have ha : (tripleCharges (sourceA2599 + difference 0 3) (sourceB2599 + difference 3 0) sourceC2599) = raw17663 := by
      apply Matrix.ext; unfold tripleCharges sourceA2599 sourceB2599 sourceC2599 difference raw17663; decide +kernel
    rw [ha]
    exact (canonical17663 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2599 + difference 0 4) (sourceB2599 + difference 4 0) sourceC2599) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA2599 + difference 0 4) (sourceB2599 + difference 4 0) sourceC2599) = raw36129 := by
      apply Matrix.ext; unfold tripleCharges sourceA2599 sourceB2599 sourceC2599 difference raw36129; decide +kernel
    rw [ha]
    exact (canonical36129 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2599 + difference 0 5) (sourceB2599 + difference 5 0) sourceC2599) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5486) := by
    have ha : (tripleCharges (sourceA2599 + difference 0 5) (sourceB2599 + difference 5 0) sourceC2599) = raw36130 := by
      apply Matrix.ext; unfold tripleCharges sourceA2599 sourceB2599 sourceC2599 difference raw36130; decide +kernel
    rw [ha]
    exact (canonical36130 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2599 + difference 1 0) (sourceB2599 + difference 0 1) sourceC2599) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA2599 + difference 1 0) (sourceB2599 + difference 0 1) sourceC2599) = raw17671 := by
      apply Matrix.ext; unfold tripleCharges sourceA2599 sourceB2599 sourceC2599 difference raw17671; decide +kernel
    rw [ha]
    exact (canonical17671 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2599 + difference 1 2) (sourceB2599 + difference 2 1) sourceC2599) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5476) := by
    have ha : (tripleCharges (sourceA2599 + difference 1 2) (sourceB2599 + difference 2 1) sourceC2599) = raw17673 := by
      apply Matrix.ext; unfold tripleCharges sourceA2599 sourceB2599 sourceC2599 difference raw17673; decide +kernel
    rw [ha]
    exact (canonical17673 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2599 + difference 1 3) (sourceB2599 + difference 3 1) sourceC2599) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5487) := by
    have ha : (tripleCharges (sourceA2599 + difference 1 3) (sourceB2599 + difference 3 1) sourceC2599) = raw2772 := by
      apply Matrix.ext; unfold tripleCharges sourceA2599 sourceB2599 sourceC2599 difference raw2772; decide +kernel
    rw [ha]
    exact (canonical2772 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2599 + difference 1 4) (sourceB2599 + difference 4 1) sourceC2599) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA2599 + difference 1 4) (sourceB2599 + difference 4 1) sourceC2599) = raw2767 := by
      apply Matrix.ext; unfold tripleCharges sourceA2599 sourceB2599 sourceC2599 difference raw2767; decide +kernel
    rw [ha]
    exact (canonical2767 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2599 + difference 1 5) (sourceB2599 + difference 5 1) sourceC2599) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5486) := by
    have ha : (tripleCharges (sourceA2599 + difference 1 5) (sourceB2599 + difference 5 1) sourceC2599) = raw17674 := by
      apply Matrix.ext; unfold tripleCharges sourceA2599 sourceB2599 sourceC2599 difference raw17674; decide +kernel
    rw [ha]
    exact (canonical17674 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2599 + difference 2 0) (sourceB2599 + difference 0 2) sourceC2599) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4941) := by
    have ha : (tripleCharges (sourceA2599 + difference 2 0) (sourceB2599 + difference 0 2) sourceC2599) = raw36131 := by
      apply Matrix.ext; unfold tripleCharges sourceA2599 sourceB2599 sourceC2599 difference raw36131; decide +kernel
    rw [ha]
    exact (canonical36131 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2599 + difference 2 1) (sourceB2599 + difference 1 2) sourceC2599) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4941) := by
    have ha : (tripleCharges (sourceA2599 + difference 2 1) (sourceB2599 + difference 1 2) sourceC2599) = raw36132 := by
      apply Matrix.ext; unfold tripleCharges sourceA2599 sourceB2599 sourceC2599 difference raw36132; decide +kernel
    rw [ha]
    exact (canonical36132 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2599 + difference 2 3) (sourceB2599 + difference 3 2) sourceC2599) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5465) := by
    have ha : (tripleCharges (sourceA2599 + difference 2 3) (sourceB2599 + difference 3 2) sourceC2599) = raw17668 := by
      apply Matrix.ext; unfold tripleCharges sourceA2599 sourceB2599 sourceC2599 difference raw17668; decide +kernel
    rw [ha]
    exact (canonical17668 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2599 + difference 2 4) (sourceB2599 + difference 4 2) sourceC2599) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5460) := by
    have ha : (tripleCharges (sourceA2599 + difference 2 4) (sourceB2599 + difference 4 2) sourceC2599) = raw36133 := by
      apply Matrix.ext; unfold tripleCharges sourceA2599 sourceB2599 sourceC2599 difference raw36133; decide +kernel
    rw [ha]
    exact (canonical36133 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2599 + difference 2 5) (sourceB2599 + difference 5 2) sourceC2599) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5464) := by
    have ha : (tripleCharges (sourceA2599 + difference 2 5) (sourceB2599 + difference 5 2) sourceC2599) = raw36134 := by
      apply Matrix.ext; unfold tripleCharges sourceA2599 sourceB2599 sourceC2599 difference raw36134; decide +kernel
    rw [ha]
    exact (canonical36134 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2599 + difference 3 0) (sourceB2599 + difference 0 3) sourceC2599) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4946) := by
    have ha : (tripleCharges (sourceA2599 + difference 3 0) (sourceB2599 + difference 0 3) sourceC2599) = raw36135 := by
      apply Matrix.ext; unfold tripleCharges sourceA2599 sourceB2599 sourceC2599 difference raw36135; decide +kernel
    rw [ha]
    exact (canonical36135 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2599 + difference 3 1) (sourceB2599 + difference 1 3) sourceC2599) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4946) := by
    have ha : (tripleCharges (sourceA2599 + difference 3 1) (sourceB2599 + difference 1 3) sourceC2599) = raw36136 := by
      apply Matrix.ext; unfold tripleCharges sourceA2599 sourceB2599 sourceC2599 difference raw36136; decide +kernel
    rw [ha]
    exact (canonical36136 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2599 + difference 3 2) (sourceB2599 + difference 2 3) sourceC2599) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5337) := by
    have ha : (tripleCharges (sourceA2599 + difference 3 2) (sourceB2599 + difference 2 3) sourceC2599) = raw36137 := by
      apply Matrix.ext; unfold tripleCharges sourceA2599 sourceB2599 sourceC2599 difference raw36137; decide +kernel
    rw [ha]
    exact (canonical36137 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2599 + difference 3 4) (sourceB2599 + difference 4 3) sourceC2599) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5356) := by
    have ha : (tripleCharges (sourceA2599 + difference 3 4) (sourceB2599 + difference 4 3) sourceC2599) = raw36138 := by
      apply Matrix.ext; unfold tripleCharges sourceA2599 sourceB2599 sourceC2599 difference raw36138; decide +kernel
    rw [ha]
    exact (canonical36138 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2599 + difference 3 5) (sourceB2599 + difference 5 3) sourceC2599) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5418) := by
    have ha : (tripleCharges (sourceA2599 + difference 3 5) (sourceB2599 + difference 5 3) sourceC2599) = raw36139 := by
      apply Matrix.ext; unfold tripleCharges sourceA2599 sourceB2599 sourceC2599 difference raw36139; decide +kernel
    rw [ha]
    exact (canonical36139 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2599 + difference 4 0) (sourceB2599 + difference 0 4) sourceC2599) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4950) := by
    have ha : (tripleCharges (sourceA2599 + difference 4 0) (sourceB2599 + difference 0 4) sourceC2599) = raw29653 := by
      apply Matrix.ext; unfold tripleCharges sourceA2599 sourceB2599 sourceC2599 difference raw29653; decide +kernel
    rw [ha]
    exact (canonical29653 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2599 + difference 4 1) (sourceB2599 + difference 1 4) sourceC2599) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4950) := by
    have ha : (tripleCharges (sourceA2599 + difference 4 1) (sourceB2599 + difference 1 4) sourceC2599) = raw35229 := by
      apply Matrix.ext; unfold tripleCharges sourceA2599 sourceB2599 sourceC2599 difference raw35229; decide +kernel
    rw [ha]
    exact (canonical35229 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2599 + difference 4 2) (sourceB2599 + difference 2 4) sourceC2599) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5457) := by
    have ha : (tripleCharges (sourceA2599 + difference 4 2) (sourceB2599 + difference 2 4) sourceC2599) = raw35230 := by
      apply Matrix.ext; unfold tripleCharges sourceA2599 sourceB2599 sourceC2599 difference raw35230; decide +kernel
    rw [ha]
    exact (canonical35230 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2599 + difference 4 3) (sourceB2599 + difference 3 4) sourceC2599) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5466) := by
    have ha : (tripleCharges (sourceA2599 + difference 4 3) (sourceB2599 + difference 3 4) sourceC2599) = raw17676 := by
      apply Matrix.ext; unfold tripleCharges sourceA2599 sourceB2599 sourceC2599 difference raw17676; decide +kernel
    rw [ha]
    exact (canonical17676 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2599 + difference 4 5) (sourceB2599 + difference 5 4) sourceC2599) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5465) := by
    have ha : (tripleCharges (sourceA2599 + difference 4 5) (sourceB2599 + difference 5 4) sourceC2599) = raw35231 := by
      apply Matrix.ext; unfold tripleCharges sourceA2599 sourceB2599 sourceC2599 difference raw35231; decide +kernel
    rw [ha]
    exact (canonical35231 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2599 + difference 5 0) (sourceB2599 + difference 0 5) sourceC2599) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4943) := by
    have ha : (tripleCharges (sourceA2599 + difference 5 0) (sourceB2599 + difference 0 5) sourceC2599) = raw27588 := by
      apply Matrix.ext; unfold tripleCharges sourceA2599 sourceB2599 sourceC2599 difference raw27588; decide +kernel
    rw [ha]
    exact (canonical27588 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2599 + difference 5 1) (sourceB2599 + difference 1 5) sourceC2599) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4943) := by
    have ha : (tripleCharges (sourceA2599 + difference 5 1) (sourceB2599 + difference 1 5) sourceC2599) = raw36140 := by
      apply Matrix.ext; unfold tripleCharges sourceA2599 sourceB2599 sourceC2599 difference raw36140; decide +kernel
    rw [ha]
    exact (canonical36140 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2599 + difference 5 2) (sourceB2599 + difference 2 5) sourceC2599) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5039) := by
    have ha : (tripleCharges (sourceA2599 + difference 5 2) (sourceB2599 + difference 2 5) sourceC2599) = raw36141 := by
      apply Matrix.ext; unfold tripleCharges sourceA2599 sourceB2599 sourceC2599 difference raw36141; decide +kernel
    rw [ha]
    exact (canonical36141 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2599 + difference 5 3) (sourceB2599 + difference 3 5) sourceC2599) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5177) := by
    have ha : (tripleCharges (sourceA2599 + difference 5 3) (sourceB2599 + difference 3 5) sourceC2599) = raw17680 := by
      apply Matrix.ext; unfold tripleCharges sourceA2599 sourceB2599 sourceC2599 difference raw17680; decide +kernel
    rw [ha]
    exact (canonical17680 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2599 + difference 5 4) (sourceB2599 + difference 4 5) sourceC2599) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5081) := by
    have ha : (tripleCharges (sourceA2599 + difference 5 4) (sourceB2599 + difference 4 5) sourceC2599) = raw36142 := by
      apply Matrix.ext; unfold tripleCharges sourceA2599 sourceB2599 sourceC2599 difference raw36142; decide +kernel
    rw [ha]
    exact (canonical36142 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2599 sourceB2599 sourceC2599
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2599, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2600 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2600 : Charge := ![1, 1, 0, -1, 1, -2]
def sourceC2600 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceForm2600 : Integer.Sparse Master := [(Sum.inr 4725, 1), (Sum.inr 4726, 2), (Sum.inr 4750, 1), (Sum.inr 4875, 1), (Sum.inr 4936, 2), (Sum.inr 4937, 2), (Sum.inr 4949, 2), (Sum.inr 5163, 2), (Sum.inr 5319, 1), (Sum.inr 5330, 1), (Sum.inr 5373, 1), (Sum.inr 5390, 1), (Sum.inr 5391, 1), (Sum.inr 5401, 2), (Sum.inr 5404, 2), (Sum.inr 5411, 2), (Sum.inr 5418, 1), (Sum.inr 5451, 2), (Sum.inr 5462, 1), (Sum.inr 5485, 2)]

theorem sourceEq2600 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2600 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2600 + difference 0 1) (sourceB2600 + difference 1 0) sourceC2600) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5163) := by
    have ha : (tripleCharges (sourceA2600 + difference 0 1) (sourceB2600 + difference 1 0) sourceC2600) = raw36143 := by
      apply Matrix.ext; unfold tripleCharges sourceA2600 sourceB2600 sourceC2600 difference raw36143; decide +kernel
    rw [ha]
    exact (canonical36143 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2600 + difference 0 2) (sourceB2600 + difference 2 0) sourceC2600) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5401) := by
    have ha : (tripleCharges (sourceA2600 + difference 0 2) (sourceB2600 + difference 2 0) sourceC2600) = raw36144 := by
      apply Matrix.ext; unfold tripleCharges sourceA2600 sourceB2600 sourceC2600 difference raw36144; decide +kernel
    rw [ha]
    exact (canonical36144 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2600 + difference 0 3) (sourceB2600 + difference 3 0) sourceC2600) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA2600 + difference 0 3) (sourceB2600 + difference 3 0) sourceC2600) = raw36145 := by
      apply Matrix.ext; unfold tripleCharges sourceA2600 sourceB2600 sourceC2600 difference raw36145; decide +kernel
    rw [ha]
    exact (canonical36145 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2600 + difference 0 4) (sourceB2600 + difference 4 0) sourceC2600) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA2600 + difference 0 4) (sourceB2600 + difference 4 0) sourceC2600) = raw36146 := by
      apply Matrix.ext; unfold tripleCharges sourceA2600 sourceB2600 sourceC2600 difference raw36146; decide +kernel
    rw [ha]
    exact (canonical36146 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2600 + difference 0 5) (sourceB2600 + difference 5 0) sourceC2600) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA2600 + difference 0 5) (sourceB2600 + difference 5 0) sourceC2600) = raw36147 := by
      apply Matrix.ext; unfold tripleCharges sourceA2600 sourceB2600 sourceC2600 difference raw36147; decide +kernel
    rw [ha]
    exact (canonical36147 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2600 + difference 1 0) (sourceB2600 + difference 0 1) sourceC2600) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5163) := by
    have ha : (tripleCharges (sourceA2600 + difference 1 0) (sourceB2600 + difference 0 1) sourceC2600) = raw9608 := by
      apply Matrix.ext; unfold tripleCharges sourceA2600 sourceB2600 sourceC2600 difference raw9608; decide +kernel
    rw [ha]
    exact (canonical9608 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2600 + difference 1 2) (sourceB2600 + difference 2 1) sourceC2600) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5401) := by
    have ha : (tripleCharges (sourceA2600 + difference 1 2) (sourceB2600 + difference 2 1) sourceC2600) = raw32792 := by
      apply Matrix.ext; unfold tripleCharges sourceA2600 sourceB2600 sourceC2600 difference raw32792; decide +kernel
    rw [ha]
    exact (canonical32792 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2600 + difference 1 3) (sourceB2600 + difference 3 1) sourceC2600) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA2600 + difference 1 3) (sourceB2600 + difference 3 1) sourceC2600) = raw9592 := by
      apply Matrix.ext; unfold tripleCharges sourceA2600 sourceB2600 sourceC2600 difference raw9592; decide +kernel
    rw [ha]
    exact (canonical9592 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2600 + difference 1 4) (sourceB2600 + difference 4 1) sourceC2600) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA2600 + difference 1 4) (sourceB2600 + difference 4 1) sourceC2600) = raw32793 := by
      apply Matrix.ext; unfold tripleCharges sourceA2600 sourceB2600 sourceC2600 difference raw32793; decide +kernel
    rw [ha]
    exact (canonical32793 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2600 + difference 1 5) (sourceB2600 + difference 5 1) sourceC2600) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA2600 + difference 1 5) (sourceB2600 + difference 5 1) sourceC2600) = raw32794 := by
      apply Matrix.ext; unfold tripleCharges sourceA2600 sourceB2600 sourceC2600 difference raw32794; decide +kernel
    rw [ha]
    exact (canonical32794 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2600 + difference 2 0) (sourceB2600 + difference 0 2) sourceC2600) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4936) := by
    have ha : (tripleCharges (sourceA2600 + difference 2 0) (sourceB2600 + difference 0 2) sourceC2600) = raw32796 := by
      apply Matrix.ext; unfold tripleCharges sourceA2600 sourceB2600 sourceC2600 difference raw32796; decide +kernel
    rw [ha]
    exact (canonical32796 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2600 + difference 2 1) (sourceB2600 + difference 1 2) sourceC2600) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4936) := by
    have ha : (tripleCharges (sourceA2600 + difference 2 1) (sourceB2600 + difference 1 2) sourceC2600) = raw36148 := by
      apply Matrix.ext; unfold tripleCharges sourceA2600 sourceB2600 sourceC2600 difference raw36148; decide +kernel
    rw [ha]
    exact (canonical36148 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2600 + difference 2 3) (sourceB2600 + difference 3 2) sourceC2600) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5404) := by
    have ha : (tripleCharges (sourceA2600 + difference 2 3) (sourceB2600 + difference 3 2) sourceC2600) = raw36149 := by
      apply Matrix.ext; unfold tripleCharges sourceA2600 sourceB2600 sourceC2600 difference raw36149; decide +kernel
    rw [ha]
    exact (canonical36149 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2600 + difference 2 4) (sourceB2600 + difference 4 2) sourceC2600) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5391) := by
    have ha : (tripleCharges (sourceA2600 + difference 2 4) (sourceB2600 + difference 4 2) sourceC2600) = raw36150 := by
      apply Matrix.ext; unfold tripleCharges sourceA2600 sourceB2600 sourceC2600 difference raw36150; decide +kernel
    rw [ha]
    exact (canonical36150 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2600 + difference 2 5) (sourceB2600 + difference 5 2) sourceC2600) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5462) := by
    have ha : (tripleCharges (sourceA2600 + difference 2 5) (sourceB2600 + difference 5 2) sourceC2600) = raw36151 := by
      apply Matrix.ext; unfold tripleCharges sourceA2600 sourceB2600 sourceC2600 difference raw36151; decide +kernel
    rw [ha]
    exact (canonical36151 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2600 + difference 3 0) (sourceB2600 + difference 0 3) sourceC2600) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4937) := by
    have ha : (tripleCharges (sourceA2600 + difference 3 0) (sourceB2600 + difference 0 3) sourceC2600) = raw32800 := by
      apply Matrix.ext; unfold tripleCharges sourceA2600 sourceB2600 sourceC2600 difference raw32800; decide +kernel
    rw [ha]
    exact (canonical32800 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2600 + difference 3 1) (sourceB2600 + difference 1 3) sourceC2600) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4937) := by
    have ha : (tripleCharges (sourceA2600 + difference 3 1) (sourceB2600 + difference 1 3) sourceC2600) = raw36152 := by
      apply Matrix.ext; unfold tripleCharges sourceA2600 sourceB2600 sourceC2600 difference raw36152; decide +kernel
    rw [ha]
    exact (canonical36152 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2600 + difference 3 2) (sourceB2600 + difference 2 3) sourceC2600) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5319) := by
    have ha : (tripleCharges (sourceA2600 + difference 3 2) (sourceB2600 + difference 2 3) sourceC2600) = raw36153 := by
      apply Matrix.ext; unfold tripleCharges sourceA2600 sourceB2600 sourceC2600 difference raw36153; decide +kernel
    rw [ha]
    exact (canonical36153 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2600 + difference 3 4) (sourceB2600 + difference 4 3) sourceC2600) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5330) := by
    have ha : (tripleCharges (sourceA2600 + difference 3 4) (sourceB2600 + difference 4 3) sourceC2600) = raw36154 := by
      apply Matrix.ext; unfold tripleCharges sourceA2600 sourceB2600 sourceC2600 difference raw36154; decide +kernel
    rw [ha]
    exact (canonical36154 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2600 + difference 3 5) (sourceB2600 + difference 5 3) sourceC2600) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5404) := by
    have ha : (tripleCharges (sourceA2600 + difference 3 5) (sourceB2600 + difference 5 3) sourceC2600) = raw36155 := by
      apply Matrix.ext; unfold tripleCharges sourceA2600 sourceB2600 sourceC2600 difference raw36155; decide +kernel
    rw [ha]
    exact (canonical36155 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2600 + difference 4 0) (sourceB2600 + difference 0 4) sourceC2600) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4949) := by
    have ha : (tripleCharges (sourceA2600 + difference 4 0) (sourceB2600 + difference 0 4) sourceC2600) = raw29537 := by
      apply Matrix.ext; unfold tripleCharges sourceA2600 sourceB2600 sourceC2600 difference raw29537; decide +kernel
    rw [ha]
    exact (canonical29537 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2600 + difference 4 1) (sourceB2600 + difference 1 4) sourceC2600) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4949) := by
    have ha : (tripleCharges (sourceA2600 + difference 4 1) (sourceB2600 + difference 1 4) sourceC2600) = raw36156 := by
      apply Matrix.ext; unfold tripleCharges sourceA2600 sourceB2600 sourceC2600 difference raw36156; decide +kernel
    rw [ha]
    exact (canonical36156 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2600 + difference 4 2) (sourceB2600 + difference 2 4) sourceC2600) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5373) := by
    have ha : (tripleCharges (sourceA2600 + difference 4 2) (sourceB2600 + difference 2 4) sourceC2600) = raw36157 := by
      apply Matrix.ext; unfold tripleCharges sourceA2600 sourceB2600 sourceC2600 difference raw36157; decide +kernel
    rw [ha]
    exact (canonical36157 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2600 + difference 4 3) (sourceB2600 + difference 3 4) sourceC2600) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5390) := by
    have ha : (tripleCharges (sourceA2600 + difference 4 3) (sourceB2600 + difference 3 4) sourceC2600) = raw29528 := by
      apply Matrix.ext; unfold tripleCharges sourceA2600 sourceB2600 sourceC2600 difference raw29528; decide +kernel
    rw [ha]
    exact (canonical29528 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2600 + difference 4 5) (sourceB2600 + difference 5 4) sourceC2600) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5418) := by
    have ha : (tripleCharges (sourceA2600 + difference 4 5) (sourceB2600 + difference 5 4) sourceC2600) = raw36158 := by
      apply Matrix.ext; unfold tripleCharges sourceA2600 sourceB2600 sourceC2600 difference raw36158; decide +kernel
    rw [ha]
    exact (canonical36158 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2600 + difference 5 0) (sourceB2600 + difference 0 5) sourceC2600) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4726) := by
    have ha : (tripleCharges (sourceA2600 + difference 5 0) (sourceB2600 + difference 0 5) sourceC2600) = raw28625 := by
      apply Matrix.ext; unfold tripleCharges sourceA2600 sourceB2600 sourceC2600 difference raw28625; decide +kernel
    rw [ha]
    exact (canonical28625 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2600 + difference 5 1) (sourceB2600 + difference 1 5) sourceC2600) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4726) := by
    have ha : (tripleCharges (sourceA2600 + difference 5 1) (sourceB2600 + difference 1 5) sourceC2600) = raw36159 := by
      apply Matrix.ext; unfold tripleCharges sourceA2600 sourceB2600 sourceC2600 difference raw36159; decide +kernel
    rw [ha]
    exact (canonical36159 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2600 + difference 5 2) (sourceB2600 + difference 2 5) sourceC2600) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4725) := by
    have ha : (tripleCharges (sourceA2600 + difference 5 2) (sourceB2600 + difference 2 5) sourceC2600) = raw36160 := by
      apply Matrix.ext; unfold tripleCharges sourceA2600 sourceB2600 sourceC2600 difference raw36160; decide +kernel
    rw [ha]
    exact (canonical36160 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2600 + difference 5 3) (sourceB2600 + difference 3 5) sourceC2600) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4875) := by
    have ha : (tripleCharges (sourceA2600 + difference 5 3) (sourceB2600 + difference 3 5) sourceC2600) = raw28615 := by
      apply Matrix.ext; unfold tripleCharges sourceA2600 sourceB2600 sourceC2600 difference raw28615; decide +kernel
    rw [ha]
    exact (canonical28615 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2600 + difference 5 4) (sourceB2600 + difference 4 5) sourceC2600) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4750) := by
    have ha : (tripleCharges (sourceA2600 + difference 5 4) (sourceB2600 + difference 4 5) sourceC2600) = raw36161 := by
      apply Matrix.ext; unfold tripleCharges sourceA2600 sourceB2600 sourceC2600 difference raw36161; decide +kernel
    rw [ha]
    exact (canonical36161 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2600 sourceB2600 sourceC2600
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2600, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2601 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2601 : Charge := ![1, 1, 0, -1, 1, -2]
def sourceC2601 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceForm2601 : Integer.Sparse Master := [(Sum.inr 1879, 1), (Sum.inr 1880, 2), (Sum.inr 1929, 1), (Sum.inr 2116, 1), (Sum.inr 2328, 2), (Sum.inr 2329, 2), (Sum.inr 2341, 2), (Sum.inr 2590, 2), (Sum.inr 3642, 1), (Sum.inr 3661, 1), (Sum.inr 3709, 1), (Sum.inr 3741, 1), (Sum.inr 3776, 1), (Sum.inr 3787, 2), (Sum.inr 3790, 2), (Sum.inr 3813, 2), (Sum.inr 3888, 2), (Sum.inr 3928, 1), (Sum.inr 3933, 1), (Sum.inr 3998, 2)]

theorem sourceEq2601 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2601 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2601 + difference 0 1) (sourceB2601 + difference 1 0) sourceC2601) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2590) := by
    have ha : (tripleCharges (sourceA2601 + difference 0 1) (sourceB2601 + difference 1 0) sourceC2601) = raw36162 := by
      apply Matrix.ext; unfold tripleCharges sourceA2601 sourceB2601 sourceC2601 difference raw36162; decide +kernel
    rw [ha]
    exact (canonical36162 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2601 + difference 0 2) (sourceB2601 + difference 2 0) sourceC2601) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3787) := by
    have ha : (tripleCharges (sourceA2601 + difference 0 2) (sourceB2601 + difference 2 0) sourceC2601) = raw36163 := by
      apply Matrix.ext; unfold tripleCharges sourceA2601 sourceB2601 sourceC2601 difference raw36163; decide +kernel
    rw [ha]
    exact (canonical36163 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2601 + difference 0 3) (sourceB2601 + difference 3 0) sourceC2601) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3888) := by
    have ha : (tripleCharges (sourceA2601 + difference 0 3) (sourceB2601 + difference 3 0) sourceC2601) = raw36164 := by
      apply Matrix.ext; unfold tripleCharges sourceA2601 sourceB2601 sourceC2601 difference raw36164; decide +kernel
    rw [ha]
    exact (canonical36164 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2601 + difference 0 4) (sourceB2601 + difference 4 0) sourceC2601) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3813) := by
    have ha : (tripleCharges (sourceA2601 + difference 0 4) (sourceB2601 + difference 4 0) sourceC2601) = raw36165 := by
      apply Matrix.ext; unfold tripleCharges sourceA2601 sourceB2601 sourceC2601 difference raw36165; decide +kernel
    rw [ha]
    exact (canonical36165 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2601 + difference 0 5) (sourceB2601 + difference 5 0) sourceC2601) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3998) := by
    have ha : (tripleCharges (sourceA2601 + difference 0 5) (sourceB2601 + difference 5 0) sourceC2601) = raw36166 := by
      apply Matrix.ext; unfold tripleCharges sourceA2601 sourceB2601 sourceC2601 difference raw36166; decide +kernel
    rw [ha]
    exact (canonical36166 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2601 + difference 1 0) (sourceB2601 + difference 0 1) sourceC2601) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2590) := by
    have ha : (tripleCharges (sourceA2601 + difference 1 0) (sourceB2601 + difference 0 1) sourceC2601) = raw9638 := by
      apply Matrix.ext; unfold tripleCharges sourceA2601 sourceB2601 sourceC2601 difference raw9638; decide +kernel
    rw [ha]
    exact (canonical9638 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2601 + difference 1 2) (sourceB2601 + difference 2 1) sourceC2601) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3787) := by
    have ha : (tripleCharges (sourceA2601 + difference 1 2) (sourceB2601 + difference 2 1) sourceC2601) = raw32805 := by
      apply Matrix.ext; unfold tripleCharges sourceA2601 sourceB2601 sourceC2601 difference raw32805; decide +kernel
    rw [ha]
    exact (canonical32805 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2601 + difference 1 3) (sourceB2601 + difference 3 1) sourceC2601) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3888) := by
    have ha : (tripleCharges (sourceA2601 + difference 1 3) (sourceB2601 + difference 3 1) sourceC2601) = raw9622 := by
      apply Matrix.ext; unfold tripleCharges sourceA2601 sourceB2601 sourceC2601 difference raw9622; decide +kernel
    rw [ha]
    exact (canonical9622 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2601 + difference 1 4) (sourceB2601 + difference 4 1) sourceC2601) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3813) := by
    have ha : (tripleCharges (sourceA2601 + difference 1 4) (sourceB2601 + difference 4 1) sourceC2601) = raw32806 := by
      apply Matrix.ext; unfold tripleCharges sourceA2601 sourceB2601 sourceC2601 difference raw32806; decide +kernel
    rw [ha]
    exact (canonical32806 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2601 + difference 1 5) (sourceB2601 + difference 5 1) sourceC2601) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3998) := by
    have ha : (tripleCharges (sourceA2601 + difference 1 5) (sourceB2601 + difference 5 1) sourceC2601) = raw32807 := by
      apply Matrix.ext; unfold tripleCharges sourceA2601 sourceB2601 sourceC2601 difference raw32807; decide +kernel
    rw [ha]
    exact (canonical32807 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2601 + difference 2 0) (sourceB2601 + difference 0 2) sourceC2601) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2328) := by
    have ha : (tripleCharges (sourceA2601 + difference 2 0) (sourceB2601 + difference 0 2) sourceC2601) = raw32809 := by
      apply Matrix.ext; unfold tripleCharges sourceA2601 sourceB2601 sourceC2601 difference raw32809; decide +kernel
    rw [ha]
    exact (canonical32809 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2601 + difference 2 1) (sourceB2601 + difference 1 2) sourceC2601) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2328) := by
    have ha : (tripleCharges (sourceA2601 + difference 2 1) (sourceB2601 + difference 1 2) sourceC2601) = raw36167 := by
      apply Matrix.ext; unfold tripleCharges sourceA2601 sourceB2601 sourceC2601 difference raw36167; decide +kernel
    rw [ha]
    exact (canonical36167 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2601 + difference 2 3) (sourceB2601 + difference 3 2) sourceC2601) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3790) := by
    have ha : (tripleCharges (sourceA2601 + difference 2 3) (sourceB2601 + difference 3 2) sourceC2601) = raw36168 := by
      apply Matrix.ext; unfold tripleCharges sourceA2601 sourceB2601 sourceC2601 difference raw36168; decide +kernel
    rw [ha]
    exact (canonical36168 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2601 + difference 2 4) (sourceB2601 + difference 4 2) sourceC2601) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3776) := by
    have ha : (tripleCharges (sourceA2601 + difference 2 4) (sourceB2601 + difference 4 2) sourceC2601) = raw36169 := by
      apply Matrix.ext; unfold tripleCharges sourceA2601 sourceB2601 sourceC2601 difference raw36169; decide +kernel
    rw [ha]
    exact (canonical36169 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2601 + difference 2 5) (sourceB2601 + difference 5 2) sourceC2601) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3928) := by
    have ha : (tripleCharges (sourceA2601 + difference 2 5) (sourceB2601 + difference 5 2) sourceC2601) = raw36170 := by
      apply Matrix.ext; unfold tripleCharges sourceA2601 sourceB2601 sourceC2601 difference raw36170; decide +kernel
    rw [ha]
    exact (canonical36170 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2601 + difference 3 0) (sourceB2601 + difference 0 3) sourceC2601) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2329) := by
    have ha : (tripleCharges (sourceA2601 + difference 3 0) (sourceB2601 + difference 0 3) sourceC2601) = raw32813 := by
      apply Matrix.ext; unfold tripleCharges sourceA2601 sourceB2601 sourceC2601 difference raw32813; decide +kernel
    rw [ha]
    exact (canonical32813 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2601 + difference 3 1) (sourceB2601 + difference 1 3) sourceC2601) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2329) := by
    have ha : (tripleCharges (sourceA2601 + difference 3 1) (sourceB2601 + difference 1 3) sourceC2601) = raw36171 := by
      apply Matrix.ext; unfold tripleCharges sourceA2601 sourceB2601 sourceC2601 difference raw36171; decide +kernel
    rw [ha]
    exact (canonical36171 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2601 + difference 3 2) (sourceB2601 + difference 2 3) sourceC2601) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3642) := by
    have ha : (tripleCharges (sourceA2601 + difference 3 2) (sourceB2601 + difference 2 3) sourceC2601) = raw36172 := by
      apply Matrix.ext; unfold tripleCharges sourceA2601 sourceB2601 sourceC2601 difference raw36172; decide +kernel
    rw [ha]
    exact (canonical36172 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2601 + difference 3 4) (sourceB2601 + difference 4 3) sourceC2601) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3661) := by
    have ha : (tripleCharges (sourceA2601 + difference 3 4) (sourceB2601 + difference 4 3) sourceC2601) = raw36173 := by
      apply Matrix.ext; unfold tripleCharges sourceA2601 sourceB2601 sourceC2601 difference raw36173; decide +kernel
    rw [ha]
    exact (canonical36173 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2601 + difference 3 5) (sourceB2601 + difference 5 3) sourceC2601) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3790) := by
    have ha : (tripleCharges (sourceA2601 + difference 3 5) (sourceB2601 + difference 5 3) sourceC2601) = raw36174 := by
      apply Matrix.ext; unfold tripleCharges sourceA2601 sourceB2601 sourceC2601 difference raw36174; decide +kernel
    rw [ha]
    exact (canonical36174 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2601 + difference 4 0) (sourceB2601 + difference 0 4) sourceC2601) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2341) := by
    have ha : (tripleCharges (sourceA2601 + difference 4 0) (sourceB2601 + difference 0 4) sourceC2601) = raw29554 := by
      apply Matrix.ext; unfold tripleCharges sourceA2601 sourceB2601 sourceC2601 difference raw29554; decide +kernel
    rw [ha]
    exact (canonical29554 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2601 + difference 4 1) (sourceB2601 + difference 1 4) sourceC2601) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2341) := by
    have ha : (tripleCharges (sourceA2601 + difference 4 1) (sourceB2601 + difference 1 4) sourceC2601) = raw36175 := by
      apply Matrix.ext; unfold tripleCharges sourceA2601 sourceB2601 sourceC2601 difference raw36175; decide +kernel
    rw [ha]
    exact (canonical36175 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2601 + difference 4 2) (sourceB2601 + difference 2 4) sourceC2601) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3709) := by
    have ha : (tripleCharges (sourceA2601 + difference 4 2) (sourceB2601 + difference 2 4) sourceC2601) = raw36176 := by
      apply Matrix.ext; unfold tripleCharges sourceA2601 sourceB2601 sourceC2601 difference raw36176; decide +kernel
    rw [ha]
    exact (canonical36176 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2601 + difference 4 3) (sourceB2601 + difference 3 4) sourceC2601) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3741) := by
    have ha : (tripleCharges (sourceA2601 + difference 4 3) (sourceB2601 + difference 3 4) sourceC2601) = raw29545 := by
      apply Matrix.ext; unfold tripleCharges sourceA2601 sourceB2601 sourceC2601 difference raw29545; decide +kernel
    rw [ha]
    exact (canonical29545 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2601 + difference 4 5) (sourceB2601 + difference 5 4) sourceC2601) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3933) := by
    have ha : (tripleCharges (sourceA2601 + difference 4 5) (sourceB2601 + difference 5 4) sourceC2601) = raw36177 := by
      apply Matrix.ext; unfold tripleCharges sourceA2601 sourceB2601 sourceC2601 difference raw36177; decide +kernel
    rw [ha]
    exact (canonical36177 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2601 + difference 5 0) (sourceB2601 + difference 0 5) sourceC2601) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1880) := by
    have ha : (tripleCharges (sourceA2601 + difference 5 0) (sourceB2601 + difference 0 5) sourceC2601) = raw28647 := by
      apply Matrix.ext; unfold tripleCharges sourceA2601 sourceB2601 sourceC2601 difference raw28647; decide +kernel
    rw [ha]
    exact (canonical28647 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2601 + difference 5 1) (sourceB2601 + difference 1 5) sourceC2601) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1880) := by
    have ha : (tripleCharges (sourceA2601 + difference 5 1) (sourceB2601 + difference 1 5) sourceC2601) = raw36178 := by
      apply Matrix.ext; unfold tripleCharges sourceA2601 sourceB2601 sourceC2601 difference raw36178; decide +kernel
    rw [ha]
    exact (canonical36178 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2601 + difference 5 2) (sourceB2601 + difference 2 5) sourceC2601) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1879) := by
    have ha : (tripleCharges (sourceA2601 + difference 5 2) (sourceB2601 + difference 2 5) sourceC2601) = raw36179 := by
      apply Matrix.ext; unfold tripleCharges sourceA2601 sourceB2601 sourceC2601 difference raw36179; decide +kernel
    rw [ha]
    exact (canonical36179 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2601 + difference 5 3) (sourceB2601 + difference 3 5) sourceC2601) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2116) := by
    have ha : (tripleCharges (sourceA2601 + difference 5 3) (sourceB2601 + difference 3 5) sourceC2601) = raw28637 := by
      apply Matrix.ext; unfold tripleCharges sourceA2601 sourceB2601 sourceC2601 difference raw28637; decide +kernel
    rw [ha]
    exact (canonical28637 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2601 + difference 5 4) (sourceB2601 + difference 4 5) sourceC2601) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1929) := by
    have ha : (tripleCharges (sourceA2601 + difference 5 4) (sourceB2601 + difference 4 5) sourceC2601) = raw36180 := by
      apply Matrix.ext; unfold tripleCharges sourceA2601 sourceB2601 sourceC2601 difference raw36180; decide +kernel
    rw [ha]
    exact (canonical36180 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2601 sourceB2601 sourceC2601
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2601, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2602 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2602 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC2602 : Charge := ![1, 1, 0, -1, 1, -2]
def sourceForm2602 : Integer.Sparse Master := [(Sum.inr 4942, 2), (Sum.inr 4944, 2), (Sum.inr 4945, 2), (Sum.inr 4951, 2), (Sum.inr 5043, 1), (Sum.inr 5081, 1), (Sum.inr 5170, 2), (Sum.inr 5189, 1), (Sum.inr 5217, 1), (Sum.inr 5236, 1), (Sum.inr 5269, 1), (Sum.inr 5340, 1), (Sum.inr 5356, 1), (Sum.inr 5393, 1), (Sum.inr 5401, 2), (Sum.inr 5410, 2), (Sum.inr 5419, 1), (Sum.inr 5438, 2), (Sum.inr 5461, 1), (Sum.inr 5463, 1), (Sum.inr 5484, 2)]

theorem sourceEq2602 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2602 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2602 + difference 0 1) (sourceB2602 + difference 1 0) sourceC2602) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5170) := by
    have ha : (tripleCharges (sourceA2602 + difference 0 1) (sourceB2602 + difference 1 0) sourceC2602) = raw36181 := by
      apply Matrix.ext; unfold tripleCharges sourceA2602 sourceB2602 sourceC2602 difference raw36181; decide +kernel
    rw [ha]
    exact (canonical36181 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2602 + difference 0 2) (sourceB2602 + difference 2 0) sourceC2602) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5401) := by
    have ha : (tripleCharges (sourceA2602 + difference 0 2) (sourceB2602 + difference 2 0) sourceC2602) = raw36182 := by
      apply Matrix.ext; unfold tripleCharges sourceA2602 sourceB2602 sourceC2602 difference raw36182; decide +kernel
    rw [ha]
    exact (canonical36182 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2602 + difference 0 3) (sourceB2602 + difference 3 0) sourceC2602) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA2602 + difference 0 3) (sourceB2602 + difference 3 0) sourceC2602) = raw36183 := by
      apply Matrix.ext; unfold tripleCharges sourceA2602 sourceB2602 sourceC2602 difference raw36183; decide +kernel
    rw [ha]
    exact (canonical36183 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2602 + difference 0 4) (sourceB2602 + difference 4 0) sourceC2602) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5410) := by
    have ha : (tripleCharges (sourceA2602 + difference 0 4) (sourceB2602 + difference 4 0) sourceC2602) = raw36184 := by
      apply Matrix.ext; unfold tripleCharges sourceA2602 sourceB2602 sourceC2602 difference raw36184; decide +kernel
    rw [ha]
    exact (canonical36184 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2602 + difference 0 5) (sourceB2602 + difference 5 0) sourceC2602) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5484) := by
    have ha : (tripleCharges (sourceA2602 + difference 0 5) (sourceB2602 + difference 5 0) sourceC2602) = raw36185 := by
      apply Matrix.ext; unfold tripleCharges sourceA2602 sourceB2602 sourceC2602 difference raw36185; decide +kernel
    rw [ha]
    exact (canonical36185 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2602 + difference 1 0) (sourceB2602 + difference 0 1) sourceC2602) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5170) := by
    have ha : (tripleCharges (sourceA2602 + difference 1 0) (sourceB2602 + difference 0 1) sourceC2602) = raw36186 := by
      apply Matrix.ext; unfold tripleCharges sourceA2602 sourceB2602 sourceC2602 difference raw36186; decide +kernel
    rw [ha]
    exact (canonical36186 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2602 + difference 1 2) (sourceB2602 + difference 2 1) sourceC2602) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5401) := by
    have ha : (tripleCharges (sourceA2602 + difference 1 2) (sourceB2602 + difference 2 1) sourceC2602) = raw32125 := by
      apply Matrix.ext; unfold tripleCharges sourceA2602 sourceB2602 sourceC2602 difference raw32125; decide +kernel
    rw [ha]
    exact (canonical32125 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2602 + difference 1 3) (sourceB2602 + difference 3 1) sourceC2602) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA2602 + difference 1 3) (sourceB2602 + difference 3 1) sourceC2602) = raw32126 := by
      apply Matrix.ext; unfold tripleCharges sourceA2602 sourceB2602 sourceC2602 difference raw32126; decide +kernel
    rw [ha]
    exact (canonical32126 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2602 + difference 1 4) (sourceB2602 + difference 4 1) sourceC2602) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5410) := by
    have ha : (tripleCharges (sourceA2602 + difference 1 4) (sourceB2602 + difference 4 1) sourceC2602) = raw32127 := by
      apply Matrix.ext; unfold tripleCharges sourceA2602 sourceB2602 sourceC2602 difference raw32127; decide +kernel
    rw [ha]
    exact (canonical32127 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2602 + difference 1 5) (sourceB2602 + difference 5 1) sourceC2602) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5484) := by
    have ha : (tripleCharges (sourceA2602 + difference 1 5) (sourceB2602 + difference 5 1) sourceC2602) = raw32128 := by
      apply Matrix.ext; unfold tripleCharges sourceA2602 sourceB2602 sourceC2602 difference raw32128; decide +kernel
    rw [ha]
    exact (canonical32128 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2602 + difference 2 0) (sourceB2602 + difference 0 2) sourceC2602) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4942) := by
    have ha : (tripleCharges (sourceA2602 + difference 2 0) (sourceB2602 + difference 0 2) sourceC2602) = raw32135 := by
      apply Matrix.ext; unfold tripleCharges sourceA2602 sourceB2602 sourceC2602 difference raw32135; decide +kernel
    rw [ha]
    exact (canonical32135 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2602 + difference 2 1) (sourceB2602 + difference 1 2) sourceC2602) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4942) := by
    have ha : (tripleCharges (sourceA2602 + difference 2 1) (sourceB2602 + difference 1 2) sourceC2602) = raw36187 := by
      apply Matrix.ext; unfold tripleCharges sourceA2602 sourceB2602 sourceC2602 difference raw36187; decide +kernel
    rw [ha]
    exact (canonical36187 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2602 + difference 2 3) (sourceB2602 + difference 3 2) sourceC2602) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5419) := by
    have ha : (tripleCharges (sourceA2602 + difference 2 3) (sourceB2602 + difference 3 2) sourceC2602) = raw36188 := by
      apply Matrix.ext; unfold tripleCharges sourceA2602 sourceB2602 sourceC2602 difference raw36188; decide +kernel
    rw [ha]
    exact (canonical36188 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2602 + difference 2 4) (sourceB2602 + difference 4 2) sourceC2602) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5393) := by
    have ha : (tripleCharges (sourceA2602 + difference 2 4) (sourceB2602 + difference 4 2) sourceC2602) = raw36189 := by
      apply Matrix.ext; unfold tripleCharges sourceA2602 sourceB2602 sourceC2602 difference raw36189; decide +kernel
    rw [ha]
    exact (canonical36189 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2602 + difference 2 5) (sourceB2602 + difference 5 2) sourceC2602) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5461) := by
    have ha : (tripleCharges (sourceA2602 + difference 2 5) (sourceB2602 + difference 5 2) sourceC2602) = raw36190 := by
      apply Matrix.ext; unfold tripleCharges sourceA2602 sourceB2602 sourceC2602 difference raw36190; decide +kernel
    rw [ha]
    exact (canonical36190 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2602 + difference 3 0) (sourceB2602 + difference 0 3) sourceC2602) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4951) := by
    have ha : (tripleCharges (sourceA2602 + difference 3 0) (sourceB2602 + difference 0 3) sourceC2602) = raw32140 := by
      apply Matrix.ext; unfold tripleCharges sourceA2602 sourceB2602 sourceC2602 difference raw32140; decide +kernel
    rw [ha]
    exact (canonical32140 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2602 + difference 3 1) (sourceB2602 + difference 1 3) sourceC2602) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4951) := by
    have ha : (tripleCharges (sourceA2602 + difference 3 1) (sourceB2602 + difference 1 3) sourceC2602) = raw36191 := by
      apply Matrix.ext; unfold tripleCharges sourceA2602 sourceB2602 sourceC2602 difference raw36191; decide +kernel
    rw [ha]
    exact (canonical36191 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2602 + difference 3 2) (sourceB2602 + difference 2 3) sourceC2602) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5340) := by
    have ha : (tripleCharges (sourceA2602 + difference 3 2) (sourceB2602 + difference 2 3) sourceC2602) = raw36192 := by
      apply Matrix.ext; unfold tripleCharges sourceA2602 sourceB2602 sourceC2602 difference raw36192; decide +kernel
    rw [ha]
    exact (canonical36192 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2602 + difference 3 4) (sourceB2602 + difference 4 3) sourceC2602) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5356) := by
    have ha : (tripleCharges (sourceA2602 + difference 3 4) (sourceB2602 + difference 4 3) sourceC2602) = raw36193 := by
      apply Matrix.ext; unfold tripleCharges sourceA2602 sourceB2602 sourceC2602 difference raw36193; decide +kernel
    rw [ha]
    exact (canonical36193 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2602 + difference 3 5) (sourceB2602 + difference 5 3) sourceC2602) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5463) := by
    have ha : (tripleCharges (sourceA2602 + difference 3 5) (sourceB2602 + difference 5 3) sourceC2602) = raw36194 := by
      apply Matrix.ext; unfold tripleCharges sourceA2602 sourceB2602 sourceC2602 difference raw36194; decide +kernel
    rw [ha]
    exact (canonical36194 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2602 + difference 4 0) (sourceB2602 + difference 0 4) sourceC2602) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4945) := by
    have ha : (tripleCharges (sourceA2602 + difference 4 0) (sourceB2602 + difference 0 4) sourceC2602) = raw32145 := by
      apply Matrix.ext; unfold tripleCharges sourceA2602 sourceB2602 sourceC2602 difference raw32145; decide +kernel
    rw [ha]
    exact (canonical32145 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2602 + difference 4 1) (sourceB2602 + difference 1 4) sourceC2602) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4945) := by
    have ha : (tripleCharges (sourceA2602 + difference 4 1) (sourceB2602 + difference 1 4) sourceC2602) = raw36195 := by
      apply Matrix.ext; unfold tripleCharges sourceA2602 sourceB2602 sourceC2602 difference raw36195; decide +kernel
    rw [ha]
    exact (canonical36195 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2602 + difference 4 2) (sourceB2602 + difference 2 4) sourceC2602) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5217) := by
    have ha : (tripleCharges (sourceA2602 + difference 4 2) (sourceB2602 + difference 2 4) sourceC2602) = raw36196 := by
      apply Matrix.ext; unfold tripleCharges sourceA2602 sourceB2602 sourceC2602 difference raw36196; decide +kernel
    rw [ha]
    exact (canonical36196 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2602 + difference 4 3) (sourceB2602 + difference 3 4) sourceC2602) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5236) := by
    have ha : (tripleCharges (sourceA2602 + difference 4 3) (sourceB2602 + difference 3 4) sourceC2602) = raw36197 := by
      apply Matrix.ext; unfold tripleCharges sourceA2602 sourceB2602 sourceC2602 difference raw36197; decide +kernel
    rw [ha]
    exact (canonical36197 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2602 + difference 4 5) (sourceB2602 + difference 5 4) sourceC2602) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5269) := by
    have ha : (tripleCharges (sourceA2602 + difference 4 5) (sourceB2602 + difference 5 4) sourceC2602) = raw36198 := by
      apply Matrix.ext; unfold tripleCharges sourceA2602 sourceB2602 sourceC2602 difference raw36198; decide +kernel
    rw [ha]
    exact (canonical36198 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2602 + difference 5 0) (sourceB2602 + difference 0 5) sourceC2602) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4944) := by
    have ha : (tripleCharges (sourceA2602 + difference 5 0) (sourceB2602 + difference 0 5) sourceC2602) = raw32150 := by
      apply Matrix.ext; unfold tripleCharges sourceA2602 sourceB2602 sourceC2602 difference raw32150; decide +kernel
    rw [ha]
    exact (canonical32150 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2602 + difference 5 1) (sourceB2602 + difference 1 5) sourceC2602) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4944) := by
    have ha : (tripleCharges (sourceA2602 + difference 5 1) (sourceB2602 + difference 1 5) sourceC2602) = raw36199 := by
      apply Matrix.ext; unfold tripleCharges sourceA2602 sourceB2602 sourceC2602 difference raw36199; decide +kernel
    rw [ha]
    exact (canonical36199 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2602 + difference 5 2) (sourceB2602 + difference 2 5) sourceC2602) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5043) := by
    have ha : (tripleCharges (sourceA2602 + difference 5 2) (sourceB2602 + difference 2 5) sourceC2602) = raw36200 := by
      apply Matrix.ext; unfold tripleCharges sourceA2602 sourceB2602 sourceC2602 difference raw36200; decide +kernel
    rw [ha]
    exact (canonical36200 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2602 + difference 5 3) (sourceB2602 + difference 3 5) sourceC2602) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5189) := by
    have ha : (tripleCharges (sourceA2602 + difference 5 3) (sourceB2602 + difference 3 5) sourceC2602) = raw36201 := by
      apply Matrix.ext; unfold tripleCharges sourceA2602 sourceB2602 sourceC2602 difference raw36201; decide +kernel
    rw [ha]
    exact (canonical36201 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2602 + difference 5 4) (sourceB2602 + difference 4 5) sourceC2602) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5081) := by
    have ha : (tripleCharges (sourceA2602 + difference 5 4) (sourceB2602 + difference 4 5) sourceC2602) = raw36202 := by
      apply Matrix.ext; unfold tripleCharges sourceA2602 sourceB2602 sourceC2602 difference raw36202; decide +kernel
    rw [ha]
    exact (canonical36202 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2602 sourceB2602 sourceC2602
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2602, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2603 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2603 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC2603 : Charge := ![1, 1, 0, -1, 1, -2]
def sourceForm2603 : Integer.Sparse Master := [(Sum.inr 2656, 1), (Sum.inr 2658, 2), (Sum.inr 2682, 1), (Sum.inr 2736, 1), (Sum.inr 3407, 2), (Sum.inr 3413, 2), (Sum.inr 3418, 2), (Sum.inr 3465, 1), (Sum.inr 3482, 1), (Sum.inr 3542, 1), (Sum.inr 3606, 2), (Sum.inr 3763, 1), (Sum.inr 3773, 1), (Sum.inr 3797, 1), (Sum.inr 3804, 2), (Sum.inr 3816, 2), (Sum.inr 3842, 1), (Sum.inr 3857, 2), (Sum.inr 3960, 1), (Sum.inr 3973, 1), (Sum.inr 3983, 2)]

theorem sourceEq2603 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2603 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2603 + difference 0 1) (sourceB2603 + difference 1 0) sourceC2603) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3606) := by
    have ha : (tripleCharges (sourceA2603 + difference 0 1) (sourceB2603 + difference 1 0) sourceC2603) = raw36203 := by
      apply Matrix.ext; unfold tripleCharges sourceA2603 sourceB2603 sourceC2603 difference raw36203; decide +kernel
    rw [ha]
    exact (canonical36203 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2603 + difference 0 2) (sourceB2603 + difference 2 0) sourceC2603) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3804) := by
    have ha : (tripleCharges (sourceA2603 + difference 0 2) (sourceB2603 + difference 2 0) sourceC2603) = raw36204 := by
      apply Matrix.ext; unfold tripleCharges sourceA2603 sourceB2603 sourceC2603 difference raw36204; decide +kernel
    rw [ha]
    exact (canonical36204 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2603 + difference 0 3) (sourceB2603 + difference 3 0) sourceC2603) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3857) := by
    have ha : (tripleCharges (sourceA2603 + difference 0 3) (sourceB2603 + difference 3 0) sourceC2603) = raw36205 := by
      apply Matrix.ext; unfold tripleCharges sourceA2603 sourceB2603 sourceC2603 difference raw36205; decide +kernel
    rw [ha]
    exact (canonical36205 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2603 + difference 0 4) (sourceB2603 + difference 4 0) sourceC2603) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3816) := by
    have ha : (tripleCharges (sourceA2603 + difference 0 4) (sourceB2603 + difference 4 0) sourceC2603) = raw36206 := by
      apply Matrix.ext; unfold tripleCharges sourceA2603 sourceB2603 sourceC2603 difference raw36206; decide +kernel
    rw [ha]
    exact (canonical36206 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2603 + difference 0 5) (sourceB2603 + difference 5 0) sourceC2603) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3983) := by
    have ha : (tripleCharges (sourceA2603 + difference 0 5) (sourceB2603 + difference 5 0) sourceC2603) = raw36207 := by
      apply Matrix.ext; unfold tripleCharges sourceA2603 sourceB2603 sourceC2603 difference raw36207; decide +kernel
    rw [ha]
    exact (canonical36207 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2603 + difference 1 0) (sourceB2603 + difference 0 1) sourceC2603) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3606) := by
    have ha : (tripleCharges (sourceA2603 + difference 1 0) (sourceB2603 + difference 0 1) sourceC2603) = raw36208 := by
      apply Matrix.ext; unfold tripleCharges sourceA2603 sourceB2603 sourceC2603 difference raw36208; decide +kernel
    rw [ha]
    exact (canonical36208 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2603 + difference 1 2) (sourceB2603 + difference 2 1) sourceC2603) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3804) := by
    have ha : (tripleCharges (sourceA2603 + difference 1 2) (sourceB2603 + difference 2 1) sourceC2603) = raw32155 := by
      apply Matrix.ext; unfold tripleCharges sourceA2603 sourceB2603 sourceC2603 difference raw32155; decide +kernel
    rw [ha]
    exact (canonical32155 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2603 + difference 1 3) (sourceB2603 + difference 3 1) sourceC2603) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3857) := by
    have ha : (tripleCharges (sourceA2603 + difference 1 3) (sourceB2603 + difference 3 1) sourceC2603) = raw32156 := by
      apply Matrix.ext; unfold tripleCharges sourceA2603 sourceB2603 sourceC2603 difference raw32156; decide +kernel
    rw [ha]
    exact (canonical32156 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2603 + difference 1 4) (sourceB2603 + difference 4 1) sourceC2603) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3816) := by
    have ha : (tripleCharges (sourceA2603 + difference 1 4) (sourceB2603 + difference 4 1) sourceC2603) = raw32157 := by
      apply Matrix.ext; unfold tripleCharges sourceA2603 sourceB2603 sourceC2603 difference raw32157; decide +kernel
    rw [ha]
    exact (canonical32157 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2603 + difference 1 5) (sourceB2603 + difference 5 1) sourceC2603) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3983) := by
    have ha : (tripleCharges (sourceA2603 + difference 1 5) (sourceB2603 + difference 5 1) sourceC2603) = raw32158 := by
      apply Matrix.ext; unfold tripleCharges sourceA2603 sourceB2603 sourceC2603 difference raw32158; decide +kernel
    rw [ha]
    exact (canonical32158 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2603 + difference 2 0) (sourceB2603 + difference 0 2) sourceC2603) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3407) := by
    have ha : (tripleCharges (sourceA2603 + difference 2 0) (sourceB2603 + difference 0 2) sourceC2603) = raw32165 := by
      apply Matrix.ext; unfold tripleCharges sourceA2603 sourceB2603 sourceC2603 difference raw32165; decide +kernel
    rw [ha]
    exact (canonical32165 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2603 + difference 2 1) (sourceB2603 + difference 1 2) sourceC2603) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3407) := by
    have ha : (tripleCharges (sourceA2603 + difference 2 1) (sourceB2603 + difference 1 2) sourceC2603) = raw36209 := by
      apply Matrix.ext; unfold tripleCharges sourceA2603 sourceB2603 sourceC2603 difference raw36209; decide +kernel
    rw [ha]
    exact (canonical36209 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2603 + difference 2 3) (sourceB2603 + difference 3 2) sourceC2603) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3842) := by
    have ha : (tripleCharges (sourceA2603 + difference 2 3) (sourceB2603 + difference 3 2) sourceC2603) = raw36210 := by
      apply Matrix.ext; unfold tripleCharges sourceA2603 sourceB2603 sourceC2603 difference raw36210; decide +kernel
    rw [ha]
    exact (canonical36210 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2603 + difference 2 4) (sourceB2603 + difference 4 2) sourceC2603) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3797) := by
    have ha : (tripleCharges (sourceA2603 + difference 2 4) (sourceB2603 + difference 4 2) sourceC2603) = raw36211 := by
      apply Matrix.ext; unfold tripleCharges sourceA2603 sourceB2603 sourceC2603 difference raw36211; decide +kernel
    rw [ha]
    exact (canonical36211 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2603 + difference 2 5) (sourceB2603 + difference 5 2) sourceC2603) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3973) := by
    have ha : (tripleCharges (sourceA2603 + difference 2 5) (sourceB2603 + difference 5 2) sourceC2603) = raw36212 := by
      apply Matrix.ext; unfold tripleCharges sourceA2603 sourceB2603 sourceC2603 difference raw36212; decide +kernel
    rw [ha]
    exact (canonical36212 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2603 + difference 3 0) (sourceB2603 + difference 0 3) sourceC2603) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3418) := by
    have ha : (tripleCharges (sourceA2603 + difference 3 0) (sourceB2603 + difference 0 3) sourceC2603) = raw32170 := by
      apply Matrix.ext; unfold tripleCharges sourceA2603 sourceB2603 sourceC2603 difference raw32170; decide +kernel
    rw [ha]
    exact (canonical32170 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2603 + difference 3 1) (sourceB2603 + difference 1 3) sourceC2603) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3418) := by
    have ha : (tripleCharges (sourceA2603 + difference 3 1) (sourceB2603 + difference 1 3) sourceC2603) = raw36213 := by
      apply Matrix.ext; unfold tripleCharges sourceA2603 sourceB2603 sourceC2603 difference raw36213; decide +kernel
    rw [ha]
    exact (canonical36213 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2603 + difference 3 2) (sourceB2603 + difference 2 3) sourceC2603) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3763) := by
    have ha : (tripleCharges (sourceA2603 + difference 3 2) (sourceB2603 + difference 2 3) sourceC2603) = raw36214 := by
      apply Matrix.ext; unfold tripleCharges sourceA2603 sourceB2603 sourceC2603 difference raw36214; decide +kernel
    rw [ha]
    exact (canonical36214 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2603 + difference 3 4) (sourceB2603 + difference 4 3) sourceC2603) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3773) := by
    have ha : (tripleCharges (sourceA2603 + difference 3 4) (sourceB2603 + difference 4 3) sourceC2603) = raw36215 := by
      apply Matrix.ext; unfold tripleCharges sourceA2603 sourceB2603 sourceC2603 difference raw36215; decide +kernel
    rw [ha]
    exact (canonical36215 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2603 + difference 3 5) (sourceB2603 + difference 5 3) sourceC2603) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3960) := by
    have ha : (tripleCharges (sourceA2603 + difference 3 5) (sourceB2603 + difference 5 3) sourceC2603) = raw36216 := by
      apply Matrix.ext; unfold tripleCharges sourceA2603 sourceB2603 sourceC2603 difference raw36216; decide +kernel
    rw [ha]
    exact (canonical36216 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2603 + difference 4 0) (sourceB2603 + difference 0 4) sourceC2603) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2658) := by
    have ha : (tripleCharges (sourceA2603 + difference 4 0) (sourceB2603 + difference 0 4) sourceC2603) = raw32175 := by
      apply Matrix.ext; unfold tripleCharges sourceA2603 sourceB2603 sourceC2603 difference raw32175; decide +kernel
    rw [ha]
    exact (canonical32175 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2603 + difference 4 1) (sourceB2603 + difference 1 4) sourceC2603) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2658) := by
    have ha : (tripleCharges (sourceA2603 + difference 4 1) (sourceB2603 + difference 1 4) sourceC2603) = raw36217 := by
      apply Matrix.ext; unfold tripleCharges sourceA2603 sourceB2603 sourceC2603 difference raw36217; decide +kernel
    rw [ha]
    exact (canonical36217 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2603 + difference 4 2) (sourceB2603 + difference 2 4) sourceC2603) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2656) := by
    have ha : (tripleCharges (sourceA2603 + difference 4 2) (sourceB2603 + difference 2 4) sourceC2603) = raw36218 := by
      apply Matrix.ext; unfold tripleCharges sourceA2603 sourceB2603 sourceC2603 difference raw36218; decide +kernel
    rw [ha]
    exact (canonical36218 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2603 + difference 4 3) (sourceB2603 + difference 3 4) sourceC2603) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2682) := by
    have ha : (tripleCharges (sourceA2603 + difference 4 3) (sourceB2603 + difference 3 4) sourceC2603) = raw36219 := by
      apply Matrix.ext; unfold tripleCharges sourceA2603 sourceB2603 sourceC2603 difference raw36219; decide +kernel
    rw [ha]
    exact (canonical36219 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2603 + difference 4 5) (sourceB2603 + difference 5 4) sourceC2603) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2736) := by
    have ha : (tripleCharges (sourceA2603 + difference 4 5) (sourceB2603 + difference 5 4) sourceC2603) = raw36220 := by
      apply Matrix.ext; unfold tripleCharges sourceA2603 sourceB2603 sourceC2603 difference raw36220; decide +kernel
    rw [ha]
    exact (canonical36220 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2603 + difference 5 0) (sourceB2603 + difference 0 5) sourceC2603) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3413) := by
    have ha : (tripleCharges (sourceA2603 + difference 5 0) (sourceB2603 + difference 0 5) sourceC2603) = raw32180 := by
      apply Matrix.ext; unfold tripleCharges sourceA2603 sourceB2603 sourceC2603 difference raw32180; decide +kernel
    rw [ha]
    exact (canonical32180 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2603 + difference 5 1) (sourceB2603 + difference 1 5) sourceC2603) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3413) := by
    have ha : (tripleCharges (sourceA2603 + difference 5 1) (sourceB2603 + difference 1 5) sourceC2603) = raw36221 := by
      apply Matrix.ext; unfold tripleCharges sourceA2603 sourceB2603 sourceC2603 difference raw36221; decide +kernel
    rw [ha]
    exact (canonical36221 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2603 + difference 5 2) (sourceB2603 + difference 2 5) sourceC2603) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3465) := by
    have ha : (tripleCharges (sourceA2603 + difference 5 2) (sourceB2603 + difference 2 5) sourceC2603) = raw36222 := by
      apply Matrix.ext; unfold tripleCharges sourceA2603 sourceB2603 sourceC2603 difference raw36222; decide +kernel
    rw [ha]
    exact (canonical36222 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2603 + difference 5 3) (sourceB2603 + difference 3 5) sourceC2603) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3542) := by
    have ha : (tripleCharges (sourceA2603 + difference 5 3) (sourceB2603 + difference 3 5) sourceC2603) = raw36223 := by
      apply Matrix.ext; unfold tripleCharges sourceA2603 sourceB2603 sourceC2603 difference raw36223; decide +kernel
    rw [ha]
    exact (canonical36223 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2603 + difference 5 4) (sourceB2603 + difference 4 5) sourceC2603) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3482) := by
    have ha : (tripleCharges (sourceA2603 + difference 5 4) (sourceB2603 + difference 4 5) sourceC2603) = raw36224 := by
      apply Matrix.ext; unfold tripleCharges sourceA2603 sourceB2603 sourceC2603 difference raw36224; decide +kernel
    rw [ha]
    exact (canonical36224 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2603 sourceB2603 sourceC2603
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2603, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2604 : Charge := ![1, 1, 0, -1, 1, -2]
def sourceB2604 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC2604 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceForm2604 : Integer.Sparse Master := [(Sum.inr 5092, 1), (Sum.inr 5095, 2), (Sum.inr 5108, 1), (Sum.inr 5269, 1), (Sum.inr 5285, 1), (Sum.inr 5287, 2), (Sum.inr 5298, 1), (Sum.inr 5349, 2), (Sum.inr 5353, 2), (Sum.inr 5362, 1), (Sum.inr 5364, 2), (Sum.inr 5367, 2), (Sum.inr 5368, 2), (Sum.inr 5370, 2), (Sum.inr 5384, 2), (Sum.inr 5393, 1), (Sum.inr 5418, 1), (Sum.inr 5419, 1), (Sum.inr 5459, 1), (Sum.inr 5463, 1), (Sum.inr 5465, 1)]

theorem sourceEq2604 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2604 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2604 + difference 0 1) (sourceB2604 + difference 1 0) sourceC2604) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5384) := by
    have ha : (tripleCharges (sourceA2604 + difference 0 1) (sourceB2604 + difference 1 0) sourceC2604) = raw36225 := by
      apply Matrix.ext; unfold tripleCharges sourceA2604 sourceB2604 sourceC2604 difference raw36225; decide +kernel
    rw [ha]
    exact (canonical36225 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2604 + difference 0 2) (sourceB2604 + difference 2 0) sourceC2604) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5349) := by
    have ha : (tripleCharges (sourceA2604 + difference 0 2) (sourceB2604 + difference 2 0) sourceC2604) = raw36226 := by
      apply Matrix.ext; unfold tripleCharges sourceA2604 sourceB2604 sourceC2604 difference raw36226; decide +kernel
    rw [ha]
    exact (canonical36226 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2604 + difference 0 3) (sourceB2604 + difference 3 0) sourceC2604) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5364) := by
    have ha : (tripleCharges (sourceA2604 + difference 0 3) (sourceB2604 + difference 3 0) sourceC2604) = raw36227 := by
      apply Matrix.ext; unfold tripleCharges sourceA2604 sourceB2604 sourceC2604 difference raw36227; decide +kernel
    rw [ha]
    exact (canonical36227 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2604 + difference 0 4) (sourceB2604 + difference 4 0) sourceC2604) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5367) := by
    have ha : (tripleCharges (sourceA2604 + difference 0 4) (sourceB2604 + difference 4 0) sourceC2604) = raw36228 := by
      apply Matrix.ext; unfold tripleCharges sourceA2604 sourceB2604 sourceC2604 difference raw36228; decide +kernel
    rw [ha]
    exact (canonical36228 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2604 + difference 0 5) (sourceB2604 + difference 5 0) sourceC2604) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5095) := by
    have ha : (tripleCharges (sourceA2604 + difference 0 5) (sourceB2604 + difference 5 0) sourceC2604) = raw36229 := by
      apply Matrix.ext; unfold tripleCharges sourceA2604 sourceB2604 sourceC2604 difference raw36229; decide +kernel
    rw [ha]
    exact (canonical36229 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2604 + difference 1 0) (sourceB2604 + difference 0 1) sourceC2604) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5384) := by
    have ha : (tripleCharges (sourceA2604 + difference 1 0) (sourceB2604 + difference 0 1) sourceC2604) = raw35635 := by
      apply Matrix.ext; unfold tripleCharges sourceA2604 sourceB2604 sourceC2604 difference raw35635; decide +kernel
    rw [ha]
    exact (canonical35635 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2604 + difference 1 2) (sourceB2604 + difference 2 1) sourceC2604) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5349) := by
    have ha : (tripleCharges (sourceA2604 + difference 1 2) (sourceB2604 + difference 2 1) sourceC2604) = raw35732 := by
      apply Matrix.ext; unfold tripleCharges sourceA2604 sourceB2604 sourceC2604 difference raw35732; decide +kernel
    rw [ha]
    exact (canonical35732 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2604 + difference 1 3) (sourceB2604 + difference 3 1) sourceC2604) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5364) := by
    have ha : (tripleCharges (sourceA2604 + difference 1 3) (sourceB2604 + difference 3 1) sourceC2604) = raw35733 := by
      apply Matrix.ext; unfold tripleCharges sourceA2604 sourceB2604 sourceC2604 difference raw35733; decide +kernel
    rw [ha]
    exact (canonical35733 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2604 + difference 1 4) (sourceB2604 + difference 4 1) sourceC2604) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5367) := by
    have ha : (tripleCharges (sourceA2604 + difference 1 4) (sourceB2604 + difference 4 1) sourceC2604) = raw35618 := by
      apply Matrix.ext; unfold tripleCharges sourceA2604 sourceB2604 sourceC2604 difference raw35618; decide +kernel
    rw [ha]
    exact (canonical35618 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2604 + difference 1 5) (sourceB2604 + difference 5 1) sourceC2604) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5095) := by
    have ha : (tripleCharges (sourceA2604 + difference 1 5) (sourceB2604 + difference 5 1) sourceC2604) = raw35734 := by
      apply Matrix.ext; unfold tripleCharges sourceA2604 sourceB2604 sourceC2604 difference raw35734; decide +kernel
    rw [ha]
    exact (canonical35734 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2604 + difference 2 0) (sourceB2604 + difference 0 2) sourceC2604) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5353) := by
    have ha : (tripleCharges (sourceA2604 + difference 2 0) (sourceB2604 + difference 0 2) sourceC2604) = raw35740 := by
      apply Matrix.ext; unfold tripleCharges sourceA2604 sourceB2604 sourceC2604 difference raw35740; decide +kernel
    rw [ha]
    exact (canonical35740 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2604 + difference 2 1) (sourceB2604 + difference 1 2) sourceC2604) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5353) := by
    have ha : (tripleCharges (sourceA2604 + difference 2 1) (sourceB2604 + difference 1 2) sourceC2604) = raw36230 := by
      apply Matrix.ext; unfold tripleCharges sourceA2604 sourceB2604 sourceC2604 difference raw36230; decide +kernel
    rw [ha]
    exact (canonical36230 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2604 + difference 2 3) (sourceB2604 + difference 3 2) sourceC2604) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5362) := by
    have ha : (tripleCharges (sourceA2604 + difference 2 3) (sourceB2604 + difference 3 2) sourceC2604) = raw36231 := by
      apply Matrix.ext; unfold tripleCharges sourceA2604 sourceB2604 sourceC2604 difference raw36231; decide +kernel
    rw [ha]
    exact (canonical36231 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2604 + difference 2 4) (sourceB2604 + difference 4 2) sourceC2604) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5393) := by
    have ha : (tripleCharges (sourceA2604 + difference 2 4) (sourceB2604 + difference 4 2) sourceC2604) = raw35919 := by
      apply Matrix.ext; unfold tripleCharges sourceA2604 sourceB2604 sourceC2604 difference raw35919; decide +kernel
    rw [ha]
    exact (canonical35919 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2604 + difference 2 5) (sourceB2604 + difference 5 2) sourceC2604) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5092) := by
    have ha : (tripleCharges (sourceA2604 + difference 2 5) (sourceB2604 + difference 5 2) sourceC2604) = raw36232 := by
      apply Matrix.ext; unfold tripleCharges sourceA2604 sourceB2604 sourceC2604 difference raw36232; decide +kernel
    rw [ha]
    exact (canonical36232 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2604 + difference 3 0) (sourceB2604 + difference 0 3) sourceC2604) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5370) := by
    have ha : (tripleCharges (sourceA2604 + difference 3 0) (sourceB2604 + difference 0 3) sourceC2604) = raw35744 := by
      apply Matrix.ext; unfold tripleCharges sourceA2604 sourceB2604 sourceC2604 difference raw35744; decide +kernel
    rw [ha]
    exact (canonical35744 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2604 + difference 3 1) (sourceB2604 + difference 1 3) sourceC2604) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5370) := by
    have ha : (tripleCharges (sourceA2604 + difference 3 1) (sourceB2604 + difference 1 3) sourceC2604) = raw36233 := by
      apply Matrix.ext; unfold tripleCharges sourceA2604 sourceB2604 sourceC2604 difference raw36233; decide +kernel
    rw [ha]
    exact (canonical36233 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2604 + difference 3 2) (sourceB2604 + difference 2 3) sourceC2604) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5419) := by
    have ha : (tripleCharges (sourceA2604 + difference 3 2) (sourceB2604 + difference 2 3) sourceC2604) = raw36234 := by
      apply Matrix.ext; unfold tripleCharges sourceA2604 sourceB2604 sourceC2604 difference raw36234; decide +kernel
    rw [ha]
    exact (canonical36234 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2604 + difference 3 4) (sourceB2604 + difference 4 3) sourceC2604) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5418) := by
    have ha : (tripleCharges (sourceA2604 + difference 3 4) (sourceB2604 + difference 4 3) sourceC2604) = raw36235 := by
      apply Matrix.ext; unfold tripleCharges sourceA2604 sourceB2604 sourceC2604 difference raw36235; decide +kernel
    rw [ha]
    exact (canonical36235 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2604 + difference 3 5) (sourceB2604 + difference 5 3) sourceC2604) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5269) := by
    have ha : (tripleCharges (sourceA2604 + difference 3 5) (sourceB2604 + difference 5 3) sourceC2604) = raw36236 := by
      apply Matrix.ext; unfold tripleCharges sourceA2604 sourceB2604 sourceC2604 difference raw36236; decide +kernel
    rw [ha]
    exact (canonical36236 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2604 + difference 4 0) (sourceB2604 + difference 0 4) sourceC2604) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5287) := by
    have ha : (tripleCharges (sourceA2604 + difference 4 0) (sourceB2604 + difference 0 4) sourceC2604) = raw35748 := by
      apply Matrix.ext; unfold tripleCharges sourceA2604 sourceB2604 sourceC2604 difference raw35748; decide +kernel
    rw [ha]
    exact (canonical35748 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2604 + difference 4 1) (sourceB2604 + difference 1 4) sourceC2604) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5287) := by
    have ha : (tripleCharges (sourceA2604 + difference 4 1) (sourceB2604 + difference 1 4) sourceC2604) = raw36237 := by
      apply Matrix.ext; unfold tripleCharges sourceA2604 sourceB2604 sourceC2604 difference raw36237; decide +kernel
    rw [ha]
    exact (canonical36237 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2604 + difference 4 2) (sourceB2604 + difference 2 4) sourceC2604) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5285) := by
    have ha : (tripleCharges (sourceA2604 + difference 4 2) (sourceB2604 + difference 2 4) sourceC2604) = raw36238 := by
      apply Matrix.ext; unfold tripleCharges sourceA2604 sourceB2604 sourceC2604 difference raw36238; decide +kernel
    rw [ha]
    exact (canonical36238 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2604 + difference 4 3) (sourceB2604 + difference 3 4) sourceC2604) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5298) := by
    have ha : (tripleCharges (sourceA2604 + difference 4 3) (sourceB2604 + difference 3 4) sourceC2604) = raw36239 := by
      apply Matrix.ext; unfold tripleCharges sourceA2604 sourceB2604 sourceC2604 difference raw36239; decide +kernel
    rw [ha]
    exact (canonical36239 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2604 + difference 4 5) (sourceB2604 + difference 5 4) sourceC2604) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5108) := by
    have ha : (tripleCharges (sourceA2604 + difference 4 5) (sourceB2604 + difference 5 4) sourceC2604) = raw36240 := by
      apply Matrix.ext; unfold tripleCharges sourceA2604 sourceB2604 sourceC2604 difference raw36240; decide +kernel
    rw [ha]
    exact (canonical36240 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2604 + difference 5 0) (sourceB2604 + difference 0 5) sourceC2604) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5368) := by
    have ha : (tripleCharges (sourceA2604 + difference 5 0) (sourceB2604 + difference 0 5) sourceC2604) = raw35632 := by
      apply Matrix.ext; unfold tripleCharges sourceA2604 sourceB2604 sourceC2604 difference raw35632; decide +kernel
    rw [ha]
    exact (canonical35632 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2604 + difference 5 1) (sourceB2604 + difference 1 5) sourceC2604) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5368) := by
    have ha : (tripleCharges (sourceA2604 + difference 5 1) (sourceB2604 + difference 1 5) sourceC2604) = raw36241 := by
      apply Matrix.ext; unfold tripleCharges sourceA2604 sourceB2604 sourceC2604 difference raw36241; decide +kernel
    rw [ha]
    exact (canonical36241 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2604 + difference 5 2) (sourceB2604 + difference 2 5) sourceC2604) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5459) := by
    have ha : (tripleCharges (sourceA2604 + difference 5 2) (sourceB2604 + difference 2 5) sourceC2604) = raw36242 := by
      apply Matrix.ext; unfold tripleCharges sourceA2604 sourceB2604 sourceC2604 difference raw36242; decide +kernel
    rw [ha]
    exact (canonical36242 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2604 + difference 5 3) (sourceB2604 + difference 3 5) sourceC2604) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5463) := by
    have ha : (tripleCharges (sourceA2604 + difference 5 3) (sourceB2604 + difference 3 5) sourceC2604) = raw36243 := by
      apply Matrix.ext; unfold tripleCharges sourceA2604 sourceB2604 sourceC2604 difference raw36243; decide +kernel
    rw [ha]
    exact (canonical36243 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2604 + difference 5 4) (sourceB2604 + difference 4 5) sourceC2604) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5465) := by
    have ha : (tripleCharges (sourceA2604 + difference 5 4) (sourceB2604 + difference 4 5) sourceC2604) = raw35615 := by
      apply Matrix.ext; unfold tripleCharges sourceA2604 sourceB2604 sourceC2604 difference raw35615; decide +kernel
    rw [ha]
    exact (canonical35615 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2604 sourceB2604 sourceC2604
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2604, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2605 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2605 : Charge := ![1, 1, 1, -1, -1, -1]
def sourceC2605 : Charge := ![1, 1, -1, 0, 0, -1]
def sourceForm2605 : Integer.Sparse Master := [(Sum.inr 4927, 2), (Sum.inr 4928, 4), (Sum.inr 4941, 2), (Sum.inr 5031, 1), (Sum.inr 5081, 2), (Sum.inr 5137, 2), (Sum.inr 5334, 2), (Sum.inr 5356, 2), (Sum.inr 5393, 2), (Sum.inr 5464, 1), (Sum.inr 5465, 2), (Sum.inr 5469, 2), (Sum.inr 5482, 2), (Sum.inr 5483, 4)]

theorem sourceEq2605 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2605 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2605 + difference 0 1) (sourceB2605 + difference 1 0) sourceC2605) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5137) := by
    have ha : (tripleCharges (sourceA2605 + difference 0 1) (sourceB2605 + difference 1 0) sourceC2605) = raw36244 := by
      apply Matrix.ext; unfold tripleCharges sourceA2605 sourceB2605 sourceC2605 difference raw36244; decide +kernel
    rw [ha]
    exact (canonical36244 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2605 + difference 0 2) (sourceB2605 + difference 2 0) sourceC2605) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5469) := by
    have ha : (tripleCharges (sourceA2605 + difference 0 2) (sourceB2605 + difference 2 0) sourceC2605) = raw36245 := by
      apply Matrix.ext; unfold tripleCharges sourceA2605 sourceB2605 sourceC2605 difference raw36245; decide +kernel
    rw [ha]
    exact (canonical36245 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2605 + difference 0 3) (sourceB2605 + difference 3 0) sourceC2605) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA2605 + difference 0 3) (sourceB2605 + difference 3 0) sourceC2605) = raw36246 := by
      apply Matrix.ext; unfold tripleCharges sourceA2605 sourceB2605 sourceC2605 difference raw36246; decide +kernel
    rw [ha]
    exact (canonical36246 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2605 + difference 0 4) (sourceB2605 + difference 4 0) sourceC2605) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA2605 + difference 0 4) (sourceB2605 + difference 4 0) sourceC2605) = raw36247 := by
      apply Matrix.ext; unfold tripleCharges sourceA2605 sourceB2605 sourceC2605 difference raw36247; decide +kernel
    rw [ha]
    exact (canonical36247 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2605 + difference 0 5) (sourceB2605 + difference 5 0) sourceC2605) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA2605 + difference 0 5) (sourceB2605 + difference 5 0) sourceC2605) = raw18765 := by
      apply Matrix.ext; unfold tripleCharges sourceA2605 sourceB2605 sourceC2605 difference raw18765; decide +kernel
    rw [ha]
    exact (canonical18765 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2605 + difference 1 0) (sourceB2605 + difference 0 1) sourceC2605) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5137) := by
    have ha : (tripleCharges (sourceA2605 + difference 1 0) (sourceB2605 + difference 0 1) sourceC2605) = raw13801 := by
      apply Matrix.ext; unfold tripleCharges sourceA2605 sourceB2605 sourceC2605 difference raw13801; decide +kernel
    rw [ha]
    exact (canonical13801 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2605 + difference 1 2) (sourceB2605 + difference 2 1) sourceC2605) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5469) := by
    have ha : (tripleCharges (sourceA2605 + difference 1 2) (sourceB2605 + difference 2 1) sourceC2605) = raw18784 := by
      apply Matrix.ext; unfold tripleCharges sourceA2605 sourceB2605 sourceC2605 difference raw18784; decide +kernel
    rw [ha]
    exact (canonical18784 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2605 + difference 1 3) (sourceB2605 + difference 3 1) sourceC2605) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA2605 + difference 1 3) (sourceB2605 + difference 3 1) sourceC2605) = raw18785 := by
      apply Matrix.ext; unfold tripleCharges sourceA2605 sourceB2605 sourceC2605 difference raw18785; decide +kernel
    rw [ha]
    exact (canonical18785 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2605 + difference 1 4) (sourceB2605 + difference 4 1) sourceC2605) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA2605 + difference 1 4) (sourceB2605 + difference 4 1) sourceC2605) = raw18786 := by
      apply Matrix.ext; unfold tripleCharges sourceA2605 sourceB2605 sourceC2605 difference raw18786; decide +kernel
    rw [ha]
    exact (canonical18786 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2605 + difference 1 5) (sourceB2605 + difference 5 1) sourceC2605) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA2605 + difference 1 5) (sourceB2605 + difference 5 1) sourceC2605) = raw13775 := by
      apply Matrix.ext; unfold tripleCharges sourceA2605 sourceB2605 sourceC2605 difference raw13775; decide +kernel
    rw [ha]
    exact (canonical13775 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2605 + difference 2 0) (sourceB2605 + difference 0 2) sourceC2605) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4941) := by
    have ha : (tripleCharges (sourceA2605 + difference 2 0) (sourceB2605 + difference 0 2) sourceC2605) = raw32882 := by
      apply Matrix.ext; unfold tripleCharges sourceA2605 sourceB2605 sourceC2605 difference raw32882; decide +kernel
    rw [ha]
    exact (canonical32882 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2605 + difference 2 1) (sourceB2605 + difference 1 2) sourceC2605) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4941) := by
    have ha : (tripleCharges (sourceA2605 + difference 2 1) (sourceB2605 + difference 1 2) sourceC2605) = raw36248 := by
      apply Matrix.ext; unfold tripleCharges sourceA2605 sourceB2605 sourceC2605 difference raw36248; decide +kernel
    rw [ha]
    exact (canonical36248 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2605 + difference 2 3) (sourceB2605 + difference 3 2) sourceC2605) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5465) := by
    have ha : (tripleCharges (sourceA2605 + difference 2 3) (sourceB2605 + difference 3 2) sourceC2605) = raw36249 := by
      apply Matrix.ext; unfold tripleCharges sourceA2605 sourceB2605 sourceC2605 difference raw36249; decide +kernel
    rw [ha]
    exact (canonical36249 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2605 + difference 2 4) (sourceB2605 + difference 4 2) sourceC2605) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5465) := by
    have ha : (tripleCharges (sourceA2605 + difference 2 4) (sourceB2605 + difference 4 2) sourceC2605) = raw36250 := by
      apply Matrix.ext; unfold tripleCharges sourceA2605 sourceB2605 sourceC2605 difference raw36250; decide +kernel
    rw [ha]
    exact (canonical36250 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2605 + difference 2 5) (sourceB2605 + difference 5 2) sourceC2605) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5464) := by
    have ha : (tripleCharges (sourceA2605 + difference 2 5) (sourceB2605 + difference 5 2) sourceC2605) = raw18771 := by
      apply Matrix.ext; unfold tripleCharges sourceA2605 sourceB2605 sourceC2605 difference raw18771; decide +kernel
    rw [ha]
    exact (canonical18771 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2605 + difference 3 0) (sourceB2605 + difference 0 3) sourceC2605) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4928) := by
    have ha : (tripleCharges (sourceA2605 + difference 3 0) (sourceB2605 + difference 0 3) sourceC2605) = raw32886 := by
      apply Matrix.ext; unfold tripleCharges sourceA2605 sourceB2605 sourceC2605 difference raw32886; decide +kernel
    rw [ha]
    exact (canonical32886 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2605 + difference 3 1) (sourceB2605 + difference 1 3) sourceC2605) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4928) := by
    have ha : (tripleCharges (sourceA2605 + difference 3 1) (sourceB2605 + difference 1 3) sourceC2605) = raw36251 := by
      apply Matrix.ext; unfold tripleCharges sourceA2605 sourceB2605 sourceC2605 difference raw36251; decide +kernel
    rw [ha]
    exact (canonical36251 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2605 + difference 3 2) (sourceB2605 + difference 2 3) sourceC2605) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5334) := by
    have ha : (tripleCharges (sourceA2605 + difference 3 2) (sourceB2605 + difference 2 3) sourceC2605) = raw36252 := by
      apply Matrix.ext; unfold tripleCharges sourceA2605 sourceB2605 sourceC2605 difference raw36252; decide +kernel
    rw [ha]
    exact (canonical36252 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2605 + difference 3 4) (sourceB2605 + difference 4 3) sourceC2605) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5356) := by
    have ha : (tripleCharges (sourceA2605 + difference 3 4) (sourceB2605 + difference 4 3) sourceC2605) = raw36253 := by
      apply Matrix.ext; unfold tripleCharges sourceA2605 sourceB2605 sourceC2605 difference raw36253; decide +kernel
    rw [ha]
    exact (canonical36253 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2605 + difference 3 5) (sourceB2605 + difference 5 3) sourceC2605) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5393) := by
    have ha : (tripleCharges (sourceA2605 + difference 3 5) (sourceB2605 + difference 5 3) sourceC2605) = raw18775 := by
      apply Matrix.ext; unfold tripleCharges sourceA2605 sourceB2605 sourceC2605 difference raw18775; decide +kernel
    rw [ha]
    exact (canonical18775 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2605 + difference 4 0) (sourceB2605 + difference 0 4) sourceC2605) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4928) := by
    have ha : (tripleCharges (sourceA2605 + difference 4 0) (sourceB2605 + difference 0 4) sourceC2605) = raw32890 := by
      apply Matrix.ext; unfold tripleCharges sourceA2605 sourceB2605 sourceC2605 difference raw32890; decide +kernel
    rw [ha]
    exact (canonical32890 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2605 + difference 4 1) (sourceB2605 + difference 1 4) sourceC2605) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4928) := by
    have ha : (tripleCharges (sourceA2605 + difference 4 1) (sourceB2605 + difference 1 4) sourceC2605) = raw36254 := by
      apply Matrix.ext; unfold tripleCharges sourceA2605 sourceB2605 sourceC2605 difference raw36254; decide +kernel
    rw [ha]
    exact (canonical36254 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2605 + difference 4 2) (sourceB2605 + difference 2 4) sourceC2605) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5334) := by
    have ha : (tripleCharges (sourceA2605 + difference 4 2) (sourceB2605 + difference 2 4) sourceC2605) = raw36255 := by
      apply Matrix.ext; unfold tripleCharges sourceA2605 sourceB2605 sourceC2605 difference raw36255; decide +kernel
    rw [ha]
    exact (canonical36255 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2605 + difference 4 3) (sourceB2605 + difference 3 4) sourceC2605) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5356) := by
    have ha : (tripleCharges (sourceA2605 + difference 4 3) (sourceB2605 + difference 3 4) sourceC2605) = raw36256 := by
      apply Matrix.ext; unfold tripleCharges sourceA2605 sourceB2605 sourceC2605 difference raw36256; decide +kernel
    rw [ha]
    exact (canonical36256 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2605 + difference 4 5) (sourceB2605 + difference 5 4) sourceC2605) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5393) := by
    have ha : (tripleCharges (sourceA2605 + difference 4 5) (sourceB2605 + difference 5 4) sourceC2605) = raw18779 := by
      apply Matrix.ext; unfold tripleCharges sourceA2605 sourceB2605 sourceC2605 difference raw18779; decide +kernel
    rw [ha]
    exact (canonical18779 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2605 + difference 5 0) (sourceB2605 + difference 0 5) sourceC2605) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4927) := by
    have ha : (tripleCharges (sourceA2605 + difference 5 0) (sourceB2605 + difference 0 5) sourceC2605) = raw32894 := by
      apply Matrix.ext; unfold tripleCharges sourceA2605 sourceB2605 sourceC2605 difference raw32894; decide +kernel
    rw [ha]
    exact (canonical32894 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2605 + difference 5 1) (sourceB2605 + difference 1 5) sourceC2605) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4927) := by
    have ha : (tripleCharges (sourceA2605 + difference 5 1) (sourceB2605 + difference 1 5) sourceC2605) = raw36257 := by
      apply Matrix.ext; unfold tripleCharges sourceA2605 sourceB2605 sourceC2605 difference raw36257; decide +kernel
    rw [ha]
    exact (canonical36257 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2605 + difference 5 2) (sourceB2605 + difference 2 5) sourceC2605) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5031) := by
    have ha : (tripleCharges (sourceA2605 + difference 5 2) (sourceB2605 + difference 2 5) sourceC2605) = raw36258 := by
      apply Matrix.ext; unfold tripleCharges sourceA2605 sourceB2605 sourceC2605 difference raw36258; decide +kernel
    rw [ha]
    exact (canonical36258 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2605 + difference 5 3) (sourceB2605 + difference 3 5) sourceC2605) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5081) := by
    have ha : (tripleCharges (sourceA2605 + difference 5 3) (sourceB2605 + difference 3 5) sourceC2605) = raw36259 := by
      apply Matrix.ext; unfold tripleCharges sourceA2605 sourceB2605 sourceC2605 difference raw36259; decide +kernel
    rw [ha]
    exact (canonical36259 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2605 + difference 5 4) (sourceB2605 + difference 4 5) sourceC2605) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5081) := by
    have ha : (tripleCharges (sourceA2605 + difference 5 4) (sourceB2605 + difference 4 5) sourceC2605) = raw36260 := by
      apply Matrix.ext; unfold tripleCharges sourceA2605 sourceB2605 sourceC2605 difference raw36260; decide +kernel
    rw [ha]
    exact (canonical36260 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2605 sourceB2605 sourceC2605
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2605, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2606 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2606 : Charge := ![1, 1, 1, -1, -1, -1]
def sourceC2606 : Charge := ![1, 1, -1, 0, 0, -1]
def sourceForm2606 : Integer.Sparse Master := [(Sum.inr 2317, 2), (Sum.inr 2318, 4), (Sum.inr 2332, 2), (Sum.inr 2420, 1), (Sum.inr 2489, 2), (Sum.inr 2556, 2), (Sum.inr 3669, 2), (Sum.inr 3694, 2), (Sum.inr 3779, 2), (Sum.inr 3930, 1), (Sum.inr 3931, 2), (Sum.inr 3945, 2), (Sum.inr 3981, 4), (Sum.inr 3992, 2)]

theorem sourceEq2606 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2606 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2606 + difference 0 1) (sourceB2606 + difference 1 0) sourceC2606) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2556) := by
    have ha : (tripleCharges (sourceA2606 + difference 0 1) (sourceB2606 + difference 1 0) sourceC2606) = raw36261 := by
      apply Matrix.ext; unfold tripleCharges sourceA2606 sourceB2606 sourceC2606 difference raw36261; decide +kernel
    rw [ha]
    exact (canonical36261 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2606 + difference 0 2) (sourceB2606 + difference 2 0) sourceC2606) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3945) := by
    have ha : (tripleCharges (sourceA2606 + difference 0 2) (sourceB2606 + difference 2 0) sourceC2606) = raw36262 := by
      apply Matrix.ext; unfold tripleCharges sourceA2606 sourceB2606 sourceC2606 difference raw36262; decide +kernel
    rw [ha]
    exact (canonical36262 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2606 + difference 0 3) (sourceB2606 + difference 3 0) sourceC2606) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3981) := by
    have ha : (tripleCharges (sourceA2606 + difference 0 3) (sourceB2606 + difference 3 0) sourceC2606) = raw36263 := by
      apply Matrix.ext; unfold tripleCharges sourceA2606 sourceB2606 sourceC2606 difference raw36263; decide +kernel
    rw [ha]
    exact (canonical36263 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2606 + difference 0 4) (sourceB2606 + difference 4 0) sourceC2606) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3981) := by
    have ha : (tripleCharges (sourceA2606 + difference 0 4) (sourceB2606 + difference 4 0) sourceC2606) = raw36264 := by
      apply Matrix.ext; unfold tripleCharges sourceA2606 sourceB2606 sourceC2606 difference raw36264; decide +kernel
    rw [ha]
    exact (canonical36264 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2606 + difference 0 5) (sourceB2606 + difference 5 0) sourceC2606) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3992) := by
    have ha : (tripleCharges (sourceA2606 + difference 0 5) (sourceB2606 + difference 5 0) sourceC2606) = raw36265 := by
      apply Matrix.ext; unfold tripleCharges sourceA2606 sourceB2606 sourceC2606 difference raw36265; decide +kernel
    rw [ha]
    exact (canonical36265 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2606 + difference 1 0) (sourceB2606 + difference 0 1) sourceC2606) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2556) := by
    have ha : (tripleCharges (sourceA2606 + difference 1 0) (sourceB2606 + difference 0 1) sourceC2606) = raw13831 := by
      apply Matrix.ext; unfold tripleCharges sourceA2606 sourceB2606 sourceC2606 difference raw13831; decide +kernel
    rw [ha]
    exact (canonical13831 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2606 + difference 1 2) (sourceB2606 + difference 2 1) sourceC2606) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3945) := by
    have ha : (tripleCharges (sourceA2606 + difference 1 2) (sourceB2606 + difference 2 1) sourceC2606) = raw36266 := by
      apply Matrix.ext; unfold tripleCharges sourceA2606 sourceB2606 sourceC2606 difference raw36266; decide +kernel
    rw [ha]
    exact (canonical36266 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2606 + difference 1 3) (sourceB2606 + difference 3 1) sourceC2606) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3981) := by
    have ha : (tripleCharges (sourceA2606 + difference 1 3) (sourceB2606 + difference 3 1) sourceC2606) = raw36267 := by
      apply Matrix.ext; unfold tripleCharges sourceA2606 sourceB2606 sourceC2606 difference raw36267; decide +kernel
    rw [ha]
    exact (canonical36267 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2606 + difference 1 4) (sourceB2606 + difference 4 1) sourceC2606) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3981) := by
    have ha : (tripleCharges (sourceA2606 + difference 1 4) (sourceB2606 + difference 4 1) sourceC2606) = raw36268 := by
      apply Matrix.ext; unfold tripleCharges sourceA2606 sourceB2606 sourceC2606 difference raw36268; decide +kernel
    rw [ha]
    exact (canonical36268 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2606 + difference 1 5) (sourceB2606 + difference 5 1) sourceC2606) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3992) := by
    have ha : (tripleCharges (sourceA2606 + difference 1 5) (sourceB2606 + difference 5 1) sourceC2606) = raw13805 := by
      apply Matrix.ext; unfold tripleCharges sourceA2606 sourceB2606 sourceC2606 difference raw13805; decide +kernel
    rw [ha]
    exact (canonical13805 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2606 + difference 2 0) (sourceB2606 + difference 0 2) sourceC2606) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2332) := by
    have ha : (tripleCharges (sourceA2606 + difference 2 0) (sourceB2606 + difference 0 2) sourceC2606) = raw36269 := by
      apply Matrix.ext; unfold tripleCharges sourceA2606 sourceB2606 sourceC2606 difference raw36269; decide +kernel
    rw [ha]
    exact (canonical36269 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2606 + difference 2 1) (sourceB2606 + difference 1 2) sourceC2606) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2332) := by
    have ha : (tripleCharges (sourceA2606 + difference 2 1) (sourceB2606 + difference 1 2) sourceC2606) = raw36270 := by
      apply Matrix.ext; unfold tripleCharges sourceA2606 sourceB2606 sourceC2606 difference raw36270; decide +kernel
    rw [ha]
    exact (canonical36270 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2606 + difference 2 3) (sourceB2606 + difference 3 2) sourceC2606) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3931) := by
    have ha : (tripleCharges (sourceA2606 + difference 2 3) (sourceB2606 + difference 3 2) sourceC2606) = raw36271 := by
      apply Matrix.ext; unfold tripleCharges sourceA2606 sourceB2606 sourceC2606 difference raw36271; decide +kernel
    rw [ha]
    exact (canonical36271 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2606 + difference 2 4) (sourceB2606 + difference 4 2) sourceC2606) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3931) := by
    have ha : (tripleCharges (sourceA2606 + difference 2 4) (sourceB2606 + difference 4 2) sourceC2606) = raw36272 := by
      apply Matrix.ext; unfold tripleCharges sourceA2606 sourceB2606 sourceC2606 difference raw36272; decide +kernel
    rw [ha]
    exact (canonical36272 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2606 + difference 2 5) (sourceB2606 + difference 5 2) sourceC2606) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3930) := by
    have ha : (tripleCharges (sourceA2606 + difference 2 5) (sourceB2606 + difference 5 2) sourceC2606) = raw36273 := by
      apply Matrix.ext; unfold tripleCharges sourceA2606 sourceB2606 sourceC2606 difference raw36273; decide +kernel
    rw [ha]
    exact (canonical36273 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2606 + difference 3 0) (sourceB2606 + difference 0 3) sourceC2606) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2318) := by
    have ha : (tripleCharges (sourceA2606 + difference 3 0) (sourceB2606 + difference 0 3) sourceC2606) = raw36274 := by
      apply Matrix.ext; unfold tripleCharges sourceA2606 sourceB2606 sourceC2606 difference raw36274; decide +kernel
    rw [ha]
    exact (canonical36274 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2606 + difference 3 1) (sourceB2606 + difference 1 3) sourceC2606) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2318) := by
    have ha : (tripleCharges (sourceA2606 + difference 3 1) (sourceB2606 + difference 1 3) sourceC2606) = raw36275 := by
      apply Matrix.ext; unfold tripleCharges sourceA2606 sourceB2606 sourceC2606 difference raw36275; decide +kernel
    rw [ha]
    exact (canonical36275 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2606 + difference 3 2) (sourceB2606 + difference 2 3) sourceC2606) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3669) := by
    have ha : (tripleCharges (sourceA2606 + difference 3 2) (sourceB2606 + difference 2 3) sourceC2606) = raw36276 := by
      apply Matrix.ext; unfold tripleCharges sourceA2606 sourceB2606 sourceC2606 difference raw36276; decide +kernel
    rw [ha]
    exact (canonical36276 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2606 + difference 3 4) (sourceB2606 + difference 4 3) sourceC2606) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3694) := by
    have ha : (tripleCharges (sourceA2606 + difference 3 4) (sourceB2606 + difference 4 3) sourceC2606) = raw36277 := by
      apply Matrix.ext; unfold tripleCharges sourceA2606 sourceB2606 sourceC2606 difference raw36277; decide +kernel
    rw [ha]
    exact (canonical36277 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2606 + difference 3 5) (sourceB2606 + difference 5 3) sourceC2606) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3779) := by
    have ha : (tripleCharges (sourceA2606 + difference 3 5) (sourceB2606 + difference 5 3) sourceC2606) = raw36278 := by
      apply Matrix.ext; unfold tripleCharges sourceA2606 sourceB2606 sourceC2606 difference raw36278; decide +kernel
    rw [ha]
    exact (canonical36278 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2606 + difference 4 0) (sourceB2606 + difference 0 4) sourceC2606) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2318) := by
    have ha : (tripleCharges (sourceA2606 + difference 4 0) (sourceB2606 + difference 0 4) sourceC2606) = raw36279 := by
      apply Matrix.ext; unfold tripleCharges sourceA2606 sourceB2606 sourceC2606 difference raw36279; decide +kernel
    rw [ha]
    exact (canonical36279 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2606 + difference 4 1) (sourceB2606 + difference 1 4) sourceC2606) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2318) := by
    have ha : (tripleCharges (sourceA2606 + difference 4 1) (sourceB2606 + difference 1 4) sourceC2606) = raw36280 := by
      apply Matrix.ext; unfold tripleCharges sourceA2606 sourceB2606 sourceC2606 difference raw36280; decide +kernel
    rw [ha]
    exact (canonical36280 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2606 + difference 4 2) (sourceB2606 + difference 2 4) sourceC2606) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3669) := by
    have ha : (tripleCharges (sourceA2606 + difference 4 2) (sourceB2606 + difference 2 4) sourceC2606) = raw36281 := by
      apply Matrix.ext; unfold tripleCharges sourceA2606 sourceB2606 sourceC2606 difference raw36281; decide +kernel
    rw [ha]
    exact (canonical36281 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2606 + difference 4 3) (sourceB2606 + difference 3 4) sourceC2606) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3694) := by
    have ha : (tripleCharges (sourceA2606 + difference 4 3) (sourceB2606 + difference 3 4) sourceC2606) = raw36282 := by
      apply Matrix.ext; unfold tripleCharges sourceA2606 sourceB2606 sourceC2606 difference raw36282; decide +kernel
    rw [ha]
    exact (canonical36282 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2606 + difference 4 5) (sourceB2606 + difference 5 4) sourceC2606) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3779) := by
    have ha : (tripleCharges (sourceA2606 + difference 4 5) (sourceB2606 + difference 5 4) sourceC2606) = raw36283 := by
      apply Matrix.ext; unfold tripleCharges sourceA2606 sourceB2606 sourceC2606 difference raw36283; decide +kernel
    rw [ha]
    exact (canonical36283 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2606 + difference 5 0) (sourceB2606 + difference 0 5) sourceC2606) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2317) := by
    have ha : (tripleCharges (sourceA2606 + difference 5 0) (sourceB2606 + difference 0 5) sourceC2606) = raw36284 := by
      apply Matrix.ext; unfold tripleCharges sourceA2606 sourceB2606 sourceC2606 difference raw36284; decide +kernel
    rw [ha]
    exact (canonical36284 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2606 + difference 5 1) (sourceB2606 + difference 1 5) sourceC2606) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2317) := by
    have ha : (tripleCharges (sourceA2606 + difference 5 1) (sourceB2606 + difference 1 5) sourceC2606) = raw36285 := by
      apply Matrix.ext; unfold tripleCharges sourceA2606 sourceB2606 sourceC2606 difference raw36285; decide +kernel
    rw [ha]
    exact (canonical36285 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2606 + difference 5 2) (sourceB2606 + difference 2 5) sourceC2606) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2420) := by
    have ha : (tripleCharges (sourceA2606 + difference 5 2) (sourceB2606 + difference 2 5) sourceC2606) = raw36286 := by
      apply Matrix.ext; unfold tripleCharges sourceA2606 sourceB2606 sourceC2606 difference raw36286; decide +kernel
    rw [ha]
    exact (canonical36286 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2606 + difference 5 3) (sourceB2606 + difference 3 5) sourceC2606) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2489) := by
    have ha : (tripleCharges (sourceA2606 + difference 5 3) (sourceB2606 + difference 3 5) sourceC2606) = raw36287 := by
      apply Matrix.ext; unfold tripleCharges sourceA2606 sourceB2606 sourceC2606 difference raw36287; decide +kernel
    rw [ha]
    exact (canonical36287 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2606 + difference 5 4) (sourceB2606 + difference 4 5) sourceC2606) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2489) := by
    have ha : (tripleCharges (sourceA2606 + difference 5 4) (sourceB2606 + difference 4 5) sourceC2606) = raw36288 := by
      apply Matrix.ext; unfold tripleCharges sourceA2606 sourceB2606 sourceC2606 difference raw36288; decide +kernel
    rw [ha]
    exact (canonical36288 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2606 sourceB2606 sourceC2606
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2606, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2607 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2607 : Charge := ![1, 1, -1, 0, -1, 0]
def sourceC2607 : Charge := ![1, 1, 1, -1, 0, -2]
def sourceForm2607 : Integer.Sparse Master := [(Sum.inr 4930, 2), (Sum.inr 4931, 2), (Sum.inr 4933, 2), (Sum.inr 4942, 2), (Sum.inr 5039, 1), (Sum.inr 5081, 1), (Sum.inr 5130, 1), (Sum.inr 5149, 2), (Sum.inr 5337, 1), (Sum.inr 5356, 1), (Sum.inr 5373, 1), (Sum.inr 5377, 1), (Sum.inr 5396, 2), (Sum.inr 5404, 1), (Sum.inr 5410, 2), (Sum.inr 5419, 2), (Sum.inr 5424, 2), (Sum.inr 5459, 1), (Sum.inr 5461, 1), (Sum.inr 5478, 2)]

theorem sourceEq2607 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2607 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2607 + difference 0 1) (sourceB2607 + difference 1 0) sourceC2607) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5149) := by
    have ha : (tripleCharges (sourceA2607 + difference 0 1) (sourceB2607 + difference 1 0) sourceC2607) = raw36289 := by
      apply Matrix.ext; unfold tripleCharges sourceA2607 sourceB2607 sourceC2607 difference raw36289; decide +kernel
    rw [ha]
    exact (canonical36289 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2607 + difference 0 2) (sourceB2607 + difference 2 0) sourceC2607) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5396) := by
    have ha : (tripleCharges (sourceA2607 + difference 0 2) (sourceB2607 + difference 2 0) sourceC2607) = raw36290 := by
      apply Matrix.ext; unfold tripleCharges sourceA2607 sourceB2607 sourceC2607 difference raw36290; decide +kernel
    rw [ha]
    exact (canonical36290 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2607 + difference 0 3) (sourceB2607 + difference 3 0) sourceC2607) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA2607 + difference 0 3) (sourceB2607 + difference 3 0) sourceC2607) = raw36291 := by
      apply Matrix.ext; unfold tripleCharges sourceA2607 sourceB2607 sourceC2607 difference raw36291; decide +kernel
    rw [ha]
    exact (canonical36291 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2607 + difference 0 4) (sourceB2607 + difference 4 0) sourceC2607) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5410) := by
    have ha : (tripleCharges (sourceA2607 + difference 0 4) (sourceB2607 + difference 4 0) sourceC2607) = raw36292 := by
      apply Matrix.ext; unfold tripleCharges sourceA2607 sourceB2607 sourceC2607 difference raw36292; decide +kernel
    rw [ha]
    exact (canonical36292 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2607 + difference 0 5) (sourceB2607 + difference 5 0) sourceC2607) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5478) := by
    have ha : (tripleCharges (sourceA2607 + difference 0 5) (sourceB2607 + difference 5 0) sourceC2607) = raw36293 := by
      apply Matrix.ext; unfold tripleCharges sourceA2607 sourceB2607 sourceC2607 difference raw36293; decide +kernel
    rw [ha]
    exact (canonical36293 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2607 + difference 1 0) (sourceB2607 + difference 0 1) sourceC2607) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5149) := by
    have ha : (tripleCharges (sourceA2607 + difference 1 0) (sourceB2607 + difference 0 1) sourceC2607) = raw36294 := by
      apply Matrix.ext; unfold tripleCharges sourceA2607 sourceB2607 sourceC2607 difference raw36294; decide +kernel
    rw [ha]
    exact (canonical36294 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2607 + difference 1 2) (sourceB2607 + difference 2 1) sourceC2607) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5396) := by
    have ha : (tripleCharges (sourceA2607 + difference 1 2) (sourceB2607 + difference 2 1) sourceC2607) = raw32383 := by
      apply Matrix.ext; unfold tripleCharges sourceA2607 sourceB2607 sourceC2607 difference raw32383; decide +kernel
    rw [ha]
    exact (canonical32383 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2607 + difference 1 3) (sourceB2607 + difference 3 1) sourceC2607) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA2607 + difference 1 3) (sourceB2607 + difference 3 1) sourceC2607) = raw32384 := by
      apply Matrix.ext; unfold tripleCharges sourceA2607 sourceB2607 sourceC2607 difference raw32384; decide +kernel
    rw [ha]
    exact (canonical32384 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2607 + difference 1 4) (sourceB2607 + difference 4 1) sourceC2607) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5410) := by
    have ha : (tripleCharges (sourceA2607 + difference 1 4) (sourceB2607 + difference 4 1) sourceC2607) = raw32385 := by
      apply Matrix.ext; unfold tripleCharges sourceA2607 sourceB2607 sourceC2607 difference raw32385; decide +kernel
    rw [ha]
    exact (canonical32385 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2607 + difference 1 5) (sourceB2607 + difference 5 1) sourceC2607) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5478) := by
    have ha : (tripleCharges (sourceA2607 + difference 1 5) (sourceB2607 + difference 5 1) sourceC2607) = raw32386 := by
      apply Matrix.ext; unfold tripleCharges sourceA2607 sourceB2607 sourceC2607 difference raw32386; decide +kernel
    rw [ha]
    exact (canonical32386 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2607 + difference 2 0) (sourceB2607 + difference 0 2) sourceC2607) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4942) := by
    have ha : (tripleCharges (sourceA2607 + difference 2 0) (sourceB2607 + difference 0 2) sourceC2607) = raw32393 := by
      apply Matrix.ext; unfold tripleCharges sourceA2607 sourceB2607 sourceC2607 difference raw32393; decide +kernel
    rw [ha]
    exact (canonical32393 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2607 + difference 2 1) (sourceB2607 + difference 1 2) sourceC2607) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4942) := by
    have ha : (tripleCharges (sourceA2607 + difference 2 1) (sourceB2607 + difference 1 2) sourceC2607) = raw36295 := by
      apply Matrix.ext; unfold tripleCharges sourceA2607 sourceB2607 sourceC2607 difference raw36295; decide +kernel
    rw [ha]
    exact (canonical36295 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2607 + difference 2 3) (sourceB2607 + difference 3 2) sourceC2607) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5419) := by
    have ha : (tripleCharges (sourceA2607 + difference 2 3) (sourceB2607 + difference 3 2) sourceC2607) = raw36296 := by
      apply Matrix.ext; unfold tripleCharges sourceA2607 sourceB2607 sourceC2607 difference raw36296; decide +kernel
    rw [ha]
    exact (canonical36296 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2607 + difference 2 4) (sourceB2607 + difference 4 2) sourceC2607) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5404) := by
    have ha : (tripleCharges (sourceA2607 + difference 2 4) (sourceB2607 + difference 4 2) sourceC2607) = raw36297 := by
      apply Matrix.ext; unfold tripleCharges sourceA2607 sourceB2607 sourceC2607 difference raw36297; decide +kernel
    rw [ha]
    exact (canonical36297 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2607 + difference 2 5) (sourceB2607 + difference 5 2) sourceC2607) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5461) := by
    have ha : (tripleCharges (sourceA2607 + difference 2 5) (sourceB2607 + difference 5 2) sourceC2607) = raw36298 := by
      apply Matrix.ext; unfold tripleCharges sourceA2607 sourceB2607 sourceC2607 difference raw36298; decide +kernel
    rw [ha]
    exact (canonical36298 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2607 + difference 3 0) (sourceB2607 + difference 0 3) sourceC2607) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4933) := by
    have ha : (tripleCharges (sourceA2607 + difference 3 0) (sourceB2607 + difference 0 3) sourceC2607) = raw32398 := by
      apply Matrix.ext; unfold tripleCharges sourceA2607 sourceB2607 sourceC2607 difference raw32398; decide +kernel
    rw [ha]
    exact (canonical32398 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2607 + difference 3 1) (sourceB2607 + difference 1 3) sourceC2607) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4933) := by
    have ha : (tripleCharges (sourceA2607 + difference 3 1) (sourceB2607 + difference 1 3) sourceC2607) = raw36299 := by
      apply Matrix.ext; unfold tripleCharges sourceA2607 sourceB2607 sourceC2607 difference raw36299; decide +kernel
    rw [ha]
    exact (canonical36299 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2607 + difference 3 2) (sourceB2607 + difference 2 3) sourceC2607) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5337) := by
    have ha : (tripleCharges (sourceA2607 + difference 3 2) (sourceB2607 + difference 2 3) sourceC2607) = raw36300 := by
      apply Matrix.ext; unfold tripleCharges sourceA2607 sourceB2607 sourceC2607 difference raw36300; decide +kernel
    rw [ha]
    exact (canonical36300 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2607 + difference 3 4) (sourceB2607 + difference 4 3) sourceC2607) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5356) := by
    have ha : (tripleCharges (sourceA2607 + difference 3 4) (sourceB2607 + difference 4 3) sourceC2607) = raw36301 := by
      apply Matrix.ext; unfold tripleCharges sourceA2607 sourceB2607 sourceC2607 difference raw36301; decide +kernel
    rw [ha]
    exact (canonical36301 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2607 + difference 3 5) (sourceB2607 + difference 5 3) sourceC2607) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5459) := by
    have ha : (tripleCharges (sourceA2607 + difference 3 5) (sourceB2607 + difference 5 3) sourceC2607) = raw36302 := by
      apply Matrix.ext; unfold tripleCharges sourceA2607 sourceB2607 sourceC2607 difference raw36302; decide +kernel
    rw [ha]
    exact (canonical36302 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2607 + difference 4 0) (sourceB2607 + difference 0 4) sourceC2607) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4931) := by
    have ha : (tripleCharges (sourceA2607 + difference 4 0) (sourceB2607 + difference 0 4) sourceC2607) = raw32403 := by
      apply Matrix.ext; unfold tripleCharges sourceA2607 sourceB2607 sourceC2607 difference raw32403; decide +kernel
    rw [ha]
    exact (canonical32403 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2607 + difference 4 1) (sourceB2607 + difference 1 4) sourceC2607) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4931) := by
    have ha : (tripleCharges (sourceA2607 + difference 4 1) (sourceB2607 + difference 1 4) sourceC2607) = raw36303 := by
      apply Matrix.ext; unfold tripleCharges sourceA2607 sourceB2607 sourceC2607 difference raw36303; decide +kernel
    rw [ha]
    exact (canonical36303 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2607 + difference 4 2) (sourceB2607 + difference 2 4) sourceC2607) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5373) := by
    have ha : (tripleCharges (sourceA2607 + difference 4 2) (sourceB2607 + difference 2 4) sourceC2607) = raw36304 := by
      apply Matrix.ext; unfold tripleCharges sourceA2607 sourceB2607 sourceC2607 difference raw36304; decide +kernel
    rw [ha]
    exact (canonical36304 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2607 + difference 4 3) (sourceB2607 + difference 3 4) sourceC2607) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5377) := by
    have ha : (tripleCharges (sourceA2607 + difference 4 3) (sourceB2607 + difference 3 4) sourceC2607) = raw36305 := by
      apply Matrix.ext; unfold tripleCharges sourceA2607 sourceB2607 sourceC2607 difference raw36305; decide +kernel
    rw [ha]
    exact (canonical36305 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2607 + difference 4 5) (sourceB2607 + difference 5 4) sourceC2607) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5419) := by
    have ha : (tripleCharges (sourceA2607 + difference 4 5) (sourceB2607 + difference 5 4) sourceC2607) = raw36306 := by
      apply Matrix.ext; unfold tripleCharges sourceA2607 sourceB2607 sourceC2607 difference raw36306; decide +kernel
    rw [ha]
    exact (canonical36306 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2607 + difference 5 0) (sourceB2607 + difference 0 5) sourceC2607) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4930) := by
    have ha : (tripleCharges (sourceA2607 + difference 5 0) (sourceB2607 + difference 0 5) sourceC2607) = raw32408 := by
      apply Matrix.ext; unfold tripleCharges sourceA2607 sourceB2607 sourceC2607 difference raw32408; decide +kernel
    rw [ha]
    exact (canonical32408 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2607 + difference 5 1) (sourceB2607 + difference 1 5) sourceC2607) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4930) := by
    have ha : (tripleCharges (sourceA2607 + difference 5 1) (sourceB2607 + difference 1 5) sourceC2607) = raw36307 := by
      apply Matrix.ext; unfold tripleCharges sourceA2607 sourceB2607 sourceC2607 difference raw36307; decide +kernel
    rw [ha]
    exact (canonical36307 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2607 + difference 5 2) (sourceB2607 + difference 2 5) sourceC2607) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5039) := by
    have ha : (tripleCharges (sourceA2607 + difference 5 2) (sourceB2607 + difference 2 5) sourceC2607) = raw36308 := by
      apply Matrix.ext; unfold tripleCharges sourceA2607 sourceB2607 sourceC2607 difference raw36308; decide +kernel
    rw [ha]
    exact (canonical36308 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2607 + difference 5 3) (sourceB2607 + difference 3 5) sourceC2607) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5130) := by
    have ha : (tripleCharges (sourceA2607 + difference 5 3) (sourceB2607 + difference 3 5) sourceC2607) = raw36309 := by
      apply Matrix.ext; unfold tripleCharges sourceA2607 sourceB2607 sourceC2607 difference raw36309; decide +kernel
    rw [ha]
    exact (canonical36309 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2607 + difference 5 4) (sourceB2607 + difference 4 5) sourceC2607) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5081) := by
    have ha : (tripleCharges (sourceA2607 + difference 5 4) (sourceB2607 + difference 4 5) sourceC2607) = raw36310 := by
      apply Matrix.ext; unfold tripleCharges sourceA2607 sourceB2607 sourceC2607 difference raw36310; decide +kernel
    rw [ha]
    exact (canonical36310 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2607 sourceB2607 sourceC2607
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2607, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2608 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2608 : Charge := ![1, 1, -1, 0, -1, 0]
def sourceC2608 : Charge := ![1, 1, 1, -1, 0, -2]
def sourceForm2608 : Integer.Sparse Master := [(Sum.inr 3406, 2), (Sum.inr 3407, 2), (Sum.inr 3408, 2), (Sum.inr 3414, 2), (Sum.inr 3456, 1), (Sum.inr 3482, 1), (Sum.inr 3520, 1), (Sum.inr 3605, 2), (Sum.inr 3756, 1), (Sum.inr 3773, 1), (Sum.inr 3792, 1), (Sum.inr 3798, 2), (Sum.inr 3815, 1), (Sum.inr 3816, 2), (Sum.inr 3835, 1), (Sum.inr 3842, 2), (Sum.inr 3843, 2), (Sum.inr 3951, 1), (Sum.inr 3973, 1), (Sum.inr 3974, 2)]

theorem sourceEq2608 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2608 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2608 + difference 0 1) (sourceB2608 + difference 1 0) sourceC2608) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3605) := by
    have ha : (tripleCharges (sourceA2608 + difference 0 1) (sourceB2608 + difference 1 0) sourceC2608) = raw36311 := by
      apply Matrix.ext; unfold tripleCharges sourceA2608 sourceB2608 sourceC2608 difference raw36311; decide +kernel
    rw [ha]
    exact (canonical36311 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2608 + difference 0 2) (sourceB2608 + difference 2 0) sourceC2608) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3798) := by
    have ha : (tripleCharges (sourceA2608 + difference 0 2) (sourceB2608 + difference 2 0) sourceC2608) = raw36312 := by
      apply Matrix.ext; unfold tripleCharges sourceA2608 sourceB2608 sourceC2608 difference raw36312; decide +kernel
    rw [ha]
    exact (canonical36312 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2608 + difference 0 3) (sourceB2608 + difference 3 0) sourceC2608) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3843) := by
    have ha : (tripleCharges (sourceA2608 + difference 0 3) (sourceB2608 + difference 3 0) sourceC2608) = raw36313 := by
      apply Matrix.ext; unfold tripleCharges sourceA2608 sourceB2608 sourceC2608 difference raw36313; decide +kernel
    rw [ha]
    exact (canonical36313 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2608 + difference 0 4) (sourceB2608 + difference 4 0) sourceC2608) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3816) := by
    have ha : (tripleCharges (sourceA2608 + difference 0 4) (sourceB2608 + difference 4 0) sourceC2608) = raw36314 := by
      apply Matrix.ext; unfold tripleCharges sourceA2608 sourceB2608 sourceC2608 difference raw36314; decide +kernel
    rw [ha]
    exact (canonical36314 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2608 + difference 0 5) (sourceB2608 + difference 5 0) sourceC2608) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3974) := by
    have ha : (tripleCharges (sourceA2608 + difference 0 5) (sourceB2608 + difference 5 0) sourceC2608) = raw36315 := by
      apply Matrix.ext; unfold tripleCharges sourceA2608 sourceB2608 sourceC2608 difference raw36315; decide +kernel
    rw [ha]
    exact (canonical36315 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2608 + difference 1 0) (sourceB2608 + difference 0 1) sourceC2608) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3605) := by
    have ha : (tripleCharges (sourceA2608 + difference 1 0) (sourceB2608 + difference 0 1) sourceC2608) = raw36316 := by
      apply Matrix.ext; unfold tripleCharges sourceA2608 sourceB2608 sourceC2608 difference raw36316; decide +kernel
    rw [ha]
    exact (canonical36316 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2608 + difference 1 2) (sourceB2608 + difference 2 1) sourceC2608) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3798) := by
    have ha : (tripleCharges (sourceA2608 + difference 1 2) (sourceB2608 + difference 2 1) sourceC2608) = raw32443 := by
      apply Matrix.ext; unfold tripleCharges sourceA2608 sourceB2608 sourceC2608 difference raw32443; decide +kernel
    rw [ha]
    exact (canonical32443 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2608 + difference 1 3) (sourceB2608 + difference 3 1) sourceC2608) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3843) := by
    have ha : (tripleCharges (sourceA2608 + difference 1 3) (sourceB2608 + difference 3 1) sourceC2608) = raw32444 := by
      apply Matrix.ext; unfold tripleCharges sourceA2608 sourceB2608 sourceC2608 difference raw32444; decide +kernel
    rw [ha]
    exact (canonical32444 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2608 + difference 1 4) (sourceB2608 + difference 4 1) sourceC2608) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3816) := by
    have ha : (tripleCharges (sourceA2608 + difference 1 4) (sourceB2608 + difference 4 1) sourceC2608) = raw32445 := by
      apply Matrix.ext; unfold tripleCharges sourceA2608 sourceB2608 sourceC2608 difference raw32445; decide +kernel
    rw [ha]
    exact (canonical32445 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2608 + difference 1 5) (sourceB2608 + difference 5 1) sourceC2608) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3974) := by
    have ha : (tripleCharges (sourceA2608 + difference 1 5) (sourceB2608 + difference 5 1) sourceC2608) = raw32446 := by
      apply Matrix.ext; unfold tripleCharges sourceA2608 sourceB2608 sourceC2608 difference raw32446; decide +kernel
    rw [ha]
    exact (canonical32446 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2608 + difference 2 0) (sourceB2608 + difference 0 2) sourceC2608) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3407) := by
    have ha : (tripleCharges (sourceA2608 + difference 2 0) (sourceB2608 + difference 0 2) sourceC2608) = raw32453 := by
      apply Matrix.ext; unfold tripleCharges sourceA2608 sourceB2608 sourceC2608 difference raw32453; decide +kernel
    rw [ha]
    exact (canonical32453 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2608 + difference 2 1) (sourceB2608 + difference 1 2) sourceC2608) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3407) := by
    have ha : (tripleCharges (sourceA2608 + difference 2 1) (sourceB2608 + difference 1 2) sourceC2608) = raw36317 := by
      apply Matrix.ext; unfold tripleCharges sourceA2608 sourceB2608 sourceC2608 difference raw36317; decide +kernel
    rw [ha]
    exact (canonical36317 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2608 + difference 2 3) (sourceB2608 + difference 3 2) sourceC2608) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3842) := by
    have ha : (tripleCharges (sourceA2608 + difference 2 3) (sourceB2608 + difference 3 2) sourceC2608) = raw36318 := by
      apply Matrix.ext; unfold tripleCharges sourceA2608 sourceB2608 sourceC2608 difference raw36318; decide +kernel
    rw [ha]
    exact (canonical36318 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2608 + difference 2 4) (sourceB2608 + difference 4 2) sourceC2608) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3815) := by
    have ha : (tripleCharges (sourceA2608 + difference 2 4) (sourceB2608 + difference 4 2) sourceC2608) = raw36319 := by
      apply Matrix.ext; unfold tripleCharges sourceA2608 sourceB2608 sourceC2608 difference raw36319; decide +kernel
    rw [ha]
    exact (canonical36319 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2608 + difference 2 5) (sourceB2608 + difference 5 2) sourceC2608) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3973) := by
    have ha : (tripleCharges (sourceA2608 + difference 2 5) (sourceB2608 + difference 5 2) sourceC2608) = raw36320 := by
      apply Matrix.ext; unfold tripleCharges sourceA2608 sourceB2608 sourceC2608 difference raw36320; decide +kernel
    rw [ha]
    exact (canonical36320 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2608 + difference 3 0) (sourceB2608 + difference 0 3) sourceC2608) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3414) := by
    have ha : (tripleCharges (sourceA2608 + difference 3 0) (sourceB2608 + difference 0 3) sourceC2608) = raw32458 := by
      apply Matrix.ext; unfold tripleCharges sourceA2608 sourceB2608 sourceC2608 difference raw32458; decide +kernel
    rw [ha]
    exact (canonical32458 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2608 + difference 3 1) (sourceB2608 + difference 1 3) sourceC2608) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3414) := by
    have ha : (tripleCharges (sourceA2608 + difference 3 1) (sourceB2608 + difference 1 3) sourceC2608) = raw36321 := by
      apply Matrix.ext; unfold tripleCharges sourceA2608 sourceB2608 sourceC2608 difference raw36321; decide +kernel
    rw [ha]
    exact (canonical36321 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2608 + difference 3 2) (sourceB2608 + difference 2 3) sourceC2608) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3756) := by
    have ha : (tripleCharges (sourceA2608 + difference 3 2) (sourceB2608 + difference 2 3) sourceC2608) = raw36322 := by
      apply Matrix.ext; unfold tripleCharges sourceA2608 sourceB2608 sourceC2608 difference raw36322; decide +kernel
    rw [ha]
    exact (canonical36322 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2608 + difference 3 4) (sourceB2608 + difference 4 3) sourceC2608) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3773) := by
    have ha : (tripleCharges (sourceA2608 + difference 3 4) (sourceB2608 + difference 4 3) sourceC2608) = raw36323 := by
      apply Matrix.ext; unfold tripleCharges sourceA2608 sourceB2608 sourceC2608 difference raw36323; decide +kernel
    rw [ha]
    exact (canonical36323 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2608 + difference 3 5) (sourceB2608 + difference 5 3) sourceC2608) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3951) := by
    have ha : (tripleCharges (sourceA2608 + difference 3 5) (sourceB2608 + difference 5 3) sourceC2608) = raw36324 := by
      apply Matrix.ext; unfold tripleCharges sourceA2608 sourceB2608 sourceC2608 difference raw36324; decide +kernel
    rw [ha]
    exact (canonical36324 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2608 + difference 4 0) (sourceB2608 + difference 0 4) sourceC2608) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3406) := by
    have ha : (tripleCharges (sourceA2608 + difference 4 0) (sourceB2608 + difference 0 4) sourceC2608) = raw32463 := by
      apply Matrix.ext; unfold tripleCharges sourceA2608 sourceB2608 sourceC2608 difference raw32463; decide +kernel
    rw [ha]
    exact (canonical32463 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2608 + difference 4 1) (sourceB2608 + difference 1 4) sourceC2608) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3406) := by
    have ha : (tripleCharges (sourceA2608 + difference 4 1) (sourceB2608 + difference 1 4) sourceC2608) = raw36325 := by
      apply Matrix.ext; unfold tripleCharges sourceA2608 sourceB2608 sourceC2608 difference raw36325; decide +kernel
    rw [ha]
    exact (canonical36325 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2608 + difference 4 2) (sourceB2608 + difference 2 4) sourceC2608) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3792) := by
    have ha : (tripleCharges (sourceA2608 + difference 4 2) (sourceB2608 + difference 2 4) sourceC2608) = raw36326 := by
      apply Matrix.ext; unfold tripleCharges sourceA2608 sourceB2608 sourceC2608 difference raw36326; decide +kernel
    rw [ha]
    exact (canonical36326 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2608 + difference 4 3) (sourceB2608 + difference 3 4) sourceC2608) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3835) := by
    have ha : (tripleCharges (sourceA2608 + difference 4 3) (sourceB2608 + difference 3 4) sourceC2608) = raw36327 := by
      apply Matrix.ext; unfold tripleCharges sourceA2608 sourceB2608 sourceC2608 difference raw36327; decide +kernel
    rw [ha]
    exact (canonical36327 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2608 + difference 4 5) (sourceB2608 + difference 5 4) sourceC2608) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3842) := by
    have ha : (tripleCharges (sourceA2608 + difference 4 5) (sourceB2608 + difference 5 4) sourceC2608) = raw36328 := by
      apply Matrix.ext; unfold tripleCharges sourceA2608 sourceB2608 sourceC2608 difference raw36328; decide +kernel
    rw [ha]
    exact (canonical36328 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2608 + difference 5 0) (sourceB2608 + difference 0 5) sourceC2608) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3408) := by
    have ha : (tripleCharges (sourceA2608 + difference 5 0) (sourceB2608 + difference 0 5) sourceC2608) = raw32468 := by
      apply Matrix.ext; unfold tripleCharges sourceA2608 sourceB2608 sourceC2608 difference raw32468; decide +kernel
    rw [ha]
    exact (canonical32468 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2608 + difference 5 1) (sourceB2608 + difference 1 5) sourceC2608) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3408) := by
    have ha : (tripleCharges (sourceA2608 + difference 5 1) (sourceB2608 + difference 1 5) sourceC2608) = raw36329 := by
      apply Matrix.ext; unfold tripleCharges sourceA2608 sourceB2608 sourceC2608 difference raw36329; decide +kernel
    rw [ha]
    exact (canonical36329 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2608 + difference 5 2) (sourceB2608 + difference 2 5) sourceC2608) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3456) := by
    have ha : (tripleCharges (sourceA2608 + difference 5 2) (sourceB2608 + difference 2 5) sourceC2608) = raw36330 := by
      apply Matrix.ext; unfold tripleCharges sourceA2608 sourceB2608 sourceC2608 difference raw36330; decide +kernel
    rw [ha]
    exact (canonical36330 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2608 + difference 5 3) (sourceB2608 + difference 3 5) sourceC2608) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3520) := by
    have ha : (tripleCharges (sourceA2608 + difference 5 3) (sourceB2608 + difference 3 5) sourceC2608) = raw36331 := by
      apply Matrix.ext; unfold tripleCharges sourceA2608 sourceB2608 sourceC2608 difference raw36331; decide +kernel
    rw [ha]
    exact (canonical36331 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2608 + difference 5 4) (sourceB2608 + difference 4 5) sourceC2608) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3482) := by
    have ha : (tripleCharges (sourceA2608 + difference 5 4) (sourceB2608 + difference 4 5) sourceC2608) = raw36332 := by
      apply Matrix.ext; unfold tripleCharges sourceA2608 sourceB2608 sourceC2608 difference raw36332; decide +kernel
    rw [ha]
    exact (canonical36332 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2608 sourceB2608 sourceC2608
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2608, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2609 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2609 : Charge := ![1, 1, 1, -1, 0, -2]
def sourceC2609 : Charge := ![1, 1, -1, 0, -1, 0]
def sourceForm2609 : Integer.Sparse Master := [(Sum.inr 4706, 2), (Sum.inr 4717, 1), (Sum.inr 4732, 1), (Sum.inr 4811, 1), (Sum.inr 4926, 2), (Sum.inr 4928, 2), (Sum.inr 4939, 2), (Sum.inr 5134, 2), (Sum.inr 5316, 1), (Sum.inr 5321, 1), (Sum.inr 5334, 1), (Sum.inr 5356, 1), (Sum.inr 5393, 2), (Sum.inr 5395, 2), (Sum.inr 5405, 2), (Sum.inr 5418, 1), (Sum.inr 5434, 2), (Sum.inr 5460, 1), (Sum.inr 5464, 1), (Sum.inr 5482, 2)]

theorem sourceEq2609 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2609 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2609 + difference 0 1) (sourceB2609 + difference 1 0) sourceC2609) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5134) := by
    have ha : (tripleCharges (sourceA2609 + difference 0 1) (sourceB2609 + difference 1 0) sourceC2609) = raw36333 := by
      apply Matrix.ext; unfold tripleCharges sourceA2609 sourceB2609 sourceC2609 difference raw36333; decide +kernel
    rw [ha]
    exact (canonical36333 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2609 + difference 0 2) (sourceB2609 + difference 2 0) sourceC2609) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5395) := by
    have ha : (tripleCharges (sourceA2609 + difference 0 2) (sourceB2609 + difference 2 0) sourceC2609) = raw36334 := by
      apply Matrix.ext; unfold tripleCharges sourceA2609 sourceB2609 sourceC2609 difference raw36334; decide +kernel
    rw [ha]
    exact (canonical36334 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2609 + difference 0 3) (sourceB2609 + difference 3 0) sourceC2609) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA2609 + difference 0 3) (sourceB2609 + difference 3 0) sourceC2609) = raw36335 := by
      apply Matrix.ext; unfold tripleCharges sourceA2609 sourceB2609 sourceC2609 difference raw36335; decide +kernel
    rw [ha]
    exact (canonical36335 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2609 + difference 0 4) (sourceB2609 + difference 4 0) sourceC2609) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5405) := by
    have ha : (tripleCharges (sourceA2609 + difference 0 4) (sourceB2609 + difference 4 0) sourceC2609) = raw36336 := by
      apply Matrix.ext; unfold tripleCharges sourceA2609 sourceB2609 sourceC2609 difference raw36336; decide +kernel
    rw [ha]
    exact (canonical36336 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2609 + difference 0 5) (sourceB2609 + difference 5 0) sourceC2609) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA2609 + difference 0 5) (sourceB2609 + difference 5 0) sourceC2609) = raw36337 := by
      apply Matrix.ext; unfold tripleCharges sourceA2609 sourceB2609 sourceC2609 difference raw36337; decide +kernel
    rw [ha]
    exact (canonical36337 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2609 + difference 1 0) (sourceB2609 + difference 0 1) sourceC2609) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5134) := by
    have ha : (tripleCharges (sourceA2609 + difference 1 0) (sourceB2609 + difference 0 1) sourceC2609) = raw36338 := by
      apply Matrix.ext; unfold tripleCharges sourceA2609 sourceB2609 sourceC2609 difference raw36338; decide +kernel
    rw [ha]
    exact (canonical36338 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2609 + difference 1 2) (sourceB2609 + difference 2 1) sourceC2609) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5395) := by
    have ha : (tripleCharges (sourceA2609 + difference 1 2) (sourceB2609 + difference 2 1) sourceC2609) = raw32967 := by
      apply Matrix.ext; unfold tripleCharges sourceA2609 sourceB2609 sourceC2609 difference raw32967; decide +kernel
    rw [ha]
    exact (canonical32967 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2609 + difference 1 3) (sourceB2609 + difference 3 1) sourceC2609) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA2609 + difference 1 3) (sourceB2609 + difference 3 1) sourceC2609) = raw32968 := by
      apply Matrix.ext; unfold tripleCharges sourceA2609 sourceB2609 sourceC2609 difference raw32968; decide +kernel
    rw [ha]
    exact (canonical32968 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2609 + difference 1 4) (sourceB2609 + difference 4 1) sourceC2609) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5405) := by
    have ha : (tripleCharges (sourceA2609 + difference 1 4) (sourceB2609 + difference 4 1) sourceC2609) = raw32969 := by
      apply Matrix.ext; unfold tripleCharges sourceA2609 sourceB2609 sourceC2609 difference raw32969; decide +kernel
    rw [ha]
    exact (canonical32969 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2609 + difference 1 5) (sourceB2609 + difference 5 1) sourceC2609) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA2609 + difference 1 5) (sourceB2609 + difference 5 1) sourceC2609) = raw32970 := by
      apply Matrix.ext; unfold tripleCharges sourceA2609 sourceB2609 sourceC2609 difference raw32970; decide +kernel
    rw [ha]
    exact (canonical32970 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2609 + difference 2 0) (sourceB2609 + difference 0 2) sourceC2609) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4939) := by
    have ha : (tripleCharges (sourceA2609 + difference 2 0) (sourceB2609 + difference 0 2) sourceC2609) = raw32977 := by
      apply Matrix.ext; unfold tripleCharges sourceA2609 sourceB2609 sourceC2609 difference raw32977; decide +kernel
    rw [ha]
    exact (canonical32977 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2609 + difference 2 1) (sourceB2609 + difference 1 2) sourceC2609) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4939) := by
    have ha : (tripleCharges (sourceA2609 + difference 2 1) (sourceB2609 + difference 1 2) sourceC2609) = raw36339 := by
      apply Matrix.ext; unfold tripleCharges sourceA2609 sourceB2609 sourceC2609 difference raw36339; decide +kernel
    rw [ha]
    exact (canonical36339 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2609 + difference 2 3) (sourceB2609 + difference 3 2) sourceC2609) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5418) := by
    have ha : (tripleCharges (sourceA2609 + difference 2 3) (sourceB2609 + difference 3 2) sourceC2609) = raw36340 := by
      apply Matrix.ext; unfold tripleCharges sourceA2609 sourceB2609 sourceC2609 difference raw36340; decide +kernel
    rw [ha]
    exact (canonical36340 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2609 + difference 2 4) (sourceB2609 + difference 4 2) sourceC2609) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5393) := by
    have ha : (tripleCharges (sourceA2609 + difference 2 4) (sourceB2609 + difference 4 2) sourceC2609) = raw36341 := by
      apply Matrix.ext; unfold tripleCharges sourceA2609 sourceB2609 sourceC2609 difference raw36341; decide +kernel
    rw [ha]
    exact (canonical36341 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2609 + difference 2 5) (sourceB2609 + difference 5 2) sourceC2609) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5464) := by
    have ha : (tripleCharges (sourceA2609 + difference 2 5) (sourceB2609 + difference 5 2) sourceC2609) = raw36342 := by
      apply Matrix.ext; unfold tripleCharges sourceA2609 sourceB2609 sourceC2609 difference raw36342; decide +kernel
    rw [ha]
    exact (canonical36342 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2609 + difference 3 0) (sourceB2609 + difference 0 3) sourceC2609) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4926) := by
    have ha : (tripleCharges (sourceA2609 + difference 3 0) (sourceB2609 + difference 0 3) sourceC2609) = raw32982 := by
      apply Matrix.ext; unfold tripleCharges sourceA2609 sourceB2609 sourceC2609 difference raw32982; decide +kernel
    rw [ha]
    exact (canonical32982 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2609 + difference 3 1) (sourceB2609 + difference 1 3) sourceC2609) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4926) := by
    have ha : (tripleCharges (sourceA2609 + difference 3 1) (sourceB2609 + difference 1 3) sourceC2609) = raw36343 := by
      apply Matrix.ext; unfold tripleCharges sourceA2609 sourceB2609 sourceC2609 difference raw36343; decide +kernel
    rw [ha]
    exact (canonical36343 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2609 + difference 3 2) (sourceB2609 + difference 2 3) sourceC2609) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5316) := by
    have ha : (tripleCharges (sourceA2609 + difference 3 2) (sourceB2609 + difference 2 3) sourceC2609) = raw36344 := by
      apply Matrix.ext; unfold tripleCharges sourceA2609 sourceB2609 sourceC2609 difference raw36344; decide +kernel
    rw [ha]
    exact (canonical36344 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2609 + difference 3 4) (sourceB2609 + difference 4 3) sourceC2609) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5321) := by
    have ha : (tripleCharges (sourceA2609 + difference 3 4) (sourceB2609 + difference 4 3) sourceC2609) = raw36345 := by
      apply Matrix.ext; unfold tripleCharges sourceA2609 sourceB2609 sourceC2609 difference raw36345; decide +kernel
    rw [ha]
    exact (canonical36345 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2609 + difference 3 5) (sourceB2609 + difference 5 3) sourceC2609) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5393) := by
    have ha : (tripleCharges (sourceA2609 + difference 3 5) (sourceB2609 + difference 5 3) sourceC2609) = raw36346 := by
      apply Matrix.ext; unfold tripleCharges sourceA2609 sourceB2609 sourceC2609 difference raw36346; decide +kernel
    rw [ha]
    exact (canonical36346 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2609 + difference 4 0) (sourceB2609 + difference 0 4) sourceC2609) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4928) := by
    have ha : (tripleCharges (sourceA2609 + difference 4 0) (sourceB2609 + difference 0 4) sourceC2609) = raw32987 := by
      apply Matrix.ext; unfold tripleCharges sourceA2609 sourceB2609 sourceC2609 difference raw32987; decide +kernel
    rw [ha]
    exact (canonical32987 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2609 + difference 4 1) (sourceB2609 + difference 1 4) sourceC2609) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4928) := by
    have ha : (tripleCharges (sourceA2609 + difference 4 1) (sourceB2609 + difference 1 4) sourceC2609) = raw36347 := by
      apply Matrix.ext; unfold tripleCharges sourceA2609 sourceB2609 sourceC2609 difference raw36347; decide +kernel
    rw [ha]
    exact (canonical36347 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2609 + difference 4 2) (sourceB2609 + difference 2 4) sourceC2609) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5334) := by
    have ha : (tripleCharges (sourceA2609 + difference 4 2) (sourceB2609 + difference 2 4) sourceC2609) = raw36348 := by
      apply Matrix.ext; unfold tripleCharges sourceA2609 sourceB2609 sourceC2609 difference raw36348; decide +kernel
    rw [ha]
    exact (canonical36348 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2609 + difference 4 3) (sourceB2609 + difference 3 4) sourceC2609) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5356) := by
    have ha : (tripleCharges (sourceA2609 + difference 4 3) (sourceB2609 + difference 3 4) sourceC2609) = raw36349 := by
      apply Matrix.ext; unfold tripleCharges sourceA2609 sourceB2609 sourceC2609 difference raw36349; decide +kernel
    rw [ha]
    exact (canonical36349 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2609 + difference 4 5) (sourceB2609 + difference 5 4) sourceC2609) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5460) := by
    have ha : (tripleCharges (sourceA2609 + difference 4 5) (sourceB2609 + difference 5 4) sourceC2609) = raw36350 := by
      apply Matrix.ext; unfold tripleCharges sourceA2609 sourceB2609 sourceC2609 difference raw36350; decide +kernel
    rw [ha]
    exact (canonical36350 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2609 + difference 5 0) (sourceB2609 + difference 0 5) sourceC2609) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4706) := by
    have ha : (tripleCharges (sourceA2609 + difference 5 0) (sourceB2609 + difference 0 5) sourceC2609) = raw32992 := by
      apply Matrix.ext; unfold tripleCharges sourceA2609 sourceB2609 sourceC2609 difference raw32992; decide +kernel
    rw [ha]
    exact (canonical32992 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2609 + difference 5 1) (sourceB2609 + difference 1 5) sourceC2609) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4706) := by
    have ha : (tripleCharges (sourceA2609 + difference 5 1) (sourceB2609 + difference 1 5) sourceC2609) = raw36351 := by
      apply Matrix.ext; unfold tripleCharges sourceA2609 sourceB2609 sourceC2609 difference raw36351; decide +kernel
    rw [ha]
    exact (canonical36351 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2609 + difference 5 2) (sourceB2609 + difference 2 5) sourceC2609) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4717) := by
    have ha : (tripleCharges (sourceA2609 + difference 5 2) (sourceB2609 + difference 2 5) sourceC2609) = raw36352 := by
      apply Matrix.ext; unfold tripleCharges sourceA2609 sourceB2609 sourceC2609 difference raw36352; decide +kernel
    rw [ha]
    exact (canonical36352 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2609 + difference 5 3) (sourceB2609 + difference 3 5) sourceC2609) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4811) := by
    have ha : (tripleCharges (sourceA2609 + difference 5 3) (sourceB2609 + difference 3 5) sourceC2609) = raw36353 := by
      apply Matrix.ext; unfold tripleCharges sourceA2609 sourceB2609 sourceC2609 difference raw36353; decide +kernel
    rw [ha]
    exact (canonical36353 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2609 + difference 5 4) (sourceB2609 + difference 4 5) sourceC2609) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4732) := by
    have ha : (tripleCharges (sourceA2609 + difference 5 4) (sourceB2609 + difference 4 5) sourceC2609) = raw36354 := by
      apply Matrix.ext; unfold tripleCharges sourceA2609 sourceB2609 sourceC2609 difference raw36354; decide +kernel
    rw [ha]
    exact (canonical36354 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2609 sourceB2609 sourceC2609
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2609, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2610 : Charge := ![1, 1, -1, 0, -1, 0]
def sourceB2610 : Charge := ![1, 1, 1, -1, 0, -2]
def sourceC2610 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceForm2610 : Integer.Sparse Master := [(Sum.inr 5056, 2), (Sum.inr 5061, 1), (Sum.inr 5092, 1), (Sum.inr 5246, 1), (Sum.inr 5344, 2), (Sum.inr 5345, 2), (Sum.inr 5347, 1), (Sum.inr 5352, 2), (Sum.inr 5353, 2), (Sum.inr 5354, 2), (Sum.inr 5360, 2), (Sum.inr 5362, 1), (Sum.inr 5367, 2), (Sum.inr 5378, 2), (Sum.inr 5391, 1), (Sum.inr 5393, 1), (Sum.inr 5404, 1), (Sum.inr 5418, 1), (Sum.inr 5459, 1), (Sum.inr 5460, 1), (Sum.inr 5465, 1)]

theorem sourceEq2610 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2610 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2610 + difference 0 1) (sourceB2610 + difference 1 0) sourceC2610) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA2610 + difference 0 1) (sourceB2610 + difference 1 0) sourceC2610) = raw36355 := by
      apply Matrix.ext; unfold tripleCharges sourceA2610 sourceB2610 sourceC2610 difference raw36355; decide +kernel
    rw [ha]
    exact (canonical36355 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2610 + difference 0 2) (sourceB2610 + difference 2 0) sourceC2610) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5360) := by
    have ha : (tripleCharges (sourceA2610 + difference 0 2) (sourceB2610 + difference 2 0) sourceC2610) = raw36356 := by
      apply Matrix.ext; unfold tripleCharges sourceA2610 sourceB2610 sourceC2610 difference raw36356; decide +kernel
    rw [ha]
    exact (canonical36356 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2610 + difference 0 3) (sourceB2610 + difference 3 0) sourceC2610) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5354) := by
    have ha : (tripleCharges (sourceA2610 + difference 0 3) (sourceB2610 + difference 3 0) sourceC2610) = raw36357 := by
      apply Matrix.ext; unfold tripleCharges sourceA2610 sourceB2610 sourceC2610 difference raw36357; decide +kernel
    rw [ha]
    exact (canonical36357 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2610 + difference 0 4) (sourceB2610 + difference 4 0) sourceC2610) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5353) := by
    have ha : (tripleCharges (sourceA2610 + difference 0 4) (sourceB2610 + difference 4 0) sourceC2610) = raw36358 := by
      apply Matrix.ext; unfold tripleCharges sourceA2610 sourceB2610 sourceC2610 difference raw36358; decide +kernel
    rw [ha]
    exact (canonical36358 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2610 + difference 0 5) (sourceB2610 + difference 5 0) sourceC2610) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5352) := by
    have ha : (tripleCharges (sourceA2610 + difference 0 5) (sourceB2610 + difference 5 0) sourceC2610) = raw36359 := by
      apply Matrix.ext; unfold tripleCharges sourceA2610 sourceB2610 sourceC2610 difference raw36359; decide +kernel
    rw [ha]
    exact (canonical36359 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2610 + difference 1 0) (sourceB2610 + difference 0 1) sourceC2610) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA2610 + difference 1 0) (sourceB2610 + difference 0 1) sourceC2610) = raw35589 := by
      apply Matrix.ext; unfold tripleCharges sourceA2610 sourceB2610 sourceC2610 difference raw35589; decide +kernel
    rw [ha]
    exact (canonical35589 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2610 + difference 1 2) (sourceB2610 + difference 2 1) sourceC2610) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5360) := by
    have ha : (tripleCharges (sourceA2610 + difference 1 2) (sourceB2610 + difference 2 1) sourceC2610) = raw36360 := by
      apply Matrix.ext; unfold tripleCharges sourceA2610 sourceB2610 sourceC2610 difference raw36360; decide +kernel
    rw [ha]
    exact (canonical36360 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2610 + difference 1 3) (sourceB2610 + difference 3 1) sourceC2610) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5354) := by
    have ha : (tripleCharges (sourceA2610 + difference 1 3) (sourceB2610 + difference 3 1) sourceC2610) = raw35573 := by
      apply Matrix.ext; unfold tripleCharges sourceA2610 sourceB2610 sourceC2610 difference raw35573; decide +kernel
    rw [ha]
    exact (canonical35573 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2610 + difference 1 4) (sourceB2610 + difference 4 1) sourceC2610) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5353) := by
    have ha : (tripleCharges (sourceA2610 + difference 1 4) (sourceB2610 + difference 4 1) sourceC2610) = raw36361 := by
      apply Matrix.ext; unfold tripleCharges sourceA2610 sourceB2610 sourceC2610 difference raw36361; decide +kernel
    rw [ha]
    exact (canonical36361 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2610 + difference 1 5) (sourceB2610 + difference 5 1) sourceC2610) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5352) := by
    have ha : (tripleCharges (sourceA2610 + difference 1 5) (sourceB2610 + difference 5 1) sourceC2610) = raw36362 := by
      apply Matrix.ext; unfold tripleCharges sourceA2610 sourceB2610 sourceC2610 difference raw36362; decide +kernel
    rw [ha]
    exact (canonical36362 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2610 + difference 2 0) (sourceB2610 + difference 0 2) sourceC2610) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5367) := by
    have ha : (tripleCharges (sourceA2610 + difference 2 0) (sourceB2610 + difference 0 2) sourceC2610) = raw35588 := by
      apply Matrix.ext; unfold tripleCharges sourceA2610 sourceB2610 sourceC2610 difference raw35588; decide +kernel
    rw [ha]
    exact (canonical35588 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2610 + difference 2 1) (sourceB2610 + difference 1 2) sourceC2610) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5367) := by
    have ha : (tripleCharges (sourceA2610 + difference 2 1) (sourceB2610 + difference 1 2) sourceC2610) = raw36363 := by
      apply Matrix.ext; unfold tripleCharges sourceA2610 sourceB2610 sourceC2610 difference raw36363; decide +kernel
    rw [ha]
    exact (canonical36363 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2610 + difference 2 3) (sourceB2610 + difference 3 2) sourceC2610) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5418) := by
    have ha : (tripleCharges (sourceA2610 + difference 2 3) (sourceB2610 + difference 3 2) sourceC2610) = raw35572 := by
      apply Matrix.ext; unfold tripleCharges sourceA2610 sourceB2610 sourceC2610 difference raw35572; decide +kernel
    rw [ha]
    exact (canonical35572 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2610 + difference 2 4) (sourceB2610 + difference 4 2) sourceC2610) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5404) := by
    have ha : (tripleCharges (sourceA2610 + difference 2 4) (sourceB2610 + difference 4 2) sourceC2610) = raw36364 := by
      apply Matrix.ext; unfold tripleCharges sourceA2610 sourceB2610 sourceC2610 difference raw36364; decide +kernel
    rw [ha]
    exact (canonical36364 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2610 + difference 2 5) (sourceB2610 + difference 5 2) sourceC2610) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5465) := by
    have ha : (tripleCharges (sourceA2610 + difference 2 5) (sourceB2610 + difference 5 2) sourceC2610) = raw36365 := by
      apply Matrix.ext; unfold tripleCharges sourceA2610 sourceB2610 sourceC2610 difference raw36365; decide +kernel
    rw [ha]
    exact (canonical36365 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2610 + difference 3 0) (sourceB2610 + difference 0 3) sourceC2610) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5344) := by
    have ha : (tripleCharges (sourceA2610 + difference 3 0) (sourceB2610 + difference 0 3) sourceC2610) = raw36366 := by
      apply Matrix.ext; unfold tripleCharges sourceA2610 sourceB2610 sourceC2610 difference raw36366; decide +kernel
    rw [ha]
    exact (canonical36366 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2610 + difference 3 1) (sourceB2610 + difference 1 3) sourceC2610) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5344) := by
    have ha : (tripleCharges (sourceA2610 + difference 3 1) (sourceB2610 + difference 1 3) sourceC2610) = raw36367 := by
      apply Matrix.ext; unfold tripleCharges sourceA2610 sourceB2610 sourceC2610 difference raw36367; decide +kernel
    rw [ha]
    exact (canonical36367 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2610 + difference 3 2) (sourceB2610 + difference 2 3) sourceC2610) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5347) := by
    have ha : (tripleCharges (sourceA2610 + difference 3 2) (sourceB2610 + difference 2 3) sourceC2610) = raw36368 := by
      apply Matrix.ext; unfold tripleCharges sourceA2610 sourceB2610 sourceC2610 difference raw36368; decide +kernel
    rw [ha]
    exact (canonical36368 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2610 + difference 3 4) (sourceB2610 + difference 4 3) sourceC2610) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5362) := by
    have ha : (tripleCharges (sourceA2610 + difference 3 4) (sourceB2610 + difference 4 3) sourceC2610) = raw36369 := by
      apply Matrix.ext; unfold tripleCharges sourceA2610 sourceB2610 sourceC2610 difference raw36369; decide +kernel
    rw [ha]
    exact (canonical36369 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2610 + difference 3 5) (sourceB2610 + difference 5 3) sourceC2610) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5459) := by
    have ha : (tripleCharges (sourceA2610 + difference 3 5) (sourceB2610 + difference 5 3) sourceC2610) = raw36370 := by
      apply Matrix.ext; unfold tripleCharges sourceA2610 sourceB2610 sourceC2610 difference raw36370; decide +kernel
    rw [ha]
    exact (canonical36370 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2610 + difference 4 0) (sourceB2610 + difference 0 4) sourceC2610) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5345) := by
    have ha : (tripleCharges (sourceA2610 + difference 4 0) (sourceB2610 + difference 0 4) sourceC2610) = raw36371 := by
      apply Matrix.ext; unfold tripleCharges sourceA2610 sourceB2610 sourceC2610 difference raw36371; decide +kernel
    rw [ha]
    exact (canonical36371 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2610 + difference 4 1) (sourceB2610 + difference 1 4) sourceC2610) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5345) := by
    have ha : (tripleCharges (sourceA2610 + difference 4 1) (sourceB2610 + difference 1 4) sourceC2610) = raw36372 := by
      apply Matrix.ext; unfold tripleCharges sourceA2610 sourceB2610 sourceC2610 difference raw36372; decide +kernel
    rw [ha]
    exact (canonical36372 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2610 + difference 4 2) (sourceB2610 + difference 2 4) sourceC2610) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5391) := by
    have ha : (tripleCharges (sourceA2610 + difference 4 2) (sourceB2610 + difference 2 4) sourceC2610) = raw36373 := by
      apply Matrix.ext; unfold tripleCharges sourceA2610 sourceB2610 sourceC2610 difference raw36373; decide +kernel
    rw [ha]
    exact (canonical36373 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2610 + difference 4 3) (sourceB2610 + difference 3 4) sourceC2610) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5393) := by
    have ha : (tripleCharges (sourceA2610 + difference 4 3) (sourceB2610 + difference 3 4) sourceC2610) = raw36374 := by
      apply Matrix.ext; unfold tripleCharges sourceA2610 sourceB2610 sourceC2610 difference raw36374; decide +kernel
    rw [ha]
    exact (canonical36374 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2610 + difference 4 5) (sourceB2610 + difference 5 4) sourceC2610) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5460) := by
    have ha : (tripleCharges (sourceA2610 + difference 4 5) (sourceB2610 + difference 5 4) sourceC2610) = raw36375 := by
      apply Matrix.ext; unfold tripleCharges sourceA2610 sourceB2610 sourceC2610 difference raw36375; decide +kernel
    rw [ha]
    exact (canonical36375 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2610 + difference 5 0) (sourceB2610 + difference 0 5) sourceC2610) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5056) := by
    have ha : (tripleCharges (sourceA2610 + difference 5 0) (sourceB2610 + difference 0 5) sourceC2610) = raw36376 := by
      apply Matrix.ext; unfold tripleCharges sourceA2610 sourceB2610 sourceC2610 difference raw36376; decide +kernel
    rw [ha]
    exact (canonical36376 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2610 + difference 5 1) (sourceB2610 + difference 1 5) sourceC2610) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5056) := by
    have ha : (tripleCharges (sourceA2610 + difference 5 1) (sourceB2610 + difference 1 5) sourceC2610) = raw36377 := by
      apply Matrix.ext; unfold tripleCharges sourceA2610 sourceB2610 sourceC2610 difference raw36377; decide +kernel
    rw [ha]
    exact (canonical36377 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2610 + difference 5 2) (sourceB2610 + difference 2 5) sourceC2610) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5061) := by
    have ha : (tripleCharges (sourceA2610 + difference 5 2) (sourceB2610 + difference 2 5) sourceC2610) = raw36378 := by
      apply Matrix.ext; unfold tripleCharges sourceA2610 sourceB2610 sourceC2610 difference raw36378; decide +kernel
    rw [ha]
    exact (canonical36378 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2610 + difference 5 3) (sourceB2610 + difference 3 5) sourceC2610) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5246) := by
    have ha : (tripleCharges (sourceA2610 + difference 5 3) (sourceB2610 + difference 3 5) sourceC2610) = raw36379 := by
      apply Matrix.ext; unfold tripleCharges sourceA2610 sourceB2610 sourceC2610 difference raw36379; decide +kernel
    rw [ha]
    exact (canonical36379 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2610 + difference 5 4) (sourceB2610 + difference 4 5) sourceC2610) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5092) := by
    have ha : (tripleCharges (sourceA2610 + difference 5 4) (sourceB2610 + difference 4 5) sourceC2610) = raw36380 := by
      apply Matrix.ext; unfold tripleCharges sourceA2610 sourceB2610 sourceC2610 difference raw36380; decide +kernel
    rw [ha]
    exact (canonical36380 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2610 sourceB2610 sourceC2610
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2610, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2611 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2611 : Charge := ![1, 0, 1, 0, 0, -2]
def sourceC2611 : Charge := ![1, 2, -1, -1, -1, 0]
def sourceForm2611 : Integer.Sparse Master := [(Sum.inr 4756, 1), (Sum.inr 4757, 1), (Sum.inr 4768, 1), (Sum.inr 4795, 2), (Sum.inr 4933, 2), (Sum.inr 4947, 1), (Sum.inr 4955, 2), (Sum.inr 4967, 1), (Sum.inr 5076, 1), (Sum.inr 5184, 1), (Sum.inr 5338, 2), (Sum.inr 5348, 2), (Sum.inr 5352, 2), (Sum.inr 5354, 2), (Sum.inr 5366, 1), (Sum.inr 5403, 1), (Sum.inr 5406, 2), (Sum.inr 5408, 1), (Sum.inr 5414, 1), (Sum.inr 5429, 2), (Sum.inr 5472, 1)]

theorem sourceEq2611 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2611 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2611 + difference 0 1) (sourceB2611 + difference 1 0) sourceC2611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5076) := by
    have ha : (tripleCharges (sourceA2611 + difference 0 1) (sourceB2611 + difference 1 0) sourceC2611) = raw36381 := by
      apply Matrix.ext; unfold tripleCharges sourceA2611 sourceB2611 sourceC2611 difference raw36381; decide +kernel
    rw [ha]
    exact (canonical36381 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2611 + difference 0 2) (sourceB2611 + difference 2 0) sourceC2611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5403) := by
    have ha : (tripleCharges (sourceA2611 + difference 0 2) (sourceB2611 + difference 2 0) sourceC2611) = raw36382 := by
      apply Matrix.ext; unfold tripleCharges sourceA2611 sourceB2611 sourceC2611 difference raw36382; decide +kernel
    rw [ha]
    exact (canonical36382 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2611 + difference 0 3) (sourceB2611 + difference 3 0) sourceC2611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5406) := by
    have ha : (tripleCharges (sourceA2611 + difference 0 3) (sourceB2611 + difference 3 0) sourceC2611) = raw36383 := by
      apply Matrix.ext; unfold tripleCharges sourceA2611 sourceB2611 sourceC2611 difference raw36383; decide +kernel
    rw [ha]
    exact (canonical36383 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2611 + difference 0 4) (sourceB2611 + difference 4 0) sourceC2611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5406) := by
    have ha : (tripleCharges (sourceA2611 + difference 0 4) (sourceB2611 + difference 4 0) sourceC2611) = raw36384 := by
      apply Matrix.ext; unfold tripleCharges sourceA2611 sourceB2611 sourceC2611 difference raw36384; decide +kernel
    rw [ha]
    exact (canonical36384 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2611 + difference 0 5) (sourceB2611 + difference 5 0) sourceC2611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5408) := by
    have ha : (tripleCharges (sourceA2611 + difference 0 5) (sourceB2611 + difference 5 0) sourceC2611) = raw19080 := by
      apply Matrix.ext; unfold tripleCharges sourceA2611 sourceB2611 sourceC2611 difference raw19080; decide +kernel
    rw [ha]
    exact (canonical19080 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2611 + difference 1 0) (sourceB2611 + difference 0 1) sourceC2611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5184) := by
    have ha : (tripleCharges (sourceA2611 + difference 1 0) (sourceB2611 + difference 0 1) sourceC2611) = raw19105 := by
      apply Matrix.ext; unfold tripleCharges sourceA2611 sourceB2611 sourceC2611 difference raw19105; decide +kernel
    rw [ha]
    exact (canonical19105 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2611 + difference 1 2) (sourceB2611 + difference 2 1) sourceC2611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5414) := by
    have ha : (tripleCharges (sourceA2611 + difference 1 2) (sourceB2611 + difference 2 1) sourceC2611) = raw19107 := by
      apply Matrix.ext; unfold tripleCharges sourceA2611 sourceB2611 sourceC2611 difference raw19107; decide +kernel
    rw [ha]
    exact (canonical19107 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2611 + difference 1 3) (sourceB2611 + difference 3 1) sourceC2611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5429) := by
    have ha : (tripleCharges (sourceA2611 + difference 1 3) (sourceB2611 + difference 3 1) sourceC2611) = raw19108 := by
      apply Matrix.ext; unfold tripleCharges sourceA2611 sourceB2611 sourceC2611 difference raw19108; decide +kernel
    rw [ha]
    exact (canonical19108 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2611 + difference 1 4) (sourceB2611 + difference 4 1) sourceC2611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5429) := by
    have ha : (tripleCharges (sourceA2611 + difference 1 4) (sourceB2611 + difference 4 1) sourceC2611) = raw19109 := by
      apply Matrix.ext; unfold tripleCharges sourceA2611 sourceB2611 sourceC2611 difference raw19109; decide +kernel
    rw [ha]
    exact (canonical19109 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2611 + difference 1 5) (sourceB2611 + difference 5 1) sourceC2611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5472) := by
    have ha : (tripleCharges (sourceA2611 + difference 1 5) (sourceB2611 + difference 5 1) sourceC2611) = raw36385 := by
      apply Matrix.ext; unfold tripleCharges sourceA2611 sourceB2611 sourceC2611 difference raw36385; decide +kernel
    rw [ha]
    exact (canonical36385 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2611 + difference 2 0) (sourceB2611 + difference 0 2) sourceC2611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4967) := by
    have ha : (tripleCharges (sourceA2611 + difference 2 0) (sourceB2611 + difference 0 2) sourceC2611) = raw36386 := by
      apply Matrix.ext; unfold tripleCharges sourceA2611 sourceB2611 sourceC2611 difference raw36386; decide +kernel
    rw [ha]
    exact (canonical36386 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2611 + difference 2 1) (sourceB2611 + difference 1 2) sourceC2611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4947) := by
    have ha : (tripleCharges (sourceA2611 + difference 2 1) (sourceB2611 + difference 1 2) sourceC2611) = raw36387 := by
      apply Matrix.ext; unfold tripleCharges sourceA2611 sourceB2611 sourceC2611 difference raw36387; decide +kernel
    rw [ha]
    exact (canonical36387 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2611 + difference 2 3) (sourceB2611 + difference 3 2) sourceC2611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5354) := by
    have ha : (tripleCharges (sourceA2611 + difference 2 3) (sourceB2611 + difference 3 2) sourceC2611) = raw36388 := by
      apply Matrix.ext; unfold tripleCharges sourceA2611 sourceB2611 sourceC2611 difference raw36388; decide +kernel
    rw [ha]
    exact (canonical36388 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2611 + difference 2 4) (sourceB2611 + difference 4 2) sourceC2611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5354) := by
    have ha : (tripleCharges (sourceA2611 + difference 2 4) (sourceB2611 + difference 4 2) sourceC2611) = raw36389 := by
      apply Matrix.ext; unfold tripleCharges sourceA2611 sourceB2611 sourceC2611 difference raw36389; decide +kernel
    rw [ha]
    exact (canonical36389 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2611 + difference 2 5) (sourceB2611 + difference 5 2) sourceC2611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5366) := by
    have ha : (tripleCharges (sourceA2611 + difference 2 5) (sourceB2611 + difference 5 2) sourceC2611) = raw19091 := by
      apply Matrix.ext; unfold tripleCharges sourceA2611 sourceB2611 sourceC2611 difference raw19091; decide +kernel
    rw [ha]
    exact (canonical19091 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2611 + difference 3 0) (sourceB2611 + difference 0 3) sourceC2611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4955) := by
    have ha : (tripleCharges (sourceA2611 + difference 3 0) (sourceB2611 + difference 0 3) sourceC2611) = raw36390 := by
      apply Matrix.ext; unfold tripleCharges sourceA2611 sourceB2611 sourceC2611 difference raw36390; decide +kernel
    rw [ha]
    exact (canonical36390 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2611 + difference 3 1) (sourceB2611 + difference 1 3) sourceC2611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4933) := by
    have ha : (tripleCharges (sourceA2611 + difference 3 1) (sourceB2611 + difference 1 3) sourceC2611) = raw36391 := by
      apply Matrix.ext; unfold tripleCharges sourceA2611 sourceB2611 sourceC2611 difference raw36391; decide +kernel
    rw [ha]
    exact (canonical36391 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2611 + difference 3 2) (sourceB2611 + difference 2 3) sourceC2611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5338) := by
    have ha : (tripleCharges (sourceA2611 + difference 3 2) (sourceB2611 + difference 2 3) sourceC2611) = raw36392 := by
      apply Matrix.ext; unfold tripleCharges sourceA2611 sourceB2611 sourceC2611 difference raw36392; decide +kernel
    rw [ha]
    exact (canonical36392 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2611 + difference 3 4) (sourceB2611 + difference 4 3) sourceC2611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5348) := by
    have ha : (tripleCharges (sourceA2611 + difference 3 4) (sourceB2611 + difference 4 3) sourceC2611) = raw36393 := by
      apply Matrix.ext; unfold tripleCharges sourceA2611 sourceB2611 sourceC2611 difference raw36393; decide +kernel
    rw [ha]
    exact (canonical36393 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2611 + difference 3 5) (sourceB2611 + difference 5 3) sourceC2611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5352) := by
    have ha : (tripleCharges (sourceA2611 + difference 3 5) (sourceB2611 + difference 5 3) sourceC2611) = raw19096 := by
      apply Matrix.ext; unfold tripleCharges sourceA2611 sourceB2611 sourceC2611 difference raw19096; decide +kernel
    rw [ha]
    exact (canonical19096 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2611 + difference 4 0) (sourceB2611 + difference 0 4) sourceC2611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4955) := by
    have ha : (tripleCharges (sourceA2611 + difference 4 0) (sourceB2611 + difference 0 4) sourceC2611) = raw36394 := by
      apply Matrix.ext; unfold tripleCharges sourceA2611 sourceB2611 sourceC2611 difference raw36394; decide +kernel
    rw [ha]
    exact (canonical36394 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2611 + difference 4 1) (sourceB2611 + difference 1 4) sourceC2611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4933) := by
    have ha : (tripleCharges (sourceA2611 + difference 4 1) (sourceB2611 + difference 1 4) sourceC2611) = raw36395 := by
      apply Matrix.ext; unfold tripleCharges sourceA2611 sourceB2611 sourceC2611 difference raw36395; decide +kernel
    rw [ha]
    exact (canonical36395 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2611 + difference 4 2) (sourceB2611 + difference 2 4) sourceC2611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5338) := by
    have ha : (tripleCharges (sourceA2611 + difference 4 2) (sourceB2611 + difference 2 4) sourceC2611) = raw36396 := by
      apply Matrix.ext; unfold tripleCharges sourceA2611 sourceB2611 sourceC2611 difference raw36396; decide +kernel
    rw [ha]
    exact (canonical36396 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2611 + difference 4 3) (sourceB2611 + difference 3 4) sourceC2611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5348) := by
    have ha : (tripleCharges (sourceA2611 + difference 4 3) (sourceB2611 + difference 3 4) sourceC2611) = raw36397 := by
      apply Matrix.ext; unfold tripleCharges sourceA2611 sourceB2611 sourceC2611 difference raw36397; decide +kernel
    rw [ha]
    exact (canonical36397 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2611 + difference 4 5) (sourceB2611 + difference 5 4) sourceC2611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5352) := by
    have ha : (tripleCharges (sourceA2611 + difference 4 5) (sourceB2611 + difference 5 4) sourceC2611) = raw19101 := by
      apply Matrix.ext; unfold tripleCharges sourceA2611 sourceB2611 sourceC2611 difference raw19101; decide +kernel
    rw [ha]
    exact (canonical19101 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2611 + difference 5 0) (sourceB2611 + difference 0 5) sourceC2611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4756) := by
    have ha : (tripleCharges (sourceA2611 + difference 5 0) (sourceB2611 + difference 0 5) sourceC2611) = raw36398 := by
      apply Matrix.ext; unfold tripleCharges sourceA2611 sourceB2611 sourceC2611 difference raw36398; decide +kernel
    rw [ha]
    exact (canonical36398 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2611 + difference 5 1) (sourceB2611 + difference 1 5) sourceC2611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4757) := by
    have ha : (tripleCharges (sourceA2611 + difference 5 1) (sourceB2611 + difference 1 5) sourceC2611) = raw36399 := by
      apply Matrix.ext; unfold tripleCharges sourceA2611 sourceB2611 sourceC2611 difference raw36399; decide +kernel
    rw [ha]
    exact (canonical36399 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2611 + difference 5 2) (sourceB2611 + difference 2 5) sourceC2611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4768) := by
    have ha : (tripleCharges (sourceA2611 + difference 5 2) (sourceB2611 + difference 2 5) sourceC2611) = raw36400 := by
      apply Matrix.ext; unfold tripleCharges sourceA2611 sourceB2611 sourceC2611 difference raw36400; decide +kernel
    rw [ha]
    exact (canonical36400 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2611 + difference 5 3) (sourceB2611 + difference 3 5) sourceC2611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4795) := by
    have ha : (tripleCharges (sourceA2611 + difference 5 3) (sourceB2611 + difference 3 5) sourceC2611) = raw36401 := by
      apply Matrix.ext; unfold tripleCharges sourceA2611 sourceB2611 sourceC2611 difference raw36401; decide +kernel
    rw [ha]
    exact (canonical36401 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2611 + difference 5 4) (sourceB2611 + difference 4 5) sourceC2611) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4795) := by
    have ha : (tripleCharges (sourceA2611 + difference 5 4) (sourceB2611 + difference 4 5) sourceC2611) = raw36402 := by
      apply Matrix.ext; unfold tripleCharges sourceA2611 sourceB2611 sourceC2611 difference raw36402; decide +kernel
    rw [ha]
    exact (canonical36402 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2611 sourceB2611 sourceC2611
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2611, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2612 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2612 : Charge := ![1, 0, 1, 0, 0, -2]
def sourceC2612 : Charge := ![1, 2, -1, -1, -1, 0]
def sourceForm2612 : Integer.Sparse Master := [(Sum.inr 2176, 1), (Sum.inr 2178, 1), (Sum.inr 2181, 1), (Sum.inr 2213, 2), (Sum.inr 3414, 2), (Sum.inr 3416, 1), (Sum.inr 3477, 1), (Sum.inr 3508, 2), (Sum.inr 3524, 1), (Sum.inr 3585, 1), (Sum.inr 3755, 2), (Sum.inr 3764, 2), (Sum.inr 3765, 1), (Sum.inr 3768, 2), (Sum.inr 3769, 2), (Sum.inr 3806, 1), (Sum.inr 3810, 1), (Sum.inr 3812, 2), (Sum.inr 3869, 1), (Sum.inr 3874, 2), (Sum.inr 3957, 1)]

theorem sourceEq2612 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2612 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2612 + difference 0 1) (sourceB2612 + difference 1 0) sourceC2612) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3477) := by
    have ha : (tripleCharges (sourceA2612 + difference 0 1) (sourceB2612 + difference 1 0) sourceC2612) = raw36403 := by
      apply Matrix.ext; unfold tripleCharges sourceA2612 sourceB2612 sourceC2612 difference raw36403; decide +kernel
    rw [ha]
    exact (canonical36403 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2612 + difference 0 2) (sourceB2612 + difference 2 0) sourceC2612) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3810) := by
    have ha : (tripleCharges (sourceA2612 + difference 0 2) (sourceB2612 + difference 2 0) sourceC2612) = raw36404 := by
      apply Matrix.ext; unfold tripleCharges sourceA2612 sourceB2612 sourceC2612 difference raw36404; decide +kernel
    rw [ha]
    exact (canonical36404 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2612 + difference 0 3) (sourceB2612 + difference 3 0) sourceC2612) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3812) := by
    have ha : (tripleCharges (sourceA2612 + difference 0 3) (sourceB2612 + difference 3 0) sourceC2612) = raw36405 := by
      apply Matrix.ext; unfold tripleCharges sourceA2612 sourceB2612 sourceC2612 difference raw36405; decide +kernel
    rw [ha]
    exact (canonical36405 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2612 + difference 0 4) (sourceB2612 + difference 4 0) sourceC2612) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3812) := by
    have ha : (tripleCharges (sourceA2612 + difference 0 4) (sourceB2612 + difference 4 0) sourceC2612) = raw36406 := by
      apply Matrix.ext; unfold tripleCharges sourceA2612 sourceB2612 sourceC2612 difference raw36406; decide +kernel
    rw [ha]
    exact (canonical36406 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2612 + difference 0 5) (sourceB2612 + difference 5 0) sourceC2612) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3806) := by
    have ha : (tripleCharges (sourceA2612 + difference 0 5) (sourceB2612 + difference 5 0) sourceC2612) = raw19110 := by
      apply Matrix.ext; unfold tripleCharges sourceA2612 sourceB2612 sourceC2612 difference raw19110; decide +kernel
    rw [ha]
    exact (canonical19110 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2612 + difference 1 0) (sourceB2612 + difference 0 1) sourceC2612) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3524) := by
    have ha : (tripleCharges (sourceA2612 + difference 1 0) (sourceB2612 + difference 0 1) sourceC2612) = raw19135 := by
      apply Matrix.ext; unfold tripleCharges sourceA2612 sourceB2612 sourceC2612 difference raw19135; decide +kernel
    rw [ha]
    exact (canonical19135 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2612 + difference 1 2) (sourceB2612 + difference 2 1) sourceC2612) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3869) := by
    have ha : (tripleCharges (sourceA2612 + difference 1 2) (sourceB2612 + difference 2 1) sourceC2612) = raw19137 := by
      apply Matrix.ext; unfold tripleCharges sourceA2612 sourceB2612 sourceC2612 difference raw19137; decide +kernel
    rw [ha]
    exact (canonical19137 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2612 + difference 1 3) (sourceB2612 + difference 3 1) sourceC2612) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3874) := by
    have ha : (tripleCharges (sourceA2612 + difference 1 3) (sourceB2612 + difference 3 1) sourceC2612) = raw19138 := by
      apply Matrix.ext; unfold tripleCharges sourceA2612 sourceB2612 sourceC2612 difference raw19138; decide +kernel
    rw [ha]
    exact (canonical19138 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2612 + difference 1 4) (sourceB2612 + difference 4 1) sourceC2612) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3874) := by
    have ha : (tripleCharges (sourceA2612 + difference 1 4) (sourceB2612 + difference 4 1) sourceC2612) = raw19139 := by
      apply Matrix.ext; unfold tripleCharges sourceA2612 sourceB2612 sourceC2612 difference raw19139; decide +kernel
    rw [ha]
    exact (canonical19139 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2612 + difference 1 5) (sourceB2612 + difference 5 1) sourceC2612) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3957) := by
    have ha : (tripleCharges (sourceA2612 + difference 1 5) (sourceB2612 + difference 5 1) sourceC2612) = raw36407 := by
      apply Matrix.ext; unfold tripleCharges sourceA2612 sourceB2612 sourceC2612 difference raw36407; decide +kernel
    rw [ha]
    exact (canonical36407 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2612 + difference 2 0) (sourceB2612 + difference 0 2) sourceC2612) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3585) := by
    have ha : (tripleCharges (sourceA2612 + difference 2 0) (sourceB2612 + difference 0 2) sourceC2612) = raw36408 := by
      apply Matrix.ext; unfold tripleCharges sourceA2612 sourceB2612 sourceC2612 difference raw36408; decide +kernel
    rw [ha]
    exact (canonical36408 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2612 + difference 2 1) (sourceB2612 + difference 1 2) sourceC2612) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3416) := by
    have ha : (tripleCharges (sourceA2612 + difference 2 1) (sourceB2612 + difference 1 2) sourceC2612) = raw36409 := by
      apply Matrix.ext; unfold tripleCharges sourceA2612 sourceB2612 sourceC2612 difference raw36409; decide +kernel
    rw [ha]
    exact (canonical36409 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2612 + difference 2 3) (sourceB2612 + difference 3 2) sourceC2612) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3769) := by
    have ha : (tripleCharges (sourceA2612 + difference 2 3) (sourceB2612 + difference 3 2) sourceC2612) = raw36410 := by
      apply Matrix.ext; unfold tripleCharges sourceA2612 sourceB2612 sourceC2612 difference raw36410; decide +kernel
    rw [ha]
    exact (canonical36410 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2612 + difference 2 4) (sourceB2612 + difference 4 2) sourceC2612) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3769) := by
    have ha : (tripleCharges (sourceA2612 + difference 2 4) (sourceB2612 + difference 4 2) sourceC2612) = raw36411 := by
      apply Matrix.ext; unfold tripleCharges sourceA2612 sourceB2612 sourceC2612 difference raw36411; decide +kernel
    rw [ha]
    exact (canonical36411 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2612 + difference 2 5) (sourceB2612 + difference 5 2) sourceC2612) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3765) := by
    have ha : (tripleCharges (sourceA2612 + difference 2 5) (sourceB2612 + difference 5 2) sourceC2612) = raw19121 := by
      apply Matrix.ext; unfold tripleCharges sourceA2612 sourceB2612 sourceC2612 difference raw19121; decide +kernel
    rw [ha]
    exact (canonical19121 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2612 + difference 3 0) (sourceB2612 + difference 0 3) sourceC2612) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3508) := by
    have ha : (tripleCharges (sourceA2612 + difference 3 0) (sourceB2612 + difference 0 3) sourceC2612) = raw36412 := by
      apply Matrix.ext; unfold tripleCharges sourceA2612 sourceB2612 sourceC2612 difference raw36412; decide +kernel
    rw [ha]
    exact (canonical36412 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2612 + difference 3 1) (sourceB2612 + difference 1 3) sourceC2612) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3414) := by
    have ha : (tripleCharges (sourceA2612 + difference 3 1) (sourceB2612 + difference 1 3) sourceC2612) = raw36413 := by
      apply Matrix.ext; unfold tripleCharges sourceA2612 sourceB2612 sourceC2612 difference raw36413; decide +kernel
    rw [ha]
    exact (canonical36413 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2612 + difference 3 2) (sourceB2612 + difference 2 3) sourceC2612) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3755) := by
    have ha : (tripleCharges (sourceA2612 + difference 3 2) (sourceB2612 + difference 2 3) sourceC2612) = raw36414 := by
      apply Matrix.ext; unfold tripleCharges sourceA2612 sourceB2612 sourceC2612 difference raw36414; decide +kernel
    rw [ha]
    exact (canonical36414 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2612 + difference 3 4) (sourceB2612 + difference 4 3) sourceC2612) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3768) := by
    have ha : (tripleCharges (sourceA2612 + difference 3 4) (sourceB2612 + difference 4 3) sourceC2612) = raw36415 := by
      apply Matrix.ext; unfold tripleCharges sourceA2612 sourceB2612 sourceC2612 difference raw36415; decide +kernel
    rw [ha]
    exact (canonical36415 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2612 + difference 3 5) (sourceB2612 + difference 5 3) sourceC2612) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3764) := by
    have ha : (tripleCharges (sourceA2612 + difference 3 5) (sourceB2612 + difference 5 3) sourceC2612) = raw19126 := by
      apply Matrix.ext; unfold tripleCharges sourceA2612 sourceB2612 sourceC2612 difference raw19126; decide +kernel
    rw [ha]
    exact (canonical19126 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2612 + difference 4 0) (sourceB2612 + difference 0 4) sourceC2612) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3508) := by
    have ha : (tripleCharges (sourceA2612 + difference 4 0) (sourceB2612 + difference 0 4) sourceC2612) = raw36416 := by
      apply Matrix.ext; unfold tripleCharges sourceA2612 sourceB2612 sourceC2612 difference raw36416; decide +kernel
    rw [ha]
    exact (canonical36416 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2612 + difference 4 1) (sourceB2612 + difference 1 4) sourceC2612) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3414) := by
    have ha : (tripleCharges (sourceA2612 + difference 4 1) (sourceB2612 + difference 1 4) sourceC2612) = raw36417 := by
      apply Matrix.ext; unfold tripleCharges sourceA2612 sourceB2612 sourceC2612 difference raw36417; decide +kernel
    rw [ha]
    exact (canonical36417 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2612 + difference 4 2) (sourceB2612 + difference 2 4) sourceC2612) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3755) := by
    have ha : (tripleCharges (sourceA2612 + difference 4 2) (sourceB2612 + difference 2 4) sourceC2612) = raw36418 := by
      apply Matrix.ext; unfold tripleCharges sourceA2612 sourceB2612 sourceC2612 difference raw36418; decide +kernel
    rw [ha]
    exact (canonical36418 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2612 + difference 4 3) (sourceB2612 + difference 3 4) sourceC2612) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3768) := by
    have ha : (tripleCharges (sourceA2612 + difference 4 3) (sourceB2612 + difference 3 4) sourceC2612) = raw36419 := by
      apply Matrix.ext; unfold tripleCharges sourceA2612 sourceB2612 sourceC2612 difference raw36419; decide +kernel
    rw [ha]
    exact (canonical36419 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2612 + difference 4 5) (sourceB2612 + difference 5 4) sourceC2612) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3764) := by
    have ha : (tripleCharges (sourceA2612 + difference 4 5) (sourceB2612 + difference 5 4) sourceC2612) = raw19131 := by
      apply Matrix.ext; unfold tripleCharges sourceA2612 sourceB2612 sourceC2612 difference raw19131; decide +kernel
    rw [ha]
    exact (canonical19131 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2612 + difference 5 0) (sourceB2612 + difference 0 5) sourceC2612) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2176) := by
    have ha : (tripleCharges (sourceA2612 + difference 5 0) (sourceB2612 + difference 0 5) sourceC2612) = raw36420 := by
      apply Matrix.ext; unfold tripleCharges sourceA2612 sourceB2612 sourceC2612 difference raw36420; decide +kernel
    rw [ha]
    exact (canonical36420 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2612 + difference 5 1) (sourceB2612 + difference 1 5) sourceC2612) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2181) := by
    have ha : (tripleCharges (sourceA2612 + difference 5 1) (sourceB2612 + difference 1 5) sourceC2612) = raw36421 := by
      apply Matrix.ext; unfold tripleCharges sourceA2612 sourceB2612 sourceC2612 difference raw36421; decide +kernel
    rw [ha]
    exact (canonical36421 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2612 + difference 5 2) (sourceB2612 + difference 2 5) sourceC2612) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2178) := by
    have ha : (tripleCharges (sourceA2612 + difference 5 2) (sourceB2612 + difference 2 5) sourceC2612) = raw36422 := by
      apply Matrix.ext; unfold tripleCharges sourceA2612 sourceB2612 sourceC2612 difference raw36422; decide +kernel
    rw [ha]
    exact (canonical36422 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2612 + difference 5 3) (sourceB2612 + difference 3 5) sourceC2612) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2213) := by
    have ha : (tripleCharges (sourceA2612 + difference 5 3) (sourceB2612 + difference 3 5) sourceC2612) = raw36423 := by
      apply Matrix.ext; unfold tripleCharges sourceA2612 sourceB2612 sourceC2612 difference raw36423; decide +kernel
    rw [ha]
    exact (canonical36423 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2612 + difference 5 4) (sourceB2612 + difference 4 5) sourceC2612) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2213) := by
    have ha : (tripleCharges (sourceA2612 + difference 5 4) (sourceB2612 + difference 4 5) sourceC2612) = raw36424 := by
      apply Matrix.ext; unfold tripleCharges sourceA2612 sourceB2612 sourceC2612 difference raw36424; decide +kernel
    rw [ha]
    exact (canonical36424 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2612 sourceB2612 sourceC2612
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2612, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2613 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2613 : Charge := ![1, 2, -1, -1, -1, 0]
def sourceC2613 : Charge := ![1, 0, 1, 0, 0, -2]
def sourceForm2613 : Integer.Sparse Master := [(Sum.inr 4633, 1), (Sum.inr 4634, 2), (Sum.inr 4648, 1), (Sum.inr 4805, 1), (Sum.inr 4904, 1), (Sum.inr 4905, 2), (Sum.inr 4917, 1), (Sum.inr 5076, 1), (Sum.inr 5117, 1), (Sum.inr 5152, 2), (Sum.inr 5336, 2), (Sum.inr 5349, 2), (Sum.inr 5355, 2), (Sum.inr 5363, 1), (Sum.inr 5370, 2), (Sum.inr 5416, 1), (Sum.inr 5417, 1), (Sum.inr 5431, 1), (Sum.inr 5434, 2), (Sum.inr 5435, 2), (Sum.inr 5481, 1)]

theorem sourceEq2613 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2613 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2613 + difference 0 1) (sourceB2613 + difference 1 0) sourceC2613) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4805) := by
    have ha : (tripleCharges (sourceA2613 + difference 0 1) (sourceB2613 + difference 1 0) sourceC2613) = raw36425 := by
      apply Matrix.ext; unfold tripleCharges sourceA2613 sourceB2613 sourceC2613 difference raw36425; decide +kernel
    rw [ha]
    exact (canonical36425 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2613 + difference 0 2) (sourceB2613 + difference 2 0) sourceC2613) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5417) := by
    have ha : (tripleCharges (sourceA2613 + difference 0 2) (sourceB2613 + difference 2 0) sourceC2613) = raw36426 := by
      apply Matrix.ext; unfold tripleCharges sourceA2613 sourceB2613 sourceC2613 difference raw36426; decide +kernel
    rw [ha]
    exact (canonical36426 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2613 + difference 0 3) (sourceB2613 + difference 3 0) sourceC2613) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA2613 + difference 0 3) (sourceB2613 + difference 3 0) sourceC2613) = raw36427 := by
      apply Matrix.ext; unfold tripleCharges sourceA2613 sourceB2613 sourceC2613 difference raw36427; decide +kernel
    rw [ha]
    exact (canonical36427 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2613 + difference 0 4) (sourceB2613 + difference 4 0) sourceC2613) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA2613 + difference 0 4) (sourceB2613 + difference 4 0) sourceC2613) = raw36428 := by
      apply Matrix.ext; unfold tripleCharges sourceA2613 sourceB2613 sourceC2613 difference raw36428; decide +kernel
    rw [ha]
    exact (canonical36428 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2613 + difference 0 5) (sourceB2613 + difference 5 0) sourceC2613) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA2613 + difference 0 5) (sourceB2613 + difference 5 0) sourceC2613) = raw18803 := by
      apply Matrix.ext; unfold tripleCharges sourceA2613 sourceB2613 sourceC2613 difference raw18803; decide +kernel
    rw [ha]
    exact (canonical18803 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2613 + difference 1 0) (sourceB2613 + difference 0 1) sourceC2613) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5076) := by
    have ha : (tripleCharges (sourceA2613 + difference 1 0) (sourceB2613 + difference 0 1) sourceC2613) = raw18828 := by
      apply Matrix.ext; unfold tripleCharges sourceA2613 sourceB2613 sourceC2613 difference raw18828; decide +kernel
    rw [ha]
    exact (canonical18828 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2613 + difference 1 2) (sourceB2613 + difference 2 1) sourceC2613) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5416) := by
    have ha : (tripleCharges (sourceA2613 + difference 1 2) (sourceB2613 + difference 2 1) sourceC2613) = raw18830 := by
      apply Matrix.ext; unfold tripleCharges sourceA2613 sourceB2613 sourceC2613 difference raw18830; decide +kernel
    rw [ha]
    exact (canonical18830 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2613 + difference 1 3) (sourceB2613 + difference 3 1) sourceC2613) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA2613 + difference 1 3) (sourceB2613 + difference 3 1) sourceC2613) = raw18831 := by
      apply Matrix.ext; unfold tripleCharges sourceA2613 sourceB2613 sourceC2613 difference raw18831; decide +kernel
    rw [ha]
    exact (canonical18831 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2613 + difference 1 4) (sourceB2613 + difference 4 1) sourceC2613) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA2613 + difference 1 4) (sourceB2613 + difference 4 1) sourceC2613) = raw18832 := by
      apply Matrix.ext; unfold tripleCharges sourceA2613 sourceB2613 sourceC2613 difference raw18832; decide +kernel
    rw [ha]
    exact (canonical18832 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2613 + difference 1 5) (sourceB2613 + difference 5 1) sourceC2613) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5481) := by
    have ha : (tripleCharges (sourceA2613 + difference 1 5) (sourceB2613 + difference 5 1) sourceC2613) = raw33016 := by
      apply Matrix.ext; unfold tripleCharges sourceA2613 sourceB2613 sourceC2613 difference raw33016; decide +kernel
    rw [ha]
    exact (canonical33016 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2613 + difference 2 0) (sourceB2613 + difference 0 2) sourceC2613) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4917) := by
    have ha : (tripleCharges (sourceA2613 + difference 2 0) (sourceB2613 + difference 0 2) sourceC2613) = raw33021 := by
      apply Matrix.ext; unfold tripleCharges sourceA2613 sourceB2613 sourceC2613 difference raw33021; decide +kernel
    rw [ha]
    exact (canonical33021 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2613 + difference 2 1) (sourceB2613 + difference 1 2) sourceC2613) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4648) := by
    have ha : (tripleCharges (sourceA2613 + difference 2 1) (sourceB2613 + difference 1 2) sourceC2613) = raw36429 := by
      apply Matrix.ext; unfold tripleCharges sourceA2613 sourceB2613 sourceC2613 difference raw36429; decide +kernel
    rw [ha]
    exact (canonical36429 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2613 + difference 2 3) (sourceB2613 + difference 3 2) sourceC2613) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5370) := by
    have ha : (tripleCharges (sourceA2613 + difference 2 3) (sourceB2613 + difference 3 2) sourceC2613) = raw36430 := by
      apply Matrix.ext; unfold tripleCharges sourceA2613 sourceB2613 sourceC2613 difference raw36430; decide +kernel
    rw [ha]
    exact (canonical36430 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2613 + difference 2 4) (sourceB2613 + difference 4 2) sourceC2613) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5370) := by
    have ha : (tripleCharges (sourceA2613 + difference 2 4) (sourceB2613 + difference 4 2) sourceC2613) = raw36431 := by
      apply Matrix.ext; unfold tripleCharges sourceA2613 sourceB2613 sourceC2613 difference raw36431; decide +kernel
    rw [ha]
    exact (canonical36431 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2613 + difference 2 5) (sourceB2613 + difference 5 2) sourceC2613) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5363) := by
    have ha : (tripleCharges (sourceA2613 + difference 2 5) (sourceB2613 + difference 5 2) sourceC2613) = raw18814 := by
      apply Matrix.ext; unfold tripleCharges sourceA2613 sourceB2613 sourceC2613 difference raw18814; decide +kernel
    rw [ha]
    exact (canonical18814 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2613 + difference 3 0) (sourceB2613 + difference 0 3) sourceC2613) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4905) := by
    have ha : (tripleCharges (sourceA2613 + difference 3 0) (sourceB2613 + difference 0 3) sourceC2613) = raw33024 := by
      apply Matrix.ext; unfold tripleCharges sourceA2613 sourceB2613 sourceC2613 difference raw33024; decide +kernel
    rw [ha]
    exact (canonical33024 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2613 + difference 3 1) (sourceB2613 + difference 1 3) sourceC2613) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4634) := by
    have ha : (tripleCharges (sourceA2613 + difference 3 1) (sourceB2613 + difference 1 3) sourceC2613) = raw36432 := by
      apply Matrix.ext; unfold tripleCharges sourceA2613 sourceB2613 sourceC2613 difference raw36432; decide +kernel
    rw [ha]
    exact (canonical36432 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2613 + difference 3 2) (sourceB2613 + difference 2 3) sourceC2613) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5336) := by
    have ha : (tripleCharges (sourceA2613 + difference 3 2) (sourceB2613 + difference 2 3) sourceC2613) = raw36433 := by
      apply Matrix.ext; unfold tripleCharges sourceA2613 sourceB2613 sourceC2613 difference raw36433; decide +kernel
    rw [ha]
    exact (canonical36433 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2613 + difference 3 4) (sourceB2613 + difference 4 3) sourceC2613) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5355) := by
    have ha : (tripleCharges (sourceA2613 + difference 3 4) (sourceB2613 + difference 4 3) sourceC2613) = raw36434 := by
      apply Matrix.ext; unfold tripleCharges sourceA2613 sourceB2613 sourceC2613 difference raw36434; decide +kernel
    rw [ha]
    exact (canonical36434 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2613 + difference 3 5) (sourceB2613 + difference 5 3) sourceC2613) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5349) := by
    have ha : (tripleCharges (sourceA2613 + difference 3 5) (sourceB2613 + difference 5 3) sourceC2613) = raw18819 := by
      apply Matrix.ext; unfold tripleCharges sourceA2613 sourceB2613 sourceC2613 difference raw18819; decide +kernel
    rw [ha]
    exact (canonical18819 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2613 + difference 4 0) (sourceB2613 + difference 0 4) sourceC2613) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4905) := by
    have ha : (tripleCharges (sourceA2613 + difference 4 0) (sourceB2613 + difference 0 4) sourceC2613) = raw30320 := by
      apply Matrix.ext; unfold tripleCharges sourceA2613 sourceB2613 sourceC2613 difference raw30320; decide +kernel
    rw [ha]
    exact (canonical30320 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2613 + difference 4 1) (sourceB2613 + difference 1 4) sourceC2613) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4634) := by
    have ha : (tripleCharges (sourceA2613 + difference 4 1) (sourceB2613 + difference 1 4) sourceC2613) = raw36435 := by
      apply Matrix.ext; unfold tripleCharges sourceA2613 sourceB2613 sourceC2613 difference raw36435; decide +kernel
    rw [ha]
    exact (canonical36435 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2613 + difference 4 2) (sourceB2613 + difference 2 4) sourceC2613) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5336) := by
    have ha : (tripleCharges (sourceA2613 + difference 4 2) (sourceB2613 + difference 2 4) sourceC2613) = raw36436 := by
      apply Matrix.ext; unfold tripleCharges sourceA2613 sourceB2613 sourceC2613 difference raw36436; decide +kernel
    rw [ha]
    exact (canonical36436 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2613 + difference 4 3) (sourceB2613 + difference 3 4) sourceC2613) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5355) := by
    have ha : (tripleCharges (sourceA2613 + difference 4 3) (sourceB2613 + difference 3 4) sourceC2613) = raw30306 := by
      apply Matrix.ext; unfold tripleCharges sourceA2613 sourceB2613 sourceC2613 difference raw30306; decide +kernel
    rw [ha]
    exact (canonical30306 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2613 + difference 4 5) (sourceB2613 + difference 5 4) sourceC2613) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5349) := by
    have ha : (tripleCharges (sourceA2613 + difference 4 5) (sourceB2613 + difference 5 4) sourceC2613) = raw18824 := by
      apply Matrix.ext; unfold tripleCharges sourceA2613 sourceB2613 sourceC2613 difference raw18824; decide +kernel
    rw [ha]
    exact (canonical18824 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2613 + difference 5 0) (sourceB2613 + difference 0 5) sourceC2613) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4904) := by
    have ha : (tripleCharges (sourceA2613 + difference 5 0) (sourceB2613 + difference 0 5) sourceC2613) = raw33029 := by
      apply Matrix.ext; unfold tripleCharges sourceA2613 sourceB2613 sourceC2613 difference raw33029; decide +kernel
    rw [ha]
    exact (canonical33029 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2613 + difference 5 1) (sourceB2613 + difference 1 5) sourceC2613) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4633) := by
    have ha : (tripleCharges (sourceA2613 + difference 5 1) (sourceB2613 + difference 1 5) sourceC2613) = raw36437 := by
      apply Matrix.ext; unfold tripleCharges sourceA2613 sourceB2613 sourceC2613 difference raw36437; decide +kernel
    rw [ha]
    exact (canonical36437 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2613 + difference 5 2) (sourceB2613 + difference 2 5) sourceC2613) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5117) := by
    have ha : (tripleCharges (sourceA2613 + difference 5 2) (sourceB2613 + difference 2 5) sourceC2613) = raw36438 := by
      apply Matrix.ext; unfold tripleCharges sourceA2613 sourceB2613 sourceC2613 difference raw36438; decide +kernel
    rw [ha]
    exact (canonical36438 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2613 + difference 5 3) (sourceB2613 + difference 3 5) sourceC2613) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5152) := by
    have ha : (tripleCharges (sourceA2613 + difference 5 3) (sourceB2613 + difference 3 5) sourceC2613) = raw36439 := by
      apply Matrix.ext; unfold tripleCharges sourceA2613 sourceB2613 sourceC2613 difference raw36439; decide +kernel
    rw [ha]
    exact (canonical36439 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2613 + difference 5 4) (sourceB2613 + difference 4 5) sourceC2613) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5152) := by
    have ha : (tripleCharges (sourceA2613 + difference 5 4) (sourceB2613 + difference 4 5) sourceC2613) = raw36440 := by
      apply Matrix.ext; unfold tripleCharges sourceA2613 sourceB2613 sourceC2613 difference raw36440; decide +kernel
    rw [ha]
    exact (canonical36440 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2613 sourceB2613 sourceC2613
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2613, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2614 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2614 : Charge := ![1, 0, 1, 0, -1, -1]
def sourceC2614 : Charge := ![1, 2, -1, -1, 0, -1]
def sourceForm2614 : Integer.Sparse Master := [(Sum.inr 4930, 1), (Sum.inr 4932, 1), (Sum.inr 4933, 1), (Sum.inr 4941, 1), (Sum.inr 4954, 1), (Sum.inr 4955, 1), (Sum.inr 4958, 1), (Sum.inr 4968, 1), (Sum.inr 5040, 1), (Sum.inr 5067, 1), (Sum.inr 5073, 1), (Sum.inr 5152, 1), (Sum.inr 5185, 1), (Sum.inr 5338, 1), (Sum.inr 5340, 1), (Sum.inr 5348, 1), (Sum.inr 5352, 2), (Sum.inr 5354, 1), (Sum.inr 5356, 1), (Sum.inr 5366, 1), (Sum.inr 5369, 1), (Sum.inr 5401, 1), (Sum.inr 5405, 1), (Sum.inr 5408, 1), (Sum.inr 5410, 1), (Sum.inr 5470, 1), (Sum.inr 5471, 1), (Sum.inr 5472, 1), (Sum.inr 5473, 1)]

theorem sourceEq2614 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2614 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2614 + difference 0 1) (sourceB2614 + difference 1 0) sourceC2614) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5073) := by
    have ha : (tripleCharges (sourceA2614 + difference 0 1) (sourceB2614 + difference 1 0) sourceC2614) = raw36441 := by
      apply Matrix.ext; unfold tripleCharges sourceA2614 sourceB2614 sourceC2614 difference raw36441; decide +kernel
    rw [ha]
    exact (canonical36441 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2614 + difference 0 2) (sourceB2614 + difference 2 0) sourceC2614) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5401) := by
    have ha : (tripleCharges (sourceA2614 + difference 0 2) (sourceB2614 + difference 2 0) sourceC2614) = raw36442 := by
      apply Matrix.ext; unfold tripleCharges sourceA2614 sourceB2614 sourceC2614 difference raw36442; decide +kernel
    rw [ha]
    exact (canonical36442 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2614 + difference 0 3) (sourceB2614 + difference 3 0) sourceC2614) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5405) := by
    have ha : (tripleCharges (sourceA2614 + difference 0 3) (sourceB2614 + difference 3 0) sourceC2614) = raw16736 := by
      apply Matrix.ext; unfold tripleCharges sourceA2614 sourceB2614 sourceC2614 difference raw16736; decide +kernel
    rw [ha]
    exact (canonical16736 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2614 + difference 0 4) (sourceB2614 + difference 4 0) sourceC2614) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5410) := by
    have ha : (tripleCharges (sourceA2614 + difference 0 4) (sourceB2614 + difference 4 0) sourceC2614) = raw36443 := by
      apply Matrix.ext; unfold tripleCharges sourceA2614 sourceB2614 sourceC2614 difference raw36443; decide +kernel
    rw [ha]
    exact (canonical36443 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2614 + difference 0 5) (sourceB2614 + difference 5 0) sourceC2614) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5408) := by
    have ha : (tripleCharges (sourceA2614 + difference 0 5) (sourceB2614 + difference 5 0) sourceC2614) = raw36444 := by
      apply Matrix.ext; unfold tripleCharges sourceA2614 sourceB2614 sourceC2614 difference raw36444; decide +kernel
    rw [ha]
    exact (canonical36444 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2614 + difference 1 0) (sourceB2614 + difference 0 1) sourceC2614) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5185) := by
    have ha : (tripleCharges (sourceA2614 + difference 1 0) (sourceB2614 + difference 0 1) sourceC2614) = raw16751 := by
      apply Matrix.ext; unfold tripleCharges sourceA2614 sourceB2614 sourceC2614 difference raw16751; decide +kernel
    rw [ha]
    exact (canonical16751 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2614 + difference 1 2) (sourceB2614 + difference 2 1) sourceC2614) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5470) := by
    have ha : (tripleCharges (sourceA2614 + difference 1 2) (sourceB2614 + difference 2 1) sourceC2614) = raw16753 := by
      apply Matrix.ext; unfold tripleCharges sourceA2614 sourceB2614 sourceC2614 difference raw16753; decide +kernel
    rw [ha]
    exact (canonical16753 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2614 + difference 1 3) (sourceB2614 + difference 3 1) sourceC2614) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5471) := by
    have ha : (tripleCharges (sourceA2614 + difference 1 3) (sourceB2614 + difference 3 1) sourceC2614) = raw36445 := by
      apply Matrix.ext; unfold tripleCharges sourceA2614 sourceB2614 sourceC2614 difference raw36445; decide +kernel
    rw [ha]
    exact (canonical36445 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2614 + difference 1 4) (sourceB2614 + difference 4 1) sourceC2614) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA2614 + difference 1 4) (sourceB2614 + difference 4 1) sourceC2614) = raw16754 := by
      apply Matrix.ext; unfold tripleCharges sourceA2614 sourceB2614 sourceC2614 difference raw16754; decide +kernel
    rw [ha]
    exact (canonical16754 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2614 + difference 1 5) (sourceB2614 + difference 5 1) sourceC2614) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5472) := by
    have ha : (tripleCharges (sourceA2614 + difference 1 5) (sourceB2614 + difference 5 1) sourceC2614) = raw16755 := by
      apply Matrix.ext; unfold tripleCharges sourceA2614 sourceB2614 sourceC2614 difference raw16755; decide +kernel
    rw [ha]
    exact (canonical16755 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2614 + difference 2 0) (sourceB2614 + difference 0 2) sourceC2614) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4968) := by
    have ha : (tripleCharges (sourceA2614 + difference 2 0) (sourceB2614 + difference 0 2) sourceC2614) = raw36446 := by
      apply Matrix.ext; unfold tripleCharges sourceA2614 sourceB2614 sourceC2614 difference raw36446; decide +kernel
    rw [ha]
    exact (canonical36446 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2614 + difference 2 1) (sourceB2614 + difference 1 2) sourceC2614) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4941) := by
    have ha : (tripleCharges (sourceA2614 + difference 2 1) (sourceB2614 + difference 1 2) sourceC2614) = raw36447 := by
      apply Matrix.ext; unfold tripleCharges sourceA2614 sourceB2614 sourceC2614 difference raw36447; decide +kernel
    rw [ha]
    exact (canonical36447 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2614 + difference 2 3) (sourceB2614 + difference 3 2) sourceC2614) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5352) := by
    have ha : (tripleCharges (sourceA2614 + difference 2 3) (sourceB2614 + difference 3 2) sourceC2614) = raw16747 := by
      apply Matrix.ext; unfold tripleCharges sourceA2614 sourceB2614 sourceC2614 difference raw16747; decide +kernel
    rw [ha]
    exact (canonical16747 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2614 + difference 2 4) (sourceB2614 + difference 4 2) sourceC2614) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5369) := by
    have ha : (tripleCharges (sourceA2614 + difference 2 4) (sourceB2614 + difference 4 2) sourceC2614) = raw36448 := by
      apply Matrix.ext; unfold tripleCharges sourceA2614 sourceB2614 sourceC2614 difference raw36448; decide +kernel
    rw [ha]
    exact (canonical36448 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2614 + difference 2 5) (sourceB2614 + difference 5 2) sourceC2614) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5366) := by
    have ha : (tripleCharges (sourceA2614 + difference 2 5) (sourceB2614 + difference 5 2) sourceC2614) = raw36449 := by
      apply Matrix.ext; unfold tripleCharges sourceA2614 sourceB2614 sourceC2614 difference raw36449; decide +kernel
    rw [ha]
    exact (canonical36449 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2614 + difference 3 0) (sourceB2614 + difference 0 3) sourceC2614) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4958) := by
    have ha : (tripleCharges (sourceA2614 + difference 3 0) (sourceB2614 + difference 0 3) sourceC2614) = raw36450 := by
      apply Matrix.ext; unfold tripleCharges sourceA2614 sourceB2614 sourceC2614 difference raw36450; decide +kernel
    rw [ha]
    exact (canonical36450 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2614 + difference 3 1) (sourceB2614 + difference 1 3) sourceC2614) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4932) := by
    have ha : (tripleCharges (sourceA2614 + difference 3 1) (sourceB2614 + difference 1 3) sourceC2614) = raw36451 := by
      apply Matrix.ext; unfold tripleCharges sourceA2614 sourceB2614 sourceC2614 difference raw36451; decide +kernel
    rw [ha]
    exact (canonical36451 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2614 + difference 3 2) (sourceB2614 + difference 2 3) sourceC2614) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5340) := by
    have ha : (tripleCharges (sourceA2614 + difference 3 2) (sourceB2614 + difference 2 3) sourceC2614) = raw36452 := by
      apply Matrix.ext; unfold tripleCharges sourceA2614 sourceB2614 sourceC2614 difference raw36452; decide +kernel
    rw [ha]
    exact (canonical36452 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2614 + difference 3 4) (sourceB2614 + difference 4 3) sourceC2614) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5356) := by
    have ha : (tripleCharges (sourceA2614 + difference 3 4) (sourceB2614 + difference 4 3) sourceC2614) = raw36453 := by
      apply Matrix.ext; unfold tripleCharges sourceA2614 sourceB2614 sourceC2614 difference raw36453; decide +kernel
    rw [ha]
    exact (canonical36453 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2614 + difference 3 5) (sourceB2614 + difference 5 3) sourceC2614) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5352) := by
    have ha : (tripleCharges (sourceA2614 + difference 3 5) (sourceB2614 + difference 5 3) sourceC2614) = raw36454 := by
      apply Matrix.ext; unfold tripleCharges sourceA2614 sourceB2614 sourceC2614 difference raw36454; decide +kernel
    rw [ha]
    exact (canonical36454 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2614 + difference 4 0) (sourceB2614 + difference 0 4) sourceC2614) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4955) := by
    have ha : (tripleCharges (sourceA2614 + difference 4 0) (sourceB2614 + difference 0 4) sourceC2614) = raw36455 := by
      apply Matrix.ext; unfold tripleCharges sourceA2614 sourceB2614 sourceC2614 difference raw36455; decide +kernel
    rw [ha]
    exact (canonical36455 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2614 + difference 4 1) (sourceB2614 + difference 1 4) sourceC2614) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4933) := by
    have ha : (tripleCharges (sourceA2614 + difference 4 1) (sourceB2614 + difference 1 4) sourceC2614) = raw36456 := by
      apply Matrix.ext; unfold tripleCharges sourceA2614 sourceB2614 sourceC2614 difference raw36456; decide +kernel
    rw [ha]
    exact (canonical36456 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2614 + difference 4 2) (sourceB2614 + difference 2 4) sourceC2614) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5338) := by
    have ha : (tripleCharges (sourceA2614 + difference 4 2) (sourceB2614 + difference 2 4) sourceC2614) = raw36457 := by
      apply Matrix.ext; unfold tripleCharges sourceA2614 sourceB2614 sourceC2614 difference raw36457; decide +kernel
    rw [ha]
    exact (canonical36457 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2614 + difference 4 3) (sourceB2614 + difference 3 4) sourceC2614) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5348) := by
    have ha : (tripleCharges (sourceA2614 + difference 4 3) (sourceB2614 + difference 3 4) sourceC2614) = raw16757 := by
      apply Matrix.ext; unfold tripleCharges sourceA2614 sourceB2614 sourceC2614 difference raw16757; decide +kernel
    rw [ha]
    exact (canonical16757 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2614 + difference 4 5) (sourceB2614 + difference 5 4) sourceC2614) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5354) := by
    have ha : (tripleCharges (sourceA2614 + difference 4 5) (sourceB2614 + difference 5 4) sourceC2614) = raw36458 := by
      apply Matrix.ext; unfold tripleCharges sourceA2614 sourceB2614 sourceC2614 difference raw36458; decide +kernel
    rw [ha]
    exact (canonical36458 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2614 + difference 5 0) (sourceB2614 + difference 0 5) sourceC2614) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4954) := by
    have ha : (tripleCharges (sourceA2614 + difference 5 0) (sourceB2614 + difference 0 5) sourceC2614) = raw36459 := by
      apply Matrix.ext; unfold tripleCharges sourceA2614 sourceB2614 sourceC2614 difference raw36459; decide +kernel
    rw [ha]
    exact (canonical36459 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2614 + difference 5 1) (sourceB2614 + difference 1 5) sourceC2614) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4930) := by
    have ha : (tripleCharges (sourceA2614 + difference 5 1) (sourceB2614 + difference 1 5) sourceC2614) = raw36460 := by
      apply Matrix.ext; unfold tripleCharges sourceA2614 sourceB2614 sourceC2614 difference raw36460; decide +kernel
    rw [ha]
    exact (canonical36460 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2614 + difference 5 2) (sourceB2614 + difference 2 5) sourceC2614) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5040) := by
    have ha : (tripleCharges (sourceA2614 + difference 5 2) (sourceB2614 + difference 2 5) sourceC2614) = raw36461 := by
      apply Matrix.ext; unfold tripleCharges sourceA2614 sourceB2614 sourceC2614 difference raw36461; decide +kernel
    rw [ha]
    exact (canonical36461 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2614 + difference 5 3) (sourceB2614 + difference 3 5) sourceC2614) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5067) := by
    have ha : (tripleCharges (sourceA2614 + difference 5 3) (sourceB2614 + difference 3 5) sourceC2614) = raw16762 := by
      apply Matrix.ext; unfold tripleCharges sourceA2614 sourceB2614 sourceC2614 difference raw16762; decide +kernel
    rw [ha]
    exact (canonical16762 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2614 + difference 5 4) (sourceB2614 + difference 4 5) sourceC2614) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5152) := by
    have ha : (tripleCharges (sourceA2614 + difference 5 4) (sourceB2614 + difference 4 5) sourceC2614) = raw36462 := by
      apply Matrix.ext; unfold tripleCharges sourceA2614 sourceB2614 sourceC2614 difference raw36462; decide +kernel
    rw [ha]
    exact (canonical36462 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2614 sourceB2614 sourceC2614
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2614, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2615 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2615 : Charge := ![1, 0, 1, 0, -1, -1]
def sourceC2615 : Charge := ![1, 2, -1, -1, 0, -1]
def sourceForm2615 : Integer.Sparse Master := [(Sum.inr 3408, 1), (Sum.inr 3409, 1), (Sum.inr 3410, 1), (Sum.inr 3414, 1), (Sum.inr 3452, 1), (Sum.inr 3454, 1), (Sum.inr 3467, 1), (Sum.inr 3476, 1), (Sum.inr 3508, 1), (Sum.inr 3511, 1), (Sum.inr 3529, 1), (Sum.inr 3587, 1), (Sum.inr 3612, 1), (Sum.inr 3755, 1), (Sum.inr 3763, 1), (Sum.inr 3764, 2), (Sum.inr 3765, 1), (Sum.inr 3768, 1), (Sum.inr 3769, 1), (Sum.inr 3773, 1), (Sum.inr 3774, 1), (Sum.inr 3804, 1), (Sum.inr 3805, 1), (Sum.inr 3806, 1), (Sum.inr 3816, 1), (Sum.inr 3955, 1), (Sum.inr 3956, 1), (Sum.inr 3957, 1), (Sum.inr 3961, 1)]

theorem sourceEq2615 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2615 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2615 + difference 0 1) (sourceB2615 + difference 1 0) sourceC2615) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3467) := by
    have ha : (tripleCharges (sourceA2615 + difference 0 1) (sourceB2615 + difference 1 0) sourceC2615) = raw36463 := by
      apply Matrix.ext; unfold tripleCharges sourceA2615 sourceB2615 sourceC2615 difference raw36463; decide +kernel
    rw [ha]
    exact (canonical36463 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2615 + difference 0 2) (sourceB2615 + difference 2 0) sourceC2615) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3804) := by
    have ha : (tripleCharges (sourceA2615 + difference 0 2) (sourceB2615 + difference 2 0) sourceC2615) = raw36464 := by
      apply Matrix.ext; unfold tripleCharges sourceA2615 sourceB2615 sourceC2615 difference raw36464; decide +kernel
    rw [ha]
    exact (canonical36464 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2615 + difference 0 3) (sourceB2615 + difference 3 0) sourceC2615) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3805) := by
    have ha : (tripleCharges (sourceA2615 + difference 0 3) (sourceB2615 + difference 3 0) sourceC2615) = raw16796 := by
      apply Matrix.ext; unfold tripleCharges sourceA2615 sourceB2615 sourceC2615 difference raw16796; decide +kernel
    rw [ha]
    exact (canonical16796 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2615 + difference 0 4) (sourceB2615 + difference 4 0) sourceC2615) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3816) := by
    have ha : (tripleCharges (sourceA2615 + difference 0 4) (sourceB2615 + difference 4 0) sourceC2615) = raw36465 := by
      apply Matrix.ext; unfold tripleCharges sourceA2615 sourceB2615 sourceC2615 difference raw36465; decide +kernel
    rw [ha]
    exact (canonical36465 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2615 + difference 0 5) (sourceB2615 + difference 5 0) sourceC2615) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3806) := by
    have ha : (tripleCharges (sourceA2615 + difference 0 5) (sourceB2615 + difference 5 0) sourceC2615) = raw36466 := by
      apply Matrix.ext; unfold tripleCharges sourceA2615 sourceB2615 sourceC2615 difference raw36466; decide +kernel
    rw [ha]
    exact (canonical36466 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2615 + difference 1 0) (sourceB2615 + difference 0 1) sourceC2615) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3529) := by
    have ha : (tripleCharges (sourceA2615 + difference 1 0) (sourceB2615 + difference 0 1) sourceC2615) = raw16811 := by
      apply Matrix.ext; unfold tripleCharges sourceA2615 sourceB2615 sourceC2615 difference raw16811; decide +kernel
    rw [ha]
    exact (canonical16811 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2615 + difference 1 2) (sourceB2615 + difference 2 1) sourceC2615) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3955) := by
    have ha : (tripleCharges (sourceA2615 + difference 1 2) (sourceB2615 + difference 2 1) sourceC2615) = raw16813 := by
      apply Matrix.ext; unfold tripleCharges sourceA2615 sourceB2615 sourceC2615 difference raw16813; decide +kernel
    rw [ha]
    exact (canonical16813 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2615 + difference 1 3) (sourceB2615 + difference 3 1) sourceC2615) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3956) := by
    have ha : (tripleCharges (sourceA2615 + difference 1 3) (sourceB2615 + difference 3 1) sourceC2615) = raw36467 := by
      apply Matrix.ext; unfold tripleCharges sourceA2615 sourceB2615 sourceC2615 difference raw36467; decide +kernel
    rw [ha]
    exact (canonical36467 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2615 + difference 1 4) (sourceB2615 + difference 4 1) sourceC2615) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3961) := by
    have ha : (tripleCharges (sourceA2615 + difference 1 4) (sourceB2615 + difference 4 1) sourceC2615) = raw16814 := by
      apply Matrix.ext; unfold tripleCharges sourceA2615 sourceB2615 sourceC2615 difference raw16814; decide +kernel
    rw [ha]
    exact (canonical16814 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2615 + difference 1 5) (sourceB2615 + difference 5 1) sourceC2615) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3957) := by
    have ha : (tripleCharges (sourceA2615 + difference 1 5) (sourceB2615 + difference 5 1) sourceC2615) = raw16815 := by
      apply Matrix.ext; unfold tripleCharges sourceA2615 sourceB2615 sourceC2615 difference raw16815; decide +kernel
    rw [ha]
    exact (canonical16815 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2615 + difference 2 0) (sourceB2615 + difference 0 2) sourceC2615) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3587) := by
    have ha : (tripleCharges (sourceA2615 + difference 2 0) (sourceB2615 + difference 0 2) sourceC2615) = raw36468 := by
      apply Matrix.ext; unfold tripleCharges sourceA2615 sourceB2615 sourceC2615 difference raw36468; decide +kernel
    rw [ha]
    exact (canonical36468 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2615 + difference 2 1) (sourceB2615 + difference 1 2) sourceC2615) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3410) := by
    have ha : (tripleCharges (sourceA2615 + difference 2 1) (sourceB2615 + difference 1 2) sourceC2615) = raw36469 := by
      apply Matrix.ext; unfold tripleCharges sourceA2615 sourceB2615 sourceC2615 difference raw36469; decide +kernel
    rw [ha]
    exact (canonical36469 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2615 + difference 2 3) (sourceB2615 + difference 3 2) sourceC2615) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3764) := by
    have ha : (tripleCharges (sourceA2615 + difference 2 3) (sourceB2615 + difference 3 2) sourceC2615) = raw16807 := by
      apply Matrix.ext; unfold tripleCharges sourceA2615 sourceB2615 sourceC2615 difference raw16807; decide +kernel
    rw [ha]
    exact (canonical16807 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2615 + difference 2 4) (sourceB2615 + difference 4 2) sourceC2615) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3774) := by
    have ha : (tripleCharges (sourceA2615 + difference 2 4) (sourceB2615 + difference 4 2) sourceC2615) = raw36470 := by
      apply Matrix.ext; unfold tripleCharges sourceA2615 sourceB2615 sourceC2615 difference raw36470; decide +kernel
    rw [ha]
    exact (canonical36470 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2615 + difference 2 5) (sourceB2615 + difference 5 2) sourceC2615) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3765) := by
    have ha : (tripleCharges (sourceA2615 + difference 2 5) (sourceB2615 + difference 5 2) sourceC2615) = raw36471 := by
      apply Matrix.ext; unfold tripleCharges sourceA2615 sourceB2615 sourceC2615 difference raw36471; decide +kernel
    rw [ha]
    exact (canonical36471 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2615 + difference 3 0) (sourceB2615 + difference 0 3) sourceC2615) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3511) := by
    have ha : (tripleCharges (sourceA2615 + difference 3 0) (sourceB2615 + difference 0 3) sourceC2615) = raw36472 := by
      apply Matrix.ext; unfold tripleCharges sourceA2615 sourceB2615 sourceC2615 difference raw36472; decide +kernel
    rw [ha]
    exact (canonical36472 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2615 + difference 3 1) (sourceB2615 + difference 1 3) sourceC2615) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3409) := by
    have ha : (tripleCharges (sourceA2615 + difference 3 1) (sourceB2615 + difference 1 3) sourceC2615) = raw36473 := by
      apply Matrix.ext; unfold tripleCharges sourceA2615 sourceB2615 sourceC2615 difference raw36473; decide +kernel
    rw [ha]
    exact (canonical36473 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2615 + difference 3 2) (sourceB2615 + difference 2 3) sourceC2615) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3763) := by
    have ha : (tripleCharges (sourceA2615 + difference 3 2) (sourceB2615 + difference 2 3) sourceC2615) = raw36474 := by
      apply Matrix.ext; unfold tripleCharges sourceA2615 sourceB2615 sourceC2615 difference raw36474; decide +kernel
    rw [ha]
    exact (canonical36474 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2615 + difference 3 4) (sourceB2615 + difference 4 3) sourceC2615) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3773) := by
    have ha : (tripleCharges (sourceA2615 + difference 3 4) (sourceB2615 + difference 4 3) sourceC2615) = raw36475 := by
      apply Matrix.ext; unfold tripleCharges sourceA2615 sourceB2615 sourceC2615 difference raw36475; decide +kernel
    rw [ha]
    exact (canonical36475 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2615 + difference 3 5) (sourceB2615 + difference 5 3) sourceC2615) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3764) := by
    have ha : (tripleCharges (sourceA2615 + difference 3 5) (sourceB2615 + difference 5 3) sourceC2615) = raw36476 := by
      apply Matrix.ext; unfold tripleCharges sourceA2615 sourceB2615 sourceC2615 difference raw36476; decide +kernel
    rw [ha]
    exact (canonical36476 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2615 + difference 4 0) (sourceB2615 + difference 0 4) sourceC2615) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3508) := by
    have ha : (tripleCharges (sourceA2615 + difference 4 0) (sourceB2615 + difference 0 4) sourceC2615) = raw36477 := by
      apply Matrix.ext; unfold tripleCharges sourceA2615 sourceB2615 sourceC2615 difference raw36477; decide +kernel
    rw [ha]
    exact (canonical36477 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2615 + difference 4 1) (sourceB2615 + difference 1 4) sourceC2615) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3414) := by
    have ha : (tripleCharges (sourceA2615 + difference 4 1) (sourceB2615 + difference 1 4) sourceC2615) = raw36478 := by
      apply Matrix.ext; unfold tripleCharges sourceA2615 sourceB2615 sourceC2615 difference raw36478; decide +kernel
    rw [ha]
    exact (canonical36478 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2615 + difference 4 2) (sourceB2615 + difference 2 4) sourceC2615) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3755) := by
    have ha : (tripleCharges (sourceA2615 + difference 4 2) (sourceB2615 + difference 2 4) sourceC2615) = raw36479 := by
      apply Matrix.ext; unfold tripleCharges sourceA2615 sourceB2615 sourceC2615 difference raw36479; decide +kernel
    rw [ha]
    exact (canonical36479 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2615 + difference 4 3) (sourceB2615 + difference 3 4) sourceC2615) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3768) := by
    have ha : (tripleCharges (sourceA2615 + difference 4 3) (sourceB2615 + difference 3 4) sourceC2615) = raw16817 := by
      apply Matrix.ext; unfold tripleCharges sourceA2615 sourceB2615 sourceC2615 difference raw16817; decide +kernel
    rw [ha]
    exact (canonical16817 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2615 + difference 4 5) (sourceB2615 + difference 5 4) sourceC2615) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3769) := by
    have ha : (tripleCharges (sourceA2615 + difference 4 5) (sourceB2615 + difference 5 4) sourceC2615) = raw36480 := by
      apply Matrix.ext; unfold tripleCharges sourceA2615 sourceB2615 sourceC2615 difference raw36480; decide +kernel
    rw [ha]
    exact (canonical36480 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2615 + difference 5 0) (sourceB2615 + difference 0 5) sourceC2615) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3452) := by
    have ha : (tripleCharges (sourceA2615 + difference 5 0) (sourceB2615 + difference 0 5) sourceC2615) = raw36481 := by
      apply Matrix.ext; unfold tripleCharges sourceA2615 sourceB2615 sourceC2615 difference raw36481; decide +kernel
    rw [ha]
    exact (canonical36481 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2615 + difference 5 1) (sourceB2615 + difference 1 5) sourceC2615) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3408) := by
    have ha : (tripleCharges (sourceA2615 + difference 5 1) (sourceB2615 + difference 1 5) sourceC2615) = raw36482 := by
      apply Matrix.ext; unfold tripleCharges sourceA2615 sourceB2615 sourceC2615 difference raw36482; decide +kernel
    rw [ha]
    exact (canonical36482 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2615 + difference 5 2) (sourceB2615 + difference 2 5) sourceC2615) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3454) := by
    have ha : (tripleCharges (sourceA2615 + difference 5 2) (sourceB2615 + difference 2 5) sourceC2615) = raw36483 := by
      apply Matrix.ext; unfold tripleCharges sourceA2615 sourceB2615 sourceC2615 difference raw36483; decide +kernel
    rw [ha]
    exact (canonical36483 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2615 + difference 5 3) (sourceB2615 + difference 3 5) sourceC2615) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3476) := by
    have ha : (tripleCharges (sourceA2615 + difference 5 3) (sourceB2615 + difference 3 5) sourceC2615) = raw16822 := by
      apply Matrix.ext; unfold tripleCharges sourceA2615 sourceB2615 sourceC2615 difference raw16822; decide +kernel
    rw [ha]
    exact (canonical16822 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2615 + difference 5 4) (sourceB2615 + difference 4 5) sourceC2615) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3612) := by
    have ha : (tripleCharges (sourceA2615 + difference 5 4) (sourceB2615 + difference 4 5) sourceC2615) = raw36484 := by
      apply Matrix.ext; unfold tripleCharges sourceA2615 sourceB2615 sourceC2615 difference raw36484; decide +kernel
    rw [ha]
    exact (canonical36484 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2615 sourceB2615 sourceC2615
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2615, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2616 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2616 : Charge := ![1, 2, -1, -1, 0, -1]
def sourceC2616 : Charge := ![1, 0, 1, 0, -1, -1]
def sourceForm2616 : Integer.Sparse Master := [(Sum.inr 4631, 1), (Sum.inr 4632, 1), (Sum.inr 4635, 1), (Sum.inr 4642, 1), (Sum.inr 4802, 1), (Sum.inr 4902, 1), (Sum.inr 4903, 1), (Sum.inr 4906, 1), (Sum.inr 4912, 1), (Sum.inr 5036, 1), (Sum.inr 5050, 1), (Sum.inr 5073, 1), (Sum.inr 5141, 1), (Sum.inr 5335, 1), (Sum.inr 5337, 1), (Sum.inr 5341, 1), (Sum.inr 5346, 1), (Sum.inr 5351, 1), (Sum.inr 5352, 1), (Sum.inr 5356, 1), (Sum.inr 5365, 1), (Sum.inr 5368, 1), (Sum.inr 5416, 1), (Sum.inr 5424, 1), (Sum.inr 5433, 1), (Sum.inr 5434, 1), (Sum.inr 5476, 1), (Sum.inr 5477, 1), (Sum.inr 5482, 1), (Sum.inr 5483, 1)]

theorem sourceEq2616 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2616 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2616 + difference 0 1) (sourceB2616 + difference 1 0) sourceC2616) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA2616 + difference 0 1) (sourceB2616 + difference 1 0) sourceC2616) = raw36485 := by
      apply Matrix.ext; unfold tripleCharges sourceA2616 sourceB2616 sourceC2616 difference raw36485; decide +kernel
    rw [ha]
    exact (canonical36485 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2616 + difference 0 2) (sourceB2616 + difference 2 0) sourceC2616) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5416) := by
    have ha : (tripleCharges (sourceA2616 + difference 0 2) (sourceB2616 + difference 2 0) sourceC2616) = raw36486 := by
      apply Matrix.ext; unfold tripleCharges sourceA2616 sourceB2616 sourceC2616 difference raw36486; decide +kernel
    rw [ha]
    exact (canonical36486 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2616 + difference 0 3) (sourceB2616 + difference 3 0) sourceC2616) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA2616 + difference 0 3) (sourceB2616 + difference 3 0) sourceC2616) = raw36487 := by
      apply Matrix.ext; unfold tripleCharges sourceA2616 sourceB2616 sourceC2616 difference raw36487; decide +kernel
    rw [ha]
    exact (canonical36487 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2616 + difference 0 4) (sourceB2616 + difference 4 0) sourceC2616) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA2616 + difference 0 4) (sourceB2616 + difference 4 0) sourceC2616) = raw36488 := by
      apply Matrix.ext; unfold tripleCharges sourceA2616 sourceB2616 sourceC2616 difference raw36488; decide +kernel
    rw [ha]
    exact (canonical36488 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2616 + difference 0 5) (sourceB2616 + difference 5 0) sourceC2616) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA2616 + difference 0 5) (sourceB2616 + difference 5 0) sourceC2616) = raw36489 := by
      apply Matrix.ext; unfold tripleCharges sourceA2616 sourceB2616 sourceC2616 difference raw36489; decide +kernel
    rw [ha]
    exact (canonical36489 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2616 + difference 1 0) (sourceB2616 + difference 0 1) sourceC2616) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5073) := by
    have ha : (tripleCharges (sourceA2616 + difference 1 0) (sourceB2616 + difference 0 1) sourceC2616) = raw30496 := by
      apply Matrix.ext; unfold tripleCharges sourceA2616 sourceB2616 sourceC2616 difference raw30496; decide +kernel
    rw [ha]
    exact (canonical30496 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2616 + difference 1 2) (sourceB2616 + difference 2 1) sourceC2616) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5476) := by
    have ha : (tripleCharges (sourceA2616 + difference 1 2) (sourceB2616 + difference 2 1) sourceC2616) = raw33093 := by
      apply Matrix.ext; unfold tripleCharges sourceA2616 sourceB2616 sourceC2616 difference raw33093; decide +kernel
    rw [ha]
    exact (canonical33093 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2616 + difference 1 3) (sourceB2616 + difference 3 1) sourceC2616) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA2616 + difference 1 3) (sourceB2616 + difference 3 1) sourceC2616) = raw30481 := by
      apply Matrix.ext; unfold tripleCharges sourceA2616 sourceB2616 sourceC2616 difference raw30481; decide +kernel
    rw [ha]
    exact (canonical30481 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2616 + difference 1 4) (sourceB2616 + difference 4 1) sourceC2616) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5477) := by
    have ha : (tripleCharges (sourceA2616 + difference 1 4) (sourceB2616 + difference 4 1) sourceC2616) = raw33094 := by
      apply Matrix.ext; unfold tripleCharges sourceA2616 sourceB2616 sourceC2616 difference raw33094; decide +kernel
    rw [ha]
    exact (canonical33094 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2616 + difference 1 5) (sourceB2616 + difference 5 1) sourceC2616) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA2616 + difference 1 5) (sourceB2616 + difference 5 1) sourceC2616) = raw33095 := by
      apply Matrix.ext; unfold tripleCharges sourceA2616 sourceB2616 sourceC2616 difference raw33095; decide +kernel
    rw [ha]
    exact (canonical33095 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2616 + difference 2 0) (sourceB2616 + difference 0 2) sourceC2616) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4912) := by
    have ha : (tripleCharges (sourceA2616 + difference 2 0) (sourceB2616 + difference 0 2) sourceC2616) = raw33098 := by
      apply Matrix.ext; unfold tripleCharges sourceA2616 sourceB2616 sourceC2616 difference raw33098; decide +kernel
    rw [ha]
    exact (canonical33098 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2616 + difference 2 1) (sourceB2616 + difference 1 2) sourceC2616) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4642) := by
    have ha : (tripleCharges (sourceA2616 + difference 2 1) (sourceB2616 + difference 1 2) sourceC2616) = raw36490 := by
      apply Matrix.ext; unfold tripleCharges sourceA2616 sourceB2616 sourceC2616 difference raw36490; decide +kernel
    rw [ha]
    exact (canonical36490 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2616 + difference 2 3) (sourceB2616 + difference 3 2) sourceC2616) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5368) := by
    have ha : (tripleCharges (sourceA2616 + difference 2 3) (sourceB2616 + difference 3 2) sourceC2616) = raw36491 := by
      apply Matrix.ext; unfold tripleCharges sourceA2616 sourceB2616 sourceC2616 difference raw36491; decide +kernel
    rw [ha]
    exact (canonical36491 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2616 + difference 2 4) (sourceB2616 + difference 4 2) sourceC2616) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5346) := by
    have ha : (tripleCharges (sourceA2616 + difference 2 4) (sourceB2616 + difference 4 2) sourceC2616) = raw36492 := by
      apply Matrix.ext; unfold tripleCharges sourceA2616 sourceB2616 sourceC2616 difference raw36492; decide +kernel
    rw [ha]
    exact (canonical36492 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2616 + difference 2 5) (sourceB2616 + difference 5 2) sourceC2616) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5365) := by
    have ha : (tripleCharges (sourceA2616 + difference 2 5) (sourceB2616 + difference 5 2) sourceC2616) = raw34561 := by
      apply Matrix.ext; unfold tripleCharges sourceA2616 sourceB2616 sourceC2616 difference raw34561; decide +kernel
    rw [ha]
    exact (canonical34561 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2616 + difference 3 0) (sourceB2616 + difference 0 3) sourceC2616) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4903) := by
    have ha : (tripleCharges (sourceA2616 + difference 3 0) (sourceB2616 + difference 0 3) sourceC2616) = raw33101 := by
      apply Matrix.ext; unfold tripleCharges sourceA2616 sourceB2616 sourceC2616 difference raw33101; decide +kernel
    rw [ha]
    exact (canonical33101 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2616 + difference 3 1) (sourceB2616 + difference 1 3) sourceC2616) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4632) := by
    have ha : (tripleCharges (sourceA2616 + difference 3 1) (sourceB2616 + difference 1 3) sourceC2616) = raw36493 := by
      apply Matrix.ext; unfold tripleCharges sourceA2616 sourceB2616 sourceC2616 difference raw36493; decide +kernel
    rw [ha]
    exact (canonical36493 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2616 + difference 3 2) (sourceB2616 + difference 2 3) sourceC2616) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5335) := by
    have ha : (tripleCharges (sourceA2616 + difference 3 2) (sourceB2616 + difference 2 3) sourceC2616) = raw36494 := by
      apply Matrix.ext; unfold tripleCharges sourceA2616 sourceB2616 sourceC2616 difference raw36494; decide +kernel
    rw [ha]
    exact (canonical36494 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2616 + difference 3 4) (sourceB2616 + difference 4 3) sourceC2616) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5341) := by
    have ha : (tripleCharges (sourceA2616 + difference 3 4) (sourceB2616 + difference 4 3) sourceC2616) = raw36495 := by
      apply Matrix.ext; unfold tripleCharges sourceA2616 sourceB2616 sourceC2616 difference raw36495; decide +kernel
    rw [ha]
    exact (canonical36495 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2616 + difference 3 5) (sourceB2616 + difference 5 3) sourceC2616) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5351) := by
    have ha : (tripleCharges (sourceA2616 + difference 3 5) (sourceB2616 + difference 5 3) sourceC2616) = raw36496 := by
      apply Matrix.ext; unfold tripleCharges sourceA2616 sourceB2616 sourceC2616 difference raw36496; decide +kernel
    rw [ha]
    exact (canonical36496 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2616 + difference 4 0) (sourceB2616 + difference 0 4) sourceC2616) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4906) := by
    have ha : (tripleCharges (sourceA2616 + difference 4 0) (sourceB2616 + difference 0 4) sourceC2616) = raw30494 := by
      apply Matrix.ext; unfold tripleCharges sourceA2616 sourceB2616 sourceC2616 difference raw30494; decide +kernel
    rw [ha]
    exact (canonical30494 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2616 + difference 4 1) (sourceB2616 + difference 1 4) sourceC2616) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4635) := by
    have ha : (tripleCharges (sourceA2616 + difference 4 1) (sourceB2616 + difference 1 4) sourceC2616) = raw36497 := by
      apply Matrix.ext; unfold tripleCharges sourceA2616 sourceB2616 sourceC2616 difference raw36497; decide +kernel
    rw [ha]
    exact (canonical36497 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2616 + difference 4 2) (sourceB2616 + difference 2 4) sourceC2616) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5337) := by
    have ha : (tripleCharges (sourceA2616 + difference 4 2) (sourceB2616 + difference 2 4) sourceC2616) = raw36498 := by
      apply Matrix.ext; unfold tripleCharges sourceA2616 sourceB2616 sourceC2616 difference raw36498; decide +kernel
    rw [ha]
    exact (canonical36498 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2616 + difference 4 3) (sourceB2616 + difference 3 4) sourceC2616) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5356) := by
    have ha : (tripleCharges (sourceA2616 + difference 4 3) (sourceB2616 + difference 3 4) sourceC2616) = raw30478 := by
      apply Matrix.ext; unfold tripleCharges sourceA2616 sourceB2616 sourceC2616 difference raw30478; decide +kernel
    rw [ha]
    exact (canonical30478 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2616 + difference 4 5) (sourceB2616 + difference 5 4) sourceC2616) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5352) := by
    have ha : (tripleCharges (sourceA2616 + difference 4 5) (sourceB2616 + difference 5 4) sourceC2616) = raw36499 := by
      apply Matrix.ext; unfold tripleCharges sourceA2616 sourceB2616 sourceC2616 difference raw36499; decide +kernel
    rw [ha]
    exact (canonical36499 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2616 + difference 5 0) (sourceB2616 + difference 0 5) sourceC2616) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4902) := by
    have ha : (tripleCharges (sourceA2616 + difference 5 0) (sourceB2616 + difference 0 5) sourceC2616) = raw33107 := by
      apply Matrix.ext; unfold tripleCharges sourceA2616 sourceB2616 sourceC2616 difference raw33107; decide +kernel
    rw [ha]
    exact (canonical33107 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2616 + difference 5 1) (sourceB2616 + difference 1 5) sourceC2616) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4631) := by
    have ha : (tripleCharges (sourceA2616 + difference 5 1) (sourceB2616 + difference 1 5) sourceC2616) = raw36500 := by
      apply Matrix.ext; unfold tripleCharges sourceA2616 sourceB2616 sourceC2616 difference raw36500; decide +kernel
    rw [ha]
    exact (canonical36500 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2616 + difference 5 2) (sourceB2616 + difference 2 5) sourceC2616) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5036) := by
    have ha : (tripleCharges (sourceA2616 + difference 5 2) (sourceB2616 + difference 2 5) sourceC2616) = raw36501 := by
      apply Matrix.ext; unfold tripleCharges sourceA2616 sourceB2616 sourceC2616 difference raw36501; decide +kernel
    rw [ha]
    exact (canonical36501 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2616 + difference 5 3) (sourceB2616 + difference 3 5) sourceC2616) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA2616 + difference 5 3) (sourceB2616 + difference 3 5) sourceC2616) = raw36502 := by
      apply Matrix.ext; unfold tripleCharges sourceA2616 sourceB2616 sourceC2616 difference raw36502; decide +kernel
    rw [ha]
    exact (canonical36502 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2616 + difference 5 4) (sourceB2616 + difference 4 5) sourceC2616) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5050) := by
    have ha : (tripleCharges (sourceA2616 + difference 5 4) (sourceB2616 + difference 4 5) sourceC2616) = raw36503 := by
      apply Matrix.ext; unfold tripleCharges sourceA2616 sourceB2616 sourceC2616 difference raw36503; decide +kernel
    rw [ha]
    exact (canonical36503 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2616 sourceB2616 sourceC2616
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2616, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2617 : Charge := ![1, 0, 1, 0, -1, -1]
def sourceB2617 : Charge := ![1, 2, -1, -1, 0, -1]
def sourceC2617 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceForm2617 : Integer.Sparse Master := [(Sum.inr 4996, 1), (Sum.inr 4997, 1), (Sum.inr 4999, 1), (Sum.inr 5013, 1), (Sum.inr 5226, 1), (Sum.inr 5323, 1), (Sum.inr 5324, 1), (Sum.inr 5325, 1), (Sum.inr 5326, 1), (Sum.inr 5349, 1), (Sum.inr 5350, 1), (Sum.inr 5351, 1), (Sum.inr 5352, 2), (Sum.inr 5353, 1), (Sum.inr 5354, 1), (Sum.inr 5358, 1), (Sum.inr 5359, 1), (Sum.inr 5360, 1), (Sum.inr 5367, 1), (Sum.inr 5368, 1), (Sum.inr 5369, 1), (Sum.inr 5378, 1), (Sum.inr 5379, 1), (Sum.inr 5380, 1), (Sum.inr 5388, 1), (Sum.inr 5393, 1), (Sum.inr 5459, 1), (Sum.inr 5460, 1), (Sum.inr 5465, 1)]

theorem sourceEq2617 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2617 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2617 + difference 0 1) (sourceB2617 + difference 1 0) sourceC2617) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5226) := by
    have ha : (tripleCharges (sourceA2617 + difference 0 1) (sourceB2617 + difference 1 0) sourceC2617) = raw36504 := by
      apply Matrix.ext; unfold tripleCharges sourceA2617 sourceB2617 sourceC2617 difference raw36504; decide +kernel
    rw [ha]
    exact (canonical36504 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2617 + difference 0 2) (sourceB2617 + difference 2 0) sourceC2617) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5388) := by
    have ha : (tripleCharges (sourceA2617 + difference 0 2) (sourceB2617 + difference 2 0) sourceC2617) = raw36505 := by
      apply Matrix.ext; unfold tripleCharges sourceA2617 sourceB2617 sourceC2617 difference raw36505; decide +kernel
    rw [ha]
    exact (canonical36505 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2617 + difference 0 3) (sourceB2617 + difference 3 0) sourceC2617) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5380) := by
    have ha : (tripleCharges (sourceA2617 + difference 0 3) (sourceB2617 + difference 3 0) sourceC2617) = raw36506 := by
      apply Matrix.ext; unfold tripleCharges sourceA2617 sourceB2617 sourceC2617 difference raw36506; decide +kernel
    rw [ha]
    exact (canonical36506 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2617 + difference 0 4) (sourceB2617 + difference 4 0) sourceC2617) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5379) := by
    have ha : (tripleCharges (sourceA2617 + difference 0 4) (sourceB2617 + difference 4 0) sourceC2617) = raw36507 := by
      apply Matrix.ext; unfold tripleCharges sourceA2617 sourceB2617 sourceC2617 difference raw36507; decide +kernel
    rw [ha]
    exact (canonical36507 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2617 + difference 0 5) (sourceB2617 + difference 5 0) sourceC2617) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA2617 + difference 0 5) (sourceB2617 + difference 5 0) sourceC2617) = raw36508 := by
      apply Matrix.ext; unfold tripleCharges sourceA2617 sourceB2617 sourceC2617 difference raw36508; decide +kernel
    rw [ha]
    exact (canonical36508 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2617 + difference 1 0) (sourceB2617 + difference 0 1) sourceC2617) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5352) := by
    have ha : (tripleCharges (sourceA2617 + difference 1 0) (sourceB2617 + difference 0 1) sourceC2617) = raw35835 := by
      apply Matrix.ext; unfold tripleCharges sourceA2617 sourceB2617 sourceC2617 difference raw35835; decide +kernel
    rw [ha]
    exact (canonical35835 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2617 + difference 1 2) (sourceB2617 + difference 2 1) sourceC2617) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5465) := by
    have ha : (tripleCharges (sourceA2617 + difference 1 2) (sourceB2617 + difference 2 1) sourceC2617) = raw36365 := by
      apply Matrix.ext; unfold tripleCharges sourceA2617 sourceB2617 sourceC2617 difference raw36365; decide +kernel
    rw [ha]
    exact (canonical36365 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2617 + difference 1 3) (sourceB2617 + difference 3 1) sourceC2617) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5460) := by
    have ha : (tripleCharges (sourceA2617 + difference 1 3) (sourceB2617 + difference 3 1) sourceC2617) = raw35821 := by
      apply Matrix.ext; unfold tripleCharges sourceA2617 sourceB2617 sourceC2617 difference raw35821; decide +kernel
    rw [ha]
    exact (canonical35821 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2617 + difference 1 4) (sourceB2617 + difference 4 1) sourceC2617) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5459) := by
    have ha : (tripleCharges (sourceA2617 + difference 1 4) (sourceB2617 + difference 4 1) sourceC2617) = raw36509 := by
      apply Matrix.ext; unfold tripleCharges sourceA2617 sourceB2617 sourceC2617 difference raw36509; decide +kernel
    rw [ha]
    exact (canonical36509 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2617 + difference 1 5) (sourceB2617 + difference 5 1) sourceC2617) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5393) := by
    have ha : (tripleCharges (sourceA2617 + difference 1 5) (sourceB2617 + difference 5 1) sourceC2617) = raw36510 := by
      apply Matrix.ext; unfold tripleCharges sourceA2617 sourceB2617 sourceC2617 difference raw36510; decide +kernel
    rw [ha]
    exact (canonical36510 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2617 + difference 2 0) (sourceB2617 + difference 0 2) sourceC2617) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5326) := by
    have ha : (tripleCharges (sourceA2617 + difference 2 0) (sourceB2617 + difference 0 2) sourceC2617) = raw36511 := by
      apply Matrix.ext; unfold tripleCharges sourceA2617 sourceB2617 sourceC2617 difference raw36511; decide +kernel
    rw [ha]
    exact (canonical36511 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2617 + difference 2 1) (sourceB2617 + difference 1 2) sourceC2617) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4999) := by
    have ha : (tripleCharges (sourceA2617 + difference 2 1) (sourceB2617 + difference 1 2) sourceC2617) = raw36512 := by
      apply Matrix.ext; unfold tripleCharges sourceA2617 sourceB2617 sourceC2617 difference raw36512; decide +kernel
    rw [ha]
    exact (canonical36512 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2617 + difference 2 3) (sourceB2617 + difference 3 2) sourceC2617) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5359) := by
    have ha : (tripleCharges (sourceA2617 + difference 2 3) (sourceB2617 + difference 3 2) sourceC2617) = raw36513 := by
      apply Matrix.ext; unfold tripleCharges sourceA2617 sourceB2617 sourceC2617 difference raw36513; decide +kernel
    rw [ha]
    exact (canonical36513 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2617 + difference 2 4) (sourceB2617 + difference 4 2) sourceC2617) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5358) := by
    have ha : (tripleCharges (sourceA2617 + difference 2 4) (sourceB2617 + difference 4 2) sourceC2617) = raw36514 := by
      apply Matrix.ext; unfold tripleCharges sourceA2617 sourceB2617 sourceC2617 difference raw36514; decide +kernel
    rw [ha]
    exact (canonical36514 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2617 + difference 2 5) (sourceB2617 + difference 5 2) sourceC2617) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5360) := by
    have ha : (tripleCharges (sourceA2617 + difference 2 5) (sourceB2617 + difference 5 2) sourceC2617) = raw36515 := by
      apply Matrix.ext; unfold tripleCharges sourceA2617 sourceB2617 sourceC2617 difference raw36515; decide +kernel
    rw [ha]
    exact (canonical36515 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2617 + difference 3 0) (sourceB2617 + difference 0 3) sourceC2617) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5324) := by
    have ha : (tripleCharges (sourceA2617 + difference 3 0) (sourceB2617 + difference 0 3) sourceC2617) = raw36516 := by
      apply Matrix.ext; unfold tripleCharges sourceA2617 sourceB2617 sourceC2617 difference raw36516; decide +kernel
    rw [ha]
    exact (canonical36516 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2617 + difference 3 1) (sourceB2617 + difference 1 3) sourceC2617) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4997) := by
    have ha : (tripleCharges (sourceA2617 + difference 3 1) (sourceB2617 + difference 1 3) sourceC2617) = raw36517 := by
      apply Matrix.ext; unfold tripleCharges sourceA2617 sourceB2617 sourceC2617 difference raw36517; decide +kernel
    rw [ha]
    exact (canonical36517 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2617 + difference 3 2) (sourceB2617 + difference 2 3) sourceC2617) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5368) := by
    have ha : (tripleCharges (sourceA2617 + difference 3 2) (sourceB2617 + difference 2 3) sourceC2617) = raw36518 := by
      apply Matrix.ext; unfold tripleCharges sourceA2617 sourceB2617 sourceC2617 difference raw36518; decide +kernel
    rw [ha]
    exact (canonical36518 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2617 + difference 3 4) (sourceB2617 + difference 4 3) sourceC2617) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5350) := by
    have ha : (tripleCharges (sourceA2617 + difference 3 4) (sourceB2617 + difference 4 3) sourceC2617) = raw36519 := by
      apply Matrix.ext; unfold tripleCharges sourceA2617 sourceB2617 sourceC2617 difference raw36519; decide +kernel
    rw [ha]
    exact (canonical36519 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2617 + difference 3 5) (sourceB2617 + difference 5 3) sourceC2617) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5353) := by
    have ha : (tripleCharges (sourceA2617 + difference 3 5) (sourceB2617 + difference 5 3) sourceC2617) = raw36520 := by
      apply Matrix.ext; unfold tripleCharges sourceA2617 sourceB2617 sourceC2617 difference raw36520; decide +kernel
    rw [ha]
    exact (canonical36520 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2617 + difference 4 0) (sourceB2617 + difference 0 4) sourceC2617) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5325) := by
    have ha : (tripleCharges (sourceA2617 + difference 4 0) (sourceB2617 + difference 0 4) sourceC2617) = raw36521 := by
      apply Matrix.ext; unfold tripleCharges sourceA2617 sourceB2617 sourceC2617 difference raw36521; decide +kernel
    rw [ha]
    exact (canonical36521 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2617 + difference 4 1) (sourceB2617 + difference 1 4) sourceC2617) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5013) := by
    have ha : (tripleCharges (sourceA2617 + difference 4 1) (sourceB2617 + difference 1 4) sourceC2617) = raw36522 := by
      apply Matrix.ext; unfold tripleCharges sourceA2617 sourceB2617 sourceC2617 difference raw36522; decide +kernel
    rw [ha]
    exact (canonical36522 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2617 + difference 4 2) (sourceB2617 + difference 2 4) sourceC2617) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5369) := by
    have ha : (tripleCharges (sourceA2617 + difference 4 2) (sourceB2617 + difference 2 4) sourceC2617) = raw36523 := by
      apply Matrix.ext; unfold tripleCharges sourceA2617 sourceB2617 sourceC2617 difference raw36523; decide +kernel
    rw [ha]
    exact (canonical36523 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2617 + difference 4 3) (sourceB2617 + difference 3 4) sourceC2617) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5352) := by
    have ha : (tripleCharges (sourceA2617 + difference 4 3) (sourceB2617 + difference 3 4) sourceC2617) = raw36524 := by
      apply Matrix.ext; unfold tripleCharges sourceA2617 sourceB2617 sourceC2617 difference raw36524; decide +kernel
    rw [ha]
    exact (canonical36524 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2617 + difference 4 5) (sourceB2617 + difference 5 4) sourceC2617) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5354) := by
    have ha : (tripleCharges (sourceA2617 + difference 4 5) (sourceB2617 + difference 5 4) sourceC2617) = raw36525 := by
      apply Matrix.ext; unfold tripleCharges sourceA2617 sourceB2617 sourceC2617 difference raw36525; decide +kernel
    rw [ha]
    exact (canonical36525 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2617 + difference 5 0) (sourceB2617 + difference 0 5) sourceC2617) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5323) := by
    have ha : (tripleCharges (sourceA2617 + difference 5 0) (sourceB2617 + difference 0 5) sourceC2617) = raw36526 := by
      apply Matrix.ext; unfold tripleCharges sourceA2617 sourceB2617 sourceC2617 difference raw36526; decide +kernel
    rw [ha]
    exact (canonical36526 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2617 + difference 5 1) (sourceB2617 + difference 1 5) sourceC2617) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4996) := by
    have ha : (tripleCharges (sourceA2617 + difference 5 1) (sourceB2617 + difference 1 5) sourceC2617) = raw36527 := by
      apply Matrix.ext; unfold tripleCharges sourceA2617 sourceB2617 sourceC2617 difference raw36527; decide +kernel
    rw [ha]
    exact (canonical36527 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2617 + difference 5 2) (sourceB2617 + difference 2 5) sourceC2617) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5367) := by
    have ha : (tripleCharges (sourceA2617 + difference 5 2) (sourceB2617 + difference 2 5) sourceC2617) = raw36363 := by
      apply Matrix.ext; unfold tripleCharges sourceA2617 sourceB2617 sourceC2617 difference raw36363; decide +kernel
    rw [ha]
    exact (canonical36363 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2617 + difference 5 3) (sourceB2617 + difference 3 5) sourceC2617) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5351) := by
    have ha : (tripleCharges (sourceA2617 + difference 5 3) (sourceB2617 + difference 3 5) sourceC2617) = raw36528 := by
      apply Matrix.ext; unfold tripleCharges sourceA2617 sourceB2617 sourceC2617 difference raw36528; decide +kernel
    rw [ha]
    exact (canonical36528 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2617 + difference 5 4) (sourceB2617 + difference 4 5) sourceC2617) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5349) := by
    have ha : (tripleCharges (sourceA2617 + difference 5 4) (sourceB2617 + difference 4 5) sourceC2617) = raw36529 := by
      apply Matrix.ext; unfold tripleCharges sourceA2617 sourceB2617 sourceC2617 difference raw36529; decide +kernel
    rw [ha]
    exact (canonical36529 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2617 sourceB2617 sourceC2617
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2617, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2618 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2618 : Charge := ![1, 0, 1, -1, -1, 0]
def sourceC2618 : Charge := ![1, 2, -1, 0, 0, -2]
def sourceForm2618 : Integer.Sparse Master := [(Sum.inr 4929, 1), (Sum.inr 4931, 2), (Sum.inr 4939, 1), (Sum.inr 4956, 1), (Sum.inr 4957, 2), (Sum.inr 4971, 1), (Sum.inr 5072, 1), (Sum.inr 5112, 1), (Sum.inr 5141, 2), (Sum.inr 5187, 1), (Sum.inr 5339, 2), (Sum.inr 5353, 2), (Sum.inr 5355, 2), (Sum.inr 5365, 1), (Sum.inr 5367, 2), (Sum.inr 5400, 1), (Sum.inr 5405, 1), (Sum.inr 5409, 2), (Sum.inr 5414, 1), (Sum.inr 5428, 2), (Sum.inr 5471, 1)]

theorem sourceEq2618 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2618 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2618 + difference 0 1) (sourceB2618 + difference 1 0) sourceC2618) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5072) := by
    have ha : (tripleCharges (sourceA2618 + difference 0 1) (sourceB2618 + difference 1 0) sourceC2618) = raw36530 := by
      apply Matrix.ext; unfold tripleCharges sourceA2618 sourceB2618 sourceC2618 difference raw36530; decide +kernel
    rw [ha]
    exact (canonical36530 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2618 + difference 0 2) (sourceB2618 + difference 2 0) sourceC2618) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5400) := by
    have ha : (tripleCharges (sourceA2618 + difference 0 2) (sourceB2618 + difference 2 0) sourceC2618) = raw36531 := by
      apply Matrix.ext; unfold tripleCharges sourceA2618 sourceB2618 sourceC2618 difference raw36531; decide +kernel
    rw [ha]
    exact (canonical36531 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2618 + difference 0 3) (sourceB2618 + difference 3 0) sourceC2618) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5409) := by
    have ha : (tripleCharges (sourceA2618 + difference 0 3) (sourceB2618 + difference 3 0) sourceC2618) = raw17888 := by
      apply Matrix.ext; unfold tripleCharges sourceA2618 sourceB2618 sourceC2618 difference raw17888; decide +kernel
    rw [ha]
    exact (canonical17888 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2618 + difference 0 4) (sourceB2618 + difference 4 0) sourceC2618) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5409) := by
    have ha : (tripleCharges (sourceA2618 + difference 0 4) (sourceB2618 + difference 4 0) sourceC2618) = raw36532 := by
      apply Matrix.ext; unfold tripleCharges sourceA2618 sourceB2618 sourceC2618 difference raw36532; decide +kernel
    rw [ha]
    exact (canonical36532 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2618 + difference 0 5) (sourceB2618 + difference 5 0) sourceC2618) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5405) := by
    have ha : (tripleCharges (sourceA2618 + difference 0 5) (sourceB2618 + difference 5 0) sourceC2618) = raw36533 := by
      apply Matrix.ext; unfold tripleCharges sourceA2618 sourceB2618 sourceC2618 difference raw36533; decide +kernel
    rw [ha]
    exact (canonical36533 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2618 + difference 1 0) (sourceB2618 + difference 0 1) sourceC2618) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5187) := by
    have ha : (tripleCharges (sourceA2618 + difference 1 0) (sourceB2618 + difference 0 1) sourceC2618) = raw17903 := by
      apply Matrix.ext; unfold tripleCharges sourceA2618 sourceB2618 sourceC2618 difference raw17903; decide +kernel
    rw [ha]
    exact (canonical17903 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2618 + difference 1 2) (sourceB2618 + difference 2 1) sourceC2618) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5414) := by
    have ha : (tripleCharges (sourceA2618 + difference 1 2) (sourceB2618 + difference 2 1) sourceC2618) = raw17905 := by
      apply Matrix.ext; unfold tripleCharges sourceA2618 sourceB2618 sourceC2618 difference raw17905; decide +kernel
    rw [ha]
    exact (canonical17905 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2618 + difference 1 3) (sourceB2618 + difference 3 1) sourceC2618) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5428) := by
    have ha : (tripleCharges (sourceA2618 + difference 1 3) (sourceB2618 + difference 3 1) sourceC2618) = raw36534 := by
      apply Matrix.ext; unfold tripleCharges sourceA2618 sourceB2618 sourceC2618 difference raw36534; decide +kernel
    rw [ha]
    exact (canonical36534 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2618 + difference 1 4) (sourceB2618 + difference 4 1) sourceC2618) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5428) := by
    have ha : (tripleCharges (sourceA2618 + difference 1 4) (sourceB2618 + difference 4 1) sourceC2618) = raw17906 := by
      apply Matrix.ext; unfold tripleCharges sourceA2618 sourceB2618 sourceC2618 difference raw17906; decide +kernel
    rw [ha]
    exact (canonical17906 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2618 + difference 1 5) (sourceB2618 + difference 5 1) sourceC2618) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5471) := by
    have ha : (tripleCharges (sourceA2618 + difference 1 5) (sourceB2618 + difference 5 1) sourceC2618) = raw17907 := by
      apply Matrix.ext; unfold tripleCharges sourceA2618 sourceB2618 sourceC2618 difference raw17907; decide +kernel
    rw [ha]
    exact (canonical17907 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2618 + difference 2 0) (sourceB2618 + difference 0 2) sourceC2618) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4971) := by
    have ha : (tripleCharges (sourceA2618 + difference 2 0) (sourceB2618 + difference 0 2) sourceC2618) = raw36535 := by
      apply Matrix.ext; unfold tripleCharges sourceA2618 sourceB2618 sourceC2618 difference raw36535; decide +kernel
    rw [ha]
    exact (canonical36535 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2618 + difference 2 1) (sourceB2618 + difference 1 2) sourceC2618) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4939) := by
    have ha : (tripleCharges (sourceA2618 + difference 2 1) (sourceB2618 + difference 1 2) sourceC2618) = raw36536 := by
      apply Matrix.ext; unfold tripleCharges sourceA2618 sourceB2618 sourceC2618 difference raw36536; decide +kernel
    rw [ha]
    exact (canonical36536 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2618 + difference 2 3) (sourceB2618 + difference 3 2) sourceC2618) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5367) := by
    have ha : (tripleCharges (sourceA2618 + difference 2 3) (sourceB2618 + difference 3 2) sourceC2618) = raw17899 := by
      apply Matrix.ext; unfold tripleCharges sourceA2618 sourceB2618 sourceC2618 difference raw17899; decide +kernel
    rw [ha]
    exact (canonical17899 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2618 + difference 2 4) (sourceB2618 + difference 4 2) sourceC2618) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5367) := by
    have ha : (tripleCharges (sourceA2618 + difference 2 4) (sourceB2618 + difference 4 2) sourceC2618) = raw36537 := by
      apply Matrix.ext; unfold tripleCharges sourceA2618 sourceB2618 sourceC2618 difference raw36537; decide +kernel
    rw [ha]
    exact (canonical36537 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2618 + difference 2 5) (sourceB2618 + difference 5 2) sourceC2618) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5365) := by
    have ha : (tripleCharges (sourceA2618 + difference 2 5) (sourceB2618 + difference 5 2) sourceC2618) = raw36538 := by
      apply Matrix.ext; unfold tripleCharges sourceA2618 sourceB2618 sourceC2618 difference raw36538; decide +kernel
    rw [ha]
    exact (canonical36538 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2618 + difference 3 0) (sourceB2618 + difference 0 3) sourceC2618) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4957) := by
    have ha : (tripleCharges (sourceA2618 + difference 3 0) (sourceB2618 + difference 0 3) sourceC2618) = raw36539 := by
      apply Matrix.ext; unfold tripleCharges sourceA2618 sourceB2618 sourceC2618 difference raw36539; decide +kernel
    rw [ha]
    exact (canonical36539 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2618 + difference 3 1) (sourceB2618 + difference 1 3) sourceC2618) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4931) := by
    have ha : (tripleCharges (sourceA2618 + difference 3 1) (sourceB2618 + difference 1 3) sourceC2618) = raw36540 := by
      apply Matrix.ext; unfold tripleCharges sourceA2618 sourceB2618 sourceC2618 difference raw36540; decide +kernel
    rw [ha]
    exact (canonical36540 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2618 + difference 3 2) (sourceB2618 + difference 2 3) sourceC2618) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5339) := by
    have ha : (tripleCharges (sourceA2618 + difference 3 2) (sourceB2618 + difference 2 3) sourceC2618) = raw36541 := by
      apply Matrix.ext; unfold tripleCharges sourceA2618 sourceB2618 sourceC2618 difference raw36541; decide +kernel
    rw [ha]
    exact (canonical36541 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2618 + difference 3 4) (sourceB2618 + difference 4 3) sourceC2618) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5355) := by
    have ha : (tripleCharges (sourceA2618 + difference 3 4) (sourceB2618 + difference 4 3) sourceC2618) = raw36542 := by
      apply Matrix.ext; unfold tripleCharges sourceA2618 sourceB2618 sourceC2618 difference raw36542; decide +kernel
    rw [ha]
    exact (canonical36542 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2618 + difference 3 5) (sourceB2618 + difference 5 3) sourceC2618) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5353) := by
    have ha : (tripleCharges (sourceA2618 + difference 3 5) (sourceB2618 + difference 5 3) sourceC2618) = raw36543 := by
      apply Matrix.ext; unfold tripleCharges sourceA2618 sourceB2618 sourceC2618 difference raw36543; decide +kernel
    rw [ha]
    exact (canonical36543 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2618 + difference 4 0) (sourceB2618 + difference 0 4) sourceC2618) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4957) := by
    have ha : (tripleCharges (sourceA2618 + difference 4 0) (sourceB2618 + difference 0 4) sourceC2618) = raw36544 := by
      apply Matrix.ext; unfold tripleCharges sourceA2618 sourceB2618 sourceC2618 difference raw36544; decide +kernel
    rw [ha]
    exact (canonical36544 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2618 + difference 4 1) (sourceB2618 + difference 1 4) sourceC2618) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4931) := by
    have ha : (tripleCharges (sourceA2618 + difference 4 1) (sourceB2618 + difference 1 4) sourceC2618) = raw36545 := by
      apply Matrix.ext; unfold tripleCharges sourceA2618 sourceB2618 sourceC2618 difference raw36545; decide +kernel
    rw [ha]
    exact (canonical36545 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2618 + difference 4 2) (sourceB2618 + difference 2 4) sourceC2618) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5339) := by
    have ha : (tripleCharges (sourceA2618 + difference 4 2) (sourceB2618 + difference 2 4) sourceC2618) = raw36546 := by
      apply Matrix.ext; unfold tripleCharges sourceA2618 sourceB2618 sourceC2618 difference raw36546; decide +kernel
    rw [ha]
    exact (canonical36546 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2618 + difference 4 3) (sourceB2618 + difference 3 4) sourceC2618) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5355) := by
    have ha : (tripleCharges (sourceA2618 + difference 4 3) (sourceB2618 + difference 3 4) sourceC2618) = raw17909 := by
      apply Matrix.ext; unfold tripleCharges sourceA2618 sourceB2618 sourceC2618 difference raw17909; decide +kernel
    rw [ha]
    exact (canonical17909 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2618 + difference 4 5) (sourceB2618 + difference 5 4) sourceC2618) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5353) := by
    have ha : (tripleCharges (sourceA2618 + difference 4 5) (sourceB2618 + difference 5 4) sourceC2618) = raw36547 := by
      apply Matrix.ext; unfold tripleCharges sourceA2618 sourceB2618 sourceC2618 difference raw36547; decide +kernel
    rw [ha]
    exact (canonical36547 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2618 + difference 5 0) (sourceB2618 + difference 0 5) sourceC2618) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4956) := by
    have ha : (tripleCharges (sourceA2618 + difference 5 0) (sourceB2618 + difference 0 5) sourceC2618) = raw36548 := by
      apply Matrix.ext; unfold tripleCharges sourceA2618 sourceB2618 sourceC2618 difference raw36548; decide +kernel
    rw [ha]
    exact (canonical36548 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2618 + difference 5 1) (sourceB2618 + difference 1 5) sourceC2618) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4929) := by
    have ha : (tripleCharges (sourceA2618 + difference 5 1) (sourceB2618 + difference 1 5) sourceC2618) = raw36549 := by
      apply Matrix.ext; unfold tripleCharges sourceA2618 sourceB2618 sourceC2618 difference raw36549; decide +kernel
    rw [ha]
    exact (canonical36549 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2618 + difference 5 2) (sourceB2618 + difference 2 5) sourceC2618) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5112) := by
    have ha : (tripleCharges (sourceA2618 + difference 5 2) (sourceB2618 + difference 2 5) sourceC2618) = raw36550 := by
      apply Matrix.ext; unfold tripleCharges sourceA2618 sourceB2618 sourceC2618 difference raw36550; decide +kernel
    rw [ha]
    exact (canonical36550 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2618 + difference 5 3) (sourceB2618 + difference 3 5) sourceC2618) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA2618 + difference 5 3) (sourceB2618 + difference 3 5) sourceC2618) = raw17914 := by
      apply Matrix.ext; unfold tripleCharges sourceA2618 sourceB2618 sourceC2618 difference raw17914; decide +kernel
    rw [ha]
    exact (canonical17914 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2618 + difference 5 4) (sourceB2618 + difference 4 5) sourceC2618) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA2618 + difference 5 4) (sourceB2618 + difference 4 5) sourceC2618) = raw36551 := by
      apply Matrix.ext; unfold tripleCharges sourceA2618 sourceB2618 sourceC2618 difference raw36551; decide +kernel
    rw [ha]
    exact (canonical36551 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2618 sourceB2618 sourceC2618
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2618, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2619 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2619 : Charge := ![1, 0, 1, -1, -1, 0]
def sourceC2619 : Charge := ![1, 2, -1, 0, 0, -2]
def sourceForm2619 : Integer.Sparse Master := [(Sum.inr 3403, 1), (Sum.inr 3404, 1), (Sum.inr 3406, 2), (Sum.inr 3459, 1), (Sum.inr 3509, 2), (Sum.inr 3510, 1), (Sum.inr 3522, 2), (Sum.inr 3537, 1), (Sum.inr 3556, 1), (Sum.inr 3590, 1), (Sum.inr 3758, 1), (Sum.inr 3760, 2), (Sum.inr 3761, 2), (Sum.inr 3766, 2), (Sum.inr 3770, 2), (Sum.inr 3799, 1), (Sum.inr 3800, 1), (Sum.inr 3807, 2), (Sum.inr 3845, 2), (Sum.inr 3869, 1), (Sum.inr 3953, 1)]

theorem sourceEq2619 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2619 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2619 + difference 0 1) (sourceB2619 + difference 1 0) sourceC2619) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3459) := by
    have ha : (tripleCharges (sourceA2619 + difference 0 1) (sourceB2619 + difference 1 0) sourceC2619) = raw36552 := by
      apply Matrix.ext; unfold tripleCharges sourceA2619 sourceB2619 sourceC2619 difference raw36552; decide +kernel
    rw [ha]
    exact (canonical36552 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2619 + difference 0 2) (sourceB2619 + difference 2 0) sourceC2619) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3799) := by
    have ha : (tripleCharges (sourceA2619 + difference 0 2) (sourceB2619 + difference 2 0) sourceC2619) = raw36553 := by
      apply Matrix.ext; unfold tripleCharges sourceA2619 sourceB2619 sourceC2619 difference raw36553; decide +kernel
    rw [ha]
    exact (canonical36553 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2619 + difference 0 3) (sourceB2619 + difference 3 0) sourceC2619) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3807) := by
    have ha : (tripleCharges (sourceA2619 + difference 0 3) (sourceB2619 + difference 3 0) sourceC2619) = raw17918 := by
      apply Matrix.ext; unfold tripleCharges sourceA2619 sourceB2619 sourceC2619 difference raw17918; decide +kernel
    rw [ha]
    exact (canonical17918 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2619 + difference 0 4) (sourceB2619 + difference 4 0) sourceC2619) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3807) := by
    have ha : (tripleCharges (sourceA2619 + difference 0 4) (sourceB2619 + difference 4 0) sourceC2619) = raw36554 := by
      apply Matrix.ext; unfold tripleCharges sourceA2619 sourceB2619 sourceC2619 difference raw36554; decide +kernel
    rw [ha]
    exact (canonical36554 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2619 + difference 0 5) (sourceB2619 + difference 5 0) sourceC2619) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3800) := by
    have ha : (tripleCharges (sourceA2619 + difference 0 5) (sourceB2619 + difference 5 0) sourceC2619) = raw36555 := by
      apply Matrix.ext; unfold tripleCharges sourceA2619 sourceB2619 sourceC2619 difference raw36555; decide +kernel
    rw [ha]
    exact (canonical36555 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2619 + difference 1 0) (sourceB2619 + difference 0 1) sourceC2619) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3537) := by
    have ha : (tripleCharges (sourceA2619 + difference 1 0) (sourceB2619 + difference 0 1) sourceC2619) = raw17933 := by
      apply Matrix.ext; unfold tripleCharges sourceA2619 sourceB2619 sourceC2619 difference raw17933; decide +kernel
    rw [ha]
    exact (canonical17933 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2619 + difference 1 2) (sourceB2619 + difference 2 1) sourceC2619) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3869) := by
    have ha : (tripleCharges (sourceA2619 + difference 1 2) (sourceB2619 + difference 2 1) sourceC2619) = raw17935 := by
      apply Matrix.ext; unfold tripleCharges sourceA2619 sourceB2619 sourceC2619 difference raw17935; decide +kernel
    rw [ha]
    exact (canonical17935 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2619 + difference 1 3) (sourceB2619 + difference 3 1) sourceC2619) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3845) := by
    have ha : (tripleCharges (sourceA2619 + difference 1 3) (sourceB2619 + difference 3 1) sourceC2619) = raw36556 := by
      apply Matrix.ext; unfold tripleCharges sourceA2619 sourceB2619 sourceC2619 difference raw36556; decide +kernel
    rw [ha]
    exact (canonical36556 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2619 + difference 1 4) (sourceB2619 + difference 4 1) sourceC2619) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3845) := by
    have ha : (tripleCharges (sourceA2619 + difference 1 4) (sourceB2619 + difference 4 1) sourceC2619) = raw17936 := by
      apply Matrix.ext; unfold tripleCharges sourceA2619 sourceB2619 sourceC2619 difference raw17936; decide +kernel
    rw [ha]
    exact (canonical17936 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2619 + difference 1 5) (sourceB2619 + difference 5 1) sourceC2619) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3953) := by
    have ha : (tripleCharges (sourceA2619 + difference 1 5) (sourceB2619 + difference 5 1) sourceC2619) = raw17937 := by
      apply Matrix.ext; unfold tripleCharges sourceA2619 sourceB2619 sourceC2619 difference raw17937; decide +kernel
    rw [ha]
    exact (canonical17937 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2619 + difference 2 0) (sourceB2619 + difference 0 2) sourceC2619) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3590) := by
    have ha : (tripleCharges (sourceA2619 + difference 2 0) (sourceB2619 + difference 0 2) sourceC2619) = raw36557 := by
      apply Matrix.ext; unfold tripleCharges sourceA2619 sourceB2619 sourceC2619 difference raw36557; decide +kernel
    rw [ha]
    exact (canonical36557 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2619 + difference 2 1) (sourceB2619 + difference 1 2) sourceC2619) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3404) := by
    have ha : (tripleCharges (sourceA2619 + difference 2 1) (sourceB2619 + difference 1 2) sourceC2619) = raw36558 := by
      apply Matrix.ext; unfold tripleCharges sourceA2619 sourceB2619 sourceC2619 difference raw36558; decide +kernel
    rw [ha]
    exact (canonical36558 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2619 + difference 2 3) (sourceB2619 + difference 3 2) sourceC2619) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3766) := by
    have ha : (tripleCharges (sourceA2619 + difference 2 3) (sourceB2619 + difference 3 2) sourceC2619) = raw17929 := by
      apply Matrix.ext; unfold tripleCharges sourceA2619 sourceB2619 sourceC2619 difference raw17929; decide +kernel
    rw [ha]
    exact (canonical17929 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2619 + difference 2 4) (sourceB2619 + difference 4 2) sourceC2619) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3766) := by
    have ha : (tripleCharges (sourceA2619 + difference 2 4) (sourceB2619 + difference 4 2) sourceC2619) = raw36559 := by
      apply Matrix.ext; unfold tripleCharges sourceA2619 sourceB2619 sourceC2619 difference raw36559; decide +kernel
    rw [ha]
    exact (canonical36559 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2619 + difference 2 5) (sourceB2619 + difference 5 2) sourceC2619) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3758) := by
    have ha : (tripleCharges (sourceA2619 + difference 2 5) (sourceB2619 + difference 5 2) sourceC2619) = raw36560 := by
      apply Matrix.ext; unfold tripleCharges sourceA2619 sourceB2619 sourceC2619 difference raw36560; decide +kernel
    rw [ha]
    exact (canonical36560 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2619 + difference 3 0) (sourceB2619 + difference 0 3) sourceC2619) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3509) := by
    have ha : (tripleCharges (sourceA2619 + difference 3 0) (sourceB2619 + difference 0 3) sourceC2619) = raw36561 := by
      apply Matrix.ext; unfold tripleCharges sourceA2619 sourceB2619 sourceC2619 difference raw36561; decide +kernel
    rw [ha]
    exact (canonical36561 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2619 + difference 3 1) (sourceB2619 + difference 1 3) sourceC2619) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3406) := by
    have ha : (tripleCharges (sourceA2619 + difference 3 1) (sourceB2619 + difference 1 3) sourceC2619) = raw36562 := by
      apply Matrix.ext; unfold tripleCharges sourceA2619 sourceB2619 sourceC2619 difference raw36562; decide +kernel
    rw [ha]
    exact (canonical36562 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2619 + difference 3 2) (sourceB2619 + difference 2 3) sourceC2619) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3760) := by
    have ha : (tripleCharges (sourceA2619 + difference 3 2) (sourceB2619 + difference 2 3) sourceC2619) = raw36563 := by
      apply Matrix.ext; unfold tripleCharges sourceA2619 sourceB2619 sourceC2619 difference raw36563; decide +kernel
    rw [ha]
    exact (canonical36563 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2619 + difference 3 4) (sourceB2619 + difference 4 3) sourceC2619) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3770) := by
    have ha : (tripleCharges (sourceA2619 + difference 3 4) (sourceB2619 + difference 4 3) sourceC2619) = raw36564 := by
      apply Matrix.ext; unfold tripleCharges sourceA2619 sourceB2619 sourceC2619 difference raw36564; decide +kernel
    rw [ha]
    exact (canonical36564 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2619 + difference 3 5) (sourceB2619 + difference 5 3) sourceC2619) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3761) := by
    have ha : (tripleCharges (sourceA2619 + difference 3 5) (sourceB2619 + difference 5 3) sourceC2619) = raw36565 := by
      apply Matrix.ext; unfold tripleCharges sourceA2619 sourceB2619 sourceC2619 difference raw36565; decide +kernel
    rw [ha]
    exact (canonical36565 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2619 + difference 4 0) (sourceB2619 + difference 0 4) sourceC2619) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3509) := by
    have ha : (tripleCharges (sourceA2619 + difference 4 0) (sourceB2619 + difference 0 4) sourceC2619) = raw36566 := by
      apply Matrix.ext; unfold tripleCharges sourceA2619 sourceB2619 sourceC2619 difference raw36566; decide +kernel
    rw [ha]
    exact (canonical36566 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2619 + difference 4 1) (sourceB2619 + difference 1 4) sourceC2619) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3406) := by
    have ha : (tripleCharges (sourceA2619 + difference 4 1) (sourceB2619 + difference 1 4) sourceC2619) = raw36567 := by
      apply Matrix.ext; unfold tripleCharges sourceA2619 sourceB2619 sourceC2619 difference raw36567; decide +kernel
    rw [ha]
    exact (canonical36567 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2619 + difference 4 2) (sourceB2619 + difference 2 4) sourceC2619) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3760) := by
    have ha : (tripleCharges (sourceA2619 + difference 4 2) (sourceB2619 + difference 2 4) sourceC2619) = raw36568 := by
      apply Matrix.ext; unfold tripleCharges sourceA2619 sourceB2619 sourceC2619 difference raw36568; decide +kernel
    rw [ha]
    exact (canonical36568 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2619 + difference 4 3) (sourceB2619 + difference 3 4) sourceC2619) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3770) := by
    have ha : (tripleCharges (sourceA2619 + difference 4 3) (sourceB2619 + difference 3 4) sourceC2619) = raw17939 := by
      apply Matrix.ext; unfold tripleCharges sourceA2619 sourceB2619 sourceC2619 difference raw17939; decide +kernel
    rw [ha]
    exact (canonical17939 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2619 + difference 4 5) (sourceB2619 + difference 5 4) sourceC2619) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3761) := by
    have ha : (tripleCharges (sourceA2619 + difference 4 5) (sourceB2619 + difference 5 4) sourceC2619) = raw36569 := by
      apply Matrix.ext; unfold tripleCharges sourceA2619 sourceB2619 sourceC2619 difference raw36569; decide +kernel
    rw [ha]
    exact (canonical36569 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2619 + difference 5 0) (sourceB2619 + difference 0 5) sourceC2619) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3510) := by
    have ha : (tripleCharges (sourceA2619 + difference 5 0) (sourceB2619 + difference 0 5) sourceC2619) = raw36570 := by
      apply Matrix.ext; unfold tripleCharges sourceA2619 sourceB2619 sourceC2619 difference raw36570; decide +kernel
    rw [ha]
    exact (canonical36570 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2619 + difference 5 1) (sourceB2619 + difference 1 5) sourceC2619) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3403) := by
    have ha : (tripleCharges (sourceA2619 + difference 5 1) (sourceB2619 + difference 1 5) sourceC2619) = raw36571 := by
      apply Matrix.ext; unfold tripleCharges sourceA2619 sourceB2619 sourceC2619 difference raw36571; decide +kernel
    rw [ha]
    exact (canonical36571 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2619 + difference 5 2) (sourceB2619 + difference 2 5) sourceC2619) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3556) := by
    have ha : (tripleCharges (sourceA2619 + difference 5 2) (sourceB2619 + difference 2 5) sourceC2619) = raw36572 := by
      apply Matrix.ext; unfold tripleCharges sourceA2619 sourceB2619 sourceC2619 difference raw36572; decide +kernel
    rw [ha]
    exact (canonical36572 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2619 + difference 5 3) (sourceB2619 + difference 3 5) sourceC2619) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3522) := by
    have ha : (tripleCharges (sourceA2619 + difference 5 3) (sourceB2619 + difference 3 5) sourceC2619) = raw17944 := by
      apply Matrix.ext; unfold tripleCharges sourceA2619 sourceB2619 sourceC2619 difference raw17944; decide +kernel
    rw [ha]
    exact (canonical17944 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2619 + difference 5 4) (sourceB2619 + difference 4 5) sourceC2619) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3522) := by
    have ha : (tripleCharges (sourceA2619 + difference 5 4) (sourceB2619 + difference 4 5) sourceC2619) = raw36573 := by
      apply Matrix.ext; unfold tripleCharges sourceA2619 sourceB2619 sourceC2619 difference raw36573; decide +kernel
    rw [ha]
    exact (canonical36573 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2619 sourceB2619 sourceC2619
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2619, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2620 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2620 : Charge := ![1, 2, -1, 0, 0, -2]
def sourceC2620 : Charge := ![1, 0, 1, -1, -1, 0]
def sourceForm2620 : Integer.Sparse Master := [(Sum.inr 4630, 1), (Sum.inr 4632, 2), (Sum.inr 4640, 1), (Sum.inr 4755, 1), (Sum.inr 4763, 1), (Sum.inr 4782, 2), (Sum.inr 4801, 1), (Sum.inr 4903, 2), (Sum.inr 4910, 1), (Sum.inr 5072, 1), (Sum.inr 5335, 2), (Sum.inr 5341, 2), (Sum.inr 5344, 2), (Sum.inr 5352, 2), (Sum.inr 5365, 1), (Sum.inr 5415, 1), (Sum.inr 5416, 1), (Sum.inr 5423, 2), (Sum.inr 5424, 2), (Sum.inr 5433, 1), (Sum.inr 5482, 1)]

theorem sourceEq2620 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2620 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2620 + difference 0 1) (sourceB2620 + difference 1 0) sourceC2620) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4801) := by
    have ha : (tripleCharges (sourceA2620 + difference 0 1) (sourceB2620 + difference 1 0) sourceC2620) = raw36574 := by
      apply Matrix.ext; unfold tripleCharges sourceA2620 sourceB2620 sourceC2620 difference raw36574; decide +kernel
    rw [ha]
    exact (canonical36574 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2620 + difference 0 2) (sourceB2620 + difference 2 0) sourceC2620) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5415) := by
    have ha : (tripleCharges (sourceA2620 + difference 0 2) (sourceB2620 + difference 2 0) sourceC2620) = raw36575 := by
      apply Matrix.ext; unfold tripleCharges sourceA2620 sourceB2620 sourceC2620 difference raw36575; decide +kernel
    rw [ha]
    exact (canonical36575 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2620 + difference 0 3) (sourceB2620 + difference 3 0) sourceC2620) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5423) := by
    have ha : (tripleCharges (sourceA2620 + difference 0 3) (sourceB2620 + difference 3 0) sourceC2620) = raw17581 := by
      apply Matrix.ext; unfold tripleCharges sourceA2620 sourceB2620 sourceC2620 difference raw17581; decide +kernel
    rw [ha]
    exact (canonical17581 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2620 + difference 0 4) (sourceB2620 + difference 4 0) sourceC2620) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5423) := by
    have ha : (tripleCharges (sourceA2620 + difference 0 4) (sourceB2620 + difference 4 0) sourceC2620) = raw36576 := by
      apply Matrix.ext; unfold tripleCharges sourceA2620 sourceB2620 sourceC2620 difference raw36576; decide +kernel
    rw [ha]
    exact (canonical36576 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2620 + difference 0 5) (sourceB2620 + difference 5 0) sourceC2620) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA2620 + difference 0 5) (sourceB2620 + difference 5 0) sourceC2620) = raw18787 := by
      apply Matrix.ext; unfold tripleCharges sourceA2620 sourceB2620 sourceC2620 difference raw18787; decide +kernel
    rw [ha]
    exact (canonical18787 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2620 + difference 1 0) (sourceB2620 + difference 0 1) sourceC2620) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5072) := by
    have ha : (tripleCharges (sourceA2620 + difference 1 0) (sourceB2620 + difference 0 1) sourceC2620) = raw12617 := by
      apply Matrix.ext; unfold tripleCharges sourceA2620 sourceB2620 sourceC2620 difference raw12617; decide +kernel
    rw [ha]
    exact (canonical12617 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2620 + difference 1 2) (sourceB2620 + difference 2 1) sourceC2620) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5416) := by
    have ha : (tripleCharges (sourceA2620 + difference 1 2) (sourceB2620 + difference 2 1) sourceC2620) = raw17595 := by
      apply Matrix.ext; unfold tripleCharges sourceA2620 sourceB2620 sourceC2620 difference raw17595; decide +kernel
    rw [ha]
    exact (canonical17595 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2620 + difference 1 3) (sourceB2620 + difference 3 1) sourceC2620) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA2620 + difference 1 3) (sourceB2620 + difference 3 1) sourceC2620) = raw18802 := by
      apply Matrix.ext; unfold tripleCharges sourceA2620 sourceB2620 sourceC2620 difference raw18802; decide +kernel
    rw [ha]
    exact (canonical18802 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2620 + difference 1 4) (sourceB2620 + difference 4 1) sourceC2620) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA2620 + difference 1 4) (sourceB2620 + difference 4 1) sourceC2620) = raw17596 := by
      apply Matrix.ext; unfold tripleCharges sourceA2620 sourceB2620 sourceC2620 difference raw17596; decide +kernel
    rw [ha]
    exact (canonical17596 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2620 + difference 1 5) (sourceB2620 + difference 5 1) sourceC2620) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA2620 + difference 1 5) (sourceB2620 + difference 5 1) sourceC2620) = raw12591 := by
      apply Matrix.ext; unfold tripleCharges sourceA2620 sourceB2620 sourceC2620 difference raw12591; decide +kernel
    rw [ha]
    exact (canonical12591 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2620 + difference 2 0) (sourceB2620 + difference 0 2) sourceC2620) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4910) := by
    have ha : (tripleCharges (sourceA2620 + difference 2 0) (sourceB2620 + difference 0 2) sourceC2620) = raw33200 := by
      apply Matrix.ext; unfold tripleCharges sourceA2620 sourceB2620 sourceC2620 difference raw33200; decide +kernel
    rw [ha]
    exact (canonical33200 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2620 + difference 2 1) (sourceB2620 + difference 1 2) sourceC2620) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4640) := by
    have ha : (tripleCharges (sourceA2620 + difference 2 1) (sourceB2620 + difference 1 2) sourceC2620) = raw36577 := by
      apply Matrix.ext; unfold tripleCharges sourceA2620 sourceB2620 sourceC2620 difference raw36577; decide +kernel
    rw [ha]
    exact (canonical36577 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2620 + difference 2 3) (sourceB2620 + difference 3 2) sourceC2620) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5344) := by
    have ha : (tripleCharges (sourceA2620 + difference 2 3) (sourceB2620 + difference 3 2) sourceC2620) = raw17590 := by
      apply Matrix.ext; unfold tripleCharges sourceA2620 sourceB2620 sourceC2620 difference raw17590; decide +kernel
    rw [ha]
    exact (canonical17590 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2620 + difference 2 4) (sourceB2620 + difference 4 2) sourceC2620) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5344) := by
    have ha : (tripleCharges (sourceA2620 + difference 2 4) (sourceB2620 + difference 4 2) sourceC2620) = raw36578 := by
      apply Matrix.ext; unfold tripleCharges sourceA2620 sourceB2620 sourceC2620 difference raw36578; decide +kernel
    rw [ha]
    exact (canonical36578 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2620 + difference 2 5) (sourceB2620 + difference 5 2) sourceC2620) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5365) := by
    have ha : (tripleCharges (sourceA2620 + difference 2 5) (sourceB2620 + difference 5 2) sourceC2620) = raw18792 := by
      apply Matrix.ext; unfold tripleCharges sourceA2620 sourceB2620 sourceC2620 difference raw18792; decide +kernel
    rw [ha]
    exact (canonical18792 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2620 + difference 3 0) (sourceB2620 + difference 0 3) sourceC2620) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4903) := by
    have ha : (tripleCharges (sourceA2620 + difference 3 0) (sourceB2620 + difference 0 3) sourceC2620) = raw33203 := by
      apply Matrix.ext; unfold tripleCharges sourceA2620 sourceB2620 sourceC2620 difference raw33203; decide +kernel
    rw [ha]
    exact (canonical33203 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2620 + difference 3 1) (sourceB2620 + difference 1 3) sourceC2620) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4632) := by
    have ha : (tripleCharges (sourceA2620 + difference 3 1) (sourceB2620 + difference 1 3) sourceC2620) = raw36579 := by
      apply Matrix.ext; unfold tripleCharges sourceA2620 sourceB2620 sourceC2620 difference raw36579; decide +kernel
    rw [ha]
    exact (canonical36579 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2620 + difference 3 2) (sourceB2620 + difference 2 3) sourceC2620) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5335) := by
    have ha : (tripleCharges (sourceA2620 + difference 3 2) (sourceB2620 + difference 2 3) sourceC2620) = raw36580 := by
      apply Matrix.ext; unfold tripleCharges sourceA2620 sourceB2620 sourceC2620 difference raw36580; decide +kernel
    rw [ha]
    exact (canonical36580 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2620 + difference 3 4) (sourceB2620 + difference 4 3) sourceC2620) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5341) := by
    have ha : (tripleCharges (sourceA2620 + difference 3 4) (sourceB2620 + difference 4 3) sourceC2620) = raw36581 := by
      apply Matrix.ext; unfold tripleCharges sourceA2620 sourceB2620 sourceC2620 difference raw36581; decide +kernel
    rw [ha]
    exact (canonical36581 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2620 + difference 3 5) (sourceB2620 + difference 5 3) sourceC2620) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5352) := by
    have ha : (tripleCharges (sourceA2620 + difference 3 5) (sourceB2620 + difference 5 3) sourceC2620) = raw18795 := by
      apply Matrix.ext; unfold tripleCharges sourceA2620 sourceB2620 sourceC2620 difference raw18795; decide +kernel
    rw [ha]
    exact (canonical18795 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2620 + difference 4 0) (sourceB2620 + difference 0 4) sourceC2620) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4903) := by
    have ha : (tripleCharges (sourceA2620 + difference 4 0) (sourceB2620 + difference 0 4) sourceC2620) = raw33207 := by
      apply Matrix.ext; unfold tripleCharges sourceA2620 sourceB2620 sourceC2620 difference raw33207; decide +kernel
    rw [ha]
    exact (canonical33207 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2620 + difference 4 1) (sourceB2620 + difference 1 4) sourceC2620) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4632) := by
    have ha : (tripleCharges (sourceA2620 + difference 4 1) (sourceB2620 + difference 1 4) sourceC2620) = raw36582 := by
      apply Matrix.ext; unfold tripleCharges sourceA2620 sourceB2620 sourceC2620 difference raw36582; decide +kernel
    rw [ha]
    exact (canonical36582 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2620 + difference 4 2) (sourceB2620 + difference 2 4) sourceC2620) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5335) := by
    have ha : (tripleCharges (sourceA2620 + difference 4 2) (sourceB2620 + difference 2 4) sourceC2620) = raw36583 := by
      apply Matrix.ext; unfold tripleCharges sourceA2620 sourceB2620 sourceC2620 difference raw36583; decide +kernel
    rw [ha]
    exact (canonical36583 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2620 + difference 4 3) (sourceB2620 + difference 3 4) sourceC2620) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5341) := by
    have ha : (tripleCharges (sourceA2620 + difference 4 3) (sourceB2620 + difference 3 4) sourceC2620) = raw17598 := by
      apply Matrix.ext; unfold tripleCharges sourceA2620 sourceB2620 sourceC2620 difference raw17598; decide +kernel
    rw [ha]
    exact (canonical17598 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2620 + difference 4 5) (sourceB2620 + difference 5 4) sourceC2620) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5352) := by
    have ha : (tripleCharges (sourceA2620 + difference 4 5) (sourceB2620 + difference 5 4) sourceC2620) = raw18799 := by
      apply Matrix.ext; unfold tripleCharges sourceA2620 sourceB2620 sourceC2620 difference raw18799; decide +kernel
    rw [ha]
    exact (canonical18799 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2620 + difference 5 0) (sourceB2620 + difference 0 5) sourceC2620) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4755) := by
    have ha : (tripleCharges (sourceA2620 + difference 5 0) (sourceB2620 + difference 0 5) sourceC2620) = raw33210 := by
      apply Matrix.ext; unfold tripleCharges sourceA2620 sourceB2620 sourceC2620 difference raw33210; decide +kernel
    rw [ha]
    exact (canonical33210 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2620 + difference 5 1) (sourceB2620 + difference 1 5) sourceC2620) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4630) := by
    have ha : (tripleCharges (sourceA2620 + difference 5 1) (sourceB2620 + difference 1 5) sourceC2620) = raw36584 := by
      apply Matrix.ext; unfold tripleCharges sourceA2620 sourceB2620 sourceC2620 difference raw36584; decide +kernel
    rw [ha]
    exact (canonical36584 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2620 + difference 5 2) (sourceB2620 + difference 2 5) sourceC2620) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4763) := by
    have ha : (tripleCharges (sourceA2620 + difference 5 2) (sourceB2620 + difference 2 5) sourceC2620) = raw36585 := by
      apply Matrix.ext; unfold tripleCharges sourceA2620 sourceB2620 sourceC2620 difference raw36585; decide +kernel
    rw [ha]
    exact (canonical36585 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2620 + difference 5 3) (sourceB2620 + difference 3 5) sourceC2620) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4782) := by
    have ha : (tripleCharges (sourceA2620 + difference 5 3) (sourceB2620 + difference 3 5) sourceC2620) = raw17603 := by
      apply Matrix.ext; unfold tripleCharges sourceA2620 sourceB2620 sourceC2620 difference raw17603; decide +kernel
    rw [ha]
    exact (canonical17603 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2620 + difference 5 4) (sourceB2620 + difference 4 5) sourceC2620) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4782) := by
    have ha : (tripleCharges (sourceA2620 + difference 5 4) (sourceB2620 + difference 4 5) sourceC2620) = raw36586 := by
      apply Matrix.ext; unfold tripleCharges sourceA2620 sourceB2620 sourceC2620 difference raw36586; decide +kernel
    rw [ha]
    exact (canonical36586 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2620 sourceB2620 sourceC2620
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2620, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2621 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2621 : Charge := ![1, 0, 0, 1, 0, -2]
def sourceC2621 : Charge := ![1, 2, 0, -2, -1, 0]
def sourceForm2621 : Integer.Sparse Master := [(Sum.inr 4775, 1), (Sum.inr 4776, 1), (Sum.inr 4777, 1), (Sum.inr 4821, 1), (Sum.inr 4856, 1), (Sum.inr 4942, 1), (Sum.inr 4949, 1), (Sum.inr 4951, 1), (Sum.inr 4963, 1), (Sum.inr 4966, 1), (Sum.inr 4973, 1), (Sum.inr 5105, 1), (Sum.inr 5198, 1), (Sum.inr 5336, 1), (Sum.inr 5338, 1), (Sum.inr 5353, 1), (Sum.inr 5355, 1), (Sum.inr 5360, 1), (Sum.inr 5361, 1), (Sum.inr 5365, 1), (Sum.inr 5367, 1), (Sum.inr 5368, 1), (Sum.inr 5397, 1), (Sum.inr 5410, 1), (Sum.inr 5411, 1), (Sum.inr 5412, 1), (Sum.inr 5421, 1), (Sum.inr 5436, 1), (Sum.inr 5446, 1), (Sum.inr 5473, 1)]

theorem sourceEq2621 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2621 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2621 + difference 0 1) (sourceB2621 + difference 1 0) sourceC2621) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5105) := by
    have ha : (tripleCharges (sourceA2621 + difference 0 1) (sourceB2621 + difference 1 0) sourceC2621) = raw36587 := by
      apply Matrix.ext; unfold tripleCharges sourceA2621 sourceB2621 sourceC2621 difference raw36587; decide +kernel
    rw [ha]
    exact (canonical36587 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2621 + difference 0 2) (sourceB2621 + difference 2 0) sourceC2621) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5397) := by
    have ha : (tripleCharges (sourceA2621 + difference 0 2) (sourceB2621 + difference 2 0) sourceC2621) = raw36588 := by
      apply Matrix.ext; unfold tripleCharges sourceA2621 sourceB2621 sourceC2621 difference raw36588; decide +kernel
    rw [ha]
    exact (canonical36588 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2621 + difference 0 3) (sourceB2621 + difference 3 0) sourceC2621) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5412) := by
    have ha : (tripleCharges (sourceA2621 + difference 0 3) (sourceB2621 + difference 3 0) sourceC2621) = raw36589 := by
      apply Matrix.ext; unfold tripleCharges sourceA2621 sourceB2621 sourceC2621 difference raw36589; decide +kernel
    rw [ha]
    exact (canonical36589 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2621 + difference 0 4) (sourceB2621 + difference 4 0) sourceC2621) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA2621 + difference 0 4) (sourceB2621 + difference 4 0) sourceC2621) = raw36590 := by
      apply Matrix.ext; unfold tripleCharges sourceA2621 sourceB2621 sourceC2621 difference raw36590; decide +kernel
    rw [ha]
    exact (canonical36590 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2621 + difference 0 5) (sourceB2621 + difference 5 0) sourceC2621) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5410) := by
    have ha : (tripleCharges (sourceA2621 + difference 0 5) (sourceB2621 + difference 5 0) sourceC2621) = raw36591 := by
      apply Matrix.ext; unfold tripleCharges sourceA2621 sourceB2621 sourceC2621 difference raw36591; decide +kernel
    rw [ha]
    exact (canonical36591 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2621 + difference 1 0) (sourceB2621 + difference 0 1) sourceC2621) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5198) := by
    have ha : (tripleCharges (sourceA2621 + difference 1 0) (sourceB2621 + difference 0 1) sourceC2621) = raw36592 := by
      apply Matrix.ext; unfold tripleCharges sourceA2621 sourceB2621 sourceC2621 difference raw36592; decide +kernel
    rw [ha]
    exact (canonical36592 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2621 + difference 1 2) (sourceB2621 + difference 2 1) sourceC2621) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5421) := by
    have ha : (tripleCharges (sourceA2621 + difference 1 2) (sourceB2621 + difference 2 1) sourceC2621) = raw36593 := by
      apply Matrix.ext; unfold tripleCharges sourceA2621 sourceB2621 sourceC2621 difference raw36593; decide +kernel
    rw [ha]
    exact (canonical36593 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2621 + difference 1 3) (sourceB2621 + difference 3 1) sourceC2621) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5436) := by
    have ha : (tripleCharges (sourceA2621 + difference 1 3) (sourceB2621 + difference 3 1) sourceC2621) = raw36594 := by
      apply Matrix.ext; unfold tripleCharges sourceA2621 sourceB2621 sourceC2621 difference raw36594; decide +kernel
    rw [ha]
    exact (canonical36594 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2621 + difference 1 4) (sourceB2621 + difference 4 1) sourceC2621) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5446) := by
    have ha : (tripleCharges (sourceA2621 + difference 1 4) (sourceB2621 + difference 4 1) sourceC2621) = raw36595 := by
      apply Matrix.ext; unfold tripleCharges sourceA2621 sourceB2621 sourceC2621 difference raw36595; decide +kernel
    rw [ha]
    exact (canonical36595 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2621 + difference 1 5) (sourceB2621 + difference 5 1) sourceC2621) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA2621 + difference 1 5) (sourceB2621 + difference 5 1) sourceC2621) = raw36596 := by
      apply Matrix.ext; unfold tripleCharges sourceA2621 sourceB2621 sourceC2621 difference raw36596; decide +kernel
    rw [ha]
    exact (canonical36596 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2621 + difference 2 0) (sourceB2621 + difference 0 2) sourceC2621) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4963) := by
    have ha : (tripleCharges (sourceA2621 + difference 2 0) (sourceB2621 + difference 0 2) sourceC2621) = raw36597 := by
      apply Matrix.ext; unfold tripleCharges sourceA2621 sourceB2621 sourceC2621 difference raw36597; decide +kernel
    rw [ha]
    exact (canonical36597 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2621 + difference 2 1) (sourceB2621 + difference 1 2) sourceC2621) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4942) := by
    have ha : (tripleCharges (sourceA2621 + difference 2 1) (sourceB2621 + difference 1 2) sourceC2621) = raw36598 := by
      apply Matrix.ext; unfold tripleCharges sourceA2621 sourceB2621 sourceC2621 difference raw36598; decide +kernel
    rw [ha]
    exact (canonical36598 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2621 + difference 2 3) (sourceB2621 + difference 3 2) sourceC2621) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5360) := by
    have ha : (tripleCharges (sourceA2621 + difference 2 3) (sourceB2621 + difference 3 2) sourceC2621) = raw36599 := by
      apply Matrix.ext; unfold tripleCharges sourceA2621 sourceB2621 sourceC2621 difference raw36599; decide +kernel
    rw [ha]
    exact (canonical36599 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2621 + difference 2 4) (sourceB2621 + difference 4 2) sourceC2621) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5353) := by
    have ha : (tripleCharges (sourceA2621 + difference 2 4) (sourceB2621 + difference 4 2) sourceC2621) = raw36600 := by
      apply Matrix.ext; unfold tripleCharges sourceA2621 sourceB2621 sourceC2621 difference raw36600; decide +kernel
    rw [ha]
    exact (canonical36600 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2621 + difference 2 5) (sourceB2621 + difference 5 2) sourceC2621) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5365) := by
    have ha : (tripleCharges (sourceA2621 + difference 2 5) (sourceB2621 + difference 5 2) sourceC2621) = raw36601 := by
      apply Matrix.ext; unfold tripleCharges sourceA2621 sourceB2621 sourceC2621 difference raw36601; decide +kernel
    rw [ha]
    exact (canonical36601 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2621 + difference 3 0) (sourceB2621 + difference 0 3) sourceC2621) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4973) := by
    have ha : (tripleCharges (sourceA2621 + difference 3 0) (sourceB2621 + difference 0 3) sourceC2621) = raw36602 := by
      apply Matrix.ext; unfold tripleCharges sourceA2621 sourceB2621 sourceC2621 difference raw36602; decide +kernel
    rw [ha]
    exact (canonical36602 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2621 + difference 3 1) (sourceB2621 + difference 1 3) sourceC2621) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4949) := by
    have ha : (tripleCharges (sourceA2621 + difference 3 1) (sourceB2621 + difference 1 3) sourceC2621) = raw36603 := by
      apply Matrix.ext; unfold tripleCharges sourceA2621 sourceB2621 sourceC2621 difference raw36603; decide +kernel
    rw [ha]
    exact (canonical36603 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2621 + difference 3 2) (sourceB2621 + difference 2 3) sourceC2621) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5336) := by
    have ha : (tripleCharges (sourceA2621 + difference 3 2) (sourceB2621 + difference 2 3) sourceC2621) = raw36604 := by
      apply Matrix.ext; unfold tripleCharges sourceA2621 sourceB2621 sourceC2621 difference raw36604; decide +kernel
    rw [ha]
    exact (canonical36604 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2621 + difference 3 4) (sourceB2621 + difference 4 3) sourceC2621) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5355) := by
    have ha : (tripleCharges (sourceA2621 + difference 3 4) (sourceB2621 + difference 4 3) sourceC2621) = raw36605 := by
      apply Matrix.ext; unfold tripleCharges sourceA2621 sourceB2621 sourceC2621 difference raw36605; decide +kernel
    rw [ha]
    exact (canonical36605 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2621 + difference 3 5) (sourceB2621 + difference 5 3) sourceC2621) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5367) := by
    have ha : (tripleCharges (sourceA2621 + difference 3 5) (sourceB2621 + difference 5 3) sourceC2621) = raw36606 := by
      apply Matrix.ext; unfold tripleCharges sourceA2621 sourceB2621 sourceC2621 difference raw36606; decide +kernel
    rw [ha]
    exact (canonical36606 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2621 + difference 4 0) (sourceB2621 + difference 0 4) sourceC2621) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4966) := by
    have ha : (tripleCharges (sourceA2621 + difference 4 0) (sourceB2621 + difference 0 4) sourceC2621) = raw36607 := by
      apply Matrix.ext; unfold tripleCharges sourceA2621 sourceB2621 sourceC2621 difference raw36607; decide +kernel
    rw [ha]
    exact (canonical36607 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2621 + difference 4 1) (sourceB2621 + difference 1 4) sourceC2621) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4951) := by
    have ha : (tripleCharges (sourceA2621 + difference 4 1) (sourceB2621 + difference 1 4) sourceC2621) = raw36608 := by
      apply Matrix.ext; unfold tripleCharges sourceA2621 sourceB2621 sourceC2621 difference raw36608; decide +kernel
    rw [ha]
    exact (canonical36608 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2621 + difference 4 2) (sourceB2621 + difference 2 4) sourceC2621) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5338) := by
    have ha : (tripleCharges (sourceA2621 + difference 4 2) (sourceB2621 + difference 2 4) sourceC2621) = raw36609 := by
      apply Matrix.ext; unfold tripleCharges sourceA2621 sourceB2621 sourceC2621 difference raw36609; decide +kernel
    rw [ha]
    exact (canonical36609 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2621 + difference 4 3) (sourceB2621 + difference 3 4) sourceC2621) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5361) := by
    have ha : (tripleCharges (sourceA2621 + difference 4 3) (sourceB2621 + difference 3 4) sourceC2621) = raw36610 := by
      apply Matrix.ext; unfold tripleCharges sourceA2621 sourceB2621 sourceC2621 difference raw36610; decide +kernel
    rw [ha]
    exact (canonical36610 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2621 + difference 4 5) (sourceB2621 + difference 5 4) sourceC2621) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5368) := by
    have ha : (tripleCharges (sourceA2621 + difference 4 5) (sourceB2621 + difference 5 4) sourceC2621) = raw36611 := by
      apply Matrix.ext; unfold tripleCharges sourceA2621 sourceB2621 sourceC2621 difference raw36611; decide +kernel
    rw [ha]
    exact (canonical36611 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2621 + difference 5 0) (sourceB2621 + difference 0 5) sourceC2621) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4776) := by
    have ha : (tripleCharges (sourceA2621 + difference 5 0) (sourceB2621 + difference 0 5) sourceC2621) = raw36612 := by
      apply Matrix.ext; unfold tripleCharges sourceA2621 sourceB2621 sourceC2621 difference raw36612; decide +kernel
    rw [ha]
    exact (canonical36612 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2621 + difference 5 1) (sourceB2621 + difference 1 5) sourceC2621) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4777) := by
    have ha : (tripleCharges (sourceA2621 + difference 5 1) (sourceB2621 + difference 1 5) sourceC2621) = raw36613 := by
      apply Matrix.ext; unfold tripleCharges sourceA2621 sourceB2621 sourceC2621 difference raw36613; decide +kernel
    rw [ha]
    exact (canonical36613 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2621 + difference 5 2) (sourceB2621 + difference 2 5) sourceC2621) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4775) := by
    have ha : (tripleCharges (sourceA2621 + difference 5 2) (sourceB2621 + difference 2 5) sourceC2621) = raw36614 := by
      apply Matrix.ext; unfold tripleCharges sourceA2621 sourceB2621 sourceC2621 difference raw36614; decide +kernel
    rw [ha]
    exact (canonical36614 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2621 + difference 5 3) (sourceB2621 + difference 3 5) sourceC2621) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4821) := by
    have ha : (tripleCharges (sourceA2621 + difference 5 3) (sourceB2621 + difference 3 5) sourceC2621) = raw36615 := by
      apply Matrix.ext; unfold tripleCharges sourceA2621 sourceB2621 sourceC2621 difference raw36615; decide +kernel
    rw [ha]
    exact (canonical36615 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2621 + difference 5 4) (sourceB2621 + difference 4 5) sourceC2621) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4856) := by
    have ha : (tripleCharges (sourceA2621 + difference 5 4) (sourceB2621 + difference 4 5) sourceC2621) = raw36616 := by
      apply Matrix.ext; unfold tripleCharges sourceA2621 sourceB2621 sourceC2621 difference raw36616; decide +kernel
    rw [ha]
    exact (canonical36616 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2621 sourceB2621 sourceC2621
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2621, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2622 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2622 : Charge := ![1, 0, 0, 1, 0, -2]
def sourceC2622 : Charge := ![1, 2, 0, -2, -1, 0]
def sourceForm2622 : Integer.Sparse Master := [(Sum.inr 2211, 1), (Sum.inr 2212, 1), (Sum.inr 2217, 1), (Sum.inr 2223, 1), (Sum.inr 2274, 1), (Sum.inr 3407, 1), (Sum.inr 3417, 1), (Sum.inr 3418, 1), (Sum.inr 3479, 1), (Sum.inr 3553, 1), (Sum.inr 3555, 1), (Sum.inr 3570, 1), (Sum.inr 3591, 1), (Sum.inr 3754, 1), (Sum.inr 3755, 1), (Sum.inr 3758, 1), (Sum.inr 3761, 1), (Sum.inr 3762, 1), (Sum.inr 3766, 1), (Sum.inr 3767, 1), (Sum.inr 3770, 1), (Sum.inr 3772, 1), (Sum.inr 3796, 1), (Sum.inr 3808, 1), (Sum.inr 3813, 1), (Sum.inr 3814, 1), (Sum.inr 3873, 1), (Sum.inr 3877, 1), (Sum.inr 3884, 1), (Sum.inr 3958, 1)]

theorem sourceEq2622 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2622 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2622 + difference 0 1) (sourceB2622 + difference 1 0) sourceC2622) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3479) := by
    have ha : (tripleCharges (sourceA2622 + difference 0 1) (sourceB2622 + difference 1 0) sourceC2622) = raw36617 := by
      apply Matrix.ext; unfold tripleCharges sourceA2622 sourceB2622 sourceC2622 difference raw36617; decide +kernel
    rw [ha]
    exact (canonical36617 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2622 + difference 0 2) (sourceB2622 + difference 2 0) sourceC2622) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3796) := by
    have ha : (tripleCharges (sourceA2622 + difference 0 2) (sourceB2622 + difference 2 0) sourceC2622) = raw36618 := by
      apply Matrix.ext; unfold tripleCharges sourceA2622 sourceB2622 sourceC2622 difference raw36618; decide +kernel
    rw [ha]
    exact (canonical36618 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2622 + difference 0 3) (sourceB2622 + difference 3 0) sourceC2622) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3814) := by
    have ha : (tripleCharges (sourceA2622 + difference 0 3) (sourceB2622 + difference 3 0) sourceC2622) = raw36619 := by
      apply Matrix.ext; unfold tripleCharges sourceA2622 sourceB2622 sourceC2622 difference raw36619; decide +kernel
    rw [ha]
    exact (canonical36619 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2622 + difference 0 4) (sourceB2622 + difference 4 0) sourceC2622) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3813) := by
    have ha : (tripleCharges (sourceA2622 + difference 0 4) (sourceB2622 + difference 4 0) sourceC2622) = raw36620 := by
      apply Matrix.ext; unfold tripleCharges sourceA2622 sourceB2622 sourceC2622 difference raw36620; decide +kernel
    rw [ha]
    exact (canonical36620 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2622 + difference 0 5) (sourceB2622 + difference 5 0) sourceC2622) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3808) := by
    have ha : (tripleCharges (sourceA2622 + difference 0 5) (sourceB2622 + difference 5 0) sourceC2622) = raw36621 := by
      apply Matrix.ext; unfold tripleCharges sourceA2622 sourceB2622 sourceC2622 difference raw36621; decide +kernel
    rw [ha]
    exact (canonical36621 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2622 + difference 1 0) (sourceB2622 + difference 0 1) sourceC2622) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3570) := by
    have ha : (tripleCharges (sourceA2622 + difference 1 0) (sourceB2622 + difference 0 1) sourceC2622) = raw36622 := by
      apply Matrix.ext; unfold tripleCharges sourceA2622 sourceB2622 sourceC2622 difference raw36622; decide +kernel
    rw [ha]
    exact (canonical36622 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2622 + difference 1 2) (sourceB2622 + difference 2 1) sourceC2622) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3873) := by
    have ha : (tripleCharges (sourceA2622 + difference 1 2) (sourceB2622 + difference 2 1) sourceC2622) = raw36623 := by
      apply Matrix.ext; unfold tripleCharges sourceA2622 sourceB2622 sourceC2622 difference raw36623; decide +kernel
    rw [ha]
    exact (canonical36623 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2622 + difference 1 3) (sourceB2622 + difference 3 1) sourceC2622) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3877) := by
    have ha : (tripleCharges (sourceA2622 + difference 1 3) (sourceB2622 + difference 3 1) sourceC2622) = raw36624 := by
      apply Matrix.ext; unfold tripleCharges sourceA2622 sourceB2622 sourceC2622 difference raw36624; decide +kernel
    rw [ha]
    exact (canonical36624 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2622 + difference 1 4) (sourceB2622 + difference 4 1) sourceC2622) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3884) := by
    have ha : (tripleCharges (sourceA2622 + difference 1 4) (sourceB2622 + difference 4 1) sourceC2622) = raw36625 := by
      apply Matrix.ext; unfold tripleCharges sourceA2622 sourceB2622 sourceC2622 difference raw36625; decide +kernel
    rw [ha]
    exact (canonical36625 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2622 + difference 1 5) (sourceB2622 + difference 5 1) sourceC2622) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3958) := by
    have ha : (tripleCharges (sourceA2622 + difference 1 5) (sourceB2622 + difference 5 1) sourceC2622) = raw36626 := by
      apply Matrix.ext; unfold tripleCharges sourceA2622 sourceB2622 sourceC2622 difference raw36626; decide +kernel
    rw [ha]
    exact (canonical36626 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2622 + difference 2 0) (sourceB2622 + difference 0 2) sourceC2622) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3553) := by
    have ha : (tripleCharges (sourceA2622 + difference 2 0) (sourceB2622 + difference 0 2) sourceC2622) = raw36627 := by
      apply Matrix.ext; unfold tripleCharges sourceA2622 sourceB2622 sourceC2622 difference raw36627; decide +kernel
    rw [ha]
    exact (canonical36627 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2622 + difference 2 1) (sourceB2622 + difference 1 2) sourceC2622) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3407) := by
    have ha : (tripleCharges (sourceA2622 + difference 2 1) (sourceB2622 + difference 1 2) sourceC2622) = raw36628 := by
      apply Matrix.ext; unfold tripleCharges sourceA2622 sourceB2622 sourceC2622 difference raw36628; decide +kernel
    rw [ha]
    exact (canonical36628 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2622 + difference 2 3) (sourceB2622 + difference 3 2) sourceC2622) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3762) := by
    have ha : (tripleCharges (sourceA2622 + difference 2 3) (sourceB2622 + difference 3 2) sourceC2622) = raw36629 := by
      apply Matrix.ext; unfold tripleCharges sourceA2622 sourceB2622 sourceC2622 difference raw36629; decide +kernel
    rw [ha]
    exact (canonical36629 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2622 + difference 2 4) (sourceB2622 + difference 4 2) sourceC2622) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3761) := by
    have ha : (tripleCharges (sourceA2622 + difference 2 4) (sourceB2622 + difference 4 2) sourceC2622) = raw36630 := by
      apply Matrix.ext; unfold tripleCharges sourceA2622 sourceB2622 sourceC2622 difference raw36630; decide +kernel
    rw [ha]
    exact (canonical36630 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2622 + difference 2 5) (sourceB2622 + difference 5 2) sourceC2622) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3758) := by
    have ha : (tripleCharges (sourceA2622 + difference 2 5) (sourceB2622 + difference 5 2) sourceC2622) = raw36631 := by
      apply Matrix.ext; unfold tripleCharges sourceA2622 sourceB2622 sourceC2622 difference raw36631; decide +kernel
    rw [ha]
    exact (canonical36631 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2622 + difference 3 0) (sourceB2622 + difference 0 3) sourceC2622) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3591) := by
    have ha : (tripleCharges (sourceA2622 + difference 3 0) (sourceB2622 + difference 0 3) sourceC2622) = raw36632 := by
      apply Matrix.ext; unfold tripleCharges sourceA2622 sourceB2622 sourceC2622 difference raw36632; decide +kernel
    rw [ha]
    exact (canonical36632 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2622 + difference 3 1) (sourceB2622 + difference 1 3) sourceC2622) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3417) := by
    have ha : (tripleCharges (sourceA2622 + difference 3 1) (sourceB2622 + difference 1 3) sourceC2622) = raw36633 := by
      apply Matrix.ext; unfold tripleCharges sourceA2622 sourceB2622 sourceC2622 difference raw36633; decide +kernel
    rw [ha]
    exact (canonical36633 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2622 + difference 3 2) (sourceB2622 + difference 2 3) sourceC2622) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3754) := by
    have ha : (tripleCharges (sourceA2622 + difference 3 2) (sourceB2622 + difference 2 3) sourceC2622) = raw36634 := by
      apply Matrix.ext; unfold tripleCharges sourceA2622 sourceB2622 sourceC2622 difference raw36634; decide +kernel
    rw [ha]
    exact (canonical36634 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2622 + difference 3 4) (sourceB2622 + difference 4 3) sourceC2622) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3770) := by
    have ha : (tripleCharges (sourceA2622 + difference 3 4) (sourceB2622 + difference 4 3) sourceC2622) = raw36635 := by
      apply Matrix.ext; unfold tripleCharges sourceA2622 sourceB2622 sourceC2622 difference raw36635; decide +kernel
    rw [ha]
    exact (canonical36635 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2622 + difference 3 5) (sourceB2622 + difference 5 3) sourceC2622) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3766) := by
    have ha : (tripleCharges (sourceA2622 + difference 3 5) (sourceB2622 + difference 5 3) sourceC2622) = raw36636 := by
      apply Matrix.ext; unfold tripleCharges sourceA2622 sourceB2622 sourceC2622 difference raw36636; decide +kernel
    rw [ha]
    exact (canonical36636 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2622 + difference 4 0) (sourceB2622 + difference 0 4) sourceC2622) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3555) := by
    have ha : (tripleCharges (sourceA2622 + difference 4 0) (sourceB2622 + difference 0 4) sourceC2622) = raw36637 := by
      apply Matrix.ext; unfold tripleCharges sourceA2622 sourceB2622 sourceC2622 difference raw36637; decide +kernel
    rw [ha]
    exact (canonical36637 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2622 + difference 4 1) (sourceB2622 + difference 1 4) sourceC2622) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3418) := by
    have ha : (tripleCharges (sourceA2622 + difference 4 1) (sourceB2622 + difference 1 4) sourceC2622) = raw36638 := by
      apply Matrix.ext; unfold tripleCharges sourceA2622 sourceB2622 sourceC2622 difference raw36638; decide +kernel
    rw [ha]
    exact (canonical36638 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2622 + difference 4 2) (sourceB2622 + difference 2 4) sourceC2622) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3755) := by
    have ha : (tripleCharges (sourceA2622 + difference 4 2) (sourceB2622 + difference 2 4) sourceC2622) = raw36639 := by
      apply Matrix.ext; unfold tripleCharges sourceA2622 sourceB2622 sourceC2622 difference raw36639; decide +kernel
    rw [ha]
    exact (canonical36639 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2622 + difference 4 3) (sourceB2622 + difference 3 4) sourceC2622) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3772) := by
    have ha : (tripleCharges (sourceA2622 + difference 4 3) (sourceB2622 + difference 3 4) sourceC2622) = raw36640 := by
      apply Matrix.ext; unfold tripleCharges sourceA2622 sourceB2622 sourceC2622 difference raw36640; decide +kernel
    rw [ha]
    exact (canonical36640 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2622 + difference 4 5) (sourceB2622 + difference 5 4) sourceC2622) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3767) := by
    have ha : (tripleCharges (sourceA2622 + difference 4 5) (sourceB2622 + difference 5 4) sourceC2622) = raw36641 := by
      apply Matrix.ext; unfold tripleCharges sourceA2622 sourceB2622 sourceC2622 difference raw36641; decide +kernel
    rw [ha]
    exact (canonical36641 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2622 + difference 5 0) (sourceB2622 + difference 0 5) sourceC2622) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2212) := by
    have ha : (tripleCharges (sourceA2622 + difference 5 0) (sourceB2622 + difference 0 5) sourceC2622) = raw36642 := by
      apply Matrix.ext; unfold tripleCharges sourceA2622 sourceB2622 sourceC2622 difference raw36642; decide +kernel
    rw [ha]
    exact (canonical36642 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2622 + difference 5 1) (sourceB2622 + difference 1 5) sourceC2622) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2223) := by
    have ha : (tripleCharges (sourceA2622 + difference 5 1) (sourceB2622 + difference 1 5) sourceC2622) = raw36643 := by
      apply Matrix.ext; unfold tripleCharges sourceA2622 sourceB2622 sourceC2622 difference raw36643; decide +kernel
    rw [ha]
    exact (canonical36643 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2622 + difference 5 2) (sourceB2622 + difference 2 5) sourceC2622) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2211) := by
    have ha : (tripleCharges (sourceA2622 + difference 5 2) (sourceB2622 + difference 2 5) sourceC2622) = raw36644 := by
      apply Matrix.ext; unfold tripleCharges sourceA2622 sourceB2622 sourceC2622 difference raw36644; decide +kernel
    rw [ha]
    exact (canonical36644 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2622 + difference 5 3) (sourceB2622 + difference 3 5) sourceC2622) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2217) := by
    have ha : (tripleCharges (sourceA2622 + difference 5 3) (sourceB2622 + difference 3 5) sourceC2622) = raw36645 := by
      apply Matrix.ext; unfold tripleCharges sourceA2622 sourceB2622 sourceC2622 difference raw36645; decide +kernel
    rw [ha]
    exact (canonical36645 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2622 + difference 5 4) (sourceB2622 + difference 4 5) sourceC2622) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2274) := by
    have ha : (tripleCharges (sourceA2622 + difference 5 4) (sourceB2622 + difference 4 5) sourceC2622) = raw36646 := by
      apply Matrix.ext; unfold tripleCharges sourceA2622 sourceB2622 sourceC2622 difference raw36646; decide +kernel
    rw [ha]
    exact (canonical36646 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2622 sourceB2622 sourceC2622
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2622, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2623 : Charge := ![-2, -2, 0, 1, 1, 2]
def sourceB2623 : Charge := ![1, 2, 0, -2, -1, 0]
def sourceC2623 : Charge := ![1, 0, 0, 1, 0, -2]
def sourceForm2623 : Integer.Sparse Master := [(Sum.inr 4648, 1), (Sum.inr 4650, 1), (Sum.inr 4651, 1), (Sum.inr 4653, 1), (Sum.inr 4839, 1), (Sum.inr 4917, 1), (Sum.inr 4919, 1), (Sum.inr 4920, 1), (Sum.inr 4922, 1), (Sum.inr 5046, 1), (Sum.inr 5095, 1), (Sum.inr 5105, 1), (Sum.inr 5119, 1), (Sum.inr 5152, 1), (Sum.inr 5207, 1), (Sum.inr 5238, 1), (Sum.inr 5333, 1), (Sum.inr 5354, 1), (Sum.inr 5355, 1), (Sum.inr 5363, 1), (Sum.inr 5364, 1), (Sum.inr 5370, 1), (Sum.inr 5397, 1), (Sum.inr 5422, 1), (Sum.inr 5434, 1), (Sum.inr 5435, 1), (Sum.inr 5438, 1), (Sum.inr 5443, 1), (Sum.inr 5451, 1), (Sum.inr 5484, 1)]

theorem sourceEq2623 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2623 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2623 + difference 0 1) (sourceB2623 + difference 1 0) sourceC2623) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4839) := by
    have ha : (tripleCharges (sourceA2623 + difference 0 1) (sourceB2623 + difference 1 0) sourceC2623) = raw36647 := by
      apply Matrix.ext; unfold tripleCharges sourceA2623 sourceB2623 sourceC2623 difference raw36647; decide +kernel
    rw [ha]
    exact (canonical36647 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2623 + difference 0 2) (sourceB2623 + difference 2 0) sourceC2623) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5397) := by
    have ha : (tripleCharges (sourceA2623 + difference 0 2) (sourceB2623 + difference 2 0) sourceC2623) = raw36648 := by
      apply Matrix.ext; unfold tripleCharges sourceA2623 sourceB2623 sourceC2623 difference raw36648; decide +kernel
    rw [ha]
    exact (canonical36648 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2623 + difference 0 3) (sourceB2623 + difference 3 0) sourceC2623) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA2623 + difference 0 3) (sourceB2623 + difference 3 0) sourceC2623) = raw36649 := by
      apply Matrix.ext; unfold tripleCharges sourceA2623 sourceB2623 sourceC2623 difference raw36649; decide +kernel
    rw [ha]
    exact (canonical36649 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2623 + difference 0 4) (sourceB2623 + difference 4 0) sourceC2623) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA2623 + difference 0 4) (sourceB2623 + difference 4 0) sourceC2623) = raw36650 := by
      apply Matrix.ext; unfold tripleCharges sourceA2623 sourceB2623 sourceC2623 difference raw36650; decide +kernel
    rw [ha]
    exact (canonical36650 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2623 + difference 0 5) (sourceB2623 + difference 5 0) sourceC2623) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA2623 + difference 0 5) (sourceB2623 + difference 5 0) sourceC2623) = raw18983 := by
      apply Matrix.ext; unfold tripleCharges sourceA2623 sourceB2623 sourceC2623 difference raw18983; decide +kernel
    rw [ha]
    exact (canonical18983 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2623 + difference 1 0) (sourceB2623 + difference 0 1) sourceC2623) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5105) := by
    have ha : (tripleCharges (sourceA2623 + difference 1 0) (sourceB2623 + difference 0 1) sourceC2623) = raw8018 := by
      apply Matrix.ext; unfold tripleCharges sourceA2623 sourceB2623 sourceC2623 difference raw8018; decide +kernel
    rw [ha]
    exact (canonical8018 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2623 + difference 1 2) (sourceB2623 + difference 2 1) sourceC2623) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5422) := by
    have ha : (tripleCharges (sourceA2623 + difference 1 2) (sourceB2623 + difference 2 1) sourceC2623) = raw19001 := by
      apply Matrix.ext; unfold tripleCharges sourceA2623 sourceB2623 sourceC2623 difference raw19001; decide +kernel
    rw [ha]
    exact (canonical19001 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2623 + difference 1 3) (sourceB2623 + difference 3 1) sourceC2623) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA2623 + difference 1 3) (sourceB2623 + difference 3 1) sourceC2623) = raw8002 := by
      apply Matrix.ext; unfold tripleCharges sourceA2623 sourceB2623 sourceC2623 difference raw8002; decide +kernel
    rw [ha]
    exact (canonical8002 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2623 + difference 1 4) (sourceB2623 + difference 4 1) sourceC2623) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA2623 + difference 1 4) (sourceB2623 + difference 4 1) sourceC2623) = raw19002 := by
      apply Matrix.ext; unfold tripleCharges sourceA2623 sourceB2623 sourceC2623 difference raw19002; decide +kernel
    rw [ha]
    exact (canonical19002 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2623 + difference 1 5) (sourceB2623 + difference 5 1) sourceC2623) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5484) := by
    have ha : (tripleCharges (sourceA2623 + difference 1 5) (sourceB2623 + difference 5 1) sourceC2623) = raw13969 := by
      apply Matrix.ext; unfold tripleCharges sourceA2623 sourceB2623 sourceC2623 difference raw13969; decide +kernel
    rw [ha]
    exact (canonical13969 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2623 + difference 2 0) (sourceB2623 + difference 0 2) sourceC2623) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4917) := by
    have ha : (tripleCharges (sourceA2623 + difference 2 0) (sourceB2623 + difference 0 2) sourceC2623) = raw33246 := by
      apply Matrix.ext; unfold tripleCharges sourceA2623 sourceB2623 sourceC2623 difference raw33246; decide +kernel
    rw [ha]
    exact (canonical33246 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2623 + difference 2 1) (sourceB2623 + difference 1 2) sourceC2623) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4648) := by
    have ha : (tripleCharges (sourceA2623 + difference 2 1) (sourceB2623 + difference 1 2) sourceC2623) = raw36651 := by
      apply Matrix.ext; unfold tripleCharges sourceA2623 sourceB2623 sourceC2623 difference raw36651; decide +kernel
    rw [ha]
    exact (canonical36651 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2623 + difference 2 3) (sourceB2623 + difference 3 2) sourceC2623) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5354) := by
    have ha : (tripleCharges (sourceA2623 + difference 2 3) (sourceB2623 + difference 3 2) sourceC2623) = raw36652 := by
      apply Matrix.ext; unfold tripleCharges sourceA2623 sourceB2623 sourceC2623 difference raw36652; decide +kernel
    rw [ha]
    exact (canonical36652 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2623 + difference 2 4) (sourceB2623 + difference 4 2) sourceC2623) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5370) := by
    have ha : (tripleCharges (sourceA2623 + difference 2 4) (sourceB2623 + difference 4 2) sourceC2623) = raw36653 := by
      apply Matrix.ext; unfold tripleCharges sourceA2623 sourceB2623 sourceC2623 difference raw36653; decide +kernel
    rw [ha]
    exact (canonical36653 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2623 + difference 2 5) (sourceB2623 + difference 5 2) sourceC2623) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5363) := by
    have ha : (tripleCharges (sourceA2623 + difference 2 5) (sourceB2623 + difference 5 2) sourceC2623) = raw18988 := by
      apply Matrix.ext; unfold tripleCharges sourceA2623 sourceB2623 sourceC2623 difference raw18988; decide +kernel
    rw [ha]
    exact (canonical18988 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2623 + difference 3 0) (sourceB2623 + difference 0 3) sourceC2623) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4920) := by
    have ha : (tripleCharges (sourceA2623 + difference 3 0) (sourceB2623 + difference 0 3) sourceC2623) = raw33248 := by
      apply Matrix.ext; unfold tripleCharges sourceA2623 sourceB2623 sourceC2623 difference raw33248; decide +kernel
    rw [ha]
    exact (canonical33248 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2623 + difference 3 1) (sourceB2623 + difference 1 3) sourceC2623) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4651) := by
    have ha : (tripleCharges (sourceA2623 + difference 3 1) (sourceB2623 + difference 1 3) sourceC2623) = raw36654 := by
      apply Matrix.ext; unfold tripleCharges sourceA2623 sourceB2623 sourceC2623 difference raw36654; decide +kernel
    rw [ha]
    exact (canonical36654 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2623 + difference 3 2) (sourceB2623 + difference 2 3) sourceC2623) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5046) := by
    have ha : (tripleCharges (sourceA2623 + difference 3 2) (sourceB2623 + difference 2 3) sourceC2623) = raw36655 := by
      apply Matrix.ext; unfold tripleCharges sourceA2623 sourceB2623 sourceC2623 difference raw36655; decide +kernel
    rw [ha]
    exact (canonical36655 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2623 + difference 3 4) (sourceB2623 + difference 4 3) sourceC2623) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5238) := by
    have ha : (tripleCharges (sourceA2623 + difference 3 4) (sourceB2623 + difference 4 3) sourceC2623) = raw36656 := by
      apply Matrix.ext; unfold tripleCharges sourceA2623 sourceB2623 sourceC2623 difference raw36656; decide +kernel
    rw [ha]
    exact (canonical36656 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2623 + difference 3 5) (sourceB2623 + difference 5 3) sourceC2623) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5095) := by
    have ha : (tripleCharges (sourceA2623 + difference 3 5) (sourceB2623 + difference 5 3) sourceC2623) = raw18992 := by
      apply Matrix.ext; unfold tripleCharges sourceA2623 sourceB2623 sourceC2623 difference raw18992; decide +kernel
    rw [ha]
    exact (canonical18992 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2623 + difference 4 0) (sourceB2623 + difference 0 4) sourceC2623) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4922) := by
    have ha : (tripleCharges (sourceA2623 + difference 4 0) (sourceB2623 + difference 0 4) sourceC2623) = raw33251 := by
      apply Matrix.ext; unfold tripleCharges sourceA2623 sourceB2623 sourceC2623 difference raw33251; decide +kernel
    rw [ha]
    exact (canonical33251 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2623 + difference 4 1) (sourceB2623 + difference 1 4) sourceC2623) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4653) := by
    have ha : (tripleCharges (sourceA2623 + difference 4 1) (sourceB2623 + difference 1 4) sourceC2623) = raw36657 := by
      apply Matrix.ext; unfold tripleCharges sourceA2623 sourceB2623 sourceC2623 difference raw36657; decide +kernel
    rw [ha]
    exact (canonical36657 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2623 + difference 4 2) (sourceB2623 + difference 2 4) sourceC2623) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5333) := by
    have ha : (tripleCharges (sourceA2623 + difference 4 2) (sourceB2623 + difference 2 4) sourceC2623) = raw36658 := by
      apply Matrix.ext; unfold tripleCharges sourceA2623 sourceB2623 sourceC2623 difference raw36658; decide +kernel
    rw [ha]
    exact (canonical36658 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2623 + difference 4 3) (sourceB2623 + difference 3 4) sourceC2623) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5355) := by
    have ha : (tripleCharges (sourceA2623 + difference 4 3) (sourceB2623 + difference 3 4) sourceC2623) = raw36659 := by
      apply Matrix.ext; unfold tripleCharges sourceA2623 sourceB2623 sourceC2623 difference raw36659; decide +kernel
    rw [ha]
    exact (canonical36659 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2623 + difference 4 5) (sourceB2623 + difference 5 4) sourceC2623) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5364) := by
    have ha : (tripleCharges (sourceA2623 + difference 4 5) (sourceB2623 + difference 5 4) sourceC2623) = raw18996 := by
      apply Matrix.ext; unfold tripleCharges sourceA2623 sourceB2623 sourceC2623 difference raw18996; decide +kernel
    rw [ha]
    exact (canonical18996 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2623 + difference 5 0) (sourceB2623 + difference 0 5) sourceC2623) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4919) := by
    have ha : (tripleCharges (sourceA2623 + difference 5 0) (sourceB2623 + difference 0 5) sourceC2623) = raw33253 := by
      apply Matrix.ext; unfold tripleCharges sourceA2623 sourceB2623 sourceC2623 difference raw33253; decide +kernel
    rw [ha]
    exact (canonical33253 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2623 + difference 5 1) (sourceB2623 + difference 1 5) sourceC2623) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4650) := by
    have ha : (tripleCharges (sourceA2623 + difference 5 1) (sourceB2623 + difference 1 5) sourceC2623) = raw36660 := by
      apply Matrix.ext; unfold tripleCharges sourceA2623 sourceB2623 sourceC2623 difference raw36660; decide +kernel
    rw [ha]
    exact (canonical36660 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2623 + difference 5 2) (sourceB2623 + difference 2 5) sourceC2623) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5119) := by
    have ha : (tripleCharges (sourceA2623 + difference 5 2) (sourceB2623 + difference 2 5) sourceC2623) = raw36661 := by
      apply Matrix.ext; unfold tripleCharges sourceA2623 sourceB2623 sourceC2623 difference raw36661; decide +kernel
    rw [ha]
    exact (canonical36661 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2623 + difference 5 3) (sourceB2623 + difference 3 5) sourceC2623) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5152) := by
    have ha : (tripleCharges (sourceA2623 + difference 5 3) (sourceB2623 + difference 3 5) sourceC2623) = raw36662 := by
      apply Matrix.ext; unfold tripleCharges sourceA2623 sourceB2623 sourceC2623 difference raw36662; decide +kernel
    rw [ha]
    exact (canonical36662 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2623 + difference 5 4) (sourceB2623 + difference 4 5) sourceC2623) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5207) := by
    have ha : (tripleCharges (sourceA2623 + difference 5 4) (sourceB2623 + difference 4 5) sourceC2623) = raw36663 := by
      apply Matrix.ext; unfold tripleCharges sourceA2623 sourceB2623 sourceC2623 difference raw36663; decide +kernel
    rw [ha]
    exact (canonical36663 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2623 sourceB2623 sourceC2623
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2623, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
