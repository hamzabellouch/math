import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical90
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical119
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical120
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical122
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical129
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical143
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical155
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical156
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical157
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical170
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical171
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical174
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical197
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical202
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical213
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical216
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical224
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical225
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical226
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical227
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical228
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical229

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA2080 : Charge := ![1, 0, 0, -1, 0, 0]
def sourceB2080 : Charge := ![2, 1, 0, 1, -1, -3]
def sourceC2080 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceForm2080 : Integer.Sparse Master := [(Sum.inr 4081, 1), (Sum.inr 4297, 1), (Sum.inr 4302, 1), (Sum.inr 4304, 1), (Sum.inr 4310, 1), (Sum.inr 4418, 1), (Sum.inr 4639, 1), (Sum.inr 4643, 1), (Sum.inr 4645, 1), (Sum.inr 4651, 1), (Sum.inr 4708, 1), (Sum.inr 4710, 1), (Sum.inr 4714, 1), (Sum.inr 4728, 1), (Sum.inr 4729, 1), (Sum.inr 4738, 1), (Sum.inr 4741, 1), (Sum.inr 4742, 1), (Sum.inr 4744, 1), (Sum.inr 4747, 1), (Sum.inr 4753, 1), (Sum.inr 4779, 1), (Sum.inr 4804, 1), (Sum.inr 4807, 1), (Sum.inr 4841, 1), (Sum.inr 5000, 1), (Sum.inr 5047, 1), (Sum.inr 5075, 1), (Sum.inr 5078, 1), (Sum.inr 5107, 1)]

theorem sourceEq2080 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2080 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2080 + difference 0 1) (sourceB2080 + difference 1 0) sourceC2080) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4742) := by
    have ha : (tripleCharges (sourceA2080 + difference 0 1) (sourceB2080 + difference 1 0) sourceC2080) = raw29176 := by
      apply Matrix.ext; unfold tripleCharges sourceA2080 sourceB2080 sourceC2080 difference raw29176; decide +kernel
    rw [ha]
    exact (canonical29176 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2080 + difference 0 2) (sourceB2080 + difference 2 0) sourceC2080) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4729) := by
    have ha : (tripleCharges (sourceA2080 + difference 0 2) (sourceB2080 + difference 2 0) sourceC2080) = raw29177 := by
      apply Matrix.ext; unfold tripleCharges sourceA2080 sourceB2080 sourceC2080 difference raw29177; decide +kernel
    rw [ha]
    exact (canonical29177 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2080 + difference 0 3) (sourceB2080 + difference 3 0) sourceC2080) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4747) := by
    have ha : (tripleCharges (sourceA2080 + difference 0 3) (sourceB2080 + difference 3 0) sourceC2080) = raw29178 := by
      apply Matrix.ext; unfold tripleCharges sourceA2080 sourceB2080 sourceC2080 difference raw29178; decide +kernel
    rw [ha]
    exact (canonical29178 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2080 + difference 0 4) (sourceB2080 + difference 4 0) sourceC2080) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA2080 + difference 0 4) (sourceB2080 + difference 4 0) sourceC2080) = raw28925 := by
      apply Matrix.ext; unfold tripleCharges sourceA2080 sourceB2080 sourceC2080 difference raw28925; decide +kernel
    rw [ha]
    exact (canonical28925 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2080 + difference 0 5) (sourceB2080 + difference 5 0) sourceC2080) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5078) := by
    have ha : (tripleCharges (sourceA2080 + difference 0 5) (sourceB2080 + difference 5 0) sourceC2080) = raw28798 := by
      apply Matrix.ext; unfold tripleCharges sourceA2080 sourceB2080 sourceC2080 difference raw28798; decide +kernel
    rw [ha]
    exact (canonical28798 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2080 + difference 1 0) (sourceB2080 + difference 0 1) sourceC2080) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4738) := by
    have ha : (tripleCharges (sourceA2080 + difference 1 0) (sourceB2080 + difference 0 1) sourceC2080) = raw28814 := by
      apply Matrix.ext; unfold tripleCharges sourceA2080 sourceB2080 sourceC2080 difference raw28814; decide +kernel
    rw [ha]
    exact (canonical28814 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2080 + difference 1 2) (sourceB2080 + difference 2 1) sourceC2080) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4728) := by
    have ha : (tripleCharges (sourceA2080 + difference 1 2) (sourceB2080 + difference 2 1) sourceC2080) = raw28816 := by
      apply Matrix.ext; unfold tripleCharges sourceA2080 sourceB2080 sourceC2080 difference raw28816; decide +kernel
    rw [ha]
    exact (canonical28816 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2080 + difference 1 3) (sourceB2080 + difference 3 1) sourceC2080) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4744) := by
    have ha : (tripleCharges (sourceA2080 + difference 1 3) (sourceB2080 + difference 3 1) sourceC2080) = raw28817 := by
      apply Matrix.ext; unfold tripleCharges sourceA2080 sourceB2080 sourceC2080 difference raw28817; decide +kernel
    rw [ha]
    exact (canonical28817 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2080 + difference 1 4) (sourceB2080 + difference 4 1) sourceC2080) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA2080 + difference 1 4) (sourceB2080 + difference 4 1) sourceC2080) = raw28681 := by
      apply Matrix.ext; unfold tripleCharges sourceA2080 sourceB2080 sourceC2080 difference raw28681; decide +kernel
    rw [ha]
    exact (canonical28681 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2080 + difference 1 5) (sourceB2080 + difference 5 1) sourceC2080) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA2080 + difference 1 5) (sourceB2080 + difference 5 1) sourceC2080) = raw27666 := by
      apply Matrix.ext; unfold tripleCharges sourceA2080 sourceB2080 sourceC2080 difference raw27666; decide +kernel
    rw [ha]
    exact (canonical27666 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2080 + difference 2 0) (sourceB2080 + difference 0 2) sourceC2080) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4708) := by
    have ha : (tripleCharges (sourceA2080 + difference 2 0) (sourceB2080 + difference 0 2) sourceC2080) = raw29179 := by
      apply Matrix.ext; unfold tripleCharges sourceA2080 sourceB2080 sourceC2080 difference raw29179; decide +kernel
    rw [ha]
    exact (canonical29179 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2080 + difference 2 1) (sourceB2080 + difference 1 2) sourceC2080) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4710) := by
    have ha : (tripleCharges (sourceA2080 + difference 2 1) (sourceB2080 + difference 1 2) sourceC2080) = raw29180 := by
      apply Matrix.ext; unfold tripleCharges sourceA2080 sourceB2080 sourceC2080 difference raw29180; decide +kernel
    rw [ha]
    exact (canonical29180 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2080 + difference 2 3) (sourceB2080 + difference 3 2) sourceC2080) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4714) := by
    have ha : (tripleCharges (sourceA2080 + difference 2 3) (sourceB2080 + difference 3 2) sourceC2080) = raw29181 := by
      apply Matrix.ext; unfold tripleCharges sourceA2080 sourceB2080 sourceC2080 difference raw29181; decide +kernel
    rw [ha]
    exact (canonical29181 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2080 + difference 2 4) (sourceB2080 + difference 4 2) sourceC2080) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4779) := by
    have ha : (tripleCharges (sourceA2080 + difference 2 4) (sourceB2080 + difference 4 2) sourceC2080) = raw28932 := by
      apply Matrix.ext; unfold tripleCharges sourceA2080 sourceB2080 sourceC2080 difference raw28932; decide +kernel
    rw [ha]
    exact (canonical28932 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2080 + difference 2 5) (sourceB2080 + difference 5 2) sourceC2080) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5047) := by
    have ha : (tripleCharges (sourceA2080 + difference 2 5) (sourceB2080 + difference 5 2) sourceC2080) = raw28807 := by
      apply Matrix.ext; unfold tripleCharges sourceA2080 sourceB2080 sourceC2080 difference raw28807; decide +kernel
    rw [ha]
    exact (canonical28807 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2080 + difference 3 0) (sourceB2080 + difference 0 3) sourceC2080) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (tripleCharges (sourceA2080 + difference 3 0) (sourceB2080 + difference 0 3) sourceC2080) = raw29182 := by
      apply Matrix.ext; unfold tripleCharges sourceA2080 sourceB2080 sourceC2080 difference raw29182; decide +kernel
    rw [ha]
    exact (canonical29182 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2080 + difference 3 1) (sourceB2080 + difference 1 3) sourceC2080) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4753) := by
    have ha : (tripleCharges (sourceA2080 + difference 3 1) (sourceB2080 + difference 1 3) sourceC2080) = raw29183 := by
      apply Matrix.ext; unfold tripleCharges sourceA2080 sourceB2080 sourceC2080 difference raw29183; decide +kernel
    rw [ha]
    exact (canonical29183 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2080 + difference 3 2) (sourceB2080 + difference 2 3) sourceC2080) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4741) := by
    have ha : (tripleCharges (sourceA2080 + difference 3 2) (sourceB2080 + difference 2 3) sourceC2080) = raw29184 := by
      apply Matrix.ext; unfold tripleCharges sourceA2080 sourceB2080 sourceC2080 difference raw29184; decide +kernel
    rw [ha]
    exact (canonical29184 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2080 + difference 3 4) (sourceB2080 + difference 4 3) sourceC2080) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4841) := by
    have ha : (tripleCharges (sourceA2080 + difference 3 4) (sourceB2080 + difference 4 3) sourceC2080) = raw28679 := by
      apply Matrix.ext; unfold tripleCharges sourceA2080 sourceB2080 sourceC2080 difference raw28679; decide +kernel
    rw [ha]
    exact (canonical28679 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2080 + difference 3 5) (sourceB2080 + difference 5 3) sourceC2080) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5107) := by
    have ha : (tripleCharges (sourceA2080 + difference 3 5) (sourceB2080 + difference 5 3) sourceC2080) = raw27664 := by
      apply Matrix.ext; unfold tripleCharges sourceA2080 sourceB2080 sourceC2080 difference raw27664; decide +kernel
    rw [ha]
    exact (canonical27664 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2080 + difference 4 0) (sourceB2080 + difference 0 4) sourceC2080) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4643) := by
    have ha : (tripleCharges (sourceA2080 + difference 4 0) (sourceB2080 + difference 0 4) sourceC2080) = raw29185 := by
      apply Matrix.ext; unfold tripleCharges sourceA2080 sourceB2080 sourceC2080 difference raw29185; decide +kernel
    rw [ha]
    exact (canonical29185 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2080 + difference 4 1) (sourceB2080 + difference 1 4) sourceC2080) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4645) := by
    have ha : (tripleCharges (sourceA2080 + difference 4 1) (sourceB2080 + difference 1 4) sourceC2080) = raw29186 := by
      apply Matrix.ext; unfold tripleCharges sourceA2080 sourceB2080 sourceC2080 difference raw29186; decide +kernel
    rw [ha]
    exact (canonical29186 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2080 + difference 4 2) (sourceB2080 + difference 2 4) sourceC2080) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4639) := by
    have ha : (tripleCharges (sourceA2080 + difference 4 2) (sourceB2080 + difference 2 4) sourceC2080) = raw29187 := by
      apply Matrix.ext; unfold tripleCharges sourceA2080 sourceB2080 sourceC2080 difference raw29187; decide +kernel
    rw [ha]
    exact (canonical29187 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2080 + difference 4 3) (sourceB2080 + difference 3 4) sourceC2080) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4651) := by
    have ha : (tripleCharges (sourceA2080 + difference 4 3) (sourceB2080 + difference 3 4) sourceC2080) = raw29188 := by
      apply Matrix.ext; unfold tripleCharges sourceA2080 sourceB2080 sourceC2080 difference raw29188; decide +kernel
    rw [ha]
    exact (canonical29188 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2080 + difference 4 5) (sourceB2080 + difference 5 4) sourceC2080) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5000) := by
    have ha : (tripleCharges (sourceA2080 + difference 4 5) (sourceB2080 + difference 5 4) sourceC2080) = raw28811 := by
      apply Matrix.ext; unfold tripleCharges sourceA2080 sourceB2080 sourceC2080 difference raw28811; decide +kernel
    rw [ha]
    exact (canonical28811 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2080 + difference 5 0) (sourceB2080 + difference 0 5) sourceC2080) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4302) := by
    have ha : (tripleCharges (sourceA2080 + difference 5 0) (sourceB2080 + difference 0 5) sourceC2080) = raw29189 := by
      apply Matrix.ext; unfold tripleCharges sourceA2080 sourceB2080 sourceC2080 difference raw29189; decide +kernel
    rw [ha]
    exact (canonical29189 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2080 + difference 5 1) (sourceB2080 + difference 1 5) sourceC2080) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4304) := by
    have ha : (tripleCharges (sourceA2080 + difference 5 1) (sourceB2080 + difference 1 5) sourceC2080) = raw29190 := by
      apply Matrix.ext; unfold tripleCharges sourceA2080 sourceB2080 sourceC2080 difference raw29190; decide +kernel
    rw [ha]
    exact (canonical29190 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2080 + difference 5 2) (sourceB2080 + difference 2 5) sourceC2080) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4297) := by
    have ha : (tripleCharges (sourceA2080 + difference 5 2) (sourceB2080 + difference 2 5) sourceC2080) = raw29191 := by
      apply Matrix.ext; unfold tripleCharges sourceA2080 sourceB2080 sourceC2080 difference raw29191; decide +kernel
    rw [ha]
    exact (canonical29191 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2080 + difference 5 3) (sourceB2080 + difference 3 5) sourceC2080) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4310) := by
    have ha : (tripleCharges (sourceA2080 + difference 5 3) (sourceB2080 + difference 3 5) sourceC2080) = raw29192 := by
      apply Matrix.ext; unfold tripleCharges sourceA2080 sourceB2080 sourceC2080 difference raw29192; decide +kernel
    rw [ha]
    exact (canonical29192 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2080 + difference 5 4) (sourceB2080 + difference 4 5) sourceC2080) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4418) := by
    have ha : (tripleCharges (sourceA2080 + difference 5 4) (sourceB2080 + difference 4 5) sourceC2080) = raw28936 := by
      apply Matrix.ext; unfold tripleCharges sourceA2080 sourceB2080 sourceC2080 difference raw28936; decide +kernel
    rw [ha]
    exact (canonical28936 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2080 sourceB2080 sourceC2080
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2080, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2081 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2081 : Charge := ![1, -1, 1, 0, -1, 0]
def sourceC2081 : Charge := ![2, 2, -1, 0, 0, -3]
def sourceForm2081 : Integer.Sparse Master := [(Sum.inr 903, 1), (Sum.inr 1788, 1), (Sum.inr 1872, 1), (Sum.inr 1954, 1), (Sum.inr 2003, 1), (Sum.inr 2007, 1), (Sum.inr 4082, -1)]

theorem sourceEq2081 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2081 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2081 + difference 0 1) (sourceB2081 + difference 1 0) sourceC2081) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2007) := by
    have ha : (tripleCharges (sourceA2081 + difference 0 1) (sourceB2081 + difference 1 0) sourceC2081) = raw29193 := by
      apply Matrix.ext; unfold tripleCharges sourceA2081 sourceB2081 sourceC2081 difference raw29193; decide +kernel
    rw [ha]
    exact (canonical29193 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2081 + difference 1 1) (sourceB2081 + difference 1 1) sourceC2081) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2003) := by
    have ha : (tripleCharges (sourceA2081 + difference 1 1) (sourceB2081 + difference 1 1) sourceC2081) = raw29194 := by
      apply Matrix.ext; unfold tripleCharges sourceA2081 sourceB2081 sourceC2081 difference raw29194; decide +kernel
    rw [ha]
    exact (canonical29194 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2081 + difference 2 1) (sourceB2081 + difference 1 2) sourceC2081) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1872) := by
    have ha : (tripleCharges (sourceA2081 + difference 2 1) (sourceB2081 + difference 1 2) sourceC2081) = raw29195 := by
      apply Matrix.ext; unfold tripleCharges sourceA2081 sourceB2081 sourceC2081 difference raw29195; decide +kernel
    rw [ha]
    exact (canonical29195 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2081 + difference 3 1) (sourceB2081 + difference 1 3) sourceC2081) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1954) := by
    have ha : (tripleCharges (sourceA2081 + difference 3 1) (sourceB2081 + difference 1 3) sourceC2081) = raw29196 := by
      apply Matrix.ext; unfold tripleCharges sourceA2081 sourceB2081 sourceC2081 difference raw29196; decide +kernel
    rw [ha]
    exact (canonical29196 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2081 + difference 4 1) (sourceB2081 + difference 1 4) sourceC2081) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1788) := by
    have ha : (tripleCharges (sourceA2081 + difference 4 1) (sourceB2081 + difference 1 4) sourceC2081) = raw29197 := by
      apply Matrix.ext; unfold tripleCharges sourceA2081 sourceB2081 sourceC2081 difference raw29197; decide +kernel
    rw [ha]
    exact (canonical29197 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2081 + difference 5 1) (sourceB2081 + difference 1 5) sourceC2081) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 903) := by
    have ha : (tripleCharges (sourceA2081 + difference 5 1) (sourceB2081 + difference 1 5) sourceC2081) = raw29198 := by
      apply Matrix.ext; unfold tripleCharges sourceA2081 sourceB2081 sourceC2081 difference raw29198; decide +kernel
    rw [ha]
    exact (canonical29198 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2081 + sourceB2081) sourceC2081) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2081 + sourceB2081) sourceC2081) = raw29199 := by
      apply Matrix.ext; unfold doubleCharges sourceA2081 sourceB2081 sourceC2081 raw29199; decide +kernel
    rw [ha]
    exact (canonical29199 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2081 sourceB2081 sourceC2081
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2081, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2082 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2082 : Charge := ![1, -1, 1, 0, -1, 0]
def sourceC2082 : Charge := ![2, 2, -1, 0, 0, -3]
def sourceForm2082 : Integer.Sparse Master := [(Sum.inr 1098, 1), (Sum.inr 1863, 1), (Sum.inr 1872, 1), (Sum.inr 1950, 1), (Sum.inr 2003, 1), (Sum.inr 2399, 1), (Sum.inr 4082, -1)]

theorem sourceEq2082 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2082 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2082 + difference 2 0) (sourceB2082 + difference 0 2) sourceC2082) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1098) := by
    have ha : (tripleCharges (sourceA2082 + difference 2 0) (sourceB2082 + difference 0 2) sourceC2082) = raw29200 := by
      apply Matrix.ext; unfold tripleCharges sourceA2082 sourceB2082 sourceC2082 difference raw29200; decide +kernel
    rw [ha]
    exact (canonical29200 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2082 + difference 2 1) (sourceB2082 + difference 1 2) sourceC2082) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1872) := by
    have ha : (tripleCharges (sourceA2082 + difference 2 1) (sourceB2082 + difference 1 2) sourceC2082) = raw29195 := by
      apply Matrix.ext; unfold tripleCharges sourceA2082 sourceB2082 sourceC2082 difference raw29195; decide +kernel
    rw [ha]
    exact (canonical29195 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2082 + difference 2 2) (sourceB2082 + difference 2 2) sourceC2082) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2003) := by
    have ha : (tripleCharges (sourceA2082 + difference 2 2) (sourceB2082 + difference 2 2) sourceC2082) = raw29194 := by
      apply Matrix.ext; unfold tripleCharges sourceA2082 sourceB2082 sourceC2082 difference raw29194; decide +kernel
    rw [ha]
    exact (canonical29194 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2082 + difference 2 3) (sourceB2082 + difference 3 2) sourceC2082) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1863) := by
    have ha : (tripleCharges (sourceA2082 + difference 2 3) (sourceB2082 + difference 3 2) sourceC2082) = raw29201 := by
      apply Matrix.ext; unfold tripleCharges sourceA2082 sourceB2082 sourceC2082 difference raw29201; decide +kernel
    rw [ha]
    exact (canonical29201 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2082 + difference 2 4) (sourceB2082 + difference 4 2) sourceC2082) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1950) := by
    have ha : (tripleCharges (sourceA2082 + difference 2 4) (sourceB2082 + difference 4 2) sourceC2082) = raw29202 := by
      apply Matrix.ext; unfold tripleCharges sourceA2082 sourceB2082 sourceC2082 difference raw29202; decide +kernel
    rw [ha]
    exact (canonical29202 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2082 + difference 2 5) (sourceB2082 + difference 5 2) sourceC2082) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2399) := by
    have ha : (tripleCharges (sourceA2082 + difference 2 5) (sourceB2082 + difference 5 2) sourceC2082) = raw29203 := by
      apply Matrix.ext; unfold tripleCharges sourceA2082 sourceB2082 sourceC2082 difference raw29203; decide +kernel
    rw [ha]
    exact (canonical29203 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2082 + sourceB2082) sourceC2082) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2082 + sourceB2082) sourceC2082) = raw29199 := by
      apply Matrix.ext; unfold doubleCharges sourceA2082 sourceB2082 sourceC2082 raw29199; decide +kernel
    rw [ha]
    exact (canonical29199 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2082 sourceB2082 sourceC2082
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2082, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2083 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2083 : Charge := ![1, -1, 1, 0, -1, 0]
def sourceC2083 : Charge := ![2, 2, -1, 0, 0, -3]
def sourceForm2083 : Integer.Sparse Master := [(Sum.inr 2003, 1), (Sum.inr 2381, 1), (Sum.inr 2387, 1), (Sum.inr 2399, 1), (Sum.inr 2670, 1), (Sum.inr 3522, 1), (Sum.inr 4082, -1)]

theorem sourceEq2083 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2083 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2083 + difference 0 5) (sourceB2083 + difference 5 0) sourceC2083) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3522) := by
    have ha : (tripleCharges (sourceA2083 + difference 0 5) (sourceB2083 + difference 5 0) sourceC2083) = raw29204 := by
      apply Matrix.ext; unfold tripleCharges sourceA2083 sourceB2083 sourceC2083 difference raw29204; decide +kernel
    rw [ha]
    exact (canonical29204 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2083 + difference 1 5) (sourceB2083 + difference 5 1) sourceC2083) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2670) := by
    have ha : (tripleCharges (sourceA2083 + difference 1 5) (sourceB2083 + difference 5 1) sourceC2083) = raw29205 := by
      apply Matrix.ext; unfold tripleCharges sourceA2083 sourceB2083 sourceC2083 difference raw29205; decide +kernel
    rw [ha]
    exact (canonical29205 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2083 + difference 2 5) (sourceB2083 + difference 5 2) sourceC2083) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2399) := by
    have ha : (tripleCharges (sourceA2083 + difference 2 5) (sourceB2083 + difference 5 2) sourceC2083) = raw29203 := by
      apply Matrix.ext; unfold tripleCharges sourceA2083 sourceB2083 sourceC2083 difference raw29203; decide +kernel
    rw [ha]
    exact (canonical29203 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2083 + difference 3 5) (sourceB2083 + difference 5 3) sourceC2083) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2381) := by
    have ha : (tripleCharges (sourceA2083 + difference 3 5) (sourceB2083 + difference 5 3) sourceC2083) = raw29206 := by
      apply Matrix.ext; unfold tripleCharges sourceA2083 sourceB2083 sourceC2083 difference raw29206; decide +kernel
    rw [ha]
    exact (canonical29206 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2083 + difference 4 5) (sourceB2083 + difference 5 4) sourceC2083) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2387) := by
    have ha : (tripleCharges (sourceA2083 + difference 4 5) (sourceB2083 + difference 5 4) sourceC2083) = raw29207 := by
      apply Matrix.ext; unfold tripleCharges sourceA2083 sourceB2083 sourceC2083 difference raw29207; decide +kernel
    rw [ha]
    exact (canonical29207 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2083 + difference 5 5) (sourceB2083 + difference 5 5) sourceC2083) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2003) := by
    have ha : (tripleCharges (sourceA2083 + difference 5 5) (sourceB2083 + difference 5 5) sourceC2083) = raw29194 := by
      apply Matrix.ext; unfold tripleCharges sourceA2083 sourceB2083 sourceC2083 difference raw29194; decide +kernel
    rw [ha]
    exact (canonical29194 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2083 + sourceB2083) sourceC2083) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2083 + sourceB2083) sourceC2083) = raw29199 := by
      apply Matrix.ext; unfold doubleCharges sourceA2083 sourceB2083 sourceC2083 raw29199; decide +kernel
    rw [ha]
    exact (canonical29199 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2083 sourceB2083 sourceC2083
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2083, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2084 : Charge := ![1, -1, 0, 0, 0, 0]
def sourceB2084 : Charge := ![2, 2, 0, 0, -1, -3]
def sourceC2084 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceForm2084 : Integer.Sparse Master := [(Sum.inr 4081, 1), (Sum.inr 4304, 2), (Sum.inr 4317, 1), (Sum.inr 4319, 1), (Sum.inr 4431, 1), (Sum.inr 4643, 2), (Sum.inr 4645, 2), (Sum.inr 4655, 1), (Sum.inr 4657, 1), (Sum.inr 4710, 2), (Sum.inr 4719, 2), (Sum.inr 4741, 2), (Sum.inr 4742, 2), (Sum.inr 4754, 1), (Sum.inr 4788, 2), (Sum.inr 4841, 1), (Sum.inr 4843, 1), (Sum.inr 5000, 2), (Sum.inr 5021, 1), (Sum.inr 5107, 1), (Sum.inr 5109, 1)]

theorem sourceEq2084 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2084 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2084 + difference 0 1) (sourceB2084 + difference 1 0) sourceC2084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4754) := by
    have ha : (tripleCharges (sourceA2084 + difference 0 1) (sourceB2084 + difference 1 0) sourceC2084) = raw29208 := by
      apply Matrix.ext; unfold tripleCharges sourceA2084 sourceB2084 sourceC2084 difference raw29208; decide +kernel
    rw [ha]
    exact (canonical29208 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2084 + difference 0 2) (sourceB2084 + difference 2 0) sourceC2084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4742) := by
    have ha : (tripleCharges (sourceA2084 + difference 0 2) (sourceB2084 + difference 2 0) sourceC2084) = raw29209 := by
      apply Matrix.ext; unfold tripleCharges sourceA2084 sourceB2084 sourceC2084 difference raw29209; decide +kernel
    rw [ha]
    exact (canonical29209 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2084 + difference 0 3) (sourceB2084 + difference 3 0) sourceC2084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4742) := by
    have ha : (tripleCharges (sourceA2084 + difference 0 3) (sourceB2084 + difference 3 0) sourceC2084) = raw29176 := by
      apply Matrix.ext; unfold tripleCharges sourceA2084 sourceB2084 sourceC2084 difference raw29176; decide +kernel
    rw [ha]
    exact (canonical29176 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2084 + difference 0 4) (sourceB2084 + difference 4 0) sourceC2084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4843) := by
    have ha : (tripleCharges (sourceA2084 + difference 0 4) (sourceB2084 + difference 4 0) sourceC2084) = raw29210 := by
      apply Matrix.ext; unfold tripleCharges sourceA2084 sourceB2084 sourceC2084 difference raw29210; decide +kernel
    rw [ha]
    exact (canonical29210 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2084 + difference 0 5) (sourceB2084 + difference 5 0) sourceC2084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5109) := by
    have ha : (tripleCharges (sourceA2084 + difference 0 5) (sourceB2084 + difference 5 0) sourceC2084) = raw29211 := by
      apply Matrix.ext; unfold tripleCharges sourceA2084 sourceB2084 sourceC2084 difference raw29211; decide +kernel
    rw [ha]
    exact (canonical29211 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2084 + difference 1 0) (sourceB2084 + difference 0 1) sourceC2084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (tripleCharges (sourceA2084 + difference 1 0) (sourceB2084 + difference 0 1) sourceC2084) = raw29182 := by
      apply Matrix.ext; unfold tripleCharges sourceA2084 sourceB2084 sourceC2084 difference raw29182; decide +kernel
    rw [ha]
    exact (canonical29182 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2084 + difference 1 2) (sourceB2084 + difference 2 1) sourceC2084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4741) := by
    have ha : (tripleCharges (sourceA2084 + difference 1 2) (sourceB2084 + difference 2 1) sourceC2084) = raw29184 := by
      apply Matrix.ext; unfold tripleCharges sourceA2084 sourceB2084 sourceC2084 difference raw29184; decide +kernel
    rw [ha]
    exact (canonical29184 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2084 + difference 1 3) (sourceB2084 + difference 3 1) sourceC2084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4741) := by
    have ha : (tripleCharges (sourceA2084 + difference 1 3) (sourceB2084 + difference 3 1) sourceC2084) = raw28815 := by
      apply Matrix.ext; unfold tripleCharges sourceA2084 sourceB2084 sourceC2084 difference raw28815; decide +kernel
    rw [ha]
    exact (canonical28815 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2084 + difference 1 4) (sourceB2084 + difference 4 1) sourceC2084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4841) := by
    have ha : (tripleCharges (sourceA2084 + difference 1 4) (sourceB2084 + difference 4 1) sourceC2084) = raw28679 := by
      apply Matrix.ext; unfold tripleCharges sourceA2084 sourceB2084 sourceC2084 difference raw28679; decide +kernel
    rw [ha]
    exact (canonical28679 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2084 + difference 1 5) (sourceB2084 + difference 5 1) sourceC2084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5107) := by
    have ha : (tripleCharges (sourceA2084 + difference 1 5) (sourceB2084 + difference 5 1) sourceC2084) = raw27664 := by
      apply Matrix.ext; unfold tripleCharges sourceA2084 sourceB2084 sourceC2084 difference raw27664; decide +kernel
    rw [ha]
    exact (canonical27664 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2084 + difference 2 0) (sourceB2084 + difference 0 2) sourceC2084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4643) := by
    have ha : (tripleCharges (sourceA2084 + difference 2 0) (sourceB2084 + difference 0 2) sourceC2084) = raw29212 := by
      apply Matrix.ext; unfold tripleCharges sourceA2084 sourceB2084 sourceC2084 difference raw29212; decide +kernel
    rw [ha]
    exact (canonical29212 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2084 + difference 2 1) (sourceB2084 + difference 1 2) sourceC2084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4719) := by
    have ha : (tripleCharges (sourceA2084 + difference 2 1) (sourceB2084 + difference 1 2) sourceC2084) = raw29213 := by
      apply Matrix.ext; unfold tripleCharges sourceA2084 sourceB2084 sourceC2084 difference raw29213; decide +kernel
    rw [ha]
    exact (canonical29213 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2084 + difference 2 3) (sourceB2084 + difference 3 2) sourceC2084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4710) := by
    have ha : (tripleCharges (sourceA2084 + difference 2 3) (sourceB2084 + difference 3 2) sourceC2084) = raw29180 := by
      apply Matrix.ext; unfold tripleCharges sourceA2084 sourceB2084 sourceC2084 difference raw29180; decide +kernel
    rw [ha]
    exact (canonical29180 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2084 + difference 2 4) (sourceB2084 + difference 4 2) sourceC2084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4788) := by
    have ha : (tripleCharges (sourceA2084 + difference 2 4) (sourceB2084 + difference 4 2) sourceC2084) = raw29214 := by
      apply Matrix.ext; unfold tripleCharges sourceA2084 sourceB2084 sourceC2084 difference raw29214; decide +kernel
    rw [ha]
    exact (canonical29214 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2084 + difference 2 5) (sourceB2084 + difference 5 2) sourceC2084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5000) := by
    have ha : (tripleCharges (sourceA2084 + difference 2 5) (sourceB2084 + difference 5 2) sourceC2084) = raw29215 := by
      apply Matrix.ext; unfold tripleCharges sourceA2084 sourceB2084 sourceC2084 difference raw29215; decide +kernel
    rw [ha]
    exact (canonical29215 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2084 + difference 3 0) (sourceB2084 + difference 0 3) sourceC2084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4643) := by
    have ha : (tripleCharges (sourceA2084 + difference 3 0) (sourceB2084 + difference 0 3) sourceC2084) = raw29216 := by
      apply Matrix.ext; unfold tripleCharges sourceA2084 sourceB2084 sourceC2084 difference raw29216; decide +kernel
    rw [ha]
    exact (canonical29216 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2084 + difference 3 1) (sourceB2084 + difference 1 3) sourceC2084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4719) := by
    have ha : (tripleCharges (sourceA2084 + difference 3 1) (sourceB2084 + difference 1 3) sourceC2084) = raw29217 := by
      apply Matrix.ext; unfold tripleCharges sourceA2084 sourceB2084 sourceC2084 difference raw29217; decide +kernel
    rw [ha]
    exact (canonical29217 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2084 + difference 3 2) (sourceB2084 + difference 2 3) sourceC2084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4710) := by
    have ha : (tripleCharges (sourceA2084 + difference 3 2) (sourceB2084 + difference 2 3) sourceC2084) = raw29218 := by
      apply Matrix.ext; unfold tripleCharges sourceA2084 sourceB2084 sourceC2084 difference raw29218; decide +kernel
    rw [ha]
    exact (canonical29218 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2084 + difference 3 4) (sourceB2084 + difference 4 3) sourceC2084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4788) := by
    have ha : (tripleCharges (sourceA2084 + difference 3 4) (sourceB2084 + difference 4 3) sourceC2084) = raw29219 := by
      apply Matrix.ext; unfold tripleCharges sourceA2084 sourceB2084 sourceC2084 difference raw29219; decide +kernel
    rw [ha]
    exact (canonical29219 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2084 + difference 3 5) (sourceB2084 + difference 5 3) sourceC2084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5000) := by
    have ha : (tripleCharges (sourceA2084 + difference 3 5) (sourceB2084 + difference 5 3) sourceC2084) = raw29220 := by
      apply Matrix.ext; unfold tripleCharges sourceA2084 sourceB2084 sourceC2084 difference raw29220; decide +kernel
    rw [ha]
    exact (canonical29220 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2084 + difference 4 0) (sourceB2084 + difference 0 4) sourceC2084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4655) := by
    have ha : (tripleCharges (sourceA2084 + difference 4 0) (sourceB2084 + difference 0 4) sourceC2084) = raw29221 := by
      apply Matrix.ext; unfold tripleCharges sourceA2084 sourceB2084 sourceC2084 difference raw29221; decide +kernel
    rw [ha]
    exact (canonical29221 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2084 + difference 4 1) (sourceB2084 + difference 1 4) sourceC2084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4657) := by
    have ha : (tripleCharges (sourceA2084 + difference 4 1) (sourceB2084 + difference 1 4) sourceC2084) = raw29222 := by
      apply Matrix.ext; unfold tripleCharges sourceA2084 sourceB2084 sourceC2084 difference raw29222; decide +kernel
    rw [ha]
    exact (canonical29222 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2084 + difference 4 2) (sourceB2084 + difference 2 4) sourceC2084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4645) := by
    have ha : (tripleCharges (sourceA2084 + difference 4 2) (sourceB2084 + difference 2 4) sourceC2084) = raw29223 := by
      apply Matrix.ext; unfold tripleCharges sourceA2084 sourceB2084 sourceC2084 difference raw29223; decide +kernel
    rw [ha]
    exact (canonical29223 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2084 + difference 4 3) (sourceB2084 + difference 3 4) sourceC2084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4645) := by
    have ha : (tripleCharges (sourceA2084 + difference 4 3) (sourceB2084 + difference 3 4) sourceC2084) = raw29186 := by
      apply Matrix.ext; unfold tripleCharges sourceA2084 sourceB2084 sourceC2084 difference raw29186; decide +kernel
    rw [ha]
    exact (canonical29186 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2084 + difference 4 5) (sourceB2084 + difference 5 4) sourceC2084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5021) := by
    have ha : (tripleCharges (sourceA2084 + difference 4 5) (sourceB2084 + difference 5 4) sourceC2084) = raw29224 := by
      apply Matrix.ext; unfold tripleCharges sourceA2084 sourceB2084 sourceC2084 difference raw29224; decide +kernel
    rw [ha]
    exact (canonical29224 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2084 + difference 5 0) (sourceB2084 + difference 0 5) sourceC2084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4317) := by
    have ha : (tripleCharges (sourceA2084 + difference 5 0) (sourceB2084 + difference 0 5) sourceC2084) = raw29225 := by
      apply Matrix.ext; unfold tripleCharges sourceA2084 sourceB2084 sourceC2084 difference raw29225; decide +kernel
    rw [ha]
    exact (canonical29225 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2084 + difference 5 1) (sourceB2084 + difference 1 5) sourceC2084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4319) := by
    have ha : (tripleCharges (sourceA2084 + difference 5 1) (sourceB2084 + difference 1 5) sourceC2084) = raw29226 := by
      apply Matrix.ext; unfold tripleCharges sourceA2084 sourceB2084 sourceC2084 difference raw29226; decide +kernel
    rw [ha]
    exact (canonical29226 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2084 + difference 5 2) (sourceB2084 + difference 2 5) sourceC2084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4304) := by
    have ha : (tripleCharges (sourceA2084 + difference 5 2) (sourceB2084 + difference 2 5) sourceC2084) = raw29227 := by
      apply Matrix.ext; unfold tripleCharges sourceA2084 sourceB2084 sourceC2084 difference raw29227; decide +kernel
    rw [ha]
    exact (canonical29227 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2084 + difference 5 3) (sourceB2084 + difference 3 5) sourceC2084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4304) := by
    have ha : (tripleCharges (sourceA2084 + difference 5 3) (sourceB2084 + difference 3 5) sourceC2084) = raw29190 := by
      apply Matrix.ext; unfold tripleCharges sourceA2084 sourceB2084 sourceC2084 difference raw29190; decide +kernel
    rw [ha]
    exact (canonical29190 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2084 + difference 5 4) (sourceB2084 + difference 4 5) sourceC2084) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4431) := by
    have ha : (tripleCharges (sourceA2084 + difference 5 4) (sourceB2084 + difference 4 5) sourceC2084) = raw29228 := by
      apply Matrix.ext; unfold tripleCharges sourceA2084 sourceB2084 sourceC2084 difference raw29228; decide +kernel
    rw [ha]
    exact (canonical29228 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2084 sourceB2084 sourceC2084
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2084, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2085 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2085 : Charge := ![0, 1, 0, 0, -1, 0]
def sourceC2085 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceForm2085 : Integer.Sparse Master := [(Sum.inr 4085, 1), (Sum.inr 4343, 4), (Sum.inr 4350, 1), (Sum.inr 4359, 2), (Sum.inr 4501, 2), (Sum.inr 4678, 4), (Sum.inr 4691, 1), (Sum.inr 4759, 2), (Sum.inr 4832, 4), (Sum.inr 4837, 4), (Sum.inr 4845, 2), (Sum.inr 4897, 2), (Sum.inr 5261, 1)]

theorem sourceEq2085 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2085 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2085 + difference 0 1) (sourceB2085 + difference 1 0) sourceC2085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4845) := by
    have ha : (tripleCharges (sourceA2085 + difference 0 1) (sourceB2085 + difference 1 0) sourceC2085) = raw29229 := by
      apply Matrix.ext; unfold tripleCharges sourceA2085 sourceB2085 sourceC2085 difference raw29229; decide +kernel
    rw [ha]
    exact (canonical29229 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2085 + difference 0 2) (sourceB2085 + difference 2 0) sourceC2085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4832) := by
    have ha : (tripleCharges (sourceA2085 + difference 0 2) (sourceB2085 + difference 2 0) sourceC2085) = raw29230 := by
      apply Matrix.ext; unfold tripleCharges sourceA2085 sourceB2085 sourceC2085 difference raw29230; decide +kernel
    rw [ha]
    exact (canonical29230 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2085 + difference 0 3) (sourceB2085 + difference 3 0) sourceC2085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4832) := by
    have ha : (tripleCharges (sourceA2085 + difference 0 3) (sourceB2085 + difference 3 0) sourceC2085) = raw29231 := by
      apply Matrix.ext; unfold tripleCharges sourceA2085 sourceB2085 sourceC2085 difference raw29231; decide +kernel
    rw [ha]
    exact (canonical29231 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2085 + difference 0 4) (sourceB2085 + difference 4 0) sourceC2085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4897) := by
    have ha : (tripleCharges (sourceA2085 + difference 0 4) (sourceB2085 + difference 4 0) sourceC2085) = raw29232 := by
      apply Matrix.ext; unfold tripleCharges sourceA2085 sourceB2085 sourceC2085 difference raw29232; decide +kernel
    rw [ha]
    exact (canonical29232 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2085 + difference 0 5) (sourceB2085 + difference 5 0) sourceC2085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5261) := by
    have ha : (tripleCharges (sourceA2085 + difference 0 5) (sourceB2085 + difference 5 0) sourceC2085) = raw29233 := by
      apply Matrix.ext; unfold tripleCharges sourceA2085 sourceB2085 sourceC2085 difference raw29233; decide +kernel
    rw [ha]
    exact (canonical29233 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2085 + difference 1 0) (sourceB2085 + difference 0 1) sourceC2085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4501) := by
    have ha : (tripleCharges (sourceA2085 + difference 1 0) (sourceB2085 + difference 0 1) sourceC2085) = raw19911 := by
      apply Matrix.ext; unfold tripleCharges sourceA2085 sourceB2085 sourceC2085 difference raw19911; decide +kernel
    rw [ha]
    exact (canonical19911 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2085 + difference 1 2) (sourceB2085 + difference 2 1) sourceC2085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4837) := by
    have ha : (tripleCharges (sourceA2085 + difference 1 2) (sourceB2085 + difference 2 1) sourceC2085) = raw21832 := by
      apply Matrix.ext; unfold tripleCharges sourceA2085 sourceB2085 sourceC2085 difference raw21832; decide +kernel
    rw [ha]
    exact (canonical21832 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2085 + difference 1 3) (sourceB2085 + difference 3 1) sourceC2085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4837) := by
    have ha : (tripleCharges (sourceA2085 + difference 1 3) (sourceB2085 + difference 3 1) sourceC2085) = raw21833 := by
      apply Matrix.ext; unfold tripleCharges sourceA2085 sourceB2085 sourceC2085 difference raw21833; decide +kernel
    rw [ha]
    exact (canonical21833 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2085 + difference 1 4) (sourceB2085 + difference 4 1) sourceC2085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (tripleCharges (sourceA2085 + difference 1 4) (sourceB2085 + difference 4 1) sourceC2085) = raw19891 := by
      apply Matrix.ext; unfold tripleCharges sourceA2085 sourceB2085 sourceC2085 difference raw19891; decide +kernel
    rw [ha]
    exact (canonical19891 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2085 + difference 1 5) (sourceB2085 + difference 5 1) sourceC2085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4897) := by
    have ha : (tripleCharges (sourceA2085 + difference 1 5) (sourceB2085 + difference 5 1) sourceC2085) = raw21834 := by
      apply Matrix.ext; unfold tripleCharges sourceA2085 sourceB2085 sourceC2085 difference raw21834; decide +kernel
    rw [ha]
    exact (canonical21834 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2085 + difference 2 0) (sourceB2085 + difference 0 2) sourceC2085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4343) := by
    have ha : (tripleCharges (sourceA2085 + difference 2 0) (sourceB2085 + difference 0 2) sourceC2085) = raw21840 := by
      apply Matrix.ext; unfold tripleCharges sourceA2085 sourceB2085 sourceC2085 difference raw21840; decide +kernel
    rw [ha]
    exact (canonical21840 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2085 + difference 2 1) (sourceB2085 + difference 1 2) sourceC2085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4678) := by
    have ha : (tripleCharges (sourceA2085 + difference 2 1) (sourceB2085 + difference 1 2) sourceC2085) = raw29234 := by
      apply Matrix.ext; unfold tripleCharges sourceA2085 sourceB2085 sourceC2085 difference raw29234; decide +kernel
    rw [ha]
    exact (canonical29234 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2085 + difference 2 3) (sourceB2085 + difference 3 2) sourceC2085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4759) := by
    have ha : (tripleCharges (sourceA2085 + difference 2 3) (sourceB2085 + difference 3 2) sourceC2085) = raw29235 := by
      apply Matrix.ext; unfold tripleCharges sourceA2085 sourceB2085 sourceC2085 difference raw29235; decide +kernel
    rw [ha]
    exact (canonical29235 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2085 + difference 2 4) (sourceB2085 + difference 4 2) sourceC2085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4837) := by
    have ha : (tripleCharges (sourceA2085 + difference 2 4) (sourceB2085 + difference 4 2) sourceC2085) = raw29236 := by
      apply Matrix.ext; unfold tripleCharges sourceA2085 sourceB2085 sourceC2085 difference raw29236; decide +kernel
    rw [ha]
    exact (canonical29236 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2085 + difference 2 5) (sourceB2085 + difference 5 2) sourceC2085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4832) := by
    have ha : (tripleCharges (sourceA2085 + difference 2 5) (sourceB2085 + difference 5 2) sourceC2085) = raw29237 := by
      apply Matrix.ext; unfold tripleCharges sourceA2085 sourceB2085 sourceC2085 difference raw29237; decide +kernel
    rw [ha]
    exact (canonical29237 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2085 + difference 3 0) (sourceB2085 + difference 0 3) sourceC2085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4343) := by
    have ha : (tripleCharges (sourceA2085 + difference 3 0) (sourceB2085 + difference 0 3) sourceC2085) = raw21844 := by
      apply Matrix.ext; unfold tripleCharges sourceA2085 sourceB2085 sourceC2085 difference raw21844; decide +kernel
    rw [ha]
    exact (canonical21844 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2085 + difference 3 1) (sourceB2085 + difference 1 3) sourceC2085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4678) := by
    have ha : (tripleCharges (sourceA2085 + difference 3 1) (sourceB2085 + difference 1 3) sourceC2085) = raw29238 := by
      apply Matrix.ext; unfold tripleCharges sourceA2085 sourceB2085 sourceC2085 difference raw29238; decide +kernel
    rw [ha]
    exact (canonical29238 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2085 + difference 3 2) (sourceB2085 + difference 2 3) sourceC2085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4759) := by
    have ha : (tripleCharges (sourceA2085 + difference 3 2) (sourceB2085 + difference 2 3) sourceC2085) = raw29239 := by
      apply Matrix.ext; unfold tripleCharges sourceA2085 sourceB2085 sourceC2085 difference raw29239; decide +kernel
    rw [ha]
    exact (canonical29239 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2085 + difference 3 4) (sourceB2085 + difference 4 3) sourceC2085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4837) := by
    have ha : (tripleCharges (sourceA2085 + difference 3 4) (sourceB2085 + difference 4 3) sourceC2085) = raw29240 := by
      apply Matrix.ext; unfold tripleCharges sourceA2085 sourceB2085 sourceC2085 difference raw29240; decide +kernel
    rw [ha]
    exact (canonical29240 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2085 + difference 3 5) (sourceB2085 + difference 5 3) sourceC2085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4832) := by
    have ha : (tripleCharges (sourceA2085 + difference 3 5) (sourceB2085 + difference 5 3) sourceC2085) = raw25922 := by
      apply Matrix.ext; unfold tripleCharges sourceA2085 sourceB2085 sourceC2085 difference raw25922; decide +kernel
    rw [ha]
    exact (canonical25922 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2085 + difference 4 0) (sourceB2085 + difference 0 4) sourceC2085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4359) := by
    have ha : (tripleCharges (sourceA2085 + difference 4 0) (sourceB2085 + difference 0 4) sourceC2085) = raw21848 := by
      apply Matrix.ext; unfold tripleCharges sourceA2085 sourceB2085 sourceC2085 difference raw21848; decide +kernel
    rw [ha]
    exact (canonical21848 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2085 + difference 4 1) (sourceB2085 + difference 1 4) sourceC2085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4691) := by
    have ha : (tripleCharges (sourceA2085 + difference 4 1) (sourceB2085 + difference 1 4) sourceC2085) = raw29241 := by
      apply Matrix.ext; unfold tripleCharges sourceA2085 sourceB2085 sourceC2085 difference raw29241; decide +kernel
    rw [ha]
    exact (canonical29241 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2085 + difference 4 2) (sourceB2085 + difference 2 4) sourceC2085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4678) := by
    have ha : (tripleCharges (sourceA2085 + difference 4 2) (sourceB2085 + difference 2 4) sourceC2085) = raw29242 := by
      apply Matrix.ext; unfold tripleCharges sourceA2085 sourceB2085 sourceC2085 difference raw29242; decide +kernel
    rw [ha]
    exact (canonical29242 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2085 + difference 4 3) (sourceB2085 + difference 3 4) sourceC2085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4678) := by
    have ha : (tripleCharges (sourceA2085 + difference 4 3) (sourceB2085 + difference 3 4) sourceC2085) = raw29243 := by
      apply Matrix.ext; unfold tripleCharges sourceA2085 sourceB2085 sourceC2085 difference raw29243; decide +kernel
    rw [ha]
    exact (canonical29243 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2085 + difference 4 5) (sourceB2085 + difference 5 4) sourceC2085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4845) := by
    have ha : (tripleCharges (sourceA2085 + difference 4 5) (sourceB2085 + difference 5 4) sourceC2085) = raw29244 := by
      apply Matrix.ext; unfold tripleCharges sourceA2085 sourceB2085 sourceC2085 difference raw29244; decide +kernel
    rw [ha]
    exact (canonical29244 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2085 + difference 5 0) (sourceB2085 + difference 0 5) sourceC2085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4350) := by
    have ha : (tripleCharges (sourceA2085 + difference 5 0) (sourceB2085 + difference 0 5) sourceC2085) = raw19908 := by
      apply Matrix.ext; unfold tripleCharges sourceA2085 sourceB2085 sourceC2085 difference raw19908; decide +kernel
    rw [ha]
    exact (canonical19908 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2085 + difference 5 1) (sourceB2085 + difference 1 5) sourceC2085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4359) := by
    have ha : (tripleCharges (sourceA2085 + difference 5 1) (sourceB2085 + difference 1 5) sourceC2085) = raw29245 := by
      apply Matrix.ext; unfold tripleCharges sourceA2085 sourceB2085 sourceC2085 difference raw29245; decide +kernel
    rw [ha]
    exact (canonical29245 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2085 + difference 5 2) (sourceB2085 + difference 2 5) sourceC2085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4343) := by
    have ha : (tripleCharges (sourceA2085 + difference 5 2) (sourceB2085 + difference 2 5) sourceC2085) = raw29246 := by
      apply Matrix.ext; unfold tripleCharges sourceA2085 sourceB2085 sourceC2085 difference raw29246; decide +kernel
    rw [ha]
    exact (canonical29246 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2085 + difference 5 3) (sourceB2085 + difference 3 5) sourceC2085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4343) := by
    have ha : (tripleCharges (sourceA2085 + difference 5 3) (sourceB2085 + difference 3 5) sourceC2085) = raw29247 := by
      apply Matrix.ext; unfold tripleCharges sourceA2085 sourceB2085 sourceC2085 difference raw29247; decide +kernel
    rw [ha]
    exact (canonical29247 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2085 + difference 5 4) (sourceB2085 + difference 4 5) sourceC2085) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4501) := by
    have ha : (tripleCharges (sourceA2085 + difference 5 4) (sourceB2085 + difference 4 5) sourceC2085) = raw19887 := by
      apply Matrix.ext; unfold tripleCharges sourceA2085 sourceB2085 sourceC2085 difference raw19887; decide +kernel
    rw [ha]
    exact (canonical19887 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2085 sourceB2085 sourceC2085
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2085, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2086 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2086 : Charge := ![0, 1, 0, 0, -1, 0]
def sourceC2086 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceForm2086 : Integer.Sparse Master := [(Sum.inr 1666, 4), (Sum.inr 1677, 1), (Sum.inr 1683, 2), (Sum.inr 1730, 2), (Sum.inr 2143, 4), (Sum.inr 2159, 1), (Sum.inr 2170, 2), (Sum.inr 2193, 4), (Sum.inr 2208, 4), (Sum.inr 2218, 2), (Sum.inr 2268, 2), (Sum.inr 2726, 1), (Sum.inr 4085, 1)]

theorem sourceEq2086 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2086 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2086 + difference 0 1) (sourceB2086 + difference 1 0) sourceC2086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2218) := by
    have ha : (tripleCharges (sourceA2086 + difference 0 1) (sourceB2086 + difference 1 0) sourceC2086) = raw29248 := by
      apply Matrix.ext; unfold tripleCharges sourceA2086 sourceB2086 sourceC2086 difference raw29248; decide +kernel
    rw [ha]
    exact (canonical29248 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2086 + difference 0 2) (sourceB2086 + difference 2 0) sourceC2086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2193) := by
    have ha : (tripleCharges (sourceA2086 + difference 0 2) (sourceB2086 + difference 2 0) sourceC2086) = raw29249 := by
      apply Matrix.ext; unfold tripleCharges sourceA2086 sourceB2086 sourceC2086 difference raw29249; decide +kernel
    rw [ha]
    exact (canonical29249 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2086 + difference 0 3) (sourceB2086 + difference 3 0) sourceC2086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2193) := by
    have ha : (tripleCharges (sourceA2086 + difference 0 3) (sourceB2086 + difference 3 0) sourceC2086) = raw29250 := by
      apply Matrix.ext; unfold tripleCharges sourceA2086 sourceB2086 sourceC2086 difference raw29250; decide +kernel
    rw [ha]
    exact (canonical29250 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2086 + difference 0 4) (sourceB2086 + difference 4 0) sourceC2086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2268) := by
    have ha : (tripleCharges (sourceA2086 + difference 0 4) (sourceB2086 + difference 4 0) sourceC2086) = raw29251 := by
      apply Matrix.ext; unfold tripleCharges sourceA2086 sourceB2086 sourceC2086 difference raw29251; decide +kernel
    rw [ha]
    exact (canonical29251 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2086 + difference 0 5) (sourceB2086 + difference 5 0) sourceC2086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2726) := by
    have ha : (tripleCharges (sourceA2086 + difference 0 5) (sourceB2086 + difference 5 0) sourceC2086) = raw29252 := by
      apply Matrix.ext; unfold tripleCharges sourceA2086 sourceB2086 sourceC2086 difference raw29252; decide +kernel
    rw [ha]
    exact (canonical29252 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2086 + difference 1 0) (sourceB2086 + difference 0 1) sourceC2086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1730) := by
    have ha : (tripleCharges (sourceA2086 + difference 1 0) (sourceB2086 + difference 0 1) sourceC2086) = raw19941 := by
      apply Matrix.ext; unfold tripleCharges sourceA2086 sourceB2086 sourceC2086 difference raw19941; decide +kernel
    rw [ha]
    exact (canonical19941 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2086 + difference 1 2) (sourceB2086 + difference 2 1) sourceC2086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2208) := by
    have ha : (tripleCharges (sourceA2086 + difference 1 2) (sourceB2086 + difference 2 1) sourceC2086) = raw21854 := by
      apply Matrix.ext; unfold tripleCharges sourceA2086 sourceB2086 sourceC2086 difference raw21854; decide +kernel
    rw [ha]
    exact (canonical21854 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2086 + difference 1 3) (sourceB2086 + difference 3 1) sourceC2086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2208) := by
    have ha : (tripleCharges (sourceA2086 + difference 1 3) (sourceB2086 + difference 3 1) sourceC2086) = raw21855 := by
      apply Matrix.ext; unfold tripleCharges sourceA2086 sourceB2086 sourceC2086 difference raw21855; decide +kernel
    rw [ha]
    exact (canonical21855 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2086 + difference 1 4) (sourceB2086 + difference 4 1) sourceC2086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (tripleCharges (sourceA2086 + difference 1 4) (sourceB2086 + difference 4 1) sourceC2086) = raw19921 := by
      apply Matrix.ext; unfold tripleCharges sourceA2086 sourceB2086 sourceC2086 difference raw19921; decide +kernel
    rw [ha]
    exact (canonical19921 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2086 + difference 1 5) (sourceB2086 + difference 5 1) sourceC2086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2268) := by
    have ha : (tripleCharges (sourceA2086 + difference 1 5) (sourceB2086 + difference 5 1) sourceC2086) = raw21856 := by
      apply Matrix.ext; unfold tripleCharges sourceA2086 sourceB2086 sourceC2086 difference raw21856; decide +kernel
    rw [ha]
    exact (canonical21856 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2086 + difference 2 0) (sourceB2086 + difference 0 2) sourceC2086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1666) := by
    have ha : (tripleCharges (sourceA2086 + difference 2 0) (sourceB2086 + difference 0 2) sourceC2086) = raw21862 := by
      apply Matrix.ext; unfold tripleCharges sourceA2086 sourceB2086 sourceC2086 difference raw21862; decide +kernel
    rw [ha]
    exact (canonical21862 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2086 + difference 2 1) (sourceB2086 + difference 1 2) sourceC2086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2143) := by
    have ha : (tripleCharges (sourceA2086 + difference 2 1) (sourceB2086 + difference 1 2) sourceC2086) = raw29253 := by
      apply Matrix.ext; unfold tripleCharges sourceA2086 sourceB2086 sourceC2086 difference raw29253; decide +kernel
    rw [ha]
    exact (canonical29253 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2086 + difference 2 3) (sourceB2086 + difference 3 2) sourceC2086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2170) := by
    have ha : (tripleCharges (sourceA2086 + difference 2 3) (sourceB2086 + difference 3 2) sourceC2086) = raw29254 := by
      apply Matrix.ext; unfold tripleCharges sourceA2086 sourceB2086 sourceC2086 difference raw29254; decide +kernel
    rw [ha]
    exact (canonical29254 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2086 + difference 2 4) (sourceB2086 + difference 4 2) sourceC2086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2208) := by
    have ha : (tripleCharges (sourceA2086 + difference 2 4) (sourceB2086 + difference 4 2) sourceC2086) = raw29255 := by
      apply Matrix.ext; unfold tripleCharges sourceA2086 sourceB2086 sourceC2086 difference raw29255; decide +kernel
    rw [ha]
    exact (canonical29255 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2086 + difference 2 5) (sourceB2086 + difference 5 2) sourceC2086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2193) := by
    have ha : (tripleCharges (sourceA2086 + difference 2 5) (sourceB2086 + difference 5 2) sourceC2086) = raw29256 := by
      apply Matrix.ext; unfold tripleCharges sourceA2086 sourceB2086 sourceC2086 difference raw29256; decide +kernel
    rw [ha]
    exact (canonical29256 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2086 + difference 3 0) (sourceB2086 + difference 0 3) sourceC2086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1666) := by
    have ha : (tripleCharges (sourceA2086 + difference 3 0) (sourceB2086 + difference 0 3) sourceC2086) = raw21866 := by
      apply Matrix.ext; unfold tripleCharges sourceA2086 sourceB2086 sourceC2086 difference raw21866; decide +kernel
    rw [ha]
    exact (canonical21866 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2086 + difference 3 1) (sourceB2086 + difference 1 3) sourceC2086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2143) := by
    have ha : (tripleCharges (sourceA2086 + difference 3 1) (sourceB2086 + difference 1 3) sourceC2086) = raw29257 := by
      apply Matrix.ext; unfold tripleCharges sourceA2086 sourceB2086 sourceC2086 difference raw29257; decide +kernel
    rw [ha]
    exact (canonical29257 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2086 + difference 3 2) (sourceB2086 + difference 2 3) sourceC2086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2170) := by
    have ha : (tripleCharges (sourceA2086 + difference 3 2) (sourceB2086 + difference 2 3) sourceC2086) = raw29258 := by
      apply Matrix.ext; unfold tripleCharges sourceA2086 sourceB2086 sourceC2086 difference raw29258; decide +kernel
    rw [ha]
    exact (canonical29258 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2086 + difference 3 4) (sourceB2086 + difference 4 3) sourceC2086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2208) := by
    have ha : (tripleCharges (sourceA2086 + difference 3 4) (sourceB2086 + difference 4 3) sourceC2086) = raw29259 := by
      apply Matrix.ext; unfold tripleCharges sourceA2086 sourceB2086 sourceC2086 difference raw29259; decide +kernel
    rw [ha]
    exact (canonical29259 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2086 + difference 3 5) (sourceB2086 + difference 5 3) sourceC2086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2193) := by
    have ha : (tripleCharges (sourceA2086 + difference 3 5) (sourceB2086 + difference 5 3) sourceC2086) = raw25973 := by
      apply Matrix.ext; unfold tripleCharges sourceA2086 sourceB2086 sourceC2086 difference raw25973; decide +kernel
    rw [ha]
    exact (canonical25973 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2086 + difference 4 0) (sourceB2086 + difference 0 4) sourceC2086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1683) := by
    have ha : (tripleCharges (sourceA2086 + difference 4 0) (sourceB2086 + difference 0 4) sourceC2086) = raw21870 := by
      apply Matrix.ext; unfold tripleCharges sourceA2086 sourceB2086 sourceC2086 difference raw21870; decide +kernel
    rw [ha]
    exact (canonical21870 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2086 + difference 4 1) (sourceB2086 + difference 1 4) sourceC2086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2159) := by
    have ha : (tripleCharges (sourceA2086 + difference 4 1) (sourceB2086 + difference 1 4) sourceC2086) = raw29260 := by
      apply Matrix.ext; unfold tripleCharges sourceA2086 sourceB2086 sourceC2086 difference raw29260; decide +kernel
    rw [ha]
    exact (canonical29260 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2086 + difference 4 2) (sourceB2086 + difference 2 4) sourceC2086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2143) := by
    have ha : (tripleCharges (sourceA2086 + difference 4 2) (sourceB2086 + difference 2 4) sourceC2086) = raw29261 := by
      apply Matrix.ext; unfold tripleCharges sourceA2086 sourceB2086 sourceC2086 difference raw29261; decide +kernel
    rw [ha]
    exact (canonical29261 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2086 + difference 4 3) (sourceB2086 + difference 3 4) sourceC2086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2143) := by
    have ha : (tripleCharges (sourceA2086 + difference 4 3) (sourceB2086 + difference 3 4) sourceC2086) = raw29262 := by
      apply Matrix.ext; unfold tripleCharges sourceA2086 sourceB2086 sourceC2086 difference raw29262; decide +kernel
    rw [ha]
    exact (canonical29262 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2086 + difference 4 5) (sourceB2086 + difference 5 4) sourceC2086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2218) := by
    have ha : (tripleCharges (sourceA2086 + difference 4 5) (sourceB2086 + difference 5 4) sourceC2086) = raw29263 := by
      apply Matrix.ext; unfold tripleCharges sourceA2086 sourceB2086 sourceC2086 difference raw29263; decide +kernel
    rw [ha]
    exact (canonical29263 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2086 + difference 5 0) (sourceB2086 + difference 0 5) sourceC2086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1677) := by
    have ha : (tripleCharges (sourceA2086 + difference 5 0) (sourceB2086 + difference 0 5) sourceC2086) = raw19938 := by
      apply Matrix.ext; unfold tripleCharges sourceA2086 sourceB2086 sourceC2086 difference raw19938; decide +kernel
    rw [ha]
    exact (canonical19938 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2086 + difference 5 1) (sourceB2086 + difference 1 5) sourceC2086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1683) := by
    have ha : (tripleCharges (sourceA2086 + difference 5 1) (sourceB2086 + difference 1 5) sourceC2086) = raw29264 := by
      apply Matrix.ext; unfold tripleCharges sourceA2086 sourceB2086 sourceC2086 difference raw29264; decide +kernel
    rw [ha]
    exact (canonical29264 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2086 + difference 5 2) (sourceB2086 + difference 2 5) sourceC2086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1666) := by
    have ha : (tripleCharges (sourceA2086 + difference 5 2) (sourceB2086 + difference 2 5) sourceC2086) = raw29265 := by
      apply Matrix.ext; unfold tripleCharges sourceA2086 sourceB2086 sourceC2086 difference raw29265; decide +kernel
    rw [ha]
    exact (canonical29265 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2086 + difference 5 3) (sourceB2086 + difference 3 5) sourceC2086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1666) := by
    have ha : (tripleCharges (sourceA2086 + difference 5 3) (sourceB2086 + difference 3 5) sourceC2086) = raw29266 := by
      apply Matrix.ext; unfold tripleCharges sourceA2086 sourceB2086 sourceC2086 difference raw29266; decide +kernel
    rw [ha]
    exact (canonical29266 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2086 + difference 5 4) (sourceB2086 + difference 4 5) sourceC2086) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1730) := by
    have ha : (tripleCharges (sourceA2086 + difference 5 4) (sourceB2086 + difference 4 5) sourceC2086) = raw19917 := by
      apply Matrix.ext; unfold tripleCharges sourceA2086 sourceB2086 sourceC2086 difference raw19917; decide +kernel
    rw [ha]
    exact (canonical19917 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2086 sourceB2086 sourceC2086
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2086, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2087 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2087 : Charge := ![0, 1, 0, 0, -1, 0]
def sourceC2087 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceForm2087 : Integer.Sparse Master := [(Sum.inr 937, 1), (Sum.inr 1804, 2), (Sum.inr 1817, 1), (Sum.inr 2056, 1), (Sum.inr 2065, 1), (Sum.inr 4085, -1)]

theorem sourceEq2087 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2087 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2087 + difference 0 1) (sourceB2087 + difference 1 0) sourceC2087) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2065) := by
    have ha : (tripleCharges (sourceA2087 + difference 0 1) (sourceB2087 + difference 1 0) sourceC2087) = raw29267 := by
      apply Matrix.ext; unfold tripleCharges sourceA2087 sourceB2087 sourceC2087 difference raw29267; decide +kernel
    rw [ha]
    exact (canonical29267 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2087 + difference 1 1) (sourceB2087 + difference 1 1) sourceC2087) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2056) := by
    have ha : (tripleCharges (sourceA2087 + difference 1 1) (sourceB2087 + difference 1 1) sourceC2087) = raw29268 := by
      apply Matrix.ext; unfold tripleCharges sourceA2087 sourceB2087 sourceC2087 difference raw29268; decide +kernel
    rw [ha]
    exact (canonical29268 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2087 + difference 2 1) (sourceB2087 + difference 1 2) sourceC2087) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1804) := by
    have ha : (tripleCharges (sourceA2087 + difference 2 1) (sourceB2087 + difference 1 2) sourceC2087) = raw29269 := by
      apply Matrix.ext; unfold tripleCharges sourceA2087 sourceB2087 sourceC2087 difference raw29269; decide +kernel
    rw [ha]
    exact (canonical29269 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2087 + difference 3 1) (sourceB2087 + difference 1 3) sourceC2087) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1804) := by
    have ha : (tripleCharges (sourceA2087 + difference 3 1) (sourceB2087 + difference 1 3) sourceC2087) = raw29270 := by
      apply Matrix.ext; unfold tripleCharges sourceA2087 sourceB2087 sourceC2087 difference raw29270; decide +kernel
    rw [ha]
    exact (canonical29270 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2087 + difference 4 1) (sourceB2087 + difference 1 4) sourceC2087) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1817) := by
    have ha : (tripleCharges (sourceA2087 + difference 4 1) (sourceB2087 + difference 1 4) sourceC2087) = raw29271 := by
      apply Matrix.ext; unfold tripleCharges sourceA2087 sourceB2087 sourceC2087 difference raw29271; decide +kernel
    rw [ha]
    exact (canonical29271 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2087 + difference 5 1) (sourceB2087 + difference 1 5) sourceC2087) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 937) := by
    have ha : (tripleCharges (sourceA2087 + difference 5 1) (sourceB2087 + difference 1 5) sourceC2087) = raw29272 := by
      apply Matrix.ext; unfold tripleCharges sourceA2087 sourceB2087 sourceC2087 difference raw29272; decide +kernel
    rw [ha]
    exact (canonical29272 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2087 + sourceB2087) sourceC2087) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA2087 + sourceB2087) sourceC2087) = raw19953 := by
      apply Matrix.ext; unfold doubleCharges sourceA2087 sourceB2087 sourceC2087 raw19953; decide +kernel
    rw [ha]
    exact (canonical19953 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2087 sourceB2087 sourceC2087
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2087, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2088 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2088 : Charge := ![0, 1, 0, -1, 0, 0]
def sourceC2088 : Charge := ![3, 0, 0, 1, -1, -3]
def sourceForm2088 : Integer.Sparse Master := [(Sum.inr 4081, 1), (Sum.inr 4286, 1), (Sum.inr 4289, 1), (Sum.inr 4294, 1), (Sum.inr 4302, 1), (Sum.inr 4320, 1), (Sum.inr 4324, 1), (Sum.inr 4338, 1), (Sum.inr 4398, 1), (Sum.inr 4426, 1), (Sum.inr 4630, 1), (Sum.inr 4636, 1), (Sum.inr 4643, 1), (Sum.inr 4658, 1), (Sum.inr 4673, 1), (Sum.inr 4708, 1), (Sum.inr 4720, 1), (Sum.inr 4728, 1), (Sum.inr 4738, 1), (Sum.inr 4741, 1), (Sum.inr 4744, 1), (Sum.inr 4778, 1), (Sum.inr 4779, 1), (Sum.inr 4788, 1), (Sum.inr 4800, 1), (Sum.inr 4804, 1), (Sum.inr 4827, 1), (Sum.inr 4837, 1), (Sum.inr 4841, 1), (Sum.inr 5075, 1)]

theorem sourceEq2088 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2088 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2088 + difference 0 1) (sourceB2088 + difference 1 0) sourceC2088) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4744) := by
    have ha : (tripleCharges (sourceA2088 + difference 0 1) (sourceB2088 + difference 1 0) sourceC2088) = raw29273 := by
      apply Matrix.ext; unfold tripleCharges sourceA2088 sourceB2088 sourceC2088 difference raw29273; decide +kernel
    rw [ha]
    exact (canonical29273 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2088 + difference 0 2) (sourceB2088 + difference 2 0) sourceC2088) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4728) := by
    have ha : (tripleCharges (sourceA2088 + difference 0 2) (sourceB2088 + difference 2 0) sourceC2088) = raw29274 := by
      apply Matrix.ext; unfold tripleCharges sourceA2088 sourceB2088 sourceC2088 difference raw29274; decide +kernel
    rw [ha]
    exact (canonical29274 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2088 + difference 0 3) (sourceB2088 + difference 3 0) sourceC2088) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4741) := by
    have ha : (tripleCharges (sourceA2088 + difference 0 3) (sourceB2088 + difference 3 0) sourceC2088) = raw29275 := by
      apply Matrix.ext; unfold tripleCharges sourceA2088 sourceB2088 sourceC2088 difference raw29275; decide +kernel
    rw [ha]
    exact (canonical29275 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2088 + difference 0 4) (sourceB2088 + difference 4 0) sourceC2088) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA2088 + difference 0 4) (sourceB2088 + difference 4 0) sourceC2088) = raw29276 := by
      apply Matrix.ext; unfold tripleCharges sourceA2088 sourceB2088 sourceC2088 difference raw29276; decide +kernel
    rw [ha]
    exact (canonical29276 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2088 + difference 0 5) (sourceB2088 + difference 5 0) sourceC2088) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA2088 + difference 0 5) (sourceB2088 + difference 5 0) sourceC2088) = raw29277 := by
      apply Matrix.ext; unfold tripleCharges sourceA2088 sourceB2088 sourceC2088 difference raw29277; decide +kernel
    rw [ha]
    exact (canonical29277 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2088 + difference 1 0) (sourceB2088 + difference 0 1) sourceC2088) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4426) := by
    have ha : (tripleCharges (sourceA2088 + difference 1 0) (sourceB2088 + difference 0 1) sourceC2088) = raw29278 := by
      apply Matrix.ext; unfold tripleCharges sourceA2088 sourceB2088 sourceC2088 difference raw29278; decide +kernel
    rw [ha]
    exact (canonical29278 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2088 + difference 1 2) (sourceB2088 + difference 2 1) sourceC2088) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4738) := by
    have ha : (tripleCharges (sourceA2088 + difference 1 2) (sourceB2088 + difference 2 1) sourceC2088) = raw21919 := by
      apply Matrix.ext; unfold tripleCharges sourceA2088 sourceB2088 sourceC2088 difference raw21919; decide +kernel
    rw [ha]
    exact (canonical21919 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2088 + difference 1 3) (sourceB2088 + difference 3 1) sourceC2088) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (tripleCharges (sourceA2088 + difference 1 3) (sourceB2088 + difference 3 1) sourceC2088) = raw21920 := by
      apply Matrix.ext; unfold tripleCharges sourceA2088 sourceB2088 sourceC2088 difference raw21920; decide +kernel
    rw [ha]
    exact (canonical21920 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2088 + difference 1 4) (sourceB2088 + difference 4 1) sourceC2088) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4837) := by
    have ha : (tripleCharges (sourceA2088 + difference 1 4) (sourceB2088 + difference 4 1) sourceC2088) = raw21921 := by
      apply Matrix.ext; unfold tripleCharges sourceA2088 sourceB2088 sourceC2088 difference raw21921; decide +kernel
    rw [ha]
    exact (canonical21921 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2088 + difference 1 5) (sourceB2088 + difference 5 1) sourceC2088) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4841) := by
    have ha : (tripleCharges (sourceA2088 + difference 1 5) (sourceB2088 + difference 5 1) sourceC2088) = raw21922 := by
      apply Matrix.ext; unfold tripleCharges sourceA2088 sourceB2088 sourceC2088 difference raw21922; decide +kernel
    rw [ha]
    exact (canonical21922 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2088 + difference 2 0) (sourceB2088 + difference 0 2) sourceC2088) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4320) := by
    have ha : (tripleCharges (sourceA2088 + difference 2 0) (sourceB2088 + difference 0 2) sourceC2088) = raw21929 := by
      apply Matrix.ext; unfold tripleCharges sourceA2088 sourceB2088 sourceC2088 difference raw21929; decide +kernel
    rw [ha]
    exact (canonical21929 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2088 + difference 2 1) (sourceB2088 + difference 1 2) sourceC2088) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4658) := by
    have ha : (tripleCharges (sourceA2088 + difference 2 1) (sourceB2088 + difference 1 2) sourceC2088) = raw29279 := by
      apply Matrix.ext; unfold tripleCharges sourceA2088 sourceB2088 sourceC2088 difference raw29279; decide +kernel
    rw [ha]
    exact (canonical29279 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2088 + difference 2 3) (sourceB2088 + difference 3 2) sourceC2088) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4708) := by
    have ha : (tripleCharges (sourceA2088 + difference 2 3) (sourceB2088 + difference 3 2) sourceC2088) = raw29280 := by
      apply Matrix.ext; unfold tripleCharges sourceA2088 sourceB2088 sourceC2088 difference raw29280; decide +kernel
    rw [ha]
    exact (canonical29280 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2088 + difference 2 4) (sourceB2088 + difference 4 2) sourceC2088) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4778) := by
    have ha : (tripleCharges (sourceA2088 + difference 2 4) (sourceB2088 + difference 4 2) sourceC2088) = raw29281 := by
      apply Matrix.ext; unfold tripleCharges sourceA2088 sourceB2088 sourceC2088 difference raw29281; decide +kernel
    rw [ha]
    exact (canonical29281 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2088 + difference 2 5) (sourceB2088 + difference 5 2) sourceC2088) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4779) := by
    have ha : (tripleCharges (sourceA2088 + difference 2 5) (sourceB2088 + difference 5 2) sourceC2088) = raw29282 := by
      apply Matrix.ext; unfold tripleCharges sourceA2088 sourceB2088 sourceC2088 difference raw29282; decide +kernel
    rw [ha]
    exact (canonical29282 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2088 + difference 3 0) (sourceB2088 + difference 0 3) sourceC2088) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4338) := by
    have ha : (tripleCharges (sourceA2088 + difference 3 0) (sourceB2088 + difference 0 3) sourceC2088) = raw21934 := by
      apply Matrix.ext; unfold tripleCharges sourceA2088 sourceB2088 sourceC2088 difference raw21934; decide +kernel
    rw [ha]
    exact (canonical21934 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2088 + difference 3 1) (sourceB2088 + difference 1 3) sourceC2088) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4673) := by
    have ha : (tripleCharges (sourceA2088 + difference 3 1) (sourceB2088 + difference 1 3) sourceC2088) = raw29283 := by
      apply Matrix.ext; unfold tripleCharges sourceA2088 sourceB2088 sourceC2088 difference raw29283; decide +kernel
    rw [ha]
    exact (canonical29283 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2088 + difference 3 2) (sourceB2088 + difference 2 3) sourceC2088) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4720) := by
    have ha : (tripleCharges (sourceA2088 + difference 3 2) (sourceB2088 + difference 2 3) sourceC2088) = raw29284 := by
      apply Matrix.ext; unfold tripleCharges sourceA2088 sourceB2088 sourceC2088 difference raw29284; decide +kernel
    rw [ha]
    exact (canonical29284 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2088 + difference 3 4) (sourceB2088 + difference 4 3) sourceC2088) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4800) := by
    have ha : (tripleCharges (sourceA2088 + difference 3 4) (sourceB2088 + difference 4 3) sourceC2088) = raw29285 := by
      apply Matrix.ext; unfold tripleCharges sourceA2088 sourceB2088 sourceC2088 difference raw29285; decide +kernel
    rw [ha]
    exact (canonical29285 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2088 + difference 3 5) (sourceB2088 + difference 5 3) sourceC2088) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4827) := by
    have ha : (tripleCharges (sourceA2088 + difference 3 5) (sourceB2088 + difference 5 3) sourceC2088) = raw29286 := by
      apply Matrix.ext; unfold tripleCharges sourceA2088 sourceB2088 sourceC2088 difference raw29286; decide +kernel
    rw [ha]
    exact (canonical29286 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2088 + difference 4 0) (sourceB2088 + difference 0 4) sourceC2088) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4324) := by
    have ha : (tripleCharges (sourceA2088 + difference 4 0) (sourceB2088 + difference 0 4) sourceC2088) = raw21939 := by
      apply Matrix.ext; unfold tripleCharges sourceA2088 sourceB2088 sourceC2088 difference raw21939; decide +kernel
    rw [ha]
    exact (canonical21939 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2088 + difference 4 1) (sourceB2088 + difference 1 4) sourceC2088) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4636) := by
    have ha : (tripleCharges (sourceA2088 + difference 4 1) (sourceB2088 + difference 1 4) sourceC2088) = raw29287 := by
      apply Matrix.ext; unfold tripleCharges sourceA2088 sourceB2088 sourceC2088 difference raw29287; decide +kernel
    rw [ha]
    exact (canonical29287 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2088 + difference 4 2) (sourceB2088 + difference 2 4) sourceC2088) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4630) := by
    have ha : (tripleCharges (sourceA2088 + difference 4 2) (sourceB2088 + difference 2 4) sourceC2088) = raw29288 := by
      apply Matrix.ext; unfold tripleCharges sourceA2088 sourceB2088 sourceC2088 difference raw29288; decide +kernel
    rw [ha]
    exact (canonical29288 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2088 + difference 4 3) (sourceB2088 + difference 3 4) sourceC2088) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4643) := by
    have ha : (tripleCharges (sourceA2088 + difference 4 3) (sourceB2088 + difference 3 4) sourceC2088) = raw29289 := by
      apply Matrix.ext; unfold tripleCharges sourceA2088 sourceB2088 sourceC2088 difference raw29289; decide +kernel
    rw [ha]
    exact (canonical29289 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2088 + difference 4 5) (sourceB2088 + difference 5 4) sourceC2088) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4788) := by
    have ha : (tripleCharges (sourceA2088 + difference 4 5) (sourceB2088 + difference 5 4) sourceC2088) = raw29290 := by
      apply Matrix.ext; unfold tripleCharges sourceA2088 sourceB2088 sourceC2088 difference raw29290; decide +kernel
    rw [ha]
    exact (canonical29290 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2088 + difference 5 0) (sourceB2088 + difference 0 5) sourceC2088) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4289) := by
    have ha : (tripleCharges (sourceA2088 + difference 5 0) (sourceB2088 + difference 0 5) sourceC2088) = raw21944 := by
      apply Matrix.ext; unfold tripleCharges sourceA2088 sourceB2088 sourceC2088 difference raw21944; decide +kernel
    rw [ha]
    exact (canonical21944 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2088 + difference 5 1) (sourceB2088 + difference 1 5) sourceC2088) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4294) := by
    have ha : (tripleCharges (sourceA2088 + difference 5 1) (sourceB2088 + difference 1 5) sourceC2088) = raw29291 := by
      apply Matrix.ext; unfold tripleCharges sourceA2088 sourceB2088 sourceC2088 difference raw29291; decide +kernel
    rw [ha]
    exact (canonical29291 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2088 + difference 5 2) (sourceB2088 + difference 2 5) sourceC2088) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4286) := by
    have ha : (tripleCharges (sourceA2088 + difference 5 2) (sourceB2088 + difference 2 5) sourceC2088) = raw29292 := by
      apply Matrix.ext; unfold tripleCharges sourceA2088 sourceB2088 sourceC2088 difference raw29292; decide +kernel
    rw [ha]
    exact (canonical29292 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2088 + difference 5 3) (sourceB2088 + difference 3 5) sourceC2088) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4302) := by
    have ha : (tripleCharges (sourceA2088 + difference 5 3) (sourceB2088 + difference 3 5) sourceC2088) = raw29293 := by
      apply Matrix.ext; unfold tripleCharges sourceA2088 sourceB2088 sourceC2088 difference raw29293; decide +kernel
    rw [ha]
    exact (canonical29293 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2088 + difference 5 4) (sourceB2088 + difference 4 5) sourceC2088) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4398) := by
    have ha : (tripleCharges (sourceA2088 + difference 5 4) (sourceB2088 + difference 4 5) sourceC2088) = raw29294 := by
      apply Matrix.ext; unfold tripleCharges sourceA2088 sourceB2088 sourceC2088 difference raw29294; decide +kernel
    rw [ha]
    exact (canonical29294 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2088 sourceB2088 sourceC2088
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2088, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2089 : Charge := ![-3, -1, 0, 0, 1, 3]
def sourceB2089 : Charge := ![3, 1, 0, 0, -1, -3]
def sourceC2089 : Charge := ![0, 0, 0, 0, 0, 0]
def sourceForm2089 : Integer.Sparse Master := [(Sum.inr 4064, 4), (Sum.inr 4066, 1), (Sum.inr 4067, 2), (Sum.inr 4070, 2), (Sum.inr 4074, 4), (Sum.inr 4076, 1), (Sum.inr 4077, 2), (Sum.inr 4080, 4), (Sum.inr 4081, 4), (Sum.inr 4082, 2), (Sum.inr 4084, 2), (Sum.inr 4085, 1), (Sum.inr 4092, 1)]

theorem sourceEq2089 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2089 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2089 + difference 0 1) (sourceB2089 + difference 1 0) sourceC2089) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (tripleCharges (sourceA2089 + difference 0 1) (sourceB2089 + difference 1 0) sourceC2089) = raw18342 := by
      apply Matrix.ext; unfold tripleCharges sourceA2089 sourceB2089 sourceC2089 difference raw18342; decide +kernel
    rw [ha]
    exact (canonical18342 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2089 + difference 0 2) (sourceB2089 + difference 2 0) sourceC2089) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA2089 + difference 0 2) (sourceB2089 + difference 2 0) sourceC2089) = raw18343 := by
      apply Matrix.ext; unfold tripleCharges sourceA2089 sourceB2089 sourceC2089 difference raw18343; decide +kernel
    rw [ha]
    exact (canonical18343 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2089 + difference 0 3) (sourceB2089 + difference 3 0) sourceC2089) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA2089 + difference 0 3) (sourceB2089 + difference 3 0) sourceC2089) = raw18344 := by
      apply Matrix.ext; unfold tripleCharges sourceA2089 sourceB2089 sourceC2089 difference raw18344; decide +kernel
    rw [ha]
    exact (canonical18344 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2089 + difference 0 4) (sourceB2089 + difference 4 0) sourceC2089) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA2089 + difference 0 4) (sourceB2089 + difference 4 0) sourceC2089) = raw2935 := by
      apply Matrix.ext; unfold tripleCharges sourceA2089 sourceB2089 sourceC2089 difference raw2935; decide +kernel
    rw [ha]
    exact (canonical2935 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2089 + difference 0 5) (sourceB2089 + difference 5 0) sourceC2089) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA2089 + difference 0 5) (sourceB2089 + difference 5 0) sourceC2089) = raw2930 := by
      apply Matrix.ext; unfold tripleCharges sourceA2089 sourceB2089 sourceC2089 difference raw2930; decide +kernel
    rw [ha]
    exact (canonical2930 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2089 + difference 1 0) (sourceB2089 + difference 0 1) sourceC2089) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (tripleCharges (sourceA2089 + difference 1 0) (sourceB2089 + difference 0 1) sourceC2089) = raw5209 := by
      apply Matrix.ext; unfold tripleCharges sourceA2089 sourceB2089 sourceC2089 difference raw5209; decide +kernel
    rw [ha]
    exact (canonical5209 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2089 + difference 1 2) (sourceB2089 + difference 2 1) sourceC2089) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (tripleCharges (sourceA2089 + difference 1 2) (sourceB2089 + difference 2 1) sourceC2089) = raw5211 := by
      apply Matrix.ext; unfold tripleCharges sourceA2089 sourceB2089 sourceC2089 difference raw5211; decide +kernel
    rw [ha]
    exact (canonical5211 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2089 + difference 1 3) (sourceB2089 + difference 3 1) sourceC2089) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (tripleCharges (sourceA2089 + difference 1 3) (sourceB2089 + difference 3 1) sourceC2089) = raw5212 := by
      apply Matrix.ext; unfold tripleCharges sourceA2089 sourceB2089 sourceC2089 difference raw5212; decide +kernel
    rw [ha]
    exact (canonical5212 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2089 + difference 1 4) (sourceB2089 + difference 4 1) sourceC2089) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (tripleCharges (sourceA2089 + difference 1 4) (sourceB2089 + difference 4 1) sourceC2089) = raw2934 := by
      apply Matrix.ext; unfold tripleCharges sourceA2089 sourceB2089 sourceC2089 difference raw2934; decide +kernel
    rw [ha]
    exact (canonical2934 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2089 + difference 1 5) (sourceB2089 + difference 5 1) sourceC2089) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA2089 + difference 1 5) (sourceB2089 + difference 5 1) sourceC2089) = raw2929 := by
      apply Matrix.ext; unfold tripleCharges sourceA2089 sourceB2089 sourceC2089 difference raw2929; decide +kernel
    rw [ha]
    exact (canonical2929 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2089 + difference 2 0) (sourceB2089 + difference 0 2) sourceC2089) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4064) := by
    have ha : (tripleCharges (sourceA2089 + difference 2 0) (sourceB2089 + difference 0 2) sourceC2089) = raw22305 := by
      apply Matrix.ext; unfold tripleCharges sourceA2089 sourceB2089 sourceC2089 difference raw22305; decide +kernel
    rw [ha]
    exact (canonical22305 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2089 + difference 2 1) (sourceB2089 + difference 1 2) sourceC2089) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4074) := by
    have ha : (tripleCharges (sourceA2089 + difference 2 1) (sourceB2089 + difference 1 2) sourceC2089) = raw29295 := by
      apply Matrix.ext; unfold tripleCharges sourceA2089 sourceB2089 sourceC2089 difference raw29295; decide +kernel
    rw [ha]
    exact (canonical29295 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2089 + difference 2 3) (sourceB2089 + difference 3 2) sourceC2089) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4077) := by
    have ha : (tripleCharges (sourceA2089 + difference 2 3) (sourceB2089 + difference 3 2) sourceC2089) = raw29296 := by
      apply Matrix.ext; unfold tripleCharges sourceA2089 sourceB2089 sourceC2089 difference raw29296; decide +kernel
    rw [ha]
    exact (canonical29296 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2089 + difference 2 4) (sourceB2089 + difference 4 2) sourceC2089) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (tripleCharges (sourceA2089 + difference 2 4) (sourceB2089 + difference 4 2) sourceC2089) = raw5202 := by
      apply Matrix.ext; unfold tripleCharges sourceA2089 sourceB2089 sourceC2089 difference raw5202; decide +kernel
    rw [ha]
    exact (canonical5202 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2089 + difference 2 5) (sourceB2089 + difference 5 2) sourceC2089) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA2089 + difference 2 5) (sourceB2089 + difference 5 2) sourceC2089) = raw11535 := by
      apply Matrix.ext; unfold tripleCharges sourceA2089 sourceB2089 sourceC2089 difference raw11535; decide +kernel
    rw [ha]
    exact (canonical11535 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2089 + difference 3 0) (sourceB2089 + difference 0 3) sourceC2089) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4064) := by
    have ha : (tripleCharges (sourceA2089 + difference 3 0) (sourceB2089 + difference 0 3) sourceC2089) = raw22308 := by
      apply Matrix.ext; unfold tripleCharges sourceA2089 sourceB2089 sourceC2089 difference raw22308; decide +kernel
    rw [ha]
    exact (canonical22308 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2089 + difference 3 1) (sourceB2089 + difference 1 3) sourceC2089) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4074) := by
    have ha : (tripleCharges (sourceA2089 + difference 3 1) (sourceB2089 + difference 1 3) sourceC2089) = raw29297 := by
      apply Matrix.ext; unfold tripleCharges sourceA2089 sourceB2089 sourceC2089 difference raw29297; decide +kernel
    rw [ha]
    exact (canonical29297 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2089 + difference 3 2) (sourceB2089 + difference 2 3) sourceC2089) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4077) := by
    have ha : (tripleCharges (sourceA2089 + difference 3 2) (sourceB2089 + difference 2 3) sourceC2089) = raw29298 := by
      apply Matrix.ext; unfold tripleCharges sourceA2089 sourceB2089 sourceC2089 difference raw29298; decide +kernel
    rw [ha]
    exact (canonical29298 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2089 + difference 3 4) (sourceB2089 + difference 4 3) sourceC2089) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (tripleCharges (sourceA2089 + difference 3 4) (sourceB2089 + difference 4 3) sourceC2089) = raw5206 := by
      apply Matrix.ext; unfold tripleCharges sourceA2089 sourceB2089 sourceC2089 difference raw5206; decide +kernel
    rw [ha]
    exact (canonical5206 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2089 + difference 3 5) (sourceB2089 + difference 5 3) sourceC2089) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (tripleCharges (sourceA2089 + difference 3 5) (sourceB2089 + difference 5 3) sourceC2089) = raw11538 := by
      apply Matrix.ext; unfold tripleCharges sourceA2089 sourceB2089 sourceC2089 difference raw11538; decide +kernel
    rw [ha]
    exact (canonical11538 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2089 + difference 4 0) (sourceB2089 + difference 0 4) sourceC2089) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4067) := by
    have ha : (tripleCharges (sourceA2089 + difference 4 0) (sourceB2089 + difference 0 4) sourceC2089) = raw22311 := by
      apply Matrix.ext; unfold tripleCharges sourceA2089 sourceB2089 sourceC2089 difference raw22311; decide +kernel
    rw [ha]
    exact (canonical22311 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2089 + difference 4 1) (sourceB2089 + difference 1 4) sourceC2089) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4076) := by
    have ha : (tripleCharges (sourceA2089 + difference 4 1) (sourceB2089 + difference 1 4) sourceC2089) = raw29299 := by
      apply Matrix.ext; unfold tripleCharges sourceA2089 sourceB2089 sourceC2089 difference raw29299; decide +kernel
    rw [ha]
    exact (canonical29299 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2089 + difference 4 2) (sourceB2089 + difference 2 4) sourceC2089) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4074) := by
    have ha : (tripleCharges (sourceA2089 + difference 4 2) (sourceB2089 + difference 2 4) sourceC2089) = raw29300 := by
      apply Matrix.ext; unfold tripleCharges sourceA2089 sourceB2089 sourceC2089 difference raw29300; decide +kernel
    rw [ha]
    exact (canonical29300 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2089 + difference 4 3) (sourceB2089 + difference 3 4) sourceC2089) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4074) := by
    have ha : (tripleCharges (sourceA2089 + difference 4 3) (sourceB2089 + difference 3 4) sourceC2089) = raw29301 := by
      apply Matrix.ext; unfold tripleCharges sourceA2089 sourceB2089 sourceC2089 difference raw29301; decide +kernel
    rw [ha]
    exact (canonical29301 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2089 + difference 4 5) (sourceB2089 + difference 5 4) sourceC2089) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (tripleCharges (sourceA2089 + difference 4 5) (sourceB2089 + difference 5 4) sourceC2089) = raw11541 := by
      apply Matrix.ext; unfold tripleCharges sourceA2089 sourceB2089 sourceC2089 difference raw11541; decide +kernel
    rw [ha]
    exact (canonical11541 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2089 + difference 5 0) (sourceB2089 + difference 0 5) sourceC2089) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4066) := by
    have ha : (tripleCharges (sourceA2089 + difference 5 0) (sourceB2089 + difference 0 5) sourceC2089) = raw20080 := by
      apply Matrix.ext; unfold tripleCharges sourceA2089 sourceB2089 sourceC2089 difference raw20080; decide +kernel
    rw [ha]
    exact (canonical20080 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2089 + difference 5 1) (sourceB2089 + difference 1 5) sourceC2089) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4067) := by
    have ha : (tripleCharges (sourceA2089 + difference 5 1) (sourceB2089 + difference 1 5) sourceC2089) = raw29302 := by
      apply Matrix.ext; unfold tripleCharges sourceA2089 sourceB2089 sourceC2089 difference raw29302; decide +kernel
    rw [ha]
    exact (canonical29302 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2089 + difference 5 2) (sourceB2089 + difference 2 5) sourceC2089) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4064) := by
    have ha : (tripleCharges (sourceA2089 + difference 5 2) (sourceB2089 + difference 2 5) sourceC2089) = raw29303 := by
      apply Matrix.ext; unfold tripleCharges sourceA2089 sourceB2089 sourceC2089 difference raw29303; decide +kernel
    rw [ha]
    exact (canonical29303 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2089 + difference 5 3) (sourceB2089 + difference 3 5) sourceC2089) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4064) := by
    have ha : (tripleCharges (sourceA2089 + difference 5 3) (sourceB2089 + difference 3 5) sourceC2089) = raw29304 := by
      apply Matrix.ext; unfold tripleCharges sourceA2089 sourceB2089 sourceC2089 difference raw29304; decide +kernel
    rw [ha]
    exact (canonical29304 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2089 + difference 5 4) (sourceB2089 + difference 4 5) sourceC2089) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (tripleCharges (sourceA2089 + difference 5 4) (sourceB2089 + difference 4 5) sourceC2089) = raw5214 := by
      apply Matrix.ext; unfold tripleCharges sourceA2089 sourceB2089 sourceC2089 difference raw5214; decide +kernel
    rw [ha]
    exact (canonical5214 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2089 sourceB2089 sourceC2089
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2089, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2090 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2090 : Charge := ![0, 1, 0, 2, -2, -1]
def sourceC2090 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceForm2090 : Integer.Sparse Master := [(Sum.inr 935, 1), (Sum.inr 1816, 1), (Sum.inr 1968, 1), (Sum.inr 2039, 1), (Sum.inr 2054, 1), (Sum.inr 2058, 1), (Sum.inr 4084, -1)]

theorem sourceEq2090 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2090 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2090 + difference 3 0) (sourceB2090 + difference 0 3) sourceC2090) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 935) := by
    have ha : (tripleCharges (sourceA2090 + difference 3 0) (sourceB2090 + difference 0 3) sourceC2090) = raw22315 := by
      apply Matrix.ext; unfold tripleCharges sourceA2090 sourceB2090 sourceC2090 difference raw22315; decide +kernel
    rw [ha]
    exact (canonical22315 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2090 + difference 3 1) (sourceB2090 + difference 1 3) sourceC2090) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1816) := by
    have ha : (tripleCharges (sourceA2090 + difference 3 1) (sourceB2090 + difference 1 3) sourceC2090) = raw29305 := by
      apply Matrix.ext; unfold tripleCharges sourceA2090 sourceB2090 sourceC2090 difference raw29305; decide +kernel
    rw [ha]
    exact (canonical29305 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2090 + difference 3 2) (sourceB2090 + difference 2 3) sourceC2090) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1968) := by
    have ha : (tripleCharges (sourceA2090 + difference 3 2) (sourceB2090 + difference 2 3) sourceC2090) = raw29306 := by
      apply Matrix.ext; unfold tripleCharges sourceA2090 sourceB2090 sourceC2090 difference raw29306; decide +kernel
    rw [ha]
    exact (canonical29306 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2090 + difference 3 3) (sourceB2090 + difference 3 3) sourceC2090) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2039) := by
    have ha : (tripleCharges (sourceA2090 + difference 3 3) (sourceB2090 + difference 3 3) sourceC2090) = raw29307 := by
      apply Matrix.ext; unfold tripleCharges sourceA2090 sourceB2090 sourceC2090 difference raw29307; decide +kernel
    rw [ha]
    exact (canonical29307 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2090 + difference 3 4) (sourceB2090 + difference 4 3) sourceC2090) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2054) := by
    have ha : (tripleCharges (sourceA2090 + difference 3 4) (sourceB2090 + difference 4 3) sourceC2090) = raw27348 := by
      apply Matrix.ext; unfold tripleCharges sourceA2090 sourceB2090 sourceC2090 difference raw27348; decide +kernel
    rw [ha]
    exact (canonical27348 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2090 + difference 3 5) (sourceB2090 + difference 5 3) sourceC2090) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2058) := by
    have ha : (tripleCharges (sourceA2090 + difference 3 5) (sourceB2090 + difference 5 3) sourceC2090) = raw29308 := by
      apply Matrix.ext; unfold tripleCharges sourceA2090 sourceB2090 sourceC2090 difference raw29308; decide +kernel
    rw [ha]
    exact (canonical29308 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2090 + sourceB2090) sourceC2090) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA2090 + sourceB2090) sourceC2090) = raw20142 := by
      apply Matrix.ext; unfold doubleCharges sourceA2090 sourceB2090 sourceC2090 raw20142; decide +kernel
    rw [ha]
    exact (canonical20142 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2090 sourceB2090 sourceC2090
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2090, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2091 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2091 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC2091 : Charge := ![0, 1, 0, 2, -2, -1]
def sourceForm2091 : Integer.Sparse Master := [(Sum.inr 2340, 1), (Sum.inr 2816, 1), (Sum.inr 3162, 1), (Sum.inr 3174, 1), (Sum.inr 3198, 1), (Sum.inr 3706, 1), (Sum.inr 4092, -1)]

theorem sourceEq2091 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2091 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2091 + difference 0 3) (sourceB2091 + difference 3 0) sourceC2091) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3706) := by
    have ha : (tripleCharges (sourceA2091 + difference 0 3) (sourceB2091 + difference 3 0) sourceC2091) = raw15376 := by
      apply Matrix.ext; unfold tripleCharges sourceA2091 sourceB2091 sourceC2091 difference raw15376; decide +kernel
    rw [ha]
    exact (canonical15376 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2091 + difference 1 3) (sourceB2091 + difference 3 1) sourceC2091) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3174) := by
    have ha : (tripleCharges (sourceA2091 + difference 1 3) (sourceB2091 + difference 3 1) sourceC2091) = raw29309 := by
      apply Matrix.ext; unfold tripleCharges sourceA2091 sourceB2091 sourceC2091 difference raw29309; decide +kernel
    rw [ha]
    exact (canonical29309 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2091 + difference 2 3) (sourceB2091 + difference 3 2) sourceC2091) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3162) := by
    have ha : (tripleCharges (sourceA2091 + difference 2 3) (sourceB2091 + difference 3 2) sourceC2091) = raw29310 := by
      apply Matrix.ext; unfold tripleCharges sourceA2091 sourceB2091 sourceC2091 difference raw29310; decide +kernel
    rw [ha]
    exact (canonical29310 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2091 + difference 3 3) (sourceB2091 + difference 3 3) sourceC2091) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3198) := by
    have ha : (tripleCharges (sourceA2091 + difference 3 3) (sourceB2091 + difference 3 3) sourceC2091) = raw15358 := by
      apply Matrix.ext; unfold tripleCharges sourceA2091 sourceB2091 sourceC2091 difference raw15358; decide +kernel
    rw [ha]
    exact (canonical15358 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2091 + difference 4 3) (sourceB2091 + difference 3 4) sourceC2091) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2340) := by
    have ha : (tripleCharges (sourceA2091 + difference 4 3) (sourceB2091 + difference 3 4) sourceC2091) = raw29311 := by
      apply Matrix.ext; unfold tripleCharges sourceA2091 sourceB2091 sourceC2091 difference raw29311; decide +kernel
    rw [ha]
    exact (canonical29311 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2091 + difference 5 3) (sourceB2091 + difference 3 5) sourceC2091) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2816) := by
    have ha : (tripleCharges (sourceA2091 + difference 5 3) (sourceB2091 + difference 3 5) sourceC2091) = raw29312 := by
      apply Matrix.ext; unfold tripleCharges sourceA2091 sourceB2091 sourceC2091 difference raw29312; decide +kernel
    rw [ha]
    exact (canonical29312 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2091 + sourceB2091) sourceC2091) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2091 + sourceB2091) sourceC2091) = raw15360 := by
      apply Matrix.ext; unfold doubleCharges sourceA2091 sourceB2091 sourceC2091 raw15360; decide +kernel
    rw [ha]
    exact (canonical15360 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2091 sourceB2091 sourceC2091
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2091, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2092 : Charge := ![0, 1, 0, 2, -2, -1]
def sourceB2092 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC2092 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceForm2092 : Integer.Sparse Master := [(Sum.inr 2213, 1), (Sum.inr 2215, 1), (Sum.inr 2217, 1), (Sum.inr 2225, 1), (Sum.inr 2274, 1), (Sum.inr 3612, 1), (Sum.inr 4082, -1)]

theorem sourceEq2092 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2092 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2092 + difference 0 3) (sourceB2092 + difference 3 0) sourceC2092) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3612) := by
    have ha : (tripleCharges (sourceA2092 + difference 0 3) (sourceB2092 + difference 3 0) sourceC2092) = raw29313 := by
      apply Matrix.ext; unfold tripleCharges sourceA2092 sourceB2092 sourceC2092 difference raw29313; decide +kernel
    rw [ha]
    exact (canonical29313 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2092 + difference 1 3) (sourceB2092 + difference 3 1) sourceC2092) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2274) := by
    have ha : (tripleCharges (sourceA2092 + difference 1 3) (sourceB2092 + difference 3 1) sourceC2092) = raw29314 := by
      apply Matrix.ext; unfold tripleCharges sourceA2092 sourceB2092 sourceC2092 difference raw29314; decide +kernel
    rw [ha]
    exact (canonical29314 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2092 + difference 2 3) (sourceB2092 + difference 3 2) sourceC2092) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2213) := by
    have ha : (tripleCharges (sourceA2092 + difference 2 3) (sourceB2092 + difference 3 2) sourceC2092) = raw29315 := by
      apply Matrix.ext; unfold tripleCharges sourceA2092 sourceB2092 sourceC2092 difference raw29315; decide +kernel
    rw [ha]
    exact (canonical29315 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2092 + difference 3 3) (sourceB2092 + difference 3 3) sourceC2092) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2217) := by
    have ha : (tripleCharges (sourceA2092 + difference 3 3) (sourceB2092 + difference 3 3) sourceC2092) = raw29316 := by
      apply Matrix.ext; unfold tripleCharges sourceA2092 sourceB2092 sourceC2092 difference raw29316; decide +kernel
    rw [ha]
    exact (canonical29316 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2092 + difference 4 3) (sourceB2092 + difference 3 4) sourceC2092) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2225) := by
    have ha : (tripleCharges (sourceA2092 + difference 4 3) (sourceB2092 + difference 3 4) sourceC2092) = raw29317 := by
      apply Matrix.ext; unfold tripleCharges sourceA2092 sourceB2092 sourceC2092 difference raw29317; decide +kernel
    rw [ha]
    exact (canonical29317 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2092 + difference 5 3) (sourceB2092 + difference 3 5) sourceC2092) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2215) := by
    have ha : (tripleCharges (sourceA2092 + difference 5 3) (sourceB2092 + difference 3 5) sourceC2092) = raw29318 := by
      apply Matrix.ext; unfold tripleCharges sourceA2092 sourceB2092 sourceC2092 difference raw29318; decide +kernel
    rw [ha]
    exact (canonical29318 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2092 + sourceB2092) sourceC2092) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2092 + sourceB2092) sourceC2092) = raw29319 := by
      apply Matrix.ext; unfold doubleCharges sourceA2092 sourceB2092 sourceC2092 raw29319; decide +kernel
    rw [ha]
    exact (canonical29319 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2092 sourceB2092 sourceC2092
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2092, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2093 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2093 : Charge := ![0, 1, 1, 1, -2, -1]
def sourceC2093 : Charge := ![3, 0, -1, -1, 0, -1]
def sourceForm2093 : Integer.Sparse Master := [(Sum.inr 910, 1), (Sum.inr 1794, 1), (Sum.inr 1977, 1), (Sum.inr 2012, 1), (Sum.inr 2020, 1), (Sum.inr 2023, 1), (Sum.inr 4083, -1)]

theorem sourceEq2093 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2093 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2093 + difference 2 0) (sourceB2093 + difference 0 2) sourceC2093) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 910) := by
    have ha : (tripleCharges (sourceA2093 + difference 2 0) (sourceB2093 + difference 0 2) sourceC2093) = raw22353 := by
      apply Matrix.ext; unfold tripleCharges sourceA2093 sourceB2093 sourceC2093 difference raw22353; decide +kernel
    rw [ha]
    exact (canonical22353 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2093 + difference 2 1) (sourceB2093 + difference 1 2) sourceC2093) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1794) := by
    have ha : (tripleCharges (sourceA2093 + difference 2 1) (sourceB2093 + difference 1 2) sourceC2093) = raw29320 := by
      apply Matrix.ext; unfold tripleCharges sourceA2093 sourceB2093 sourceC2093 difference raw29320; decide +kernel
    rw [ha]
    exact (canonical29320 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2093 + difference 2 2) (sourceB2093 + difference 2 2) sourceC2093) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2012) := by
    have ha : (tripleCharges (sourceA2093 + difference 2 2) (sourceB2093 + difference 2 2) sourceC2093) = raw29321 := by
      apply Matrix.ext; unfold tripleCharges sourceA2093 sourceB2093 sourceC2093 difference raw29321; decide +kernel
    rw [ha]
    exact (canonical29321 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2093 + difference 2 3) (sourceB2093 + difference 3 2) sourceC2093) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1977) := by
    have ha : (tripleCharges (sourceA2093 + difference 2 3) (sourceB2093 + difference 3 2) sourceC2093) = raw29322 := by
      apply Matrix.ext; unfold tripleCharges sourceA2093 sourceB2093 sourceC2093 difference raw29322; decide +kernel
    rw [ha]
    exact (canonical29322 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2093 + difference 2 4) (sourceB2093 + difference 4 2) sourceC2093) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2020) := by
    have ha : (tripleCharges (sourceA2093 + difference 2 4) (sourceB2093 + difference 4 2) sourceC2093) = raw27373 := by
      apply Matrix.ext; unfold tripleCharges sourceA2093 sourceB2093 sourceC2093 difference raw27373; decide +kernel
    rw [ha]
    exact (canonical27373 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2093 + difference 2 5) (sourceB2093 + difference 5 2) sourceC2093) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2023) := by
    have ha : (tripleCharges (sourceA2093 + difference 2 5) (sourceB2093 + difference 5 2) sourceC2093) = raw29323 := by
      apply Matrix.ext; unfold tripleCharges sourceA2093 sourceB2093 sourceC2093 difference raw29323; decide +kernel
    rw [ha]
    exact (canonical29323 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2093 + sourceB2093) sourceC2093) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA2093 + sourceB2093) sourceC2093) = raw20196 := by
      apply Matrix.ext; unfold doubleCharges sourceA2093 sourceB2093 sourceC2093 raw20196; decide +kernel
    rw [ha]
    exact (canonical20196 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2093 sourceB2093 sourceC2093
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2093, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2094 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2094 : Charge := ![3, 0, -1, -1, 0, -1]
def sourceC2094 : Charge := ![0, 1, 1, 1, -2, -1]
def sourceForm2094 : Integer.Sparse Master := [(Sum.inr 2323, 1), (Sum.inr 2800, 1), (Sum.inr 3189, 1), (Sum.inr 3199, 2), (Sum.inr 3692, 1), (Sum.inr 4091, -1)]

theorem sourceEq2094 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2094 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2094 + difference 0 2) (sourceB2094 + difference 2 0) sourceC2094) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3692) := by
    have ha : (tripleCharges (sourceA2094 + difference 0 2) (sourceB2094 + difference 2 0) sourceC2094) = raw15657 := by
      apply Matrix.ext; unfold tripleCharges sourceA2094 sourceB2094 sourceC2094 difference raw15657; decide +kernel
    rw [ha]
    exact (canonical15657 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2094 + difference 1 2) (sourceB2094 + difference 2 1) sourceC2094) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3199) := by
    have ha : (tripleCharges (sourceA2094 + difference 1 2) (sourceB2094 + difference 2 1) sourceC2094) = raw29324 := by
      apply Matrix.ext; unfold tripleCharges sourceA2094 sourceB2094 sourceC2094 difference raw29324; decide +kernel
    rw [ha]
    exact (canonical29324 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2094 + difference 2 2) (sourceB2094 + difference 2 2) sourceC2094) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3199) := by
    have ha : (tripleCharges (sourceA2094 + difference 2 2) (sourceB2094 + difference 2 2) sourceC2094) = raw15643 := by
      apply Matrix.ext; unfold tripleCharges sourceA2094 sourceB2094 sourceC2094 difference raw15643; decide +kernel
    rw [ha]
    exact (canonical15643 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2094 + difference 3 2) (sourceB2094 + difference 2 3) sourceC2094) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3189) := by
    have ha : (tripleCharges (sourceA2094 + difference 3 2) (sourceB2094 + difference 2 3) sourceC2094) = raw29325 := by
      apply Matrix.ext; unfold tripleCharges sourceA2094 sourceB2094 sourceC2094 difference raw29325; decide +kernel
    rw [ha]
    exact (canonical29325 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2094 + difference 4 2) (sourceB2094 + difference 2 4) sourceC2094) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2323) := by
    have ha : (tripleCharges (sourceA2094 + difference 4 2) (sourceB2094 + difference 2 4) sourceC2094) = raw29326 := by
      apply Matrix.ext; unfold tripleCharges sourceA2094 sourceB2094 sourceC2094 difference raw29326; decide +kernel
    rw [ha]
    exact (canonical29326 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2094 + difference 5 2) (sourceB2094 + difference 2 5) sourceC2094) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2800) := by
    have ha : (tripleCharges (sourceA2094 + difference 5 2) (sourceB2094 + difference 2 5) sourceC2094) = raw29327 := by
      apply Matrix.ext; unfold tripleCharges sourceA2094 sourceB2094 sourceC2094 difference raw29327; decide +kernel
    rw [ha]
    exact (canonical29327 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2094 + sourceB2094) sourceC2094) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA2094 + sourceB2094) sourceC2094) = raw15639 := by
      apply Matrix.ext; unfold doubleCharges sourceA2094 sourceB2094 sourceC2094 raw15639; decide +kernel
    rw [ha]
    exact (canonical15639 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2094 sourceB2094 sourceC2094
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2094, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2095 : Charge := ![0, 1, 1, 1, -2, -1]
def sourceB2095 : Charge := ![3, 0, -1, -1, 0, -1]
def sourceC2095 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceForm2095 : Integer.Sparse Master := [(Sum.inr 2213, 1), (Sum.inr 2396, 1), (Sum.inr 3476, 1), (Sum.inr 3610, 1), (Sum.inr 3612, 2), (Sum.inr 4082, -1)]

theorem sourceEq2095 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2095 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2095 + difference 0 0) (sourceB2095 + difference 0 0) sourceC2095) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2213) := by
    have ha : (tripleCharges (sourceA2095 + difference 0 0) (sourceB2095 + difference 0 0) sourceC2095) = raw29315 := by
      apply Matrix.ext; unfold tripleCharges sourceA2095 sourceB2095 sourceC2095 difference raw29315; decide +kernel
    rw [ha]
    exact (canonical29315 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2095 + difference 0 1) (sourceB2095 + difference 1 0) sourceC2095) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3476) := by
    have ha : (tripleCharges (sourceA2095 + difference 0 1) (sourceB2095 + difference 1 0) sourceC2095) = raw29328 := by
      apply Matrix.ext; unfold tripleCharges sourceA2095 sourceB2095 sourceC2095 difference raw29328; decide +kernel
    rw [ha]
    exact (canonical29328 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2095 + difference 0 2) (sourceB2095 + difference 2 0) sourceC2095) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3612) := by
    have ha : (tripleCharges (sourceA2095 + difference 0 2) (sourceB2095 + difference 2 0) sourceC2095) = raw29313 := by
      apply Matrix.ext; unfold tripleCharges sourceA2095 sourceB2095 sourceC2095 difference raw29313; decide +kernel
    rw [ha]
    exact (canonical29313 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2095 + difference 0 3) (sourceB2095 + difference 3 0) sourceC2095) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3612) := by
    have ha : (tripleCharges (sourceA2095 + difference 0 3) (sourceB2095 + difference 3 0) sourceC2095) = raw29329 := by
      apply Matrix.ext; unfold tripleCharges sourceA2095 sourceB2095 sourceC2095 difference raw29329; decide +kernel
    rw [ha]
    exact (canonical29329 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2095 + difference 0 4) (sourceB2095 + difference 4 0) sourceC2095) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2396) := by
    have ha : (tripleCharges (sourceA2095 + difference 0 4) (sourceB2095 + difference 4 0) sourceC2095) = raw29330 := by
      apply Matrix.ext; unfold tripleCharges sourceA2095 sourceB2095 sourceC2095 difference raw29330; decide +kernel
    rw [ha]
    exact (canonical29330 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2095 + difference 0 5) (sourceB2095 + difference 5 0) sourceC2095) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3610) := by
    have ha : (tripleCharges (sourceA2095 + difference 0 5) (sourceB2095 + difference 5 0) sourceC2095) = raw29331 := by
      apply Matrix.ext; unfold tripleCharges sourceA2095 sourceB2095 sourceC2095 difference raw29331; decide +kernel
    rw [ha]
    exact (canonical29331 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2095 + sourceB2095) sourceC2095) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2095 + sourceB2095) sourceC2095) = raw29319 := by
      apply Matrix.ext; unfold doubleCharges sourceA2095 sourceB2095 sourceC2095 raw29319; decide +kernel
    rw [ha]
    exact (canonical29319 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2095 sourceB2095 sourceC2095
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2095, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2096 : Charge := ![0, 1, 1, 1, -2, -1]
def sourceB2096 : Charge := ![3, 0, -1, -1, 0, -1]
def sourceC2096 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceForm2096 : Integer.Sparse Master := [(Sum.inr 2209, 2), (Sum.inr 2213, 2), (Sum.inr 2269, 1), (Sum.inr 3610, 1), (Sum.inr 4082, -1)]

theorem sourceEq2096 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2096 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2096 + difference 0 5) (sourceB2096 + difference 5 0) sourceC2096) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3610) := by
    have ha : (tripleCharges (sourceA2096 + difference 0 5) (sourceB2096 + difference 5 0) sourceC2096) = raw29331 := by
      apply Matrix.ext; unfold tripleCharges sourceA2096 sourceB2096 sourceC2096 difference raw29331; decide +kernel
    rw [ha]
    exact (canonical29331 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2096 + difference 1 5) (sourceB2096 + difference 5 1) sourceC2096) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2269) := by
    have ha : (tripleCharges (sourceA2096 + difference 1 5) (sourceB2096 + difference 5 1) sourceC2096) = raw29332 := by
      apply Matrix.ext; unfold tripleCharges sourceA2096 sourceB2096 sourceC2096 difference raw29332; decide +kernel
    rw [ha]
    exact (canonical29332 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2096 + difference 2 5) (sourceB2096 + difference 5 2) sourceC2096) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2209) := by
    have ha : (tripleCharges (sourceA2096 + difference 2 5) (sourceB2096 + difference 5 2) sourceC2096) = raw29333 := by
      apply Matrix.ext; unfold tripleCharges sourceA2096 sourceB2096 sourceC2096 difference raw29333; decide +kernel
    rw [ha]
    exact (canonical29333 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2096 + difference 3 5) (sourceB2096 + difference 5 3) sourceC2096) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2209) := by
    have ha : (tripleCharges (sourceA2096 + difference 3 5) (sourceB2096 + difference 5 3) sourceC2096) = raw29334 := by
      apply Matrix.ext; unfold tripleCharges sourceA2096 sourceB2096 sourceC2096 difference raw29334; decide +kernel
    rw [ha]
    exact (canonical29334 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2096 + difference 4 5) (sourceB2096 + difference 5 4) sourceC2096) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2213) := by
    have ha : (tripleCharges (sourceA2096 + difference 4 5) (sourceB2096 + difference 5 4) sourceC2096) = raw29335 := by
      apply Matrix.ext; unfold tripleCharges sourceA2096 sourceB2096 sourceC2096 difference raw29335; decide +kernel
    rw [ha]
    exact (canonical29335 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2096 + difference 5 5) (sourceB2096 + difference 5 5) sourceC2096) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2213) := by
    have ha : (tripleCharges (sourceA2096 + difference 5 5) (sourceB2096 + difference 5 5) sourceC2096) = raw29315 := by
      apply Matrix.ext; unfold tripleCharges sourceA2096 sourceB2096 sourceC2096 difference raw29315; decide +kernel
    rw [ha]
    exact (canonical29315 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2096 + sourceB2096) sourceC2096) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2096 + sourceB2096) sourceC2096) = raw29319 := by
      apply Matrix.ext; unfold doubleCharges sourceA2096 sourceB2096 sourceC2096 raw29319; decide +kernel
    rw [ha]
    exact (canonical29319 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2096 sourceB2096 sourceC2096
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2096, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2097 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2097 : Charge := ![3, 0, -1, -2, 0, 0]
def sourceC2097 : Charge := ![0, 1, 1, 2, -2, -2]
def sourceForm2097 : Integer.Sparse Master := [(Sum.inr 3193, 1), (Sum.inr 3648, 1), (Sum.inr 3653, 1), (Sum.inr 3659, 1), (Sum.inr 3762, 2), (Sum.inr 4088, -1)]

theorem sourceEq2097 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2097 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2097 + difference 0 0) (sourceB2097 + difference 0 0) sourceC2097) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3193) := by
    have ha : (tripleCharges (sourceA2097 + difference 0 0) (sourceB2097 + difference 0 0) sourceC2097) = raw29336 := by
      apply Matrix.ext; unfold tripleCharges sourceA2097 sourceB2097 sourceC2097 difference raw29336; decide +kernel
    rw [ha]
    exact (canonical29336 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2097 + difference 0 1) (sourceB2097 + difference 1 0) sourceC2097) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3648) := by
    have ha : (tripleCharges (sourceA2097 + difference 0 1) (sourceB2097 + difference 1 0) sourceC2097) = raw29337 := by
      apply Matrix.ext; unfold tripleCharges sourceA2097 sourceB2097 sourceC2097 difference raw29337; decide +kernel
    rw [ha]
    exact (canonical29337 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2097 + difference 0 2) (sourceB2097 + difference 2 0) sourceC2097) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3659) := by
    have ha : (tripleCharges (sourceA2097 + difference 0 2) (sourceB2097 + difference 2 0) sourceC2097) = raw29338 := by
      apply Matrix.ext; unfold tripleCharges sourceA2097 sourceB2097 sourceC2097 difference raw29338; decide +kernel
    rw [ha]
    exact (canonical29338 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2097 + difference 0 3) (sourceB2097 + difference 3 0) sourceC2097) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3653) := by
    have ha : (tripleCharges (sourceA2097 + difference 0 3) (sourceB2097 + difference 3 0) sourceC2097) = raw29339 := by
      apply Matrix.ext; unfold tripleCharges sourceA2097 sourceB2097 sourceC2097 difference raw29339; decide +kernel
    rw [ha]
    exact (canonical29339 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2097 + difference 0 4) (sourceB2097 + difference 4 0) sourceC2097) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3762) := by
    have ha : (tripleCharges (sourceA2097 + difference 0 4) (sourceB2097 + difference 4 0) sourceC2097) = raw29340 := by
      apply Matrix.ext; unfold tripleCharges sourceA2097 sourceB2097 sourceC2097 difference raw29340; decide +kernel
    rw [ha]
    exact (canonical29340 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2097 + difference 0 5) (sourceB2097 + difference 5 0) sourceC2097) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3762) := by
    have ha : (tripleCharges (sourceA2097 + difference 0 5) (sourceB2097 + difference 5 0) sourceC2097) = raw29341 := by
      apply Matrix.ext; unfold tripleCharges sourceA2097 sourceB2097 sourceC2097 difference raw29341; decide +kernel
    rw [ha]
    exact (canonical29341 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2097 + sourceB2097) sourceC2097) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA2097 + sourceB2097) sourceC2097) = raw29342 := by
      apply Matrix.ext; unfold doubleCharges sourceA2097 sourceB2097 sourceC2097 raw29342; decide +kernel
    rw [ha]
    exact (canonical29342 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2097 sourceB2097 sourceC2097
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2097, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2098 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2098 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceC2098 : Charge := ![3, -1, 0, -1, 0, -1]
def sourceForm2098 : Integer.Sparse Master := [(Sum.inr 950, 1), (Sum.inr 1829, 1), (Sum.inr 1977, 1), (Sum.inr 2094, 1), (Sum.inr 2107, 1), (Sum.inr 2110, 1), (Sum.inr 4083, -1)]

theorem sourceEq2098 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2098 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2098 + difference 3 0) (sourceB2098 + difference 0 3) sourceC2098) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 950) := by
    have ha : (tripleCharges (sourceA2098 + difference 3 0) (sourceB2098 + difference 0 3) sourceC2098) = raw25239 := by
      apply Matrix.ext; unfold tripleCharges sourceA2098 sourceB2098 sourceC2098 difference raw25239; decide +kernel
    rw [ha]
    exact (canonical25239 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2098 + difference 3 1) (sourceB2098 + difference 1 3) sourceC2098) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1829) := by
    have ha : (tripleCharges (sourceA2098 + difference 3 1) (sourceB2098 + difference 1 3) sourceC2098) = raw29343 := by
      apply Matrix.ext; unfold tripleCharges sourceA2098 sourceB2098 sourceC2098 difference raw29343; decide +kernel
    rw [ha]
    exact (canonical29343 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2098 + difference 3 2) (sourceB2098 + difference 2 3) sourceC2098) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1977) := by
    have ha : (tripleCharges (sourceA2098 + difference 3 2) (sourceB2098 + difference 2 3) sourceC2098) = raw29344 := by
      apply Matrix.ext; unfold tripleCharges sourceA2098 sourceB2098 sourceC2098 difference raw29344; decide +kernel
    rw [ha]
    exact (canonical29344 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2098 + difference 3 3) (sourceB2098 + difference 3 3) sourceC2098) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2094) := by
    have ha : (tripleCharges (sourceA2098 + difference 3 3) (sourceB2098 + difference 3 3) sourceC2098) = raw29345 := by
      apply Matrix.ext; unfold tripleCharges sourceA2098 sourceB2098 sourceC2098 difference raw29345; decide +kernel
    rw [ha]
    exact (canonical29345 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2098 + difference 3 4) (sourceB2098 + difference 4 3) sourceC2098) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2107) := by
    have ha : (tripleCharges (sourceA2098 + difference 3 4) (sourceB2098 + difference 4 3) sourceC2098) = raw25236 := by
      apply Matrix.ext; unfold tripleCharges sourceA2098 sourceB2098 sourceC2098 difference raw25236; decide +kernel
    rw [ha]
    exact (canonical25236 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2098 + difference 3 5) (sourceB2098 + difference 5 3) sourceC2098) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2110) := by
    have ha : (tripleCharges (sourceA2098 + difference 3 5) (sourceB2098 + difference 5 3) sourceC2098) = raw29346 := by
      apply Matrix.ext; unfold tripleCharges sourceA2098 sourceB2098 sourceC2098 difference raw29346; decide +kernel
    rw [ha]
    exact (canonical29346 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2098 + sourceB2098) sourceC2098) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA2098 + sourceB2098) sourceC2098) = raw25231 := by
      apply Matrix.ext; unfold doubleCharges sourceA2098 sourceB2098 sourceC2098 raw25231; decide +kernel
    rw [ha]
    exact (canonical25231 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2098 sourceB2098 sourceC2098
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2098, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2099 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2099 : Charge := ![3, -1, 0, -1, 0, -1]
def sourceC2099 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceForm2099 : Integer.Sparse Master := [(Sum.inr 2327, 1), (Sum.inr 2803, 1), (Sum.inr 3133, 1), (Sum.inr 3138, 1), (Sum.inr 3174, 1), (Sum.inr 3693, 1), (Sum.inr 4092, -1)]

theorem sourceEq2099 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2099 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2099 + difference 0 1) (sourceB2099 + difference 1 0) sourceC2099) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3693) := by
    have ha : (tripleCharges (sourceA2099 + difference 0 1) (sourceB2099 + difference 1 0) sourceC2099) = raw16542 := by
      apply Matrix.ext; unfold tripleCharges sourceA2099 sourceB2099 sourceC2099 difference raw16542; decide +kernel
    rw [ha]
    exact (canonical16542 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2099 + difference 1 1) (sourceB2099 + difference 1 1) sourceC2099) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3174) := by
    have ha : (tripleCharges (sourceA2099 + difference 1 1) (sourceB2099 + difference 1 1) sourceC2099) = raw16536 := by
      apply Matrix.ext; unfold tripleCharges sourceA2099 sourceB2099 sourceC2099 difference raw16536; decide +kernel
    rw [ha]
    exact (canonical16536 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2099 + difference 2 1) (sourceB2099 + difference 1 2) sourceC2099) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3133) := by
    have ha : (tripleCharges (sourceA2099 + difference 2 1) (sourceB2099 + difference 1 2) sourceC2099) = raw29347 := by
      apply Matrix.ext; unfold tripleCharges sourceA2099 sourceB2099 sourceC2099 difference raw29347; decide +kernel
    rw [ha]
    exact (canonical29347 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2099 + difference 3 1) (sourceB2099 + difference 1 3) sourceC2099) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3138) := by
    have ha : (tripleCharges (sourceA2099 + difference 3 1) (sourceB2099 + difference 1 3) sourceC2099) = raw29348 := by
      apply Matrix.ext; unfold tripleCharges sourceA2099 sourceB2099 sourceC2099 difference raw29348; decide +kernel
    rw [ha]
    exact (canonical29348 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2099 + difference 4 1) (sourceB2099 + difference 1 4) sourceC2099) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2327) := by
    have ha : (tripleCharges (sourceA2099 + difference 4 1) (sourceB2099 + difference 1 4) sourceC2099) = raw29349 := by
      apply Matrix.ext; unfold tripleCharges sourceA2099 sourceB2099 sourceC2099 difference raw29349; decide +kernel
    rw [ha]
    exact (canonical29349 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2099 + difference 5 1) (sourceB2099 + difference 1 5) sourceC2099) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2803) := by
    have ha : (tripleCharges (sourceA2099 + difference 5 1) (sourceB2099 + difference 1 5) sourceC2099) = raw29350 := by
      apply Matrix.ext; unfold tripleCharges sourceA2099 sourceB2099 sourceC2099 difference raw29350; decide +kernel
    rw [ha]
    exact (canonical29350 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2099 + sourceB2099) sourceC2099) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2099 + sourceB2099) sourceC2099) = raw16538 := by
      apply Matrix.ext; unfold doubleCharges sourceA2099 sourceB2099 sourceC2099 raw16538; decide +kernel
    rw [ha]
    exact (canonical16538 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2099 sourceB2099 sourceC2099
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2099, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2100 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceB2100 : Charge := ![3, -1, 0, -1, 0, -1]
def sourceC2100 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceForm2100 : Integer.Sparse Master := [(Sum.inr 2274, 1), (Sum.inr 2401, 1), (Sum.inr 3536, 1), (Sum.inr 3612, 1), (Sum.inr 3630, 1), (Sum.inr 3631, 1), (Sum.inr 4082, -1)]

theorem sourceEq2100 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2100 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2100 + difference 0 0) (sourceB2100 + difference 0 0) sourceC2100) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2274) := by
    have ha : (tripleCharges (sourceA2100 + difference 0 0) (sourceB2100 + difference 0 0) sourceC2100) = raw29314 := by
      apply Matrix.ext; unfold tripleCharges sourceA2100 sourceB2100 sourceC2100 difference raw29314; decide +kernel
    rw [ha]
    exact (canonical29314 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2100 + difference 0 1) (sourceB2100 + difference 1 0) sourceC2100) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3612) := by
    have ha : (tripleCharges (sourceA2100 + difference 0 1) (sourceB2100 + difference 1 0) sourceC2100) = raw29313 := by
      apply Matrix.ext; unfold tripleCharges sourceA2100 sourceB2100 sourceC2100 difference raw29313; decide +kernel
    rw [ha]
    exact (canonical29313 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2100 + difference 0 2) (sourceB2100 + difference 2 0) sourceC2100) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3536) := by
    have ha : (tripleCharges (sourceA2100 + difference 0 2) (sourceB2100 + difference 2 0) sourceC2100) = raw29351 := by
      apply Matrix.ext; unfold tripleCharges sourceA2100 sourceB2100 sourceC2100 difference raw29351; decide +kernel
    rw [ha]
    exact (canonical29351 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2100 + difference 0 3) (sourceB2100 + difference 3 0) sourceC2100) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3631) := by
    have ha : (tripleCharges (sourceA2100 + difference 0 3) (sourceB2100 + difference 3 0) sourceC2100) = raw29352 := by
      apply Matrix.ext; unfold tripleCharges sourceA2100 sourceB2100 sourceC2100 difference raw29352; decide +kernel
    rw [ha]
    exact (canonical29352 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2100 + difference 0 4) (sourceB2100 + difference 4 0) sourceC2100) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2401) := by
    have ha : (tripleCharges (sourceA2100 + difference 0 4) (sourceB2100 + difference 4 0) sourceC2100) = raw29353 := by
      apply Matrix.ext; unfold tripleCharges sourceA2100 sourceB2100 sourceC2100 difference raw29353; decide +kernel
    rw [ha]
    exact (canonical29353 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2100 + difference 0 5) (sourceB2100 + difference 5 0) sourceC2100) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3630) := by
    have ha : (tripleCharges (sourceA2100 + difference 0 5) (sourceB2100 + difference 5 0) sourceC2100) = raw29354 := by
      apply Matrix.ext; unfold tripleCharges sourceA2100 sourceB2100 sourceC2100 difference raw29354; decide +kernel
    rw [ha]
    exact (canonical29354 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2100 + sourceB2100) sourceC2100) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2100 + sourceB2100) sourceC2100) = raw29319 := by
      apply Matrix.ext; unfold doubleCharges sourceA2100 sourceB2100 sourceC2100 raw29319; decide +kernel
    rw [ha]
    exact (canonical29319 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2100 sourceB2100 sourceC2100
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2100, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2101 : Charge := ![0, 2, 0, 1, -2, -1]
def sourceB2101 : Charge := ![3, -1, 0, -1, 0, -1]
def sourceC2101 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceForm2101 : Integer.Sparse Master := [(Sum.inr 2274, 2), (Sum.inr 2276, 1), (Sum.inr 2280, 1), (Sum.inr 2288, 1), (Sum.inr 3631, 1), (Sum.inr 4082, -1)]

theorem sourceEq2101 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2101 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2101 + difference 0 3) (sourceB2101 + difference 3 0) sourceC2101) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3631) := by
    have ha : (tripleCharges (sourceA2101 + difference 0 3) (sourceB2101 + difference 3 0) sourceC2101) = raw29352 := by
      apply Matrix.ext; unfold tripleCharges sourceA2101 sourceB2101 sourceC2101 difference raw29352; decide +kernel
    rw [ha]
    exact (canonical29352 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2101 + difference 1 3) (sourceB2101 + difference 3 1) sourceC2101) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2280) := by
    have ha : (tripleCharges (sourceA2101 + difference 1 3) (sourceB2101 + difference 3 1) sourceC2101) = raw29355 := by
      apply Matrix.ext; unfold tripleCharges sourceA2101 sourceB2101 sourceC2101 difference raw29355; decide +kernel
    rw [ha]
    exact (canonical29355 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2101 + difference 2 3) (sourceB2101 + difference 3 2) sourceC2101) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2274) := by
    have ha : (tripleCharges (sourceA2101 + difference 2 3) (sourceB2101 + difference 3 2) sourceC2101) = raw29356 := by
      apply Matrix.ext; unfold tripleCharges sourceA2101 sourceB2101 sourceC2101 difference raw29356; decide +kernel
    rw [ha]
    exact (canonical29356 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2101 + difference 3 3) (sourceB2101 + difference 3 3) sourceC2101) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2274) := by
    have ha : (tripleCharges (sourceA2101 + difference 3 3) (sourceB2101 + difference 3 3) sourceC2101) = raw29314 := by
      apply Matrix.ext; unfold tripleCharges sourceA2101 sourceB2101 sourceC2101 difference raw29314; decide +kernel
    rw [ha]
    exact (canonical29314 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2101 + difference 4 3) (sourceB2101 + difference 3 4) sourceC2101) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2288) := by
    have ha : (tripleCharges (sourceA2101 + difference 4 3) (sourceB2101 + difference 3 4) sourceC2101) = raw29357 := by
      apply Matrix.ext; unfold tripleCharges sourceA2101 sourceB2101 sourceC2101 difference raw29357; decide +kernel
    rw [ha]
    exact (canonical29357 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2101 + difference 5 3) (sourceB2101 + difference 3 5) sourceC2101) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2276) := by
    have ha : (tripleCharges (sourceA2101 + difference 5 3) (sourceB2101 + difference 3 5) sourceC2101) = raw29358 := by
      apply Matrix.ext; unfold tripleCharges sourceA2101 sourceB2101 sourceC2101 difference raw29358; decide +kernel
    rw [ha]
    exact (canonical29358 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2101 + sourceB2101) sourceC2101) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2101 + sourceB2101) sourceC2101) = raw29319 := by
      apply Matrix.ext; unfold doubleCharges sourceA2101 sourceB2101 sourceC2101 raw29319; decide +kernel
    rw [ha]
    exact (canonical29319 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2101 sourceB2101 sourceC2101
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2101, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2102 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2102 : Charge := ![3, -1, 0, -2, 0, 0]
def sourceC2102 : Charge := ![0, 2, 0, 2, -2, -2]
def sourceForm2102 : Integer.Sparse Master := [(Sum.inr 3166, 1), (Sum.inr 3658, 1), (Sum.inr 3660, 1), (Sum.inr 3666, 1), (Sum.inr 3772, 2), (Sum.inr 4089, -1)]

theorem sourceEq2102 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2102 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2102 + difference 0 0) (sourceB2102 + difference 0 0) sourceC2102) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3166) := by
    have ha : (tripleCharges (sourceA2102 + difference 0 0) (sourceB2102 + difference 0 0) sourceC2102) = raw29359 := by
      apply Matrix.ext; unfold tripleCharges sourceA2102 sourceB2102 sourceC2102 difference raw29359; decide +kernel
    rw [ha]
    exact (canonical29359 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2102 + difference 0 1) (sourceB2102 + difference 1 0) sourceC2102) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3660) := by
    have ha : (tripleCharges (sourceA2102 + difference 0 1) (sourceB2102 + difference 1 0) sourceC2102) = raw29360 := by
      apply Matrix.ext; unfold tripleCharges sourceA2102 sourceB2102 sourceC2102 difference raw29360; decide +kernel
    rw [ha]
    exact (canonical29360 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2102 + difference 0 2) (sourceB2102 + difference 2 0) sourceC2102) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3658) := by
    have ha : (tripleCharges (sourceA2102 + difference 0 2) (sourceB2102 + difference 2 0) sourceC2102) = raw29361 := by
      apply Matrix.ext; unfold tripleCharges sourceA2102 sourceB2102 sourceC2102 difference raw29361; decide +kernel
    rw [ha]
    exact (canonical29361 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2102 + difference 0 3) (sourceB2102 + difference 3 0) sourceC2102) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3666) := by
    have ha : (tripleCharges (sourceA2102 + difference 0 3) (sourceB2102 + difference 3 0) sourceC2102) = raw29362 := by
      apply Matrix.ext; unfold tripleCharges sourceA2102 sourceB2102 sourceC2102 difference raw29362; decide +kernel
    rw [ha]
    exact (canonical29362 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2102 + difference 0 4) (sourceB2102 + difference 4 0) sourceC2102) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3772) := by
    have ha : (tripleCharges (sourceA2102 + difference 0 4) (sourceB2102 + difference 4 0) sourceC2102) = raw29363 := by
      apply Matrix.ext; unfold tripleCharges sourceA2102 sourceB2102 sourceC2102 difference raw29363; decide +kernel
    rw [ha]
    exact (canonical29363 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2102 + difference 0 5) (sourceB2102 + difference 5 0) sourceC2102) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3772) := by
    have ha : (tripleCharges (sourceA2102 + difference 0 5) (sourceB2102 + difference 5 0) sourceC2102) = raw29364 := by
      apply Matrix.ext; unfold tripleCharges sourceA2102 sourceB2102 sourceC2102 difference raw29364; decide +kernel
    rw [ha]
    exact (canonical29364 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2102 + sourceB2102) sourceC2102) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4089) := by
    have ha : (doubleCharges (sourceA2102 + sourceB2102) sourceC2102) = raw29365 := by
      apply Matrix.ext; unfold doubleCharges sourceA2102 sourceB2102 sourceC2102 raw29365; decide +kernel
    rw [ha]
    exact (canonical29365 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2102 sourceB2102 sourceC2102
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2102, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2103 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2103 : Charge := ![3, -2, 0, 0, 0, -1]
def sourceC2103 : Charge := ![0, 3, 0, 0, -2, -1]
def sourceForm2103 : Integer.Sparse Master := [(Sum.inr 2346, 1), (Sum.inr 2821, 1), (Sum.inr 3129, 2), (Sum.inr 3161, 1), (Sum.inr 3397, 1), (Sum.inr 4084, -1)]

theorem sourceEq2103 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2103 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2103 + difference 0 1) (sourceB2103 + difference 1 0) sourceC2103) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3397) := by
    have ha : (tripleCharges (sourceA2103 + difference 0 1) (sourceB2103 + difference 1 0) sourceC2103) = raw29366 := by
      apply Matrix.ext; unfold tripleCharges sourceA2103 sourceB2103 sourceC2103 difference raw29366; decide +kernel
    rw [ha]
    exact (canonical29366 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2103 + difference 1 1) (sourceB2103 + difference 1 1) sourceC2103) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3161) := by
    have ha : (tripleCharges (sourceA2103 + difference 1 1) (sourceB2103 + difference 1 1) sourceC2103) = raw29367 := by
      apply Matrix.ext; unfold tripleCharges sourceA2103 sourceB2103 sourceC2103 difference raw29367; decide +kernel
    rw [ha]
    exact (canonical29367 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2103 + difference 2 1) (sourceB2103 + difference 1 2) sourceC2103) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3129) := by
    have ha : (tripleCharges (sourceA2103 + difference 2 1) (sourceB2103 + difference 1 2) sourceC2103) = raw29368 := by
      apply Matrix.ext; unfold tripleCharges sourceA2103 sourceB2103 sourceC2103 difference raw29368; decide +kernel
    rw [ha]
    exact (canonical29368 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2103 + difference 3 1) (sourceB2103 + difference 1 3) sourceC2103) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3129) := by
    have ha : (tripleCharges (sourceA2103 + difference 3 1) (sourceB2103 + difference 1 3) sourceC2103) = raw29369 := by
      apply Matrix.ext; unfold tripleCharges sourceA2103 sourceB2103 sourceC2103 difference raw29369; decide +kernel
    rw [ha]
    exact (canonical29369 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2103 + difference 4 1) (sourceB2103 + difference 1 4) sourceC2103) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2346) := by
    have ha : (tripleCharges (sourceA2103 + difference 4 1) (sourceB2103 + difference 1 4) sourceC2103) = raw29370 := by
      apply Matrix.ext; unfold tripleCharges sourceA2103 sourceB2103 sourceC2103 difference raw29370; decide +kernel
    rw [ha]
    exact (canonical29370 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2103 + difference 5 1) (sourceB2103 + difference 1 5) sourceC2103) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2821) := by
    have ha : (tripleCharges (sourceA2103 + difference 5 1) (sourceB2103 + difference 1 5) sourceC2103) = raw29371 := by
      apply Matrix.ext; unfold tripleCharges sourceA2103 sourceB2103 sourceC2103 difference raw29371; decide +kernel
    rw [ha]
    exact (canonical29371 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2103 + sourceB2103) sourceC2103) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA2103 + sourceB2103) sourceC2103) = raw29372 := by
      apply Matrix.ext; unfold doubleCharges sourceA2103 sourceB2103 sourceC2103 raw29372; decide +kernel
    rw [ha]
    exact (canonical29372 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2103 sourceB2103 sourceC2103
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2103, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2104 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2104 : Charge := ![3, -2, 0, -1, 0, 0]
def sourceC2104 : Charge := ![0, 3, 0, 1, -2, -2]
def sourceForm2104 : Integer.Sparse Master := [(Sum.inr 3147, 1), (Sum.inr 3372, 1), (Sum.inr 3473, 1), (Sum.inr 3480, 2), (Sum.inr 3611, 1), (Sum.inr 4082, -1)]

theorem sourceEq2104 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2104 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2104 + difference 0 0) (sourceB2104 + difference 0 0) sourceC2104) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3147) := by
    have ha : (tripleCharges (sourceA2104 + difference 0 0) (sourceB2104 + difference 0 0) sourceC2104) = raw29373 := by
      apply Matrix.ext; unfold tripleCharges sourceA2104 sourceB2104 sourceC2104 difference raw29373; decide +kernel
    rw [ha]
    exact (canonical29373 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2104 + difference 0 1) (sourceB2104 + difference 1 0) sourceC2104) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3372) := by
    have ha : (tripleCharges (sourceA2104 + difference 0 1) (sourceB2104 + difference 1 0) sourceC2104) = raw29374 := by
      apply Matrix.ext; unfold tripleCharges sourceA2104 sourceB2104 sourceC2104 difference raw29374; decide +kernel
    rw [ha]
    exact (canonical29374 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2104 + difference 0 2) (sourceB2104 + difference 2 0) sourceC2104) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3473) := by
    have ha : (tripleCharges (sourceA2104 + difference 0 2) (sourceB2104 + difference 2 0) sourceC2104) = raw29375 := by
      apply Matrix.ext; unfold tripleCharges sourceA2104 sourceB2104 sourceC2104 difference raw29375; decide +kernel
    rw [ha]
    exact (canonical29375 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2104 + difference 0 3) (sourceB2104 + difference 3 0) sourceC2104) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3611) := by
    have ha : (tripleCharges (sourceA2104 + difference 0 3) (sourceB2104 + difference 3 0) sourceC2104) = raw29376 := by
      apply Matrix.ext; unfold tripleCharges sourceA2104 sourceB2104 sourceC2104 difference raw29376; decide +kernel
    rw [ha]
    exact (canonical29376 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2104 + difference 0 4) (sourceB2104 + difference 4 0) sourceC2104) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3480) := by
    have ha : (tripleCharges (sourceA2104 + difference 0 4) (sourceB2104 + difference 4 0) sourceC2104) = raw29377 := by
      apply Matrix.ext; unfold tripleCharges sourceA2104 sourceB2104 sourceC2104 difference raw29377; decide +kernel
    rw [ha]
    exact (canonical29377 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2104 + difference 0 5) (sourceB2104 + difference 5 0) sourceC2104) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3480) := by
    have ha : (tripleCharges (sourceA2104 + difference 0 5) (sourceB2104 + difference 5 0) sourceC2104) = raw29378 := by
      apply Matrix.ext; unfold tripleCharges sourceA2104 sourceB2104 sourceC2104 difference raw29378; decide +kernel
    rw [ha]
    exact (canonical29378 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2104 + sourceB2104) sourceC2104) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2104 + sourceB2104) sourceC2104) = raw29379 := by
      apply Matrix.ext; unfold doubleCharges sourceA2104 sourceB2104 sourceC2104 raw29379; decide +kernel
    rw [ha]
    exact (canonical29379 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2104 sourceB2104 sourceC2104
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2104, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2105 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2105 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceC2105 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceForm2105 : Integer.Sparse Master := [(Sum.inr 1141, 1), (Sum.inr 2343, 1), (Sum.inr 2433, 1), (Sum.inr 2499, 1), (Sum.inr 2512, 1), (Sum.inr 2515, 1), (Sum.inr 4092, -1)]

theorem sourceEq2105 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2105 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2105 + difference 3 0) (sourceB2105 + difference 0 3) sourceC2105) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1141) := by
    have ha : (tripleCharges (sourceA2105 + difference 3 0) (sourceB2105 + difference 0 3) sourceC2105) = raw29380 := by
      apply Matrix.ext; unfold tripleCharges sourceA2105 sourceB2105 sourceC2105 difference raw29380; decide +kernel
    rw [ha]
    exact (canonical29380 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2105 + difference 3 1) (sourceB2105 + difference 1 3) sourceC2105) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2343) := by
    have ha : (tripleCharges (sourceA2105 + difference 3 1) (sourceB2105 + difference 1 3) sourceC2105) = raw29381 := by
      apply Matrix.ext; unfold tripleCharges sourceA2105 sourceB2105 sourceC2105 difference raw29381; decide +kernel
    rw [ha]
    exact (canonical29381 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2105 + difference 3 2) (sourceB2105 + difference 2 3) sourceC2105) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2433) := by
    have ha : (tripleCharges (sourceA2105 + difference 3 2) (sourceB2105 + difference 2 3) sourceC2105) = raw29382 := by
      apply Matrix.ext; unfold tripleCharges sourceA2105 sourceB2105 sourceC2105 difference raw29382; decide +kernel
    rw [ha]
    exact (canonical29382 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2105 + difference 3 3) (sourceB2105 + difference 3 3) sourceC2105) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2499) := by
    have ha : (tripleCharges (sourceA2105 + difference 3 3) (sourceB2105 + difference 3 3) sourceC2105) = raw6565 := by
      apply Matrix.ext; unfold tripleCharges sourceA2105 sourceB2105 sourceC2105 difference raw6565; decide +kernel
    rw [ha]
    exact (canonical6565 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2105 + difference 3 4) (sourceB2105 + difference 4 3) sourceC2105) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2512) := by
    have ha : (tripleCharges (sourceA2105 + difference 3 4) (sourceB2105 + difference 4 3) sourceC2105) = raw6564 := by
      apply Matrix.ext; unfold tripleCharges sourceA2105 sourceB2105 sourceC2105 difference raw6564; decide +kernel
    rw [ha]
    exact (canonical6564 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2105 + difference 3 5) (sourceB2105 + difference 5 3) sourceC2105) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2515) := by
    have ha : (tripleCharges (sourceA2105 + difference 3 5) (sourceB2105 + difference 5 3) sourceC2105) = raw29383 := by
      apply Matrix.ext; unfold tripleCharges sourceA2105 sourceB2105 sourceC2105 difference raw29383; decide +kernel
    rw [ha]
    exact (canonical29383 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2105 + sourceB2105) sourceC2105) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2105 + sourceB2105) sourceC2105) = raw6553 := by
      apply Matrix.ext; unfold doubleCharges sourceA2105 sourceB2105 sourceC2105 raw6553; decide +kernel
    rw [ha]
    exact (canonical6553 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2105 sourceB2105 sourceC2105
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2105, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2106 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2106 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC2106 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceForm2106 : Integer.Sparse Master := [(Sum.inr 2335, 1), (Sum.inr 2811, 1), (Sum.inr 2846, 1), (Sum.inr 2889, 1), (Sum.inr 2979, 1), (Sum.inr 3705, 1), (Sum.inr 4092, -1)]

theorem sourceEq2106 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2106 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2106 + difference 0 3) (sourceB2106 + difference 3 0) sourceC2106) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3705) := by
    have ha : (tripleCharges (sourceA2106 + difference 0 3) (sourceB2106 + difference 3 0) sourceC2106) = raw29384 := by
      apply Matrix.ext; unfold tripleCharges sourceA2106 sourceB2106 sourceC2106 difference raw29384; decide +kernel
    rw [ha]
    exact (canonical29384 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2106 + difference 1 3) (sourceB2106 + difference 3 1) sourceC2106) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2889) := by
    have ha : (tripleCharges (sourceA2106 + difference 1 3) (sourceB2106 + difference 3 1) sourceC2106) = raw8546 := by
      apply Matrix.ext; unfold tripleCharges sourceA2106 sourceB2106 sourceC2106 difference raw8546; decide +kernel
    rw [ha]
    exact (canonical8546 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2106 + difference 2 3) (sourceB2106 + difference 3 2) sourceC2106) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2846) := by
    have ha : (tripleCharges (sourceA2106 + difference 2 3) (sourceB2106 + difference 3 2) sourceC2106) = raw29385 := by
      apply Matrix.ext; unfold tripleCharges sourceA2106 sourceB2106 sourceC2106 difference raw29385; decide +kernel
    rw [ha]
    exact (canonical29385 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2106 + difference 3 3) (sourceB2106 + difference 3 3) sourceC2106) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2979) := by
    have ha : (tripleCharges (sourceA2106 + difference 3 3) (sourceB2106 + difference 3 3) sourceC2106) = raw8543 := by
      apply Matrix.ext; unfold tripleCharges sourceA2106 sourceB2106 sourceC2106 difference raw8543; decide +kernel
    rw [ha]
    exact (canonical8543 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2106 + difference 4 3) (sourceB2106 + difference 3 4) sourceC2106) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2335) := by
    have ha : (tripleCharges (sourceA2106 + difference 4 3) (sourceB2106 + difference 3 4) sourceC2106) = raw29386 := by
      apply Matrix.ext; unfold tripleCharges sourceA2106 sourceB2106 sourceC2106 difference raw29386; decide +kernel
    rw [ha]
    exact (canonical29386 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2106 + difference 5 3) (sourceB2106 + difference 3 5) sourceC2106) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2811) := by
    have ha : (tripleCharges (sourceA2106 + difference 5 3) (sourceB2106 + difference 3 5) sourceC2106) = raw29387 := by
      apply Matrix.ext; unfold tripleCharges sourceA2106 sourceB2106 sourceC2106 difference raw29387; decide +kernel
    rw [ha]
    exact (canonical29387 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2106 + sourceB2106) sourceC2106) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2106 + sourceB2106) sourceC2106) = raw8531 := by
      apply Matrix.ext; unfold doubleCharges sourceA2106 sourceB2106 sourceC2106 raw8531; decide +kernel
    rw [ha]
    exact (canonical8531 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2106 sourceB2106 sourceC2106
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2106, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2107 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceB2107 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC2107 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceForm2107 : Integer.Sparse Master := [(Sum.inr 2387, 1), (Sum.inr 3369, 1), (Sum.inr 3372, 1), (Sum.inr 3386, 1), (Sum.inr 3480, 1), (Sum.inr 3522, 1), (Sum.inr 4082, -1)]

theorem sourceEq2107 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2107 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2107 + difference 0 0) (sourceB2107 + difference 0 0) sourceC2107) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3480) := by
    have ha : (tripleCharges (sourceA2107 + difference 0 0) (sourceB2107 + difference 0 0) sourceC2107) = raw29388 := by
      apply Matrix.ext; unfold tripleCharges sourceA2107 sourceB2107 sourceC2107 difference raw29388; decide +kernel
    rw [ha]
    exact (canonical29388 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2107 + difference 0 1) (sourceB2107 + difference 1 0) sourceC2107) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3386) := by
    have ha : (tripleCharges (sourceA2107 + difference 0 1) (sourceB2107 + difference 1 0) sourceC2107) = raw29389 := by
      apply Matrix.ext; unfold tripleCharges sourceA2107 sourceB2107 sourceC2107 difference raw29389; decide +kernel
    rw [ha]
    exact (canonical29389 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2107 + difference 0 2) (sourceB2107 + difference 2 0) sourceC2107) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3369) := by
    have ha : (tripleCharges (sourceA2107 + difference 0 2) (sourceB2107 + difference 2 0) sourceC2107) = raw29390 := by
      apply Matrix.ext; unfold tripleCharges sourceA2107 sourceB2107 sourceC2107 difference raw29390; decide +kernel
    rw [ha]
    exact (canonical29390 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2107 + difference 0 3) (sourceB2107 + difference 3 0) sourceC2107) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3522) := by
    have ha : (tripleCharges (sourceA2107 + difference 0 3) (sourceB2107 + difference 3 0) sourceC2107) = raw29391 := by
      apply Matrix.ext; unfold tripleCharges sourceA2107 sourceB2107 sourceC2107 difference raw29391; decide +kernel
    rw [ha]
    exact (canonical29391 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2107 + difference 0 4) (sourceB2107 + difference 4 0) sourceC2107) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2387) := by
    have ha : (tripleCharges (sourceA2107 + difference 0 4) (sourceB2107 + difference 4 0) sourceC2107) = raw29392 := by
      apply Matrix.ext; unfold tripleCharges sourceA2107 sourceB2107 sourceC2107 difference raw29392; decide +kernel
    rw [ha]
    exact (canonical29392 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2107 + difference 0 5) (sourceB2107 + difference 5 0) sourceC2107) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3372) := by
    have ha : (tripleCharges (sourceA2107 + difference 0 5) (sourceB2107 + difference 5 0) sourceC2107) = raw29393 := by
      apply Matrix.ext; unfold tripleCharges sourceA2107 sourceB2107 sourceC2107 difference raw29393; decide +kernel
    rw [ha]
    exact (canonical29393 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2107 + sourceB2107) sourceC2107) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2107 + sourceB2107) sourceC2107) = raw29319 := by
      apply Matrix.ext; unfold doubleCharges sourceA2107 sourceB2107 sourceC2107 raw29319; decide +kernel
    rw [ha]
    exact (canonical29319 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2107 sourceB2107 sourceC2107
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2107, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2108 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceB2108 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC2108 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceForm2108 : Integer.Sparse Master := [(Sum.inr 3476, 1), (Sum.inr 3478, 1), (Sum.inr 3480, 1), (Sum.inr 3482, 1), (Sum.inr 3522, 1), (Sum.inr 3612, 1), (Sum.inr 4082, -1)]

theorem sourceEq2108 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2108 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2108 + difference 0 3) (sourceB2108 + difference 3 0) sourceC2108) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3522) := by
    have ha : (tripleCharges (sourceA2108 + difference 0 3) (sourceB2108 + difference 3 0) sourceC2108) = raw29391 := by
      apply Matrix.ext; unfold tripleCharges sourceA2108 sourceB2108 sourceC2108 difference raw29391; decide +kernel
    rw [ha]
    exact (canonical29391 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2108 + difference 1 3) (sourceB2108 + difference 3 1) sourceC2108) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3612) := by
    have ha : (tripleCharges (sourceA2108 + difference 1 3) (sourceB2108 + difference 3 1) sourceC2108) = raw29313 := by
      apply Matrix.ext; unfold tripleCharges sourceA2108 sourceB2108 sourceC2108 difference raw29313; decide +kernel
    rw [ha]
    exact (canonical29313 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2108 + difference 2 3) (sourceB2108 + difference 3 2) sourceC2108) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3476) := by
    have ha : (tripleCharges (sourceA2108 + difference 2 3) (sourceB2108 + difference 3 2) sourceC2108) = raw29328 := by
      apply Matrix.ext; unfold tripleCharges sourceA2108 sourceB2108 sourceC2108 difference raw29328; decide +kernel
    rw [ha]
    exact (canonical29328 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2108 + difference 3 3) (sourceB2108 + difference 3 3) sourceC2108) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3480) := by
    have ha : (tripleCharges (sourceA2108 + difference 3 3) (sourceB2108 + difference 3 3) sourceC2108) = raw29388 := by
      apply Matrix.ext; unfold tripleCharges sourceA2108 sourceB2108 sourceC2108 difference raw29388; decide +kernel
    rw [ha]
    exact (canonical29388 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2108 + difference 4 3) (sourceB2108 + difference 3 4) sourceC2108) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3482) := by
    have ha : (tripleCharges (sourceA2108 + difference 4 3) (sourceB2108 + difference 3 4) sourceC2108) = raw29394 := by
      apply Matrix.ext; unfold tripleCharges sourceA2108 sourceB2108 sourceC2108 difference raw29394; decide +kernel
    rw [ha]
    exact (canonical29394 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2108 + difference 5 3) (sourceB2108 + difference 3 5) sourceC2108) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3478) := by
    have ha : (tripleCharges (sourceA2108 + difference 5 3) (sourceB2108 + difference 3 5) sourceC2108) = raw29395 := by
      apply Matrix.ext; unfold tripleCharges sourceA2108 sourceB2108 sourceC2108 difference raw29395; decide +kernel
    rw [ha]
    exact (canonical29395 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2108 + sourceB2108) sourceC2108) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2108 + sourceB2108) sourceC2108) = raw29319 := by
      apply Matrix.ext; unfold doubleCharges sourceA2108 sourceB2108 sourceC2108 raw29319; decide +kernel
    rw [ha]
    exact (canonical29319 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2108 sourceB2108 sourceC2108
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2108, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2109 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceB2109 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC2109 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceForm2109 : Integer.Sparse Master := [(Sum.inr 1949, 1), (Sum.inr 3359, 1), (Sum.inr 3438, 1), (Sum.inr 3480, 2), (Sum.inr 3482, 1), (Sum.inr 4082, -1)]

theorem sourceEq2109 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2109 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2109 + difference 4 0) (sourceB2109 + difference 0 4) sourceC2109) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1949) := by
    have ha : (tripleCharges (sourceA2109 + difference 4 0) (sourceB2109 + difference 0 4) sourceC2109) = raw29396 := by
      apply Matrix.ext; unfold tripleCharges sourceA2109 sourceB2109 sourceC2109 difference raw29396; decide +kernel
    rw [ha]
    exact (canonical29396 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2109 + difference 4 1) (sourceB2109 + difference 1 4) sourceC2109) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3359) := by
    have ha : (tripleCharges (sourceA2109 + difference 4 1) (sourceB2109 + difference 1 4) sourceC2109) = raw29397 := by
      apply Matrix.ext; unfold tripleCharges sourceA2109 sourceB2109 sourceC2109 difference raw29397; decide +kernel
    rw [ha]
    exact (canonical29397 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2109 + difference 4 2) (sourceB2109 + difference 2 4) sourceC2109) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3438) := by
    have ha : (tripleCharges (sourceA2109 + difference 4 2) (sourceB2109 + difference 2 4) sourceC2109) = raw29398 := by
      apply Matrix.ext; unfold tripleCharges sourceA2109 sourceB2109 sourceC2109 difference raw29398; decide +kernel
    rw [ha]
    exact (canonical29398 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2109 + difference 4 3) (sourceB2109 + difference 3 4) sourceC2109) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3482) := by
    have ha : (tripleCharges (sourceA2109 + difference 4 3) (sourceB2109 + difference 3 4) sourceC2109) = raw29394 := by
      apply Matrix.ext; unfold tripleCharges sourceA2109 sourceB2109 sourceC2109 difference raw29394; decide +kernel
    rw [ha]
    exact (canonical29394 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2109 + difference 4 4) (sourceB2109 + difference 4 4) sourceC2109) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3480) := by
    have ha : (tripleCharges (sourceA2109 + difference 4 4) (sourceB2109 + difference 4 4) sourceC2109) = raw29388 := by
      apply Matrix.ext; unfold tripleCharges sourceA2109 sourceB2109 sourceC2109 difference raw29388; decide +kernel
    rw [ha]
    exact (canonical29388 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2109 + difference 4 5) (sourceB2109 + difference 5 4) sourceC2109) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3480) := by
    have ha : (tripleCharges (sourceA2109 + difference 4 5) (sourceB2109 + difference 5 4) sourceC2109) = raw29399 := by
      apply Matrix.ext; unfold tripleCharges sourceA2109 sourceB2109 sourceC2109 difference raw29399; decide +kernel
    rw [ha]
    exact (canonical29399 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2109 + sourceB2109) sourceC2109) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2109 + sourceB2109) sourceC2109) = raw29319 := by
      apply Matrix.ext; unfold doubleCharges sourceA2109 sourceB2109 sourceC2109 raw29319; decide +kernel
    rw [ha]
    exact (canonical29319 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2109 sourceB2109 sourceC2109
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2109, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2110 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceB2110 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC2110 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceForm2110 : Integer.Sparse Master := [(Sum.inr 1928, 1), (Sum.inr 2674, 1), (Sum.inr 3348, 1), (Sum.inr 3430, 1), (Sum.inr 3478, 1), (Sum.inr 3480, 1), (Sum.inr 4082, -1)]

theorem sourceEq2110 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2110 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2110 + difference 5 0) (sourceB2110 + difference 0 5) sourceC2110) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1928) := by
    have ha : (tripleCharges (sourceA2110 + difference 5 0) (sourceB2110 + difference 0 5) sourceC2110) = raw29400 := by
      apply Matrix.ext; unfold tripleCharges sourceA2110 sourceB2110 sourceC2110 difference raw29400; decide +kernel
    rw [ha]
    exact (canonical29400 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2110 + difference 5 1) (sourceB2110 + difference 1 5) sourceC2110) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3348) := by
    have ha : (tripleCharges (sourceA2110 + difference 5 1) (sourceB2110 + difference 1 5) sourceC2110) = raw29401 := by
      apply Matrix.ext; unfold tripleCharges sourceA2110 sourceB2110 sourceC2110 difference raw29401; decide +kernel
    rw [ha]
    exact (canonical29401 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2110 + difference 5 2) (sourceB2110 + difference 2 5) sourceC2110) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3430) := by
    have ha : (tripleCharges (sourceA2110 + difference 5 2) (sourceB2110 + difference 2 5) sourceC2110) = raw29402 := by
      apply Matrix.ext; unfold tripleCharges sourceA2110 sourceB2110 sourceC2110 difference raw29402; decide +kernel
    rw [ha]
    exact (canonical29402 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2110 + difference 5 3) (sourceB2110 + difference 3 5) sourceC2110) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3478) := by
    have ha : (tripleCharges (sourceA2110 + difference 5 3) (sourceB2110 + difference 3 5) sourceC2110) = raw29395 := by
      apply Matrix.ext; unfold tripleCharges sourceA2110 sourceB2110 sourceC2110 difference raw29395; decide +kernel
    rw [ha]
    exact (canonical29395 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2110 + difference 5 4) (sourceB2110 + difference 4 5) sourceC2110) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2674) := by
    have ha : (tripleCharges (sourceA2110 + difference 5 4) (sourceB2110 + difference 4 5) sourceC2110) = raw29403 := by
      apply Matrix.ext; unfold tripleCharges sourceA2110 sourceB2110 sourceC2110 difference raw29403; decide +kernel
    rw [ha]
    exact (canonical29403 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2110 + difference 5 5) (sourceB2110 + difference 5 5) sourceC2110) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3480) := by
    have ha : (tripleCharges (sourceA2110 + difference 5 5) (sourceB2110 + difference 5 5) sourceC2110) = raw29388 := by
      apply Matrix.ext; unfold tripleCharges sourceA2110 sourceB2110 sourceC2110 difference raw29388; decide +kernel
    rw [ha]
    exact (canonical29388 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2110 + sourceB2110) sourceC2110) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2110 + sourceB2110) sourceC2110) = raw29319 := by
      apply Matrix.ext; unfold doubleCharges sourceA2110 sourceB2110 sourceC2110 raw29319; decide +kernel
    rw [ha]
    exact (canonical29319 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2110 sourceB2110 sourceC2110
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2110, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2111 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2111 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceC2111 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceForm2111 : Integer.Sparse Master := [(Sum.inr 1117, 1), (Sum.inr 2324, 1), (Sum.inr 2441, 1), (Sum.inr 2473, 1), (Sum.inr 2480, 1), (Sum.inr 2483, 1), (Sum.inr 4091, -1)]

theorem sourceEq2111 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2111 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2111 + difference 2 0) (sourceB2111 + difference 0 2) sourceC2111) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1117) := by
    have ha : (tripleCharges (sourceA2111 + difference 2 0) (sourceB2111 + difference 0 2) sourceC2111) = raw29404 := by
      apply Matrix.ext; unfold tripleCharges sourceA2111 sourceB2111 sourceC2111 difference raw29404; decide +kernel
    rw [ha]
    exact (canonical29404 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2111 + difference 2 1) (sourceB2111 + difference 1 2) sourceC2111) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2324) := by
    have ha : (tripleCharges (sourceA2111 + difference 2 1) (sourceB2111 + difference 1 2) sourceC2111) = raw29405 := by
      apply Matrix.ext; unfold tripleCharges sourceA2111 sourceB2111 sourceC2111 difference raw29405; decide +kernel
    rw [ha]
    exact (canonical29405 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2111 + difference 2 2) (sourceB2111 + difference 2 2) sourceC2111) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2473) := by
    have ha : (tripleCharges (sourceA2111 + difference 2 2) (sourceB2111 + difference 2 2) sourceC2111) = raw7211 := by
      apply Matrix.ext; unfold tripleCharges sourceA2111 sourceB2111 sourceC2111 difference raw7211; decide +kernel
    rw [ha]
    exact (canonical7211 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2111 + difference 2 3) (sourceB2111 + difference 3 2) sourceC2111) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2441) := by
    have ha : (tripleCharges (sourceA2111 + difference 2 3) (sourceB2111 + difference 3 2) sourceC2111) = raw29406 := by
      apply Matrix.ext; unfold tripleCharges sourceA2111 sourceB2111 sourceC2111 difference raw29406; decide +kernel
    rw [ha]
    exact (canonical29406 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2111 + difference 2 4) (sourceB2111 + difference 4 2) sourceC2111) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2480) := by
    have ha : (tripleCharges (sourceA2111 + difference 2 4) (sourceB2111 + difference 4 2) sourceC2111) = raw7209 := by
      apply Matrix.ext; unfold tripleCharges sourceA2111 sourceB2111 sourceC2111 difference raw7209; decide +kernel
    rw [ha]
    exact (canonical7209 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2111 + difference 2 5) (sourceB2111 + difference 5 2) sourceC2111) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2483) := by
    have ha : (tripleCharges (sourceA2111 + difference 2 5) (sourceB2111 + difference 5 2) sourceC2111) = raw29407 := by
      apply Matrix.ext; unfold tripleCharges sourceA2111 sourceB2111 sourceC2111 difference raw29407; decide +kernel
    rw [ha]
    exact (canonical29407 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2111 + sourceB2111) sourceC2111) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA2111 + sourceB2111) sourceC2111) = raw7199 := by
      apply Matrix.ext; unfold doubleCharges sourceA2111 sourceB2111 sourceC2111 raw7199; decide +kernel
    rw [ha]
    exact (canonical7199 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2111 sourceB2111 sourceC2111
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2111, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
