import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical85
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical89
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical127
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical149
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical165
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical168
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical179
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical180
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical181
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical182
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical214
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical227
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical229
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical230
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical231
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical233
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical234
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical235
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical237
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical238
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical239
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical240
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical241
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical242
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical243
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical244

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA2240 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2240 : Charge := ![1, 0, 0, -1, 0, 0]
def sourceC2240 : Charge := ![2, 1, 0, 1, -2, -2]
def sourceForm2240 : Integer.Sparse Master := [(Sum.inr 1106, 1), (Sum.inr 2316, 1), (Sum.inr 2414, 1), (Sum.inr 2459, 2), (Sum.inr 2468, 1), (Sum.inr 4088, -1)]

theorem sourceEq2240 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2240 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2240 + difference 2 0) (sourceB2240 + difference 0 2) sourceC2240) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1106) := by
    have ha : (tripleCharges (sourceA2240 + difference 2 0) (sourceB2240 + difference 0 2) sourceC2240) = raw30825 := by
      apply Matrix.ext; unfold tripleCharges sourceA2240 sourceB2240 sourceC2240 difference raw30825; decide +kernel
    rw [ha]
    exact (canonical30825 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2240 + difference 2 1) (sourceB2240 + difference 1 2) sourceC2240) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2316) := by
    have ha : (tripleCharges (sourceA2240 + difference 2 1) (sourceB2240 + difference 1 2) sourceC2240) = raw30826 := by
      apply Matrix.ext; unfold tripleCharges sourceA2240 sourceB2240 sourceC2240 difference raw30826; decide +kernel
    rw [ha]
    exact (canonical30826 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2240 + difference 2 2) (sourceB2240 + difference 2 2) sourceC2240) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2468) := by
    have ha : (tripleCharges (sourceA2240 + difference 2 2) (sourceB2240 + difference 2 2) sourceC2240) = raw29137 := by
      apply Matrix.ext; unfold tripleCharges sourceA2240 sourceB2240 sourceC2240 difference raw29137; decide +kernel
    rw [ha]
    exact (canonical29137 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2240 + difference 2 3) (sourceB2240 + difference 3 2) sourceC2240) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2414) := by
    have ha : (tripleCharges (sourceA2240 + difference 2 3) (sourceB2240 + difference 3 2) sourceC2240) = raw30827 := by
      apply Matrix.ext; unfold tripleCharges sourceA2240 sourceB2240 sourceC2240 difference raw30827; decide +kernel
    rw [ha]
    exact (canonical30827 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2240 + difference 2 4) (sourceB2240 + difference 4 2) sourceC2240) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2459) := by
    have ha : (tripleCharges (sourceA2240 + difference 2 4) (sourceB2240 + difference 4 2) sourceC2240) = raw29139 := by
      apply Matrix.ext; unfold tripleCharges sourceA2240 sourceB2240 sourceC2240 difference raw29139; decide +kernel
    rw [ha]
    exact (canonical29139 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2240 + difference 2 5) (sourceB2240 + difference 5 2) sourceC2240) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2459) := by
    have ha : (tripleCharges (sourceA2240 + difference 2 5) (sourceB2240 + difference 5 2) sourceC2240) = raw30828 := by
      apply Matrix.ext; unfold tripleCharges sourceA2240 sourceB2240 sourceC2240 difference raw30828; decide +kernel
    rw [ha]
    exact (canonical30828 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2240 + sourceB2240) sourceC2240) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA2240 + sourceB2240) sourceC2240) = raw29129 := by
      apply Matrix.ext; unfold doubleCharges sourceA2240 sourceB2240 sourceC2240 raw29129; decide +kernel
    rw [ha]
    exact (canonical29129 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2240 sourceB2240 sourceC2240
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2240, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2241 : Charge := ![1, 0, 0, -1, 0, 0]
def sourceB2241 : Charge := ![2, 1, 0, 1, -2, -2]
def sourceC2241 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceForm2241 : Integer.Sparse Master := [(Sum.inr 4082, 1), (Sum.inr 4711, 1), (Sum.inr 4718, 2), (Sum.inr 4790, 1), (Sum.inr 4909, 2), (Sum.inr 4914, 2), (Sum.inr 4920, 2), (Sum.inr 4988, 1), (Sum.inr 5014, 2), (Sum.inr 5024, 1), (Sum.inr 5045, 1), (Sum.inr 5050, 2), (Sum.inr 5063, 1), (Sum.inr 5111, 2), (Sum.inr 5125, 1), (Sum.inr 5126, 1), (Sum.inr 5141, 2), (Sum.inr 5142, 1), (Sum.inr 5152, 2), (Sum.inr 5156, 1), (Sum.inr 5193, 1)]

theorem sourceEq2241 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2241 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2241 + difference 0 1) (sourceB2241 + difference 1 0) sourceC2241) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5193) := by
    have ha : (tripleCharges (sourceA2241 + difference 0 1) (sourceB2241 + difference 1 0) sourceC2241) = raw30829 := by
      apply Matrix.ext; unfold tripleCharges sourceA2241 sourceB2241 sourceC2241 difference raw30829; decide +kernel
    rw [ha]
    exact (canonical30829 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2241 + difference 0 2) (sourceB2241 + difference 2 0) sourceC2241) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5142) := by
    have ha : (tripleCharges (sourceA2241 + difference 0 2) (sourceB2241 + difference 2 0) sourceC2241) = raw30830 := by
      apply Matrix.ext; unfold tripleCharges sourceA2241 sourceB2241 sourceC2241 difference raw30830; decide +kernel
    rw [ha]
    exact (canonical30830 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2241 + difference 0 3) (sourceB2241 + difference 3 0) sourceC2241) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5156) := by
    have ha : (tripleCharges (sourceA2241 + difference 0 3) (sourceB2241 + difference 3 0) sourceC2241) = raw30831 := by
      apply Matrix.ext; unfold tripleCharges sourceA2241 sourceB2241 sourceC2241 difference raw30831; decide +kernel
    rw [ha]
    exact (canonical30831 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2241 + difference 0 4) (sourceB2241 + difference 4 0) sourceC2241) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5152) := by
    have ha : (tripleCharges (sourceA2241 + difference 0 4) (sourceB2241 + difference 4 0) sourceC2241) = raw30832 := by
      apply Matrix.ext; unfold tripleCharges sourceA2241 sourceB2241 sourceC2241 difference raw30832; decide +kernel
    rw [ha]
    exact (canonical30832 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2241 + difference 0 5) (sourceB2241 + difference 5 0) sourceC2241) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5152) := by
    have ha : (tripleCharges (sourceA2241 + difference 0 5) (sourceB2241 + difference 5 0) sourceC2241) = raw30165 := by
      apply Matrix.ext; unfold tripleCharges sourceA2241 sourceB2241 sourceC2241 difference raw30165; decide +kernel
    rw [ha]
    exact (canonical30165 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2241 + difference 1 0) (sourceB2241 + difference 0 1) sourceC2241) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4790) := by
    have ha : (tripleCharges (sourceA2241 + difference 1 0) (sourceB2241 + difference 0 1) sourceC2241) = raw30182 := by
      apply Matrix.ext; unfold tripleCharges sourceA2241 sourceB2241 sourceC2241 difference raw30182; decide +kernel
    rw [ha]
    exact (canonical30182 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2241 + difference 1 2) (sourceB2241 + difference 2 1) sourceC2241) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5126) := by
    have ha : (tripleCharges (sourceA2241 + difference 1 2) (sourceB2241 + difference 2 1) sourceC2241) = raw30184 := by
      apply Matrix.ext; unfold tripleCharges sourceA2241 sourceB2241 sourceC2241 difference raw30184; decide +kernel
    rw [ha]
    exact (canonical30184 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2241 + difference 1 3) (sourceB2241 + difference 3 1) sourceC2241) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5125) := by
    have ha : (tripleCharges (sourceA2241 + difference 1 3) (sourceB2241 + difference 3 1) sourceC2241) = raw30185 := by
      apply Matrix.ext; unfold tripleCharges sourceA2241 sourceB2241 sourceC2241 difference raw30185; decide +kernel
    rw [ha]
    exact (canonical30185 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2241 + difference 1 4) (sourceB2241 + difference 4 1) sourceC2241) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA2241 + difference 1 4) (sourceB2241 + difference 4 1) sourceC2241) = raw29585 := by
      apply Matrix.ext; unfold tripleCharges sourceA2241 sourceB2241 sourceC2241 difference raw29585; decide +kernel
    rw [ha]
    exact (canonical29585 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2241 + difference 1 5) (sourceB2241 + difference 5 1) sourceC2241) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA2241 + difference 1 5) (sourceB2241 + difference 5 1) sourceC2241) = raw29693 := by
      apply Matrix.ext; unfold tripleCharges sourceA2241 sourceB2241 sourceC2241 difference raw29693; decide +kernel
    rw [ha]
    exact (canonical29693 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2241 + difference 2 0) (sourceB2241 + difference 0 2) sourceC2241) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4711) := by
    have ha : (tripleCharges (sourceA2241 + difference 2 0) (sourceB2241 + difference 0 2) sourceC2241) = raw30833 := by
      apply Matrix.ext; unfold tripleCharges sourceA2241 sourceB2241 sourceC2241 difference raw30833; decide +kernel
    rw [ha]
    exact (canonical30833 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2241 + difference 2 1) (sourceB2241 + difference 1 2) sourceC2241) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4988) := by
    have ha : (tripleCharges (sourceA2241 + difference 2 1) (sourceB2241 + difference 1 2) sourceC2241) = raw30834 := by
      apply Matrix.ext; unfold tripleCharges sourceA2241 sourceB2241 sourceC2241 difference raw30834; decide +kernel
    rw [ha]
    exact (canonical30834 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2241 + difference 2 3) (sourceB2241 + difference 3 2) sourceC2241) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5045) := by
    have ha : (tripleCharges (sourceA2241 + difference 2 3) (sourceB2241 + difference 3 2) sourceC2241) = raw30835 := by
      apply Matrix.ext; unfold tripleCharges sourceA2241 sourceB2241 sourceC2241 difference raw30835; decide +kernel
    rw [ha]
    exact (canonical30835 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2241 + difference 2 4) (sourceB2241 + difference 4 2) sourceC2241) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5050) := by
    have ha : (tripleCharges (sourceA2241 + difference 2 4) (sourceB2241 + difference 4 2) sourceC2241) = raw30550 := by
      apply Matrix.ext; unfold tripleCharges sourceA2241 sourceB2241 sourceC2241 difference raw30550; decide +kernel
    rw [ha]
    exact (canonical30550 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2241 + difference 2 5) (sourceB2241 + difference 5 2) sourceC2241) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5050) := by
    have ha : (tripleCharges (sourceA2241 + difference 2 5) (sourceB2241 + difference 5 2) sourceC2241) = raw30174 := by
      apply Matrix.ext; unfold tripleCharges sourceA2241 sourceB2241 sourceC2241 difference raw30174; decide +kernel
    rw [ha]
    exact (canonical30174 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2241 + difference 3 0) (sourceB2241 + difference 0 3) sourceC2241) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (tripleCharges (sourceA2241 + difference 3 0) (sourceB2241 + difference 0 3) sourceC2241) = raw30836 := by
      apply Matrix.ext; unfold tripleCharges sourceA2241 sourceB2241 sourceC2241 difference raw30836; decide +kernel
    rw [ha]
    exact (canonical30836 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2241 + difference 3 1) (sourceB2241 + difference 1 3) sourceC2241) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5024) := by
    have ha : (tripleCharges (sourceA2241 + difference 3 1) (sourceB2241 + difference 1 3) sourceC2241) = raw30837 := by
      apply Matrix.ext; unfold tripleCharges sourceA2241 sourceB2241 sourceC2241 difference raw30837; decide +kernel
    rw [ha]
    exact (canonical30837 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2241 + difference 3 2) (sourceB2241 + difference 2 3) sourceC2241) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5063) := by
    have ha : (tripleCharges (sourceA2241 + difference 3 2) (sourceB2241 + difference 2 3) sourceC2241) = raw30838 := by
      apply Matrix.ext; unfold tripleCharges sourceA2241 sourceB2241 sourceC2241 difference raw30838; decide +kernel
    rw [ha]
    exact (canonical30838 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2241 + difference 3 4) (sourceB2241 + difference 4 3) sourceC2241) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5111) := by
    have ha : (tripleCharges (sourceA2241 + difference 3 4) (sourceB2241 + difference 4 3) sourceC2241) = raw29583 := by
      apply Matrix.ext; unfold tripleCharges sourceA2241 sourceB2241 sourceC2241 difference raw29583; decide +kernel
    rw [ha]
    exact (canonical29583 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2241 + difference 3 5) (sourceB2241 + difference 5 3) sourceC2241) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5111) := by
    have ha : (tripleCharges (sourceA2241 + difference 3 5) (sourceB2241 + difference 5 3) sourceC2241) = raw29691 := by
      apply Matrix.ext; unfold tripleCharges sourceA2241 sourceB2241 sourceC2241 difference raw29691; decide +kernel
    rw [ha]
    exact (canonical29691 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2241 + difference 4 0) (sourceB2241 + difference 0 4) sourceC2241) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4718) := by
    have ha : (tripleCharges (sourceA2241 + difference 4 0) (sourceB2241 + difference 0 4) sourceC2241) = raw30839 := by
      apply Matrix.ext; unfold tripleCharges sourceA2241 sourceB2241 sourceC2241 difference raw30839; decide +kernel
    rw [ha]
    exact (canonical30839 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2241 + difference 4 1) (sourceB2241 + difference 1 4) sourceC2241) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4914) := by
    have ha : (tripleCharges (sourceA2241 + difference 4 1) (sourceB2241 + difference 1 4) sourceC2241) = raw30840 := by
      apply Matrix.ext; unfold tripleCharges sourceA2241 sourceB2241 sourceC2241 difference raw30840; decide +kernel
    rw [ha]
    exact (canonical30840 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2241 + difference 4 2) (sourceB2241 + difference 2 4) sourceC2241) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4909) := by
    have ha : (tripleCharges (sourceA2241 + difference 4 2) (sourceB2241 + difference 2 4) sourceC2241) = raw30841 := by
      apply Matrix.ext; unfold tripleCharges sourceA2241 sourceB2241 sourceC2241 difference raw30841; decide +kernel
    rw [ha]
    exact (canonical30841 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2241 + difference 4 3) (sourceB2241 + difference 3 4) sourceC2241) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4920) := by
    have ha : (tripleCharges (sourceA2241 + difference 4 3) (sourceB2241 + difference 3 4) sourceC2241) = raw30842 := by
      apply Matrix.ext; unfold tripleCharges sourceA2241 sourceB2241 sourceC2241 difference raw30842; decide +kernel
    rw [ha]
    exact (canonical30842 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2241 + difference 4 5) (sourceB2241 + difference 5 4) sourceC2241) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5014) := by
    have ha : (tripleCharges (sourceA2241 + difference 4 5) (sourceB2241 + difference 5 4) sourceC2241) = raw30178 := by
      apply Matrix.ext; unfold tripleCharges sourceA2241 sourceB2241 sourceC2241 difference raw30178; decide +kernel
    rw [ha]
    exact (canonical30178 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2241 + difference 5 0) (sourceB2241 + difference 0 5) sourceC2241) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4718) := by
    have ha : (tripleCharges (sourceA2241 + difference 5 0) (sourceB2241 + difference 0 5) sourceC2241) = raw30843 := by
      apply Matrix.ext; unfold tripleCharges sourceA2241 sourceB2241 sourceC2241 difference raw30843; decide +kernel
    rw [ha]
    exact (canonical30843 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2241 + difference 5 1) (sourceB2241 + difference 1 5) sourceC2241) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4914) := by
    have ha : (tripleCharges (sourceA2241 + difference 5 1) (sourceB2241 + difference 1 5) sourceC2241) = raw30844 := by
      apply Matrix.ext; unfold tripleCharges sourceA2241 sourceB2241 sourceC2241 difference raw30844; decide +kernel
    rw [ha]
    exact (canonical30844 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2241 + difference 5 2) (sourceB2241 + difference 2 5) sourceC2241) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4909) := by
    have ha : (tripleCharges (sourceA2241 + difference 5 2) (sourceB2241 + difference 2 5) sourceC2241) = raw30845 := by
      apply Matrix.ext; unfold tripleCharges sourceA2241 sourceB2241 sourceC2241 difference raw30845; decide +kernel
    rw [ha]
    exact (canonical30845 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2241 + difference 5 3) (sourceB2241 + difference 3 5) sourceC2241) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4920) := by
    have ha : (tripleCharges (sourceA2241 + difference 5 3) (sourceB2241 + difference 3 5) sourceC2241) = raw30846 := by
      apply Matrix.ext; unfold tripleCharges sourceA2241 sourceB2241 sourceC2241 difference raw30846; decide +kernel
    rw [ha]
    exact (canonical30846 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2241 + difference 5 4) (sourceB2241 + difference 4 5) sourceC2241) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5014) := by
    have ha : (tripleCharges (sourceA2241 + difference 5 4) (sourceB2241 + difference 4 5) sourceC2241) = raw30847 := by
      apply Matrix.ext; unfold tripleCharges sourceA2241 sourceB2241 sourceC2241 difference raw30847; decide +kernel
    rw [ha]
    exact (canonical30847 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2241 sourceB2241 sourceC2241
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2241, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2242 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2242 : Charge := ![1, -1, 2, 0, 0, -2]
def sourceC2242 : Charge := ![2, 2, -2, 0, -2, 0]
def sourceForm2242 : Integer.Sparse Master := [(Sum.inr 2394, 1), (Sum.inr 2679, 1), (Sum.inr 3660, 1), (Sum.inr 3712, 1), (Sum.inr 3770, 1), (Sum.inr 3772, 1), (Sum.inr 4089, -1)]

theorem sourceEq2242 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2242 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2242 + difference 0 0) (sourceB2242 + difference 0 0) sourceC2242) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2394) := by
    have ha : (tripleCharges (sourceA2242 + difference 0 0) (sourceB2242 + difference 0 0) sourceC2242) = raw30848 := by
      apply Matrix.ext; unfold tripleCharges sourceA2242 sourceB2242 sourceC2242 difference raw30848; decide +kernel
    rw [ha]
    exact (canonical30848 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2242 + difference 0 1) (sourceB2242 + difference 1 0) sourceC2242) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3660) := by
    have ha : (tripleCharges (sourceA2242 + difference 0 1) (sourceB2242 + difference 1 0) sourceC2242) = raw30849 := by
      apply Matrix.ext; unfold tripleCharges sourceA2242 sourceB2242 sourceC2242 difference raw30849; decide +kernel
    rw [ha]
    exact (canonical30849 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2242 + difference 0 2) (sourceB2242 + difference 2 0) sourceC2242) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2679) := by
    have ha : (tripleCharges (sourceA2242 + difference 0 2) (sourceB2242 + difference 2 0) sourceC2242) = raw30850 := by
      apply Matrix.ext; unfold tripleCharges sourceA2242 sourceB2242 sourceC2242 difference raw30850; decide +kernel
    rw [ha]
    exact (canonical30850 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2242 + difference 0 3) (sourceB2242 + difference 3 0) sourceC2242) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3712) := by
    have ha : (tripleCharges (sourceA2242 + difference 0 3) (sourceB2242 + difference 3 0) sourceC2242) = raw30851 := by
      apply Matrix.ext; unfold tripleCharges sourceA2242 sourceB2242 sourceC2242 difference raw30851; decide +kernel
    rw [ha]
    exact (canonical30851 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2242 + difference 0 4) (sourceB2242 + difference 4 0) sourceC2242) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3772) := by
    have ha : (tripleCharges (sourceA2242 + difference 0 4) (sourceB2242 + difference 4 0) sourceC2242) = raw30852 := by
      apply Matrix.ext; unfold tripleCharges sourceA2242 sourceB2242 sourceC2242 difference raw30852; decide +kernel
    rw [ha]
    exact (canonical30852 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2242 + difference 0 5) (sourceB2242 + difference 5 0) sourceC2242) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3770) := by
    have ha : (tripleCharges (sourceA2242 + difference 0 5) (sourceB2242 + difference 5 0) sourceC2242) = raw30853 := by
      apply Matrix.ext; unfold tripleCharges sourceA2242 sourceB2242 sourceC2242 difference raw30853; decide +kernel
    rw [ha]
    exact (canonical30853 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2242 + sourceB2242) sourceC2242) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4089) := by
    have ha : (doubleCharges (sourceA2242 + sourceB2242) sourceC2242) = raw30854 := by
      apply Matrix.ext; unfold doubleCharges sourceA2242 sourceB2242 sourceC2242 raw30854; decide +kernel
    rw [ha]
    exact (canonical30854 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2242 sourceB2242 sourceC2242
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2242, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2243 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2243 : Charge := ![1, -1, 2, 0, -1, -1]
def sourceC2243 : Charge := ![2, 2, -2, 0, -1, -1]
def sourceForm2243 : Integer.Sparse Master := [(Sum.inr 2395, 1), (Sum.inr 2772, 1), (Sum.inr 3661, 1), (Sum.inr 3743, 1), (Sum.inr 3771, 2), (Sum.inr 4088, -1)]

theorem sourceEq2243 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2243 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2243 + difference 0 0) (sourceB2243 + difference 0 0) sourceC2243) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2395) := by
    have ha : (tripleCharges (sourceA2243 + difference 0 0) (sourceB2243 + difference 0 0) sourceC2243) = raw30855 := by
      apply Matrix.ext; unfold tripleCharges sourceA2243 sourceB2243 sourceC2243 difference raw30855; decide +kernel
    rw [ha]
    exact (canonical30855 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2243 + difference 0 1) (sourceB2243 + difference 1 0) sourceC2243) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3661) := by
    have ha : (tripleCharges (sourceA2243 + difference 0 1) (sourceB2243 + difference 1 0) sourceC2243) = raw30856 := by
      apply Matrix.ext; unfold tripleCharges sourceA2243 sourceB2243 sourceC2243 difference raw30856; decide +kernel
    rw [ha]
    exact (canonical30856 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2243 + difference 0 2) (sourceB2243 + difference 2 0) sourceC2243) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2772) := by
    have ha : (tripleCharges (sourceA2243 + difference 0 2) (sourceB2243 + difference 2 0) sourceC2243) = raw30857 := by
      apply Matrix.ext; unfold tripleCharges sourceA2243 sourceB2243 sourceC2243 difference raw30857; decide +kernel
    rw [ha]
    exact (canonical30857 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2243 + difference 0 3) (sourceB2243 + difference 3 0) sourceC2243) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3743) := by
    have ha : (tripleCharges (sourceA2243 + difference 0 3) (sourceB2243 + difference 3 0) sourceC2243) = raw30858 := by
      apply Matrix.ext; unfold tripleCharges sourceA2243 sourceB2243 sourceC2243 difference raw30858; decide +kernel
    rw [ha]
    exact (canonical30858 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2243 + difference 0 4) (sourceB2243 + difference 4 0) sourceC2243) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3771) := by
    have ha : (tripleCharges (sourceA2243 + difference 0 4) (sourceB2243 + difference 4 0) sourceC2243) = raw30859 := by
      apply Matrix.ext; unfold tripleCharges sourceA2243 sourceB2243 sourceC2243 difference raw30859; decide +kernel
    rw [ha]
    exact (canonical30859 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2243 + difference 0 5) (sourceB2243 + difference 5 0) sourceC2243) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3771) := by
    have ha : (tripleCharges (sourceA2243 + difference 0 5) (sourceB2243 + difference 5 0) sourceC2243) = raw30860 := by
      apply Matrix.ext; unfold tripleCharges sourceA2243 sourceB2243 sourceC2243 difference raw30860; decide +kernel
    rw [ha]
    exact (canonical30860 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2243 + sourceB2243) sourceC2243) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA2243 + sourceB2243) sourceC2243) = raw30861 := by
      apply Matrix.ext; unfold doubleCharges sourceA2243 sourceB2243 sourceC2243 raw30861; decide +kernel
    rw [ha]
    exact (canonical30861 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2243 sourceB2243 sourceC2243
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2243, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2244 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2244 : Charge := ![1, -1, 1, 1, 0, -2]
def sourceC2244 : Charge := ![2, 2, -1, -1, -2, 0]
def sourceForm2244 : Integer.Sparse Master := [(Sum.inr 2379, 1), (Sum.inr 3646, 1), (Sum.inr 3718, 2), (Sum.inr 3757, 1), (Sum.inr 3759, 1), (Sum.inr 4088, -1)]

theorem sourceEq2244 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2244 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2244 + difference 0 0) (sourceB2244 + difference 0 0) sourceC2244) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2379) := by
    have ha : (tripleCharges (sourceA2244 + difference 0 0) (sourceB2244 + difference 0 0) sourceC2244) = raw30862 := by
      apply Matrix.ext; unfold tripleCharges sourceA2244 sourceB2244 sourceC2244 difference raw30862; decide +kernel
    rw [ha]
    exact (canonical30862 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2244 + difference 0 1) (sourceB2244 + difference 1 0) sourceC2244) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3646) := by
    have ha : (tripleCharges (sourceA2244 + difference 0 1) (sourceB2244 + difference 1 0) sourceC2244) = raw30863 := by
      apply Matrix.ext; unfold tripleCharges sourceA2244 sourceB2244 sourceC2244 difference raw30863; decide +kernel
    rw [ha]
    exact (canonical30863 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2244 + difference 0 2) (sourceB2244 + difference 2 0) sourceC2244) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3718) := by
    have ha : (tripleCharges (sourceA2244 + difference 0 2) (sourceB2244 + difference 2 0) sourceC2244) = raw30864 := by
      apply Matrix.ext; unfold tripleCharges sourceA2244 sourceB2244 sourceC2244 difference raw30864; decide +kernel
    rw [ha]
    exact (canonical30864 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2244 + difference 0 3) (sourceB2244 + difference 3 0) sourceC2244) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3718) := by
    have ha : (tripleCharges (sourceA2244 + difference 0 3) (sourceB2244 + difference 3 0) sourceC2244) = raw30865 := by
      apply Matrix.ext; unfold tripleCharges sourceA2244 sourceB2244 sourceC2244 difference raw30865; decide +kernel
    rw [ha]
    exact (canonical30865 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2244 + difference 0 4) (sourceB2244 + difference 4 0) sourceC2244) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3759) := by
    have ha : (tripleCharges (sourceA2244 + difference 0 4) (sourceB2244 + difference 4 0) sourceC2244) = raw30866 := by
      apply Matrix.ext; unfold tripleCharges sourceA2244 sourceB2244 sourceC2244 difference raw30866; decide +kernel
    rw [ha]
    exact (canonical30866 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2244 + difference 0 5) (sourceB2244 + difference 5 0) sourceC2244) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3757) := by
    have ha : (tripleCharges (sourceA2244 + difference 0 5) (sourceB2244 + difference 5 0) sourceC2244) = raw30867 := by
      apply Matrix.ext; unfold tripleCharges sourceA2244 sourceB2244 sourceC2244 difference raw30867; decide +kernel
    rw [ha]
    exact (canonical30867 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2244 + sourceB2244) sourceC2244) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA2244 + sourceB2244) sourceC2244) = raw30868 := by
      apply Matrix.ext; unfold doubleCharges sourceA2244 sourceB2244 sourceC2244 raw30868; decide +kernel
    rw [ha]
    exact (canonical30868 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2244 sourceB2244 sourceC2244
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2244, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2245 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2245 : Charge := ![1, -1, 1, 0, 0, -1]
def sourceC2245 : Charge := ![2, 2, -1, 0, -2, -1]
def sourceForm2245 : Integer.Sparse Master := [(Sum.inr 2388, 1), (Sum.inr 3654, 1), (Sum.inr 3681, 1), (Sum.inr 3702, 1), (Sum.inr 3766, 1), (Sum.inr 3767, 1), (Sum.inr 4088, -1)]

theorem sourceEq2245 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2245 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2245 + difference 0 0) (sourceB2245 + difference 0 0) sourceC2245) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2388) := by
    have ha : (tripleCharges (sourceA2245 + difference 0 0) (sourceB2245 + difference 0 0) sourceC2245) = raw30869 := by
      apply Matrix.ext; unfold tripleCharges sourceA2245 sourceB2245 sourceC2245 difference raw30869; decide +kernel
    rw [ha]
    exact (canonical30869 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2245 + difference 0 1) (sourceB2245 + difference 1 0) sourceC2245) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3654) := by
    have ha : (tripleCharges (sourceA2245 + difference 0 1) (sourceB2245 + difference 1 0) sourceC2245) = raw30870 := by
      apply Matrix.ext; unfold tripleCharges sourceA2245 sourceB2245 sourceC2245 difference raw30870; decide +kernel
    rw [ha]
    exact (canonical30870 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2245 + difference 0 2) (sourceB2245 + difference 2 0) sourceC2245) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3702) := by
    have ha : (tripleCharges (sourceA2245 + difference 0 2) (sourceB2245 + difference 2 0) sourceC2245) = raw30871 := by
      apply Matrix.ext; unfold tripleCharges sourceA2245 sourceB2245 sourceC2245 difference raw30871; decide +kernel
    rw [ha]
    exact (canonical30871 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2245 + difference 0 3) (sourceB2245 + difference 3 0) sourceC2245) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3681) := by
    have ha : (tripleCharges (sourceA2245 + difference 0 3) (sourceB2245 + difference 3 0) sourceC2245) = raw30872 := by
      apply Matrix.ext; unfold tripleCharges sourceA2245 sourceB2245 sourceC2245 difference raw30872; decide +kernel
    rw [ha]
    exact (canonical30872 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2245 + difference 0 4) (sourceB2245 + difference 4 0) sourceC2245) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3767) := by
    have ha : (tripleCharges (sourceA2245 + difference 0 4) (sourceB2245 + difference 4 0) sourceC2245) = raw30873 := by
      apply Matrix.ext; unfold tripleCharges sourceA2245 sourceB2245 sourceC2245 difference raw30873; decide +kernel
    rw [ha]
    exact (canonical30873 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2245 + difference 0 5) (sourceB2245 + difference 5 0) sourceC2245) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3766) := by
    have ha : (tripleCharges (sourceA2245 + difference 0 5) (sourceB2245 + difference 5 0) sourceC2245) = raw30874 := by
      apply Matrix.ext; unfold tripleCharges sourceA2245 sourceB2245 sourceC2245 difference raw30874; decide +kernel
    rw [ha]
    exact (canonical30874 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2245 + sourceB2245) sourceC2245) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA2245 + sourceB2245) sourceC2245) = raw30875 := by
      apply Matrix.ext; unfold doubleCharges sourceA2245 sourceB2245 sourceC2245 raw30875; decide +kernel
    rw [ha]
    exact (canonical30875 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2245 sourceB2245 sourceC2245
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2245, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2246 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2246 : Charge := ![1, -1, 1, 0, 0, -1]
def sourceC2246 : Charge := ![2, 2, -1, 0, -2, -1]
def sourceForm2246 : Integer.Sparse Master := [(Sum.inr 2296, 1), (Sum.inr 2300, 1), (Sum.inr 2301, 1), (Sum.inr 2312, 1), (Sum.inr 2388, 1), (Sum.inr 3654, 1), (Sum.inr 4088, -1)]

theorem sourceEq2246 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2246 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2246 + difference 0 1) (sourceB2246 + difference 1 0) sourceC2246) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3654) := by
    have ha : (tripleCharges (sourceA2246 + difference 0 1) (sourceB2246 + difference 1 0) sourceC2246) = raw30870 := by
      apply Matrix.ext; unfold tripleCharges sourceA2246 sourceB2246 sourceC2246 difference raw30870; decide +kernel
    rw [ha]
    exact (canonical30870 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2246 + difference 1 1) (sourceB2246 + difference 1 1) sourceC2246) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2388) := by
    have ha : (tripleCharges (sourceA2246 + difference 1 1) (sourceB2246 + difference 1 1) sourceC2246) = raw30869 := by
      apply Matrix.ext; unfold tripleCharges sourceA2246 sourceB2246 sourceC2246 difference raw30869; decide +kernel
    rw [ha]
    exact (canonical30869 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2246 + difference 2 1) (sourceB2246 + difference 1 2) sourceC2246) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2312) := by
    have ha : (tripleCharges (sourceA2246 + difference 2 1) (sourceB2246 + difference 1 2) sourceC2246) = raw30876 := by
      apply Matrix.ext; unfold tripleCharges sourceA2246 sourceB2246 sourceC2246 difference raw30876; decide +kernel
    rw [ha]
    exact (canonical30876 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2246 + difference 3 1) (sourceB2246 + difference 1 3) sourceC2246) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2296) := by
    have ha : (tripleCharges (sourceA2246 + difference 3 1) (sourceB2246 + difference 1 3) sourceC2246) = raw30877 := by
      apply Matrix.ext; unfold tripleCharges sourceA2246 sourceB2246 sourceC2246 difference raw30877; decide +kernel
    rw [ha]
    exact (canonical30877 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2246 + difference 4 1) (sourceB2246 + difference 1 4) sourceC2246) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2300) := by
    have ha : (tripleCharges (sourceA2246 + difference 4 1) (sourceB2246 + difference 1 4) sourceC2246) = raw30878 := by
      apply Matrix.ext; unfold tripleCharges sourceA2246 sourceB2246 sourceC2246 difference raw30878; decide +kernel
    rw [ha]
    exact (canonical30878 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2246 + difference 5 1) (sourceB2246 + difference 1 5) sourceC2246) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2301) := by
    have ha : (tripleCharges (sourceA2246 + difference 5 1) (sourceB2246 + difference 1 5) sourceC2246) = raw30879 := by
      apply Matrix.ext; unfold tripleCharges sourceA2246 sourceB2246 sourceC2246 difference raw30879; decide +kernel
    rw [ha]
    exact (canonical30879 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2246 + sourceB2246) sourceC2246) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA2246 + sourceB2246) sourceC2246) = raw30875 := by
      apply Matrix.ext; unfold doubleCharges sourceA2246 sourceB2246 sourceC2246 raw30875; decide +kernel
    rw [ha]
    exact (canonical30875 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2246 sourceB2246 sourceC2246
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2246, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2247 : Charge := ![1, -1, 1, 0, 0, -1]
def sourceB2247 : Charge := ![2, 2, -1, 0, -2, -1]
def sourceC2247 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceForm2247 : Integer.Sparse Master := [(Sum.inr 1769, 1), (Sum.inr 1773, 1), (Sum.inr 1775, 1), (Sum.inr 1781, 1), (Sum.inr 1945, 1), (Sum.inr 3354, 1), (Sum.inr 4082, -1)]

theorem sourceEq2247 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2247 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2247 + difference 0 0) (sourceB2247 + difference 0 0) sourceC2247) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3354) := by
    have ha : (tripleCharges (sourceA2247 + difference 0 0) (sourceB2247 + difference 0 0) sourceC2247) = raw30880 := by
      apply Matrix.ext; unfold tripleCharges sourceA2247 sourceB2247 sourceC2247 difference raw30880; decide +kernel
    rw [ha]
    exact (canonical30880 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2247 + difference 1 0) (sourceB2247 + difference 0 1) sourceC2247) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1945) := by
    have ha : (tripleCharges (sourceA2247 + difference 1 0) (sourceB2247 + difference 0 1) sourceC2247) = raw30594 := by
      apply Matrix.ext; unfold tripleCharges sourceA2247 sourceB2247 sourceC2247 difference raw30594; decide +kernel
    rw [ha]
    exact (canonical30594 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2247 + difference 2 0) (sourceB2247 + difference 0 2) sourceC2247) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1781) := by
    have ha : (tripleCharges (sourceA2247 + difference 2 0) (sourceB2247 + difference 0 2) sourceC2247) = raw30881 := by
      apply Matrix.ext; unfold tripleCharges sourceA2247 sourceB2247 sourceC2247 difference raw30881; decide +kernel
    rw [ha]
    exact (canonical30881 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2247 + difference 3 0) (sourceB2247 + difference 0 3) sourceC2247) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1769) := by
    have ha : (tripleCharges (sourceA2247 + difference 3 0) (sourceB2247 + difference 0 3) sourceC2247) = raw30882 := by
      apply Matrix.ext; unfold tripleCharges sourceA2247 sourceB2247 sourceC2247 difference raw30882; decide +kernel
    rw [ha]
    exact (canonical30882 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2247 + difference 4 0) (sourceB2247 + difference 0 4) sourceC2247) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1773) := by
    have ha : (tripleCharges (sourceA2247 + difference 4 0) (sourceB2247 + difference 0 4) sourceC2247) = raw30883 := by
      apply Matrix.ext; unfold tripleCharges sourceA2247 sourceB2247 sourceC2247 difference raw30883; decide +kernel
    rw [ha]
    exact (canonical30883 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2247 + difference 5 0) (sourceB2247 + difference 0 5) sourceC2247) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1775) := by
    have ha : (tripleCharges (sourceA2247 + difference 5 0) (sourceB2247 + difference 0 5) sourceC2247) = raw30884 := by
      apply Matrix.ext; unfold tripleCharges sourceA2247 sourceB2247 sourceC2247 difference raw30884; decide +kernel
    rw [ha]
    exact (canonical30884 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2247 + sourceB2247) sourceC2247) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2247 + sourceB2247) sourceC2247) = raw29319 := by
      apply Matrix.ext; unfold doubleCharges sourceA2247 sourceB2247 sourceC2247 raw29319; decide +kernel
    rw [ha]
    exact (canonical29319 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2247 sourceB2247 sourceC2247
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2247, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2248 : Charge := ![1, -1, 1, 0, 0, -1]
def sourceB2248 : Charge := ![2, 2, -1, 0, -2, -1]
def sourceC2248 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceForm2248 : Integer.Sparse Master := [(Sum.inr 1775, 1), (Sum.inr 2792, 1), (Sum.inr 3332, 1), (Sum.inr 3354, 2), (Sum.inr 3361, 1), (Sum.inr 4082, -1)]

theorem sourceEq2248 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2248 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2248 + difference 5 0) (sourceB2248 + difference 0 5) sourceC2248) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1775) := by
    have ha : (tripleCharges (sourceA2248 + difference 5 0) (sourceB2248 + difference 0 5) sourceC2248) = raw30884 := by
      apply Matrix.ext; unfold tripleCharges sourceA2248 sourceB2248 sourceC2248 difference raw30884; decide +kernel
    rw [ha]
    exact (canonical30884 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2248 + difference 5 1) (sourceB2248 + difference 1 5) sourceC2248) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2792) := by
    have ha : (tripleCharges (sourceA2248 + difference 5 1) (sourceB2248 + difference 1 5) sourceC2248) = raw30885 := by
      apply Matrix.ext; unfold tripleCharges sourceA2248 sourceB2248 sourceC2248 difference raw30885; decide +kernel
    rw [ha]
    exact (canonical30885 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2248 + difference 5 2) (sourceB2248 + difference 2 5) sourceC2248) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3361) := by
    have ha : (tripleCharges (sourceA2248 + difference 5 2) (sourceB2248 + difference 2 5) sourceC2248) = raw30886 := by
      apply Matrix.ext; unfold tripleCharges sourceA2248 sourceB2248 sourceC2248 difference raw30886; decide +kernel
    rw [ha]
    exact (canonical30886 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2248 + difference 5 3) (sourceB2248 + difference 3 5) sourceC2248) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3332) := by
    have ha : (tripleCharges (sourceA2248 + difference 5 3) (sourceB2248 + difference 3 5) sourceC2248) = raw30597 := by
      apply Matrix.ext; unfold tripleCharges sourceA2248 sourceB2248 sourceC2248 difference raw30597; decide +kernel
    rw [ha]
    exact (canonical30597 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2248 + difference 5 4) (sourceB2248 + difference 4 5) sourceC2248) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3354) := by
    have ha : (tripleCharges (sourceA2248 + difference 5 4) (sourceB2248 + difference 4 5) sourceC2248) = raw30887 := by
      apply Matrix.ext; unfold tripleCharges sourceA2248 sourceB2248 sourceC2248 difference raw30887; decide +kernel
    rw [ha]
    exact (canonical30887 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2248 + difference 5 5) (sourceB2248 + difference 5 5) sourceC2248) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3354) := by
    have ha : (tripleCharges (sourceA2248 + difference 5 5) (sourceB2248 + difference 5 5) sourceC2248) = raw30880 := by
      apply Matrix.ext; unfold tripleCharges sourceA2248 sourceB2248 sourceC2248 difference raw30880; decide +kernel
    rw [ha]
    exact (canonical30880 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2248 + sourceB2248) sourceC2248) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2248 + sourceB2248) sourceC2248) = raw29319 := by
      apply Matrix.ext; unfold doubleCharges sourceA2248 sourceB2248 sourceC2248 raw29319; decide +kernel
    rw [ha]
    exact (canonical29319 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2248 sourceB2248 sourceC2248
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2248, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2249 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2249 : Charge := ![1, -1, 0, 0, 0, 0]
def sourceC2249 : Charge := ![2, 2, 0, 0, -2, -2]
def sourceForm2249 : Integer.Sparse Master := [(Sum.inr 4089, 1), (Sum.inr 4515, 2), (Sum.inr 4520, 2), (Sum.inr 4575, 1), (Sum.inr 4913, 4), (Sum.inr 4915, 2), (Sum.inr 4924, 2), (Sum.inr 4985, 2), (Sum.inr 5015, 4), (Sum.inr 5021, 2), (Sum.inr 5125, 2), (Sum.inr 5238, 2), (Sum.inr 5327, 2), (Sum.inr 5371, 2)]

theorem sourceEq2249 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2249 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2249 + difference 0 1) (sourceB2249 + difference 1 0) sourceC2249) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4089) := by
    have ha : (tripleCharges (sourceA2249 + difference 0 1) (sourceB2249 + difference 1 0) sourceC2249) = raw30888 := by
      apply Matrix.ext; unfold tripleCharges sourceA2249 sourceB2249 sourceC2249 difference raw30888; decide +kernel
    rw [ha]
    exact (canonical30888 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2249 + difference 0 2) (sourceB2249 + difference 2 0) sourceC2249) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5327) := by
    have ha : (tripleCharges (sourceA2249 + difference 0 2) (sourceB2249 + difference 2 0) sourceC2249) = raw30889 := by
      apply Matrix.ext; unfold tripleCharges sourceA2249 sourceB2249 sourceC2249 difference raw30889; decide +kernel
    rw [ha]
    exact (canonical30889 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2249 + difference 0 3) (sourceB2249 + difference 3 0) sourceC2249) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5327) := by
    have ha : (tripleCharges (sourceA2249 + difference 0 3) (sourceB2249 + difference 3 0) sourceC2249) = raw30890 := by
      apply Matrix.ext; unfold tripleCharges sourceA2249 sourceB2249 sourceC2249 difference raw30890; decide +kernel
    rw [ha]
    exact (canonical30890 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2249 + difference 0 4) (sourceB2249 + difference 4 0) sourceC2249) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5371) := by
    have ha : (tripleCharges (sourceA2249 + difference 0 4) (sourceB2249 + difference 4 0) sourceC2249) = raw30891 := by
      apply Matrix.ext; unfold tripleCharges sourceA2249 sourceB2249 sourceC2249 difference raw30891; decide +kernel
    rw [ha]
    exact (canonical30891 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2249 + difference 0 5) (sourceB2249 + difference 5 0) sourceC2249) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5371) := by
    have ha : (tripleCharges (sourceA2249 + difference 0 5) (sourceB2249 + difference 5 0) sourceC2249) = raw30892 := by
      apply Matrix.ext; unfold tripleCharges sourceA2249 sourceB2249 sourceC2249 difference raw30892; decide +kernel
    rw [ha]
    exact (canonical30892 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2249 + difference 1 0) (sourceB2249 + difference 0 1) sourceC2249) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4575) := by
    have ha : (tripleCharges (sourceA2249 + difference 1 0) (sourceB2249 + difference 0 1) sourceC2249) = raw30893 := by
      apply Matrix.ext; unfold tripleCharges sourceA2249 sourceB2249 sourceC2249 difference raw30893; decide +kernel
    rw [ha]
    exact (canonical30893 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2249 + difference 1 2) (sourceB2249 + difference 2 1) sourceC2249) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5125) := by
    have ha : (tripleCharges (sourceA2249 + difference 1 2) (sourceB2249 + difference 2 1) sourceC2249) = raw30894 := by
      apply Matrix.ext; unfold tripleCharges sourceA2249 sourceB2249 sourceC2249 difference raw30894; decide +kernel
    rw [ha]
    exact (canonical30894 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2249 + difference 1 3) (sourceB2249 + difference 3 1) sourceC2249) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5125) := by
    have ha : (tripleCharges (sourceA2249 + difference 1 3) (sourceB2249 + difference 3 1) sourceC2249) = raw30895 := by
      apply Matrix.ext; unfold tripleCharges sourceA2249 sourceB2249 sourceC2249 difference raw30895; decide +kernel
    rw [ha]
    exact (canonical30895 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2249 + difference 1 4) (sourceB2249 + difference 4 1) sourceC2249) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5238) := by
    have ha : (tripleCharges (sourceA2249 + difference 1 4) (sourceB2249 + difference 4 1) sourceC2249) = raw30896 := by
      apply Matrix.ext; unfold tripleCharges sourceA2249 sourceB2249 sourceC2249 difference raw30896; decide +kernel
    rw [ha]
    exact (canonical30896 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2249 + difference 1 5) (sourceB2249 + difference 5 1) sourceC2249) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5238) := by
    have ha : (tripleCharges (sourceA2249 + difference 1 5) (sourceB2249 + difference 5 1) sourceC2249) = raw30897 := by
      apply Matrix.ext; unfold tripleCharges sourceA2249 sourceB2249 sourceC2249 difference raw30897; decide +kernel
    rw [ha]
    exact (canonical30897 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2249 + difference 2 0) (sourceB2249 + difference 0 2) sourceC2249) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4515) := by
    have ha : (tripleCharges (sourceA2249 + difference 2 0) (sourceB2249 + difference 0 2) sourceC2249) = raw30898 := by
      apply Matrix.ext; unfold tripleCharges sourceA2249 sourceB2249 sourceC2249 difference raw30898; decide +kernel
    rw [ha]
    exact (canonical30898 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2249 + difference 2 1) (sourceB2249 + difference 1 2) sourceC2249) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4915) := by
    have ha : (tripleCharges (sourceA2249 + difference 2 1) (sourceB2249 + difference 1 2) sourceC2249) = raw30899 := by
      apply Matrix.ext; unfold tripleCharges sourceA2249 sourceB2249 sourceC2249 difference raw30899; decide +kernel
    rw [ha]
    exact (canonical30899 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2249 + difference 2 3) (sourceB2249 + difference 3 2) sourceC2249) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4985) := by
    have ha : (tripleCharges (sourceA2249 + difference 2 3) (sourceB2249 + difference 3 2) sourceC2249) = raw30900 := by
      apply Matrix.ext; unfold tripleCharges sourceA2249 sourceB2249 sourceC2249 difference raw30900; decide +kernel
    rw [ha]
    exact (canonical30900 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2249 + difference 2 4) (sourceB2249 + difference 4 2) sourceC2249) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5015) := by
    have ha : (tripleCharges (sourceA2249 + difference 2 4) (sourceB2249 + difference 4 2) sourceC2249) = raw30901 := by
      apply Matrix.ext; unfold tripleCharges sourceA2249 sourceB2249 sourceC2249 difference raw30901; decide +kernel
    rw [ha]
    exact (canonical30901 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2249 + difference 2 5) (sourceB2249 + difference 5 2) sourceC2249) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5015) := by
    have ha : (tripleCharges (sourceA2249 + difference 2 5) (sourceB2249 + difference 5 2) sourceC2249) = raw30902 := by
      apply Matrix.ext; unfold tripleCharges sourceA2249 sourceB2249 sourceC2249 difference raw30902; decide +kernel
    rw [ha]
    exact (canonical30902 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2249 + difference 3 0) (sourceB2249 + difference 0 3) sourceC2249) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4515) := by
    have ha : (tripleCharges (sourceA2249 + difference 3 0) (sourceB2249 + difference 0 3) sourceC2249) = raw30903 := by
      apply Matrix.ext; unfold tripleCharges sourceA2249 sourceB2249 sourceC2249 difference raw30903; decide +kernel
    rw [ha]
    exact (canonical30903 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2249 + difference 3 1) (sourceB2249 + difference 1 3) sourceC2249) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4915) := by
    have ha : (tripleCharges (sourceA2249 + difference 3 1) (sourceB2249 + difference 1 3) sourceC2249) = raw30904 := by
      apply Matrix.ext; unfold tripleCharges sourceA2249 sourceB2249 sourceC2249 difference raw30904; decide +kernel
    rw [ha]
    exact (canonical30904 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2249 + difference 3 2) (sourceB2249 + difference 2 3) sourceC2249) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4985) := by
    have ha : (tripleCharges (sourceA2249 + difference 3 2) (sourceB2249 + difference 2 3) sourceC2249) = raw30905 := by
      apply Matrix.ext; unfold tripleCharges sourceA2249 sourceB2249 sourceC2249 difference raw30905; decide +kernel
    rw [ha]
    exact (canonical30905 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2249 + difference 3 4) (sourceB2249 + difference 4 3) sourceC2249) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5015) := by
    have ha : (tripleCharges (sourceA2249 + difference 3 4) (sourceB2249 + difference 4 3) sourceC2249) = raw30906 := by
      apply Matrix.ext; unfold tripleCharges sourceA2249 sourceB2249 sourceC2249 difference raw30906; decide +kernel
    rw [ha]
    exact (canonical30906 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2249 + difference 3 5) (sourceB2249 + difference 5 3) sourceC2249) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5015) := by
    have ha : (tripleCharges (sourceA2249 + difference 3 5) (sourceB2249 + difference 5 3) sourceC2249) = raw30907 := by
      apply Matrix.ext; unfold tripleCharges sourceA2249 sourceB2249 sourceC2249 difference raw30907; decide +kernel
    rw [ha]
    exact (canonical30907 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2249 + difference 4 0) (sourceB2249 + difference 0 4) sourceC2249) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4520) := by
    have ha : (tripleCharges (sourceA2249 + difference 4 0) (sourceB2249 + difference 0 4) sourceC2249) = raw30908 := by
      apply Matrix.ext; unfold tripleCharges sourceA2249 sourceB2249 sourceC2249 difference raw30908; decide +kernel
    rw [ha]
    exact (canonical30908 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2249 + difference 4 1) (sourceB2249 + difference 1 4) sourceC2249) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4924) := by
    have ha : (tripleCharges (sourceA2249 + difference 4 1) (sourceB2249 + difference 1 4) sourceC2249) = raw30909 := by
      apply Matrix.ext; unfold tripleCharges sourceA2249 sourceB2249 sourceC2249 difference raw30909; decide +kernel
    rw [ha]
    exact (canonical30909 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2249 + difference 4 2) (sourceB2249 + difference 2 4) sourceC2249) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4913) := by
    have ha : (tripleCharges (sourceA2249 + difference 4 2) (sourceB2249 + difference 2 4) sourceC2249) = raw30910 := by
      apply Matrix.ext; unfold tripleCharges sourceA2249 sourceB2249 sourceC2249 difference raw30910; decide +kernel
    rw [ha]
    exact (canonical30910 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2249 + difference 4 3) (sourceB2249 + difference 3 4) sourceC2249) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4913) := by
    have ha : (tripleCharges (sourceA2249 + difference 4 3) (sourceB2249 + difference 3 4) sourceC2249) = raw30911 := by
      apply Matrix.ext; unfold tripleCharges sourceA2249 sourceB2249 sourceC2249 difference raw30911; decide +kernel
    rw [ha]
    exact (canonical30911 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2249 + difference 4 5) (sourceB2249 + difference 5 4) sourceC2249) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5021) := by
    have ha : (tripleCharges (sourceA2249 + difference 4 5) (sourceB2249 + difference 5 4) sourceC2249) = raw30912 := by
      apply Matrix.ext; unfold tripleCharges sourceA2249 sourceB2249 sourceC2249 difference raw30912; decide +kernel
    rw [ha]
    exact (canonical30912 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2249 + difference 5 0) (sourceB2249 + difference 0 5) sourceC2249) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4520) := by
    have ha : (tripleCharges (sourceA2249 + difference 5 0) (sourceB2249 + difference 0 5) sourceC2249) = raw30913 := by
      apply Matrix.ext; unfold tripleCharges sourceA2249 sourceB2249 sourceC2249 difference raw30913; decide +kernel
    rw [ha]
    exact (canonical30913 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2249 + difference 5 1) (sourceB2249 + difference 1 5) sourceC2249) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4924) := by
    have ha : (tripleCharges (sourceA2249 + difference 5 1) (sourceB2249 + difference 1 5) sourceC2249) = raw30914 := by
      apply Matrix.ext; unfold tripleCharges sourceA2249 sourceB2249 sourceC2249 difference raw30914; decide +kernel
    rw [ha]
    exact (canonical30914 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2249 + difference 5 2) (sourceB2249 + difference 2 5) sourceC2249) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4913) := by
    have ha : (tripleCharges (sourceA2249 + difference 5 2) (sourceB2249 + difference 2 5) sourceC2249) = raw30915 := by
      apply Matrix.ext; unfold tripleCharges sourceA2249 sourceB2249 sourceC2249 difference raw30915; decide +kernel
    rw [ha]
    exact (canonical30915 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2249 + difference 5 3) (sourceB2249 + difference 3 5) sourceC2249) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4913) := by
    have ha : (tripleCharges (sourceA2249 + difference 5 3) (sourceB2249 + difference 3 5) sourceC2249) = raw30916 := by
      apply Matrix.ext; unfold tripleCharges sourceA2249 sourceB2249 sourceC2249 difference raw30916; decide +kernel
    rw [ha]
    exact (canonical30916 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2249 + difference 5 4) (sourceB2249 + difference 4 5) sourceC2249) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5021) := by
    have ha : (tripleCharges (sourceA2249 + difference 5 4) (sourceB2249 + difference 4 5) sourceC2249) = raw30917 := by
      apply Matrix.ext; unfold tripleCharges sourceA2249 sourceB2249 sourceC2249 difference raw30917; decide +kernel
    rw [ha]
    exact (canonical30917 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2249 sourceB2249 sourceC2249
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2249, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2250 : Charge := ![1, -1, 0, 0, 0, 0]
def sourceB2250 : Charge := ![2, 2, 0, 0, -2, -2]
def sourceC2250 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceForm2250 : Integer.Sparse Master := [(Sum.inr 4082, 1), (Sum.inr 4646, 2), (Sum.inr 4656, 2), (Sum.inr 4914, 4), (Sum.inr 4925, 2), (Sum.inr 4984, 2), (Sum.inr 4988, 2), (Sum.inr 5003, 4), (Sum.inr 5023, 2), (Sum.inr 5063, 2), (Sum.inr 5111, 2), (Sum.inr 5193, 2), (Sum.inr 5207, 2), (Sum.inr 5214, 1)]

theorem sourceEq2250 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2250 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2250 + difference 0 1) (sourceB2250 + difference 1 0) sourceC2250) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5214) := by
    have ha : (tripleCharges (sourceA2250 + difference 0 1) (sourceB2250 + difference 1 0) sourceC2250) = raw30918 := by
      apply Matrix.ext; unfold tripleCharges sourceA2250 sourceB2250 sourceC2250 difference raw30918; decide +kernel
    rw [ha]
    exact (canonical30918 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2250 + difference 0 2) (sourceB2250 + difference 2 0) sourceC2250) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5193) := by
    have ha : (tripleCharges (sourceA2250 + difference 0 2) (sourceB2250 + difference 2 0) sourceC2250) = raw30919 := by
      apply Matrix.ext; unfold tripleCharges sourceA2250 sourceB2250 sourceC2250 difference raw30919; decide +kernel
    rw [ha]
    exact (canonical30919 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2250 + difference 0 3) (sourceB2250 + difference 3 0) sourceC2250) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5193) := by
    have ha : (tripleCharges (sourceA2250 + difference 0 3) (sourceB2250 + difference 3 0) sourceC2250) = raw30829 := by
      apply Matrix.ext; unfold tripleCharges sourceA2250 sourceB2250 sourceC2250 difference raw30829; decide +kernel
    rw [ha]
    exact (canonical30829 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2250 + difference 0 4) (sourceB2250 + difference 4 0) sourceC2250) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5207) := by
    have ha : (tripleCharges (sourceA2250 + difference 0 4) (sourceB2250 + difference 4 0) sourceC2250) = raw30920 := by
      apply Matrix.ext; unfold tripleCharges sourceA2250 sourceB2250 sourceC2250 difference raw30920; decide +kernel
    rw [ha]
    exact (canonical30920 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2250 + difference 0 5) (sourceB2250 + difference 5 0) sourceC2250) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5207) := by
    have ha : (tripleCharges (sourceA2250 + difference 0 5) (sourceB2250 + difference 5 0) sourceC2250) = raw30921 := by
      apply Matrix.ext; unfold tripleCharges sourceA2250 sourceB2250 sourceC2250 difference raw30921; decide +kernel
    rw [ha]
    exact (canonical30921 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2250 + difference 1 0) (sourceB2250 + difference 0 1) sourceC2250) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (tripleCharges (sourceA2250 + difference 1 0) (sourceB2250 + difference 0 1) sourceC2250) = raw30836 := by
      apply Matrix.ext; unfold tripleCharges sourceA2250 sourceB2250 sourceC2250 difference raw30836; decide +kernel
    rw [ha]
    exact (canonical30836 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2250 + difference 1 2) (sourceB2250 + difference 2 1) sourceC2250) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5063) := by
    have ha : (tripleCharges (sourceA2250 + difference 1 2) (sourceB2250 + difference 2 1) sourceC2250) = raw30838 := by
      apply Matrix.ext; unfold tripleCharges sourceA2250 sourceB2250 sourceC2250 difference raw30838; decide +kernel
    rw [ha]
    exact (canonical30838 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2250 + difference 1 3) (sourceB2250 + difference 3 1) sourceC2250) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5063) := by
    have ha : (tripleCharges (sourceA2250 + difference 1 3) (sourceB2250 + difference 3 1) sourceC2250) = raw30183 := by
      apply Matrix.ext; unfold tripleCharges sourceA2250 sourceB2250 sourceC2250 difference raw30183; decide +kernel
    rw [ha]
    exact (canonical30183 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2250 + difference 1 4) (sourceB2250 + difference 4 1) sourceC2250) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5111) := by
    have ha : (tripleCharges (sourceA2250 + difference 1 4) (sourceB2250 + difference 4 1) sourceC2250) = raw29583 := by
      apply Matrix.ext; unfold tripleCharges sourceA2250 sourceB2250 sourceC2250 difference raw29583; decide +kernel
    rw [ha]
    exact (canonical29583 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2250 + difference 1 5) (sourceB2250 + difference 5 1) sourceC2250) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5111) := by
    have ha : (tripleCharges (sourceA2250 + difference 1 5) (sourceB2250 + difference 5 1) sourceC2250) = raw29691 := by
      apply Matrix.ext; unfold tripleCharges sourceA2250 sourceB2250 sourceC2250 difference raw29691; decide +kernel
    rw [ha]
    exact (canonical29691 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2250 + difference 2 0) (sourceB2250 + difference 0 2) sourceC2250) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4646) := by
    have ha : (tripleCharges (sourceA2250 + difference 2 0) (sourceB2250 + difference 0 2) sourceC2250) = raw30922 := by
      apply Matrix.ext; unfold tripleCharges sourceA2250 sourceB2250 sourceC2250 difference raw30922; decide +kernel
    rw [ha]
    exact (canonical30922 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2250 + difference 2 1) (sourceB2250 + difference 1 2) sourceC2250) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4984) := by
    have ha : (tripleCharges (sourceA2250 + difference 2 1) (sourceB2250 + difference 1 2) sourceC2250) = raw30923 := by
      apply Matrix.ext; unfold tripleCharges sourceA2250 sourceB2250 sourceC2250 difference raw30923; decide +kernel
    rw [ha]
    exact (canonical30923 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2250 + difference 2 3) (sourceB2250 + difference 3 2) sourceC2250) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4988) := by
    have ha : (tripleCharges (sourceA2250 + difference 2 3) (sourceB2250 + difference 3 2) sourceC2250) = raw30834 := by
      apply Matrix.ext; unfold tripleCharges sourceA2250 sourceB2250 sourceC2250 difference raw30834; decide +kernel
    rw [ha]
    exact (canonical30834 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2250 + difference 2 4) (sourceB2250 + difference 4 2) sourceC2250) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5003) := by
    have ha : (tripleCharges (sourceA2250 + difference 2 4) (sourceB2250 + difference 4 2) sourceC2250) = raw30549 := by
      apply Matrix.ext; unfold tripleCharges sourceA2250 sourceB2250 sourceC2250 difference raw30549; decide +kernel
    rw [ha]
    exact (canonical30549 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2250 + difference 2 5) (sourceB2250 + difference 5 2) sourceC2250) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5003) := by
    have ha : (tripleCharges (sourceA2250 + difference 2 5) (sourceB2250 + difference 5 2) sourceC2250) = raw30381 := by
      apply Matrix.ext; unfold tripleCharges sourceA2250 sourceB2250 sourceC2250 difference raw30381; decide +kernel
    rw [ha]
    exact (canonical30381 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2250 + difference 3 0) (sourceB2250 + difference 0 3) sourceC2250) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4646) := by
    have ha : (tripleCharges (sourceA2250 + difference 3 0) (sourceB2250 + difference 0 3) sourceC2250) = raw30924 := by
      apply Matrix.ext; unfold tripleCharges sourceA2250 sourceB2250 sourceC2250 difference raw30924; decide +kernel
    rw [ha]
    exact (canonical30924 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2250 + difference 3 1) (sourceB2250 + difference 1 3) sourceC2250) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4984) := by
    have ha : (tripleCharges (sourceA2250 + difference 3 1) (sourceB2250 + difference 1 3) sourceC2250) = raw30925 := by
      apply Matrix.ext; unfold tripleCharges sourceA2250 sourceB2250 sourceC2250 difference raw30925; decide +kernel
    rw [ha]
    exact (canonical30925 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2250 + difference 3 2) (sourceB2250 + difference 2 3) sourceC2250) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4988) := by
    have ha : (tripleCharges (sourceA2250 + difference 3 2) (sourceB2250 + difference 2 3) sourceC2250) = raw30926 := by
      apply Matrix.ext; unfold tripleCharges sourceA2250 sourceB2250 sourceC2250 difference raw30926; decide +kernel
    rw [ha]
    exact (canonical30926 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2250 + difference 3 4) (sourceB2250 + difference 4 3) sourceC2250) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5003) := by
    have ha : (tripleCharges (sourceA2250 + difference 3 4) (sourceB2250 + difference 4 3) sourceC2250) = raw30927 := by
      apply Matrix.ext; unfold tripleCharges sourceA2250 sourceB2250 sourceC2250 difference raw30927; decide +kernel
    rw [ha]
    exact (canonical30927 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2250 + difference 3 5) (sourceB2250 + difference 5 3) sourceC2250) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5003) := by
    have ha : (tripleCharges (sourceA2250 + difference 3 5) (sourceB2250 + difference 5 3) sourceC2250) = raw30928 := by
      apply Matrix.ext; unfold tripleCharges sourceA2250 sourceB2250 sourceC2250 difference raw30928; decide +kernel
    rw [ha]
    exact (canonical30928 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2250 + difference 4 0) (sourceB2250 + difference 0 4) sourceC2250) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4656) := by
    have ha : (tripleCharges (sourceA2250 + difference 4 0) (sourceB2250 + difference 0 4) sourceC2250) = raw30929 := by
      apply Matrix.ext; unfold tripleCharges sourceA2250 sourceB2250 sourceC2250 difference raw30929; decide +kernel
    rw [ha]
    exact (canonical30929 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2250 + difference 4 1) (sourceB2250 + difference 1 4) sourceC2250) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4925) := by
    have ha : (tripleCharges (sourceA2250 + difference 4 1) (sourceB2250 + difference 1 4) sourceC2250) = raw30930 := by
      apply Matrix.ext; unfold tripleCharges sourceA2250 sourceB2250 sourceC2250 difference raw30930; decide +kernel
    rw [ha]
    exact (canonical30930 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2250 + difference 4 2) (sourceB2250 + difference 2 4) sourceC2250) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4914) := by
    have ha : (tripleCharges (sourceA2250 + difference 4 2) (sourceB2250 + difference 2 4) sourceC2250) = raw30931 := by
      apply Matrix.ext; unfold tripleCharges sourceA2250 sourceB2250 sourceC2250 difference raw30931; decide +kernel
    rw [ha]
    exact (canonical30931 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2250 + difference 4 3) (sourceB2250 + difference 3 4) sourceC2250) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4914) := by
    have ha : (tripleCharges (sourceA2250 + difference 4 3) (sourceB2250 + difference 3 4) sourceC2250) = raw30840 := by
      apply Matrix.ext; unfold tripleCharges sourceA2250 sourceB2250 sourceC2250 difference raw30840; decide +kernel
    rw [ha]
    exact (canonical30840 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2250 + difference 4 5) (sourceB2250 + difference 5 4) sourceC2250) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5023) := by
    have ha : (tripleCharges (sourceA2250 + difference 4 5) (sourceB2250 + difference 5 4) sourceC2250) = raw30700 := by
      apply Matrix.ext; unfold tripleCharges sourceA2250 sourceB2250 sourceC2250 difference raw30700; decide +kernel
    rw [ha]
    exact (canonical30700 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2250 + difference 5 0) (sourceB2250 + difference 0 5) sourceC2250) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4656) := by
    have ha : (tripleCharges (sourceA2250 + difference 5 0) (sourceB2250 + difference 0 5) sourceC2250) = raw30932 := by
      apply Matrix.ext; unfold tripleCharges sourceA2250 sourceB2250 sourceC2250 difference raw30932; decide +kernel
    rw [ha]
    exact (canonical30932 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2250 + difference 5 1) (sourceB2250 + difference 1 5) sourceC2250) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4925) := by
    have ha : (tripleCharges (sourceA2250 + difference 5 1) (sourceB2250 + difference 1 5) sourceC2250) = raw30933 := by
      apply Matrix.ext; unfold tripleCharges sourceA2250 sourceB2250 sourceC2250 difference raw30933; decide +kernel
    rw [ha]
    exact (canonical30933 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2250 + difference 5 2) (sourceB2250 + difference 2 5) sourceC2250) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4914) := by
    have ha : (tripleCharges (sourceA2250 + difference 5 2) (sourceB2250 + difference 2 5) sourceC2250) = raw30934 := by
      apply Matrix.ext; unfold tripleCharges sourceA2250 sourceB2250 sourceC2250 difference raw30934; decide +kernel
    rw [ha]
    exact (canonical30934 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2250 + difference 5 3) (sourceB2250 + difference 3 5) sourceC2250) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4914) := by
    have ha : (tripleCharges (sourceA2250 + difference 5 3) (sourceB2250 + difference 3 5) sourceC2250) = raw30844 := by
      apply Matrix.ext; unfold tripleCharges sourceA2250 sourceB2250 sourceC2250 difference raw30844; decide +kernel
    rw [ha]
    exact (canonical30844 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2250 + difference 5 4) (sourceB2250 + difference 4 5) sourceC2250) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5023) := by
    have ha : (tripleCharges (sourceA2250 + difference 5 4) (sourceB2250 + difference 4 5) sourceC2250) = raw30935 := by
      apply Matrix.ext; unfold tripleCharges sourceA2250 sourceB2250 sourceC2250 difference raw30935; decide +kernel
    rw [ha]
    exact (canonical30935 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2250 sourceB2250 sourceC2250
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2250, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2251 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2251 : Charge := ![0, 2, 0, 0, 0, -2]
def sourceC2251 : Charge := ![3, -1, 0, 0, -2, 0]
def sourceForm2251 : Integer.Sparse Master := [(Sum.inr 4368, 2), (Sum.inr 4373, 1), (Sum.inr 4375, 1), (Sum.inr 4466, 1), (Sum.inr 4687, 2), (Sum.inr 4694, 1), (Sum.inr 4700, 2), (Sum.inr 4704, 1), (Sum.inr 4773, 2), (Sum.inr 4776, 2), (Sum.inr 4810, 2), (Sum.inr 4865, 2), (Sum.inr 4867, 2), (Sum.inr 4868, 1), (Sum.inr 4872, 1), (Sum.inr 4894, 1), (Sum.inr 4896, 1), (Sum.inr 5264, 2), (Sum.inr 5291, 1), (Sum.inr 5297, 1), (Sum.inr 5300, 1)]

theorem sourceEq2251 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2251 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2251 + difference 0 1) (sourceB2251 + difference 1 0) sourceC2251) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5297) := by
    have ha : (tripleCharges (sourceA2251 + difference 0 1) (sourceB2251 + difference 1 0) sourceC2251) = raw30936 := by
      apply Matrix.ext; unfold tripleCharges sourceA2251 sourceB2251 sourceC2251 difference raw30936; decide +kernel
    rw [ha]
    exact (canonical30936 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2251 + difference 0 2) (sourceB2251 + difference 2 0) sourceC2251) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5264) := by
    have ha : (tripleCharges (sourceA2251 + difference 0 2) (sourceB2251 + difference 2 0) sourceC2251) = raw30937 := by
      apply Matrix.ext; unfold tripleCharges sourceA2251 sourceB2251 sourceC2251 difference raw30937; decide +kernel
    rw [ha]
    exact (canonical30937 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2251 + difference 0 3) (sourceB2251 + difference 3 0) sourceC2251) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5264) := by
    have ha : (tripleCharges (sourceA2251 + difference 0 3) (sourceB2251 + difference 3 0) sourceC2251) = raw30938 := by
      apply Matrix.ext; unfold tripleCharges sourceA2251 sourceB2251 sourceC2251 difference raw30938; decide +kernel
    rw [ha]
    exact (canonical30938 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2251 + difference 0 4) (sourceB2251 + difference 4 0) sourceC2251) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5300) := by
    have ha : (tripleCharges (sourceA2251 + difference 0 4) (sourceB2251 + difference 4 0) sourceC2251) = raw30939 := by
      apply Matrix.ext; unfold tripleCharges sourceA2251 sourceB2251 sourceC2251 difference raw30939; decide +kernel
    rw [ha]
    exact (canonical30939 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2251 + difference 0 5) (sourceB2251 + difference 5 0) sourceC2251) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5291) := by
    have ha : (tripleCharges (sourceA2251 + difference 0 5) (sourceB2251 + difference 5 0) sourceC2251) = raw30940 := by
      apply Matrix.ext; unfold tripleCharges sourceA2251 sourceB2251 sourceC2251 difference raw30940; decide +kernel
    rw [ha]
    exact (canonical30940 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2251 + difference 1 0) (sourceB2251 + difference 0 1) sourceC2251) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4466) := by
    have ha : (tripleCharges (sourceA2251 + difference 1 0) (sourceB2251 + difference 0 1) sourceC2251) = raw30941 := by
      apply Matrix.ext; unfold tripleCharges sourceA2251 sourceB2251 sourceC2251 difference raw30941; decide +kernel
    rw [ha]
    exact (canonical30941 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2251 + difference 1 2) (sourceB2251 + difference 2 1) sourceC2251) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4810) := by
    have ha : (tripleCharges (sourceA2251 + difference 1 2) (sourceB2251 + difference 2 1) sourceC2251) = raw22928 := by
      apply Matrix.ext; unfold tripleCharges sourceA2251 sourceB2251 sourceC2251 difference raw22928; decide +kernel
    rw [ha]
    exact (canonical22928 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2251 + difference 1 3) (sourceB2251 + difference 3 1) sourceC2251) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4810) := by
    have ha : (tripleCharges (sourceA2251 + difference 1 3) (sourceB2251 + difference 3 1) sourceC2251) = raw22929 := by
      apply Matrix.ext; unfold tripleCharges sourceA2251 sourceB2251 sourceC2251 difference raw22929; decide +kernel
    rw [ha]
    exact (canonical22929 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2251 + difference 1 4) (sourceB2251 + difference 4 1) sourceC2251) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4896) := by
    have ha : (tripleCharges (sourceA2251 + difference 1 4) (sourceB2251 + difference 4 1) sourceC2251) = raw22930 := by
      apply Matrix.ext; unfold tripleCharges sourceA2251 sourceB2251 sourceC2251 difference raw22930; decide +kernel
    rw [ha]
    exact (canonical22930 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2251 + difference 1 5) (sourceB2251 + difference 5 1) sourceC2251) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4894) := by
    have ha : (tripleCharges (sourceA2251 + difference 1 5) (sourceB2251 + difference 5 1) sourceC2251) = raw22931 := by
      apply Matrix.ext; unfold tripleCharges sourceA2251 sourceB2251 sourceC2251 difference raw22931; decide +kernel
    rw [ha]
    exact (canonical22931 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2251 + difference 2 0) (sourceB2251 + difference 0 2) sourceC2251) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4368) := by
    have ha : (tripleCharges (sourceA2251 + difference 2 0) (sourceB2251 + difference 0 2) sourceC2251) = raw22938 := by
      apply Matrix.ext; unfold tripleCharges sourceA2251 sourceB2251 sourceC2251 difference raw22938; decide +kernel
    rw [ha]
    exact (canonical22938 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2251 + difference 2 1) (sourceB2251 + difference 1 2) sourceC2251) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4700) := by
    have ha : (tripleCharges (sourceA2251 + difference 2 1) (sourceB2251 + difference 1 2) sourceC2251) = raw30942 := by
      apply Matrix.ext; unfold tripleCharges sourceA2251 sourceB2251 sourceC2251 difference raw30942; decide +kernel
    rw [ha]
    exact (canonical30942 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2251 + difference 2 3) (sourceB2251 + difference 3 2) sourceC2251) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4773) := by
    have ha : (tripleCharges (sourceA2251 + difference 2 3) (sourceB2251 + difference 3 2) sourceC2251) = raw30943 := by
      apply Matrix.ext; unfold tripleCharges sourceA2251 sourceB2251 sourceC2251 difference raw30943; decide +kernel
    rw [ha]
    exact (canonical30943 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2251 + difference 2 4) (sourceB2251 + difference 4 2) sourceC2251) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4867) := by
    have ha : (tripleCharges (sourceA2251 + difference 2 4) (sourceB2251 + difference 4 2) sourceC2251) = raw30944 := by
      apply Matrix.ext; unfold tripleCharges sourceA2251 sourceB2251 sourceC2251 difference raw30944; decide +kernel
    rw [ha]
    exact (canonical30944 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2251 + difference 2 5) (sourceB2251 + difference 5 2) sourceC2251) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4865) := by
    have ha : (tripleCharges (sourceA2251 + difference 2 5) (sourceB2251 + difference 5 2) sourceC2251) = raw30945 := by
      apply Matrix.ext; unfold tripleCharges sourceA2251 sourceB2251 sourceC2251 difference raw30945; decide +kernel
    rw [ha]
    exact (canonical30945 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2251 + difference 3 0) (sourceB2251 + difference 0 3) sourceC2251) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4368) := by
    have ha : (tripleCharges (sourceA2251 + difference 3 0) (sourceB2251 + difference 0 3) sourceC2251) = raw22943 := by
      apply Matrix.ext; unfold tripleCharges sourceA2251 sourceB2251 sourceC2251 difference raw22943; decide +kernel
    rw [ha]
    exact (canonical22943 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2251 + difference 3 1) (sourceB2251 + difference 1 3) sourceC2251) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4700) := by
    have ha : (tripleCharges (sourceA2251 + difference 3 1) (sourceB2251 + difference 1 3) sourceC2251) = raw30946 := by
      apply Matrix.ext; unfold tripleCharges sourceA2251 sourceB2251 sourceC2251 difference raw30946; decide +kernel
    rw [ha]
    exact (canonical30946 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2251 + difference 3 2) (sourceB2251 + difference 2 3) sourceC2251) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4773) := by
    have ha : (tripleCharges (sourceA2251 + difference 3 2) (sourceB2251 + difference 2 3) sourceC2251) = raw30947 := by
      apply Matrix.ext; unfold tripleCharges sourceA2251 sourceB2251 sourceC2251 difference raw30947; decide +kernel
    rw [ha]
    exact (canonical30947 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2251 + difference 3 4) (sourceB2251 + difference 4 3) sourceC2251) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4867) := by
    have ha : (tripleCharges (sourceA2251 + difference 3 4) (sourceB2251 + difference 4 3) sourceC2251) = raw30948 := by
      apply Matrix.ext; unfold tripleCharges sourceA2251 sourceB2251 sourceC2251 difference raw30948; decide +kernel
    rw [ha]
    exact (canonical30948 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2251 + difference 3 5) (sourceB2251 + difference 5 3) sourceC2251) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4865) := by
    have ha : (tripleCharges (sourceA2251 + difference 3 5) (sourceB2251 + difference 5 3) sourceC2251) = raw30949 := by
      apply Matrix.ext; unfold tripleCharges sourceA2251 sourceB2251 sourceC2251 difference raw30949; decide +kernel
    rw [ha]
    exact (canonical30949 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2251 + difference 4 0) (sourceB2251 + difference 0 4) sourceC2251) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4373) := by
    have ha : (tripleCharges (sourceA2251 + difference 4 0) (sourceB2251 + difference 0 4) sourceC2251) = raw22948 := by
      apply Matrix.ext; unfold tripleCharges sourceA2251 sourceB2251 sourceC2251 difference raw22948; decide +kernel
    rw [ha]
    exact (canonical22948 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2251 + difference 4 1) (sourceB2251 + difference 1 4) sourceC2251) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4704) := by
    have ha : (tripleCharges (sourceA2251 + difference 4 1) (sourceB2251 + difference 1 4) sourceC2251) = raw30950 := by
      apply Matrix.ext; unfold tripleCharges sourceA2251 sourceB2251 sourceC2251 difference raw30950; decide +kernel
    rw [ha]
    exact (canonical30950 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2251 + difference 4 2) (sourceB2251 + difference 2 4) sourceC2251) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4776) := by
    have ha : (tripleCharges (sourceA2251 + difference 4 2) (sourceB2251 + difference 2 4) sourceC2251) = raw30951 := by
      apply Matrix.ext; unfold tripleCharges sourceA2251 sourceB2251 sourceC2251 difference raw30951; decide +kernel
    rw [ha]
    exact (canonical30951 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2251 + difference 4 3) (sourceB2251 + difference 3 4) sourceC2251) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4776) := by
    have ha : (tripleCharges (sourceA2251 + difference 4 3) (sourceB2251 + difference 3 4) sourceC2251) = raw30952 := by
      apply Matrix.ext; unfold tripleCharges sourceA2251 sourceB2251 sourceC2251 difference raw30952; decide +kernel
    rw [ha]
    exact (canonical30952 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2251 + difference 4 5) (sourceB2251 + difference 5 4) sourceC2251) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4868) := by
    have ha : (tripleCharges (sourceA2251 + difference 4 5) (sourceB2251 + difference 5 4) sourceC2251) = raw30953 := by
      apply Matrix.ext; unfold tripleCharges sourceA2251 sourceB2251 sourceC2251 difference raw30953; decide +kernel
    rw [ha]
    exact (canonical30953 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2251 + difference 5 0) (sourceB2251 + difference 0 5) sourceC2251) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4375) := by
    have ha : (tripleCharges (sourceA2251 + difference 5 0) (sourceB2251 + difference 0 5) sourceC2251) = raw22953 := by
      apply Matrix.ext; unfold tripleCharges sourceA2251 sourceB2251 sourceC2251 difference raw22953; decide +kernel
    rw [ha]
    exact (canonical22953 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2251 + difference 5 1) (sourceB2251 + difference 1 5) sourceC2251) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4694) := by
    have ha : (tripleCharges (sourceA2251 + difference 5 1) (sourceB2251 + difference 1 5) sourceC2251) = raw30954 := by
      apply Matrix.ext; unfold tripleCharges sourceA2251 sourceB2251 sourceC2251 difference raw30954; decide +kernel
    rw [ha]
    exact (canonical30954 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2251 + difference 5 2) (sourceB2251 + difference 2 5) sourceC2251) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4687) := by
    have ha : (tripleCharges (sourceA2251 + difference 5 2) (sourceB2251 + difference 2 5) sourceC2251) = raw30955 := by
      apply Matrix.ext; unfold tripleCharges sourceA2251 sourceB2251 sourceC2251 difference raw30955; decide +kernel
    rw [ha]
    exact (canonical30955 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2251 + difference 5 3) (sourceB2251 + difference 3 5) sourceC2251) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4687) := by
    have ha : (tripleCharges (sourceA2251 + difference 5 3) (sourceB2251 + difference 3 5) sourceC2251) = raw30956 := by
      apply Matrix.ext; unfold tripleCharges sourceA2251 sourceB2251 sourceC2251 difference raw30956; decide +kernel
    rw [ha]
    exact (canonical30956 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2251 + difference 5 4) (sourceB2251 + difference 4 5) sourceC2251) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4872) := by
    have ha : (tripleCharges (sourceA2251 + difference 5 4) (sourceB2251 + difference 4 5) sourceC2251) = raw30957 := by
      apply Matrix.ext; unfold tripleCharges sourceA2251 sourceB2251 sourceC2251 difference raw30957; decide +kernel
    rw [ha]
    exact (canonical30957 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2251 sourceB2251 sourceC2251
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2251, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2252 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2252 : Charge := ![0, 2, 0, 0, 0, -2]
def sourceC2252 : Charge := ![3, -1, 0, 0, -2, 0]
def sourceForm2252 : Integer.Sparse Master := [(Sum.inr 1321, 2), (Sum.inr 1323, 1), (Sum.inr 1325, 1), (Sum.inr 1419, 1), (Sum.inr 1813, 2), (Sum.inr 1820, 1), (Sum.inr 2113, 1), (Sum.inr 2816, 2), (Sum.inr 2821, 1), (Sum.inr 2966, 1), (Sum.inr 3040, 2), (Sum.inr 3055, 1), (Sum.inr 3056, 1), (Sum.inr 3103, 1), (Sum.inr 3131, 2), (Sum.inr 3163, 2), (Sum.inr 3180, 2), (Sum.inr 3185, 2), (Sum.inr 3206, 2), (Sum.inr 3225, 1), (Sum.inr 3230, 1)]

theorem sourceEq2252 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2252 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2252 + difference 0 1) (sourceB2252 + difference 1 0) sourceC2252) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3056) := by
    have ha : (tripleCharges (sourceA2252 + difference 0 1) (sourceB2252 + difference 1 0) sourceC2252) = raw30958 := by
      apply Matrix.ext; unfold tripleCharges sourceA2252 sourceB2252 sourceC2252 difference raw30958; decide +kernel
    rw [ha]
    exact (canonical30958 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2252 + difference 0 2) (sourceB2252 + difference 2 0) sourceC2252) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3040) := by
    have ha : (tripleCharges (sourceA2252 + difference 0 2) (sourceB2252 + difference 2 0) sourceC2252) = raw30959 := by
      apply Matrix.ext; unfold tripleCharges sourceA2252 sourceB2252 sourceC2252 difference raw30959; decide +kernel
    rw [ha]
    exact (canonical30959 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2252 + difference 0 3) (sourceB2252 + difference 3 0) sourceC2252) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3040) := by
    have ha : (tripleCharges (sourceA2252 + difference 0 3) (sourceB2252 + difference 3 0) sourceC2252) = raw30960 := by
      apply Matrix.ext; unfold tripleCharges sourceA2252 sourceB2252 sourceC2252 difference raw30960; decide +kernel
    rw [ha]
    exact (canonical30960 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2252 + difference 0 4) (sourceB2252 + difference 4 0) sourceC2252) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3055) := by
    have ha : (tripleCharges (sourceA2252 + difference 0 4) (sourceB2252 + difference 4 0) sourceC2252) = raw30961 := by
      apply Matrix.ext; unfold tripleCharges sourceA2252 sourceB2252 sourceC2252 difference raw30961; decide +kernel
    rw [ha]
    exact (canonical30961 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2252 + difference 0 5) (sourceB2252 + difference 5 0) sourceC2252) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3103) := by
    have ha : (tripleCharges (sourceA2252 + difference 0 5) (sourceB2252 + difference 5 0) sourceC2252) = raw30962 := by
      apply Matrix.ext; unfold tripleCharges sourceA2252 sourceB2252 sourceC2252 difference raw30962; decide +kernel
    rw [ha]
    exact (canonical30962 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2252 + difference 1 0) (sourceB2252 + difference 0 1) sourceC2252) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1419) := by
    have ha : (tripleCharges (sourceA2252 + difference 1 0) (sourceB2252 + difference 0 1) sourceC2252) = raw30963 := by
      apply Matrix.ext; unfold tripleCharges sourceA2252 sourceB2252 sourceC2252 difference raw30963; decide +kernel
    rw [ha]
    exact (canonical30963 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2252 + difference 1 2) (sourceB2252 + difference 2 1) sourceC2252) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3206) := by
    have ha : (tripleCharges (sourceA2252 + difference 1 2) (sourceB2252 + difference 2 1) sourceC2252) = raw22958 := by
      apply Matrix.ext; unfold tripleCharges sourceA2252 sourceB2252 sourceC2252 difference raw22958; decide +kernel
    rw [ha]
    exact (canonical22958 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2252 + difference 1 3) (sourceB2252 + difference 3 1) sourceC2252) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3206) := by
    have ha : (tripleCharges (sourceA2252 + difference 1 3) (sourceB2252 + difference 3 1) sourceC2252) = raw22959 := by
      apply Matrix.ext; unfold tripleCharges sourceA2252 sourceB2252 sourceC2252 difference raw22959; decide +kernel
    rw [ha]
    exact (canonical22959 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2252 + difference 1 4) (sourceB2252 + difference 4 1) sourceC2252) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3225) := by
    have ha : (tripleCharges (sourceA2252 + difference 1 4) (sourceB2252 + difference 4 1) sourceC2252) = raw22960 := by
      apply Matrix.ext; unfold tripleCharges sourceA2252 sourceB2252 sourceC2252 difference raw22960; decide +kernel
    rw [ha]
    exact (canonical22960 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2252 + difference 1 5) (sourceB2252 + difference 5 1) sourceC2252) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3230) := by
    have ha : (tripleCharges (sourceA2252 + difference 1 5) (sourceB2252 + difference 5 1) sourceC2252) = raw22961 := by
      apply Matrix.ext; unfold tripleCharges sourceA2252 sourceB2252 sourceC2252 difference raw22961; decide +kernel
    rw [ha]
    exact (canonical22961 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2252 + difference 2 0) (sourceB2252 + difference 0 2) sourceC2252) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1321) := by
    have ha : (tripleCharges (sourceA2252 + difference 2 0) (sourceB2252 + difference 0 2) sourceC2252) = raw22968 := by
      apply Matrix.ext; unfold tripleCharges sourceA2252 sourceB2252 sourceC2252 difference raw22968; decide +kernel
    rw [ha]
    exact (canonical22968 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2252 + difference 2 1) (sourceB2252 + difference 1 2) sourceC2252) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3131) := by
    have ha : (tripleCharges (sourceA2252 + difference 2 1) (sourceB2252 + difference 1 2) sourceC2252) = raw30964 := by
      apply Matrix.ext; unfold tripleCharges sourceA2252 sourceB2252 sourceC2252 difference raw30964; decide +kernel
    rw [ha]
    exact (canonical30964 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2252 + difference 2 3) (sourceB2252 + difference 3 2) sourceC2252) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3163) := by
    have ha : (tripleCharges (sourceA2252 + difference 2 3) (sourceB2252 + difference 3 2) sourceC2252) = raw30965 := by
      apply Matrix.ext; unfold tripleCharges sourceA2252 sourceB2252 sourceC2252 difference raw30965; decide +kernel
    rw [ha]
    exact (canonical30965 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2252 + difference 2 4) (sourceB2252 + difference 4 2) sourceC2252) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3180) := by
    have ha : (tripleCharges (sourceA2252 + difference 2 4) (sourceB2252 + difference 4 2) sourceC2252) = raw30966 := by
      apply Matrix.ext; unfold tripleCharges sourceA2252 sourceB2252 sourceC2252 difference raw30966; decide +kernel
    rw [ha]
    exact (canonical30966 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2252 + difference 2 5) (sourceB2252 + difference 5 2) sourceC2252) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3185) := by
    have ha : (tripleCharges (sourceA2252 + difference 2 5) (sourceB2252 + difference 5 2) sourceC2252) = raw30967 := by
      apply Matrix.ext; unfold tripleCharges sourceA2252 sourceB2252 sourceC2252 difference raw30967; decide +kernel
    rw [ha]
    exact (canonical30967 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2252 + difference 3 0) (sourceB2252 + difference 0 3) sourceC2252) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1321) := by
    have ha : (tripleCharges (sourceA2252 + difference 3 0) (sourceB2252 + difference 0 3) sourceC2252) = raw22973 := by
      apply Matrix.ext; unfold tripleCharges sourceA2252 sourceB2252 sourceC2252 difference raw22973; decide +kernel
    rw [ha]
    exact (canonical22973 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2252 + difference 3 1) (sourceB2252 + difference 1 3) sourceC2252) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3131) := by
    have ha : (tripleCharges (sourceA2252 + difference 3 1) (sourceB2252 + difference 1 3) sourceC2252) = raw30968 := by
      apply Matrix.ext; unfold tripleCharges sourceA2252 sourceB2252 sourceC2252 difference raw30968; decide +kernel
    rw [ha]
    exact (canonical30968 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2252 + difference 3 2) (sourceB2252 + difference 2 3) sourceC2252) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3163) := by
    have ha : (tripleCharges (sourceA2252 + difference 3 2) (sourceB2252 + difference 2 3) sourceC2252) = raw30969 := by
      apply Matrix.ext; unfold tripleCharges sourceA2252 sourceB2252 sourceC2252 difference raw30969; decide +kernel
    rw [ha]
    exact (canonical30969 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2252 + difference 3 4) (sourceB2252 + difference 4 3) sourceC2252) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3180) := by
    have ha : (tripleCharges (sourceA2252 + difference 3 4) (sourceB2252 + difference 4 3) sourceC2252) = raw30970 := by
      apply Matrix.ext; unfold tripleCharges sourceA2252 sourceB2252 sourceC2252 difference raw30970; decide +kernel
    rw [ha]
    exact (canonical30970 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2252 + difference 3 5) (sourceB2252 + difference 5 3) sourceC2252) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3185) := by
    have ha : (tripleCharges (sourceA2252 + difference 3 5) (sourceB2252 + difference 5 3) sourceC2252) = raw30971 := by
      apply Matrix.ext; unfold tripleCharges sourceA2252 sourceB2252 sourceC2252 difference raw30971; decide +kernel
    rw [ha]
    exact (canonical30971 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2252 + difference 4 0) (sourceB2252 + difference 0 4) sourceC2252) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1325) := by
    have ha : (tripleCharges (sourceA2252 + difference 4 0) (sourceB2252 + difference 0 4) sourceC2252) = raw22978 := by
      apply Matrix.ext; unfold tripleCharges sourceA2252 sourceB2252 sourceC2252 difference raw22978; decide +kernel
    rw [ha]
    exact (canonical22978 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2252 + difference 4 1) (sourceB2252 + difference 1 4) sourceC2252) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2821) := by
    have ha : (tripleCharges (sourceA2252 + difference 4 1) (sourceB2252 + difference 1 4) sourceC2252) = raw30972 := by
      apply Matrix.ext; unfold tripleCharges sourceA2252 sourceB2252 sourceC2252 difference raw30972; decide +kernel
    rw [ha]
    exact (canonical30972 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2252 + difference 4 2) (sourceB2252 + difference 2 4) sourceC2252) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2816) := by
    have ha : (tripleCharges (sourceA2252 + difference 4 2) (sourceB2252 + difference 2 4) sourceC2252) = raw30973 := by
      apply Matrix.ext; unfold tripleCharges sourceA2252 sourceB2252 sourceC2252 difference raw30973; decide +kernel
    rw [ha]
    exact (canonical30973 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2252 + difference 4 3) (sourceB2252 + difference 3 4) sourceC2252) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2816) := by
    have ha : (tripleCharges (sourceA2252 + difference 4 3) (sourceB2252 + difference 3 4) sourceC2252) = raw30974 := by
      apply Matrix.ext; unfold tripleCharges sourceA2252 sourceB2252 sourceC2252 difference raw30974; decide +kernel
    rw [ha]
    exact (canonical30974 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2252 + difference 4 5) (sourceB2252 + difference 5 4) sourceC2252) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2966) := by
    have ha : (tripleCharges (sourceA2252 + difference 4 5) (sourceB2252 + difference 5 4) sourceC2252) = raw30975 := by
      apply Matrix.ext; unfold tripleCharges sourceA2252 sourceB2252 sourceC2252 difference raw30975; decide +kernel
    rw [ha]
    exact (canonical30975 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2252 + difference 5 0) (sourceB2252 + difference 0 5) sourceC2252) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1323) := by
    have ha : (tripleCharges (sourceA2252 + difference 5 0) (sourceB2252 + difference 0 5) sourceC2252) = raw22983 := by
      apply Matrix.ext; unfold tripleCharges sourceA2252 sourceB2252 sourceC2252 difference raw22983; decide +kernel
    rw [ha]
    exact (canonical22983 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2252 + difference 5 1) (sourceB2252 + difference 1 5) sourceC2252) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1820) := by
    have ha : (tripleCharges (sourceA2252 + difference 5 1) (sourceB2252 + difference 1 5) sourceC2252) = raw30976 := by
      apply Matrix.ext; unfold tripleCharges sourceA2252 sourceB2252 sourceC2252 difference raw30976; decide +kernel
    rw [ha]
    exact (canonical30976 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2252 + difference 5 2) (sourceB2252 + difference 2 5) sourceC2252) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1813) := by
    have ha : (tripleCharges (sourceA2252 + difference 5 2) (sourceB2252 + difference 2 5) sourceC2252) = raw30977 := by
      apply Matrix.ext; unfold tripleCharges sourceA2252 sourceB2252 sourceC2252 difference raw30977; decide +kernel
    rw [ha]
    exact (canonical30977 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2252 + difference 5 3) (sourceB2252 + difference 3 5) sourceC2252) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1813) := by
    have ha : (tripleCharges (sourceA2252 + difference 5 3) (sourceB2252 + difference 3 5) sourceC2252) = raw30978 := by
      apply Matrix.ext; unfold tripleCharges sourceA2252 sourceB2252 sourceC2252 difference raw30978; decide +kernel
    rw [ha]
    exact (canonical30978 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2252 + difference 5 4) (sourceB2252 + difference 4 5) sourceC2252) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2113) := by
    have ha : (tripleCharges (sourceA2252 + difference 5 4) (sourceB2252 + difference 4 5) sourceC2252) = raw30979 := by
      apply Matrix.ext; unfold tripleCharges sourceA2252 sourceB2252 sourceC2252 difference raw30979; decide +kernel
    rw [ha]
    exact (canonical30979 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2252 sourceB2252 sourceC2252
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2252, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2253 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2253 : Charge := ![0, 2, 0, 0, 0, -2]
def sourceC2253 : Charge := ![3, -1, 0, 0, -2, 0]
def sourceForm2253 : Integer.Sparse Master := [(Sum.inr 1712, 2), (Sum.inr 1735, 1), (Sum.inr 1738, 1), (Sum.inr 1743, 1), (Sum.inr 2162, 2), (Sum.inr 2163, 1), (Sum.inr 2194, 2), (Sum.inr 2212, 2), (Sum.inr 2215, 2), (Sum.inr 2242, 2), (Sum.inr 2249, 2), (Sum.inr 2251, 2), (Sum.inr 2261, 1), (Sum.inr 2264, 1), (Sum.inr 2273, 1), (Sum.inr 2278, 1), (Sum.inr 2282, 1), (Sum.inr 2729, 2), (Sum.inr 2765, 1), (Sum.inr 2771, 1), (Sum.inr 2774, 1)]

theorem sourceEq2253 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2253 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2253 + difference 0 1) (sourceB2253 + difference 1 0) sourceC2253) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2771) := by
    have ha : (tripleCharges (sourceA2253 + difference 0 1) (sourceB2253 + difference 1 0) sourceC2253) = raw30980 := by
      apply Matrix.ext; unfold tripleCharges sourceA2253 sourceB2253 sourceC2253 difference raw30980; decide +kernel
    rw [ha]
    exact (canonical30980 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2253 + difference 0 2) (sourceB2253 + difference 2 0) sourceC2253) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2729) := by
    have ha : (tripleCharges (sourceA2253 + difference 0 2) (sourceB2253 + difference 2 0) sourceC2253) = raw30981 := by
      apply Matrix.ext; unfold tripleCharges sourceA2253 sourceB2253 sourceC2253 difference raw30981; decide +kernel
    rw [ha]
    exact (canonical30981 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2253 + difference 0 3) (sourceB2253 + difference 3 0) sourceC2253) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2729) := by
    have ha : (tripleCharges (sourceA2253 + difference 0 3) (sourceB2253 + difference 3 0) sourceC2253) = raw30982 := by
      apply Matrix.ext; unfold tripleCharges sourceA2253 sourceB2253 sourceC2253 difference raw30982; decide +kernel
    rw [ha]
    exact (canonical30982 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2253 + difference 0 4) (sourceB2253 + difference 4 0) sourceC2253) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2774) := by
    have ha : (tripleCharges (sourceA2253 + difference 0 4) (sourceB2253 + difference 4 0) sourceC2253) = raw30983 := by
      apply Matrix.ext; unfold tripleCharges sourceA2253 sourceB2253 sourceC2253 difference raw30983; decide +kernel
    rw [ha]
    exact (canonical30983 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2253 + difference 0 5) (sourceB2253 + difference 5 0) sourceC2253) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2765) := by
    have ha : (tripleCharges (sourceA2253 + difference 0 5) (sourceB2253 + difference 5 0) sourceC2253) = raw30984 := by
      apply Matrix.ext; unfold tripleCharges sourceA2253 sourceB2253 sourceC2253 difference raw30984; decide +kernel
    rw [ha]
    exact (canonical30984 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2253 + difference 1 0) (sourceB2253 + difference 0 1) sourceC2253) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1738) := by
    have ha : (tripleCharges (sourceA2253 + difference 1 0) (sourceB2253 + difference 0 1) sourceC2253) = raw30985 := by
      apply Matrix.ext; unfold tripleCharges sourceA2253 sourceB2253 sourceC2253 difference raw30985; decide +kernel
    rw [ha]
    exact (canonical30985 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2253 + difference 1 2) (sourceB2253 + difference 2 1) sourceC2253) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2215) := by
    have ha : (tripleCharges (sourceA2253 + difference 1 2) (sourceB2253 + difference 2 1) sourceC2253) = raw22988 := by
      apply Matrix.ext; unfold tripleCharges sourceA2253 sourceB2253 sourceC2253 difference raw22988; decide +kernel
    rw [ha]
    exact (canonical22988 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2253 + difference 1 3) (sourceB2253 + difference 3 1) sourceC2253) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2215) := by
    have ha : (tripleCharges (sourceA2253 + difference 1 3) (sourceB2253 + difference 3 1) sourceC2253) = raw22989 := by
      apply Matrix.ext; unfold tripleCharges sourceA2253 sourceB2253 sourceC2253 difference raw22989; decide +kernel
    rw [ha]
    exact (canonical22989 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2253 + difference 1 4) (sourceB2253 + difference 4 1) sourceC2253) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2278) := by
    have ha : (tripleCharges (sourceA2253 + difference 1 4) (sourceB2253 + difference 4 1) sourceC2253) = raw22990 := by
      apply Matrix.ext; unfold tripleCharges sourceA2253 sourceB2253 sourceC2253 difference raw22990; decide +kernel
    rw [ha]
    exact (canonical22990 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2253 + difference 1 5) (sourceB2253 + difference 5 1) sourceC2253) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2264) := by
    have ha : (tripleCharges (sourceA2253 + difference 1 5) (sourceB2253 + difference 5 1) sourceC2253) = raw22991 := by
      apply Matrix.ext; unfold tripleCharges sourceA2253 sourceB2253 sourceC2253 difference raw22991; decide +kernel
    rw [ha]
    exact (canonical22991 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2253 + difference 2 0) (sourceB2253 + difference 0 2) sourceC2253) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1712) := by
    have ha : (tripleCharges (sourceA2253 + difference 2 0) (sourceB2253 + difference 0 2) sourceC2253) = raw22998 := by
      apply Matrix.ext; unfold tripleCharges sourceA2253 sourceB2253 sourceC2253 difference raw22998; decide +kernel
    rw [ha]
    exact (canonical22998 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2253 + difference 2 1) (sourceB2253 + difference 1 2) sourceC2253) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2249) := by
    have ha : (tripleCharges (sourceA2253 + difference 2 1) (sourceB2253 + difference 1 2) sourceC2253) = raw30986 := by
      apply Matrix.ext; unfold tripleCharges sourceA2253 sourceB2253 sourceC2253 difference raw30986; decide +kernel
    rw [ha]
    exact (canonical30986 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2253 + difference 2 3) (sourceB2253 + difference 3 2) sourceC2253) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2194) := by
    have ha : (tripleCharges (sourceA2253 + difference 2 3) (sourceB2253 + difference 3 2) sourceC2253) = raw30987 := by
      apply Matrix.ext; unfold tripleCharges sourceA2253 sourceB2253 sourceC2253 difference raw30987; decide +kernel
    rw [ha]
    exact (canonical30987 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2253 + difference 2 4) (sourceB2253 + difference 4 2) sourceC2253) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2251) := by
    have ha : (tripleCharges (sourceA2253 + difference 2 4) (sourceB2253 + difference 4 2) sourceC2253) = raw30988 := by
      apply Matrix.ext; unfold tripleCharges sourceA2253 sourceB2253 sourceC2253 difference raw30988; decide +kernel
    rw [ha]
    exact (canonical30988 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2253 + difference 2 5) (sourceB2253 + difference 5 2) sourceC2253) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2242) := by
    have ha : (tripleCharges (sourceA2253 + difference 2 5) (sourceB2253 + difference 5 2) sourceC2253) = raw30989 := by
      apply Matrix.ext; unfold tripleCharges sourceA2253 sourceB2253 sourceC2253 difference raw30989; decide +kernel
    rw [ha]
    exact (canonical30989 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2253 + difference 3 0) (sourceB2253 + difference 0 3) sourceC2253) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1712) := by
    have ha : (tripleCharges (sourceA2253 + difference 3 0) (sourceB2253 + difference 0 3) sourceC2253) = raw23003 := by
      apply Matrix.ext; unfold tripleCharges sourceA2253 sourceB2253 sourceC2253 difference raw23003; decide +kernel
    rw [ha]
    exact (canonical23003 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2253 + difference 3 1) (sourceB2253 + difference 1 3) sourceC2253) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2249) := by
    have ha : (tripleCharges (sourceA2253 + difference 3 1) (sourceB2253 + difference 1 3) sourceC2253) = raw30990 := by
      apply Matrix.ext; unfold tripleCharges sourceA2253 sourceB2253 sourceC2253 difference raw30990; decide +kernel
    rw [ha]
    exact (canonical30990 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2253 + difference 3 2) (sourceB2253 + difference 2 3) sourceC2253) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2194) := by
    have ha : (tripleCharges (sourceA2253 + difference 3 2) (sourceB2253 + difference 2 3) sourceC2253) = raw30991 := by
      apply Matrix.ext; unfold tripleCharges sourceA2253 sourceB2253 sourceC2253 difference raw30991; decide +kernel
    rw [ha]
    exact (canonical30991 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2253 + difference 3 4) (sourceB2253 + difference 4 3) sourceC2253) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2251) := by
    have ha : (tripleCharges (sourceA2253 + difference 3 4) (sourceB2253 + difference 4 3) sourceC2253) = raw30992 := by
      apply Matrix.ext; unfold tripleCharges sourceA2253 sourceB2253 sourceC2253 difference raw30992; decide +kernel
    rw [ha]
    exact (canonical30992 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2253 + difference 3 5) (sourceB2253 + difference 5 3) sourceC2253) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2242) := by
    have ha : (tripleCharges (sourceA2253 + difference 3 5) (sourceB2253 + difference 5 3) sourceC2253) = raw30993 := by
      apply Matrix.ext; unfold tripleCharges sourceA2253 sourceB2253 sourceC2253 difference raw30993; decide +kernel
    rw [ha]
    exact (canonical30993 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2253 + difference 4 0) (sourceB2253 + difference 0 4) sourceC2253) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1735) := by
    have ha : (tripleCharges (sourceA2253 + difference 4 0) (sourceB2253 + difference 0 4) sourceC2253) = raw23008 := by
      apply Matrix.ext; unfold tripleCharges sourceA2253 sourceB2253 sourceC2253 difference raw23008; decide +kernel
    rw [ha]
    exact (canonical23008 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2253 + difference 4 1) (sourceB2253 + difference 1 4) sourceC2253) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2273) := by
    have ha : (tripleCharges (sourceA2253 + difference 4 1) (sourceB2253 + difference 1 4) sourceC2253) = raw30994 := by
      apply Matrix.ext; unfold tripleCharges sourceA2253 sourceB2253 sourceC2253 difference raw30994; decide +kernel
    rw [ha]
    exact (canonical30994 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2253 + difference 4 2) (sourceB2253 + difference 2 4) sourceC2253) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2212) := by
    have ha : (tripleCharges (sourceA2253 + difference 4 2) (sourceB2253 + difference 2 4) sourceC2253) = raw30995 := by
      apply Matrix.ext; unfold tripleCharges sourceA2253 sourceB2253 sourceC2253 difference raw30995; decide +kernel
    rw [ha]
    exact (canonical30995 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2253 + difference 4 3) (sourceB2253 + difference 3 4) sourceC2253) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2212) := by
    have ha : (tripleCharges (sourceA2253 + difference 4 3) (sourceB2253 + difference 3 4) sourceC2253) = raw30996 := by
      apply Matrix.ext; unfold tripleCharges sourceA2253 sourceB2253 sourceC2253 difference raw30996; decide +kernel
    rw [ha]
    exact (canonical30996 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2253 + difference 4 5) (sourceB2253 + difference 5 4) sourceC2253) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2261) := by
    have ha : (tripleCharges (sourceA2253 + difference 4 5) (sourceB2253 + difference 5 4) sourceC2253) = raw30997 := by
      apply Matrix.ext; unfold tripleCharges sourceA2253 sourceB2253 sourceC2253 difference raw30997; decide +kernel
    rw [ha]
    exact (canonical30997 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2253 + difference 5 0) (sourceB2253 + difference 0 5) sourceC2253) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1743) := by
    have ha : (tripleCharges (sourceA2253 + difference 5 0) (sourceB2253 + difference 0 5) sourceC2253) = raw23013 := by
      apply Matrix.ext; unfold tripleCharges sourceA2253 sourceB2253 sourceC2253 difference raw23013; decide +kernel
    rw [ha]
    exact (canonical23013 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2253 + difference 5 1) (sourceB2253 + difference 1 5) sourceC2253) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2163) := by
    have ha : (tripleCharges (sourceA2253 + difference 5 1) (sourceB2253 + difference 1 5) sourceC2253) = raw30998 := by
      apply Matrix.ext; unfold tripleCharges sourceA2253 sourceB2253 sourceC2253 difference raw30998; decide +kernel
    rw [ha]
    exact (canonical30998 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2253 + difference 5 2) (sourceB2253 + difference 2 5) sourceC2253) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2162) := by
    have ha : (tripleCharges (sourceA2253 + difference 5 2) (sourceB2253 + difference 2 5) sourceC2253) = raw30999 := by
      apply Matrix.ext; unfold tripleCharges sourceA2253 sourceB2253 sourceC2253 difference raw30999; decide +kernel
    rw [ha]
    exact (canonical30999 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2253 + difference 5 3) (sourceB2253 + difference 3 5) sourceC2253) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2162) := by
    have ha : (tripleCharges (sourceA2253 + difference 5 3) (sourceB2253 + difference 3 5) sourceC2253) = raw31000 := by
      apply Matrix.ext; unfold tripleCharges sourceA2253 sourceB2253 sourceC2253 difference raw31000; decide +kernel
    rw [ha]
    exact (canonical31000 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2253 + difference 5 4) (sourceB2253 + difference 4 5) sourceC2253) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2282) := by
    have ha : (tripleCharges (sourceA2253 + difference 5 4) (sourceB2253 + difference 4 5) sourceC2253) = raw31001 := by
      apply Matrix.ext; unfold tripleCharges sourceA2253 sourceB2253 sourceC2253 difference raw31001; decide +kernel
    rw [ha]
    exact (canonical31001 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2253 sourceB2253 sourceC2253
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2253, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2254 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2254 : Charge := ![0, 2, 0, 0, 0, -2]
def sourceC2254 : Charge := ![3, -1, 0, 0, -2, 0]
def sourceForm2254 : Integer.Sparse Master := [(Sum.inr 1826, 2), (Sum.inr 1830, 1), (Sum.inr 1832, 1), (Sum.inr 2115, 1), (Sum.inr 3056, 1), (Sum.inr 4084, -1)]

theorem sourceEq2254 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2254 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2254 + difference 0 1) (sourceB2254 + difference 1 0) sourceC2254) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3056) := by
    have ha : (tripleCharges (sourceA2254 + difference 0 1) (sourceB2254 + difference 1 0) sourceC2254) = raw31002 := by
      apply Matrix.ext; unfold tripleCharges sourceA2254 sourceB2254 sourceC2254 difference raw31002; decide +kernel
    rw [ha]
    exact (canonical31002 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2254 + difference 1 1) (sourceB2254 + difference 1 1) sourceC2254) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2115) := by
    have ha : (tripleCharges (sourceA2254 + difference 1 1) (sourceB2254 + difference 1 1) sourceC2254) = raw23028 := by
      apply Matrix.ext; unfold tripleCharges sourceA2254 sourceB2254 sourceC2254 difference raw23028; decide +kernel
    rw [ha]
    exact (canonical23028 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2254 + difference 2 1) (sourceB2254 + difference 1 2) sourceC2254) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1826) := by
    have ha : (tripleCharges (sourceA2254 + difference 2 1) (sourceB2254 + difference 1 2) sourceC2254) = raw31003 := by
      apply Matrix.ext; unfold tripleCharges sourceA2254 sourceB2254 sourceC2254 difference raw31003; decide +kernel
    rw [ha]
    exact (canonical31003 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2254 + difference 3 1) (sourceB2254 + difference 1 3) sourceC2254) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1826) := by
    have ha : (tripleCharges (sourceA2254 + difference 3 1) (sourceB2254 + difference 1 3) sourceC2254) = raw31004 := by
      apply Matrix.ext; unfold tripleCharges sourceA2254 sourceB2254 sourceC2254 difference raw31004; decide +kernel
    rw [ha]
    exact (canonical31004 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2254 + difference 4 1) (sourceB2254 + difference 1 4) sourceC2254) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1830) := by
    have ha : (tripleCharges (sourceA2254 + difference 4 1) (sourceB2254 + difference 1 4) sourceC2254) = raw31005 := by
      apply Matrix.ext; unfold tripleCharges sourceA2254 sourceB2254 sourceC2254 difference raw31005; decide +kernel
    rw [ha]
    exact (canonical31005 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2254 + difference 5 1) (sourceB2254 + difference 1 5) sourceC2254) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1832) := by
    have ha : (tripleCharges (sourceA2254 + difference 5 1) (sourceB2254 + difference 1 5) sourceC2254) = raw27395 := by
      apply Matrix.ext; unfold tripleCharges sourceA2254 sourceB2254 sourceC2254 difference raw27395; decide +kernel
    rw [ha]
    exact (canonical27395 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2254 + sourceB2254) sourceC2254) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA2254 + sourceB2254) sourceC2254) = raw23023 := by
      apply Matrix.ext; unfold doubleCharges sourceA2254 sourceB2254 sourceC2254 raw23023; decide +kernel
    rw [ha]
    exact (canonical23023 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2254 sourceB2254 sourceC2254
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2254, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2255 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2255 : Charge := ![0, 2, 0, 0, 0, -2]
def sourceC2255 : Charge := ![3, -1, 0, 0, -2, 0]
def sourceForm2255 : Integer.Sparse Master := [(Sum.inr 946, 1), (Sum.inr 1826, 1), (Sum.inr 1974, 1), (Sum.inr 2106, 1), (Sum.inr 2108, 1), (Sum.inr 2115, 1), (Sum.inr 4084, -1)]

theorem sourceEq2255 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2255 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2255 + difference 2 0) (sourceB2255 + difference 0 2) sourceC2255) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 946) := by
    have ha : (tripleCharges (sourceA2255 + difference 2 0) (sourceB2255 + difference 0 2) sourceC2255) = raw23029 := by
      apply Matrix.ext; unfold tripleCharges sourceA2255 sourceB2255 sourceC2255 difference raw23029; decide +kernel
    rw [ha]
    exact (canonical23029 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2255 + difference 2 1) (sourceB2255 + difference 1 2) sourceC2255) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1826) := by
    have ha : (tripleCharges (sourceA2255 + difference 2 1) (sourceB2255 + difference 1 2) sourceC2255) = raw31003 := by
      apply Matrix.ext; unfold tripleCharges sourceA2255 sourceB2255 sourceC2255 difference raw31003; decide +kernel
    rw [ha]
    exact (canonical31003 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2255 + difference 2 2) (sourceB2255 + difference 2 2) sourceC2255) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2115) := by
    have ha : (tripleCharges (sourceA2255 + difference 2 2) (sourceB2255 + difference 2 2) sourceC2255) = raw23028 := by
      apply Matrix.ext; unfold tripleCharges sourceA2255 sourceB2255 sourceC2255 difference raw23028; decide +kernel
    rw [ha]
    exact (canonical23028 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2255 + difference 2 3) (sourceB2255 + difference 3 2) sourceC2255) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1974) := by
    have ha : (tripleCharges (sourceA2255 + difference 2 3) (sourceB2255 + difference 3 2) sourceC2255) = raw31006 := by
      apply Matrix.ext; unfold tripleCharges sourceA2255 sourceB2255 sourceC2255 difference raw31006; decide +kernel
    rw [ha]
    exact (canonical31006 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2255 + difference 2 4) (sourceB2255 + difference 4 2) sourceC2255) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2108) := by
    have ha : (tripleCharges (sourceA2255 + difference 2 4) (sourceB2255 + difference 4 2) sourceC2255) = raw31007 := by
      apply Matrix.ext; unfold tripleCharges sourceA2255 sourceB2255 sourceC2255 difference raw31007; decide +kernel
    rw [ha]
    exact (canonical31007 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2255 + difference 2 5) (sourceB2255 + difference 5 2) sourceC2255) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2106) := by
    have ha : (tripleCharges (sourceA2255 + difference 2 5) (sourceB2255 + difference 5 2) sourceC2255) = raw31008 := by
      apply Matrix.ext; unfold tripleCharges sourceA2255 sourceB2255 sourceC2255 difference raw31008; decide +kernel
    rw [ha]
    exact (canonical31008 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2255 + sourceB2255) sourceC2255) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA2255 + sourceB2255) sourceC2255) = raw23023 := by
      apply Matrix.ext; unfold doubleCharges sourceA2255 sourceB2255 sourceC2255 raw23023; decide +kernel
    rw [ha]
    exact (canonical23023 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2255 sourceB2255 sourceC2255
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2255, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2256 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2256 : Charge := ![3, -1, 0, 0, -2, 0]
def sourceC2256 : Charge := ![0, 2, 0, 0, 0, -2]
def sourceForm2256 : Integer.Sparse Master := [(Sum.inr 4238, 2), (Sum.inr 4241, 1), (Sum.inr 4243, 1), (Sum.inr 4278, 1), (Sum.inr 4673, 2), (Sum.inr 4688, 2), (Sum.inr 4691, 1), (Sum.inr 4693, 1), (Sum.inr 4724, 2), (Sum.inr 4727, 2), (Sum.inr 4749, 2), (Sum.inr 4860, 2), (Sum.inr 4862, 1), (Sum.inr 4869, 2), (Sum.inr 4871, 1), (Sum.inr 4874, 1), (Sum.inr 4898, 1), (Sum.inr 5384, 2), (Sum.inr 5389, 1), (Sum.inr 5443, 1), (Sum.inr 5449, 1)]

theorem sourceEq2256 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2256 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2256 + difference 0 1) (sourceB2256 + difference 1 0) sourceC2256) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5389) := by
    have ha : (tripleCharges (sourceA2256 + difference 0 1) (sourceB2256 + difference 1 0) sourceC2256) = raw31009 := by
      apply Matrix.ext; unfold tripleCharges sourceA2256 sourceB2256 sourceC2256 difference raw31009; decide +kernel
    rw [ha]
    exact (canonical31009 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2256 + difference 0 2) (sourceB2256 + difference 2 0) sourceC2256) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5384) := by
    have ha : (tripleCharges (sourceA2256 + difference 0 2) (sourceB2256 + difference 2 0) sourceC2256) = raw31010 := by
      apply Matrix.ext; unfold tripleCharges sourceA2256 sourceB2256 sourceC2256 difference raw31010; decide +kernel
    rw [ha]
    exact (canonical31010 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2256 + difference 0 3) (sourceB2256 + difference 3 0) sourceC2256) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5384) := by
    have ha : (tripleCharges (sourceA2256 + difference 0 3) (sourceB2256 + difference 3 0) sourceC2256) = raw31011 := by
      apply Matrix.ext; unfold tripleCharges sourceA2256 sourceB2256 sourceC2256 difference raw31011; decide +kernel
    rw [ha]
    exact (canonical31011 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2256 + difference 0 4) (sourceB2256 + difference 4 0) sourceC2256) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA2256 + difference 0 4) (sourceB2256 + difference 4 0) sourceC2256) = raw10769 := by
      apply Matrix.ext; unfold tripleCharges sourceA2256 sourceB2256 sourceC2256 difference raw10769; decide +kernel
    rw [ha]
    exact (canonical10769 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2256 + difference 0 5) (sourceB2256 + difference 5 0) sourceC2256) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5449) := by
    have ha : (tripleCharges (sourceA2256 + difference 0 5) (sourceB2256 + difference 5 0) sourceC2256) = raw19191 := by
      apply Matrix.ext; unfold tripleCharges sourceA2256 sourceB2256 sourceC2256 difference raw19191; decide +kernel
    rw [ha]
    exact (canonical19191 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2256 + difference 1 0) (sourceB2256 + difference 0 1) sourceC2256) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4278) := by
    have ha : (tripleCharges (sourceA2256 + difference 1 0) (sourceB2256 + difference 0 1) sourceC2256) = raw10789 := by
      apply Matrix.ext; unfold tripleCharges sourceA2256 sourceB2256 sourceC2256 difference raw10789; decide +kernel
    rw [ha]
    exact (canonical10789 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2256 + difference 1 2) (sourceB2256 + difference 2 1) sourceC2256) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4749) := by
    have ha : (tripleCharges (sourceA2256 + difference 1 2) (sourceB2256 + difference 2 1) sourceC2256) = raw10791 := by
      apply Matrix.ext; unfold tripleCharges sourceA2256 sourceB2256 sourceC2256 difference raw10791; decide +kernel
    rw [ha]
    exact (canonical10791 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2256 + difference 1 3) (sourceB2256 + difference 3 1) sourceC2256) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4749) := by
    have ha : (tripleCharges (sourceA2256 + difference 1 3) (sourceB2256 + difference 3 1) sourceC2256) = raw10792 := by
      apply Matrix.ext; unfold tripleCharges sourceA2256 sourceB2256 sourceC2256 difference raw10792; decide +kernel
    rw [ha]
    exact (canonical10792 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2256 + difference 1 4) (sourceB2256 + difference 4 1) sourceC2256) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4898) := by
    have ha : (tripleCharges (sourceA2256 + difference 1 4) (sourceB2256 + difference 4 1) sourceC2256) = raw31012 := by
      apply Matrix.ext; unfold tripleCharges sourceA2256 sourceB2256 sourceC2256 difference raw31012; decide +kernel
    rw [ha]
    exact (canonical31012 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2256 + difference 1 5) (sourceB2256 + difference 5 1) sourceC2256) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4874) := by
    have ha : (tripleCharges (sourceA2256 + difference 1 5) (sourceB2256 + difference 5 1) sourceC2256) = raw10793 := by
      apply Matrix.ext; unfold tripleCharges sourceA2256 sourceB2256 sourceC2256 difference raw10793; decide +kernel
    rw [ha]
    exact (canonical10793 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2256 + difference 2 0) (sourceB2256 + difference 0 2) sourceC2256) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4238) := by
    have ha : (tripleCharges (sourceA2256 + difference 2 0) (sourceB2256 + difference 0 2) sourceC2256) = raw31013 := by
      apply Matrix.ext; unfold tripleCharges sourceA2256 sourceB2256 sourceC2256 difference raw31013; decide +kernel
    rw [ha]
    exact (canonical31013 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2256 + difference 2 1) (sourceB2256 + difference 1 2) sourceC2256) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4688) := by
    have ha : (tripleCharges (sourceA2256 + difference 2 1) (sourceB2256 + difference 1 2) sourceC2256) = raw31014 := by
      apply Matrix.ext; unfold tripleCharges sourceA2256 sourceB2256 sourceC2256 difference raw31014; decide +kernel
    rw [ha]
    exact (canonical31014 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2256 + difference 2 3) (sourceB2256 + difference 3 2) sourceC2256) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4724) := by
    have ha : (tripleCharges (sourceA2256 + difference 2 3) (sourceB2256 + difference 3 2) sourceC2256) = raw31015 := by
      apply Matrix.ext; unfold tripleCharges sourceA2256 sourceB2256 sourceC2256 difference raw31015; decide +kernel
    rw [ha]
    exact (canonical31015 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2256 + difference 2 4) (sourceB2256 + difference 4 2) sourceC2256) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4869) := by
    have ha : (tripleCharges (sourceA2256 + difference 2 4) (sourceB2256 + difference 4 2) sourceC2256) = raw10780 := by
      apply Matrix.ext; unfold tripleCharges sourceA2256 sourceB2256 sourceC2256 difference raw10780; decide +kernel
    rw [ha]
    exact (canonical10780 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2256 + difference 2 5) (sourceB2256 + difference 5 2) sourceC2256) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4860) := by
    have ha : (tripleCharges (sourceA2256 + difference 2 5) (sourceB2256 + difference 5 2) sourceC2256) = raw31016 := by
      apply Matrix.ext; unfold tripleCharges sourceA2256 sourceB2256 sourceC2256 difference raw31016; decide +kernel
    rw [ha]
    exact (canonical31016 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2256 + difference 3 0) (sourceB2256 + difference 0 3) sourceC2256) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4238) := by
    have ha : (tripleCharges (sourceA2256 + difference 3 0) (sourceB2256 + difference 0 3) sourceC2256) = raw31017 := by
      apply Matrix.ext; unfold tripleCharges sourceA2256 sourceB2256 sourceC2256 difference raw31017; decide +kernel
    rw [ha]
    exact (canonical31017 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2256 + difference 3 1) (sourceB2256 + difference 1 3) sourceC2256) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4688) := by
    have ha : (tripleCharges (sourceA2256 + difference 3 1) (sourceB2256 + difference 1 3) sourceC2256) = raw31018 := by
      apply Matrix.ext; unfold tripleCharges sourceA2256 sourceB2256 sourceC2256 difference raw31018; decide +kernel
    rw [ha]
    exact (canonical31018 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2256 + difference 3 2) (sourceB2256 + difference 2 3) sourceC2256) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4724) := by
    have ha : (tripleCharges (sourceA2256 + difference 3 2) (sourceB2256 + difference 2 3) sourceC2256) = raw31019 := by
      apply Matrix.ext; unfold tripleCharges sourceA2256 sourceB2256 sourceC2256 difference raw31019; decide +kernel
    rw [ha]
    exact (canonical31019 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2256 + difference 3 4) (sourceB2256 + difference 4 3) sourceC2256) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4869) := by
    have ha : (tripleCharges (sourceA2256 + difference 3 4) (sourceB2256 + difference 4 3) sourceC2256) = raw10785 := by
      apply Matrix.ext; unfold tripleCharges sourceA2256 sourceB2256 sourceC2256 difference raw10785; decide +kernel
    rw [ha]
    exact (canonical10785 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2256 + difference 3 5) (sourceB2256 + difference 5 3) sourceC2256) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4860) := by
    have ha : (tripleCharges (sourceA2256 + difference 3 5) (sourceB2256 + difference 5 3) sourceC2256) = raw19188 := by
      apply Matrix.ext; unfold tripleCharges sourceA2256 sourceB2256 sourceC2256 difference raw19188; decide +kernel
    rw [ha]
    exact (canonical19188 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2256 + difference 4 0) (sourceB2256 + difference 0 4) sourceC2256) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4241) := by
    have ha : (tripleCharges (sourceA2256 + difference 4 0) (sourceB2256 + difference 0 4) sourceC2256) = raw31020 := by
      apply Matrix.ext; unfold tripleCharges sourceA2256 sourceB2256 sourceC2256 difference raw31020; decide +kernel
    rw [ha]
    exact (canonical31020 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2256 + difference 4 1) (sourceB2256 + difference 1 4) sourceC2256) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4691) := by
    have ha : (tripleCharges (sourceA2256 + difference 4 1) (sourceB2256 + difference 1 4) sourceC2256) = raw31021 := by
      apply Matrix.ext; unfold tripleCharges sourceA2256 sourceB2256 sourceC2256 difference raw31021; decide +kernel
    rw [ha]
    exact (canonical31021 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2256 + difference 4 2) (sourceB2256 + difference 2 4) sourceC2256) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4673) := by
    have ha : (tripleCharges (sourceA2256 + difference 4 2) (sourceB2256 + difference 2 4) sourceC2256) = raw31022 := by
      apply Matrix.ext; unfold tripleCharges sourceA2256 sourceB2256 sourceC2256 difference raw31022; decide +kernel
    rw [ha]
    exact (canonical31022 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2256 + difference 4 3) (sourceB2256 + difference 3 4) sourceC2256) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4673) := by
    have ha : (tripleCharges (sourceA2256 + difference 4 3) (sourceB2256 + difference 3 4) sourceC2256) = raw31023 := by
      apply Matrix.ext; unfold tripleCharges sourceA2256 sourceB2256 sourceC2256 difference raw31023; decide +kernel
    rw [ha]
    exact (canonical31023 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2256 + difference 4 5) (sourceB2256 + difference 5 4) sourceC2256) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4862) := by
    have ha : (tripleCharges (sourceA2256 + difference 4 5) (sourceB2256 + difference 5 4) sourceC2256) = raw31024 := by
      apply Matrix.ext; unfold tripleCharges sourceA2256 sourceB2256 sourceC2256 difference raw31024; decide +kernel
    rw [ha]
    exact (canonical31024 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2256 + difference 5 0) (sourceB2256 + difference 0 5) sourceC2256) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4243) := by
    have ha : (tripleCharges (sourceA2256 + difference 5 0) (sourceB2256 + difference 0 5) sourceC2256) = raw31025 := by
      apply Matrix.ext; unfold tripleCharges sourceA2256 sourceB2256 sourceC2256 difference raw31025; decide +kernel
    rw [ha]
    exact (canonical31025 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2256 + difference 5 1) (sourceB2256 + difference 1 5) sourceC2256) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4693) := by
    have ha : (tripleCharges (sourceA2256 + difference 5 1) (sourceB2256 + difference 1 5) sourceC2256) = raw31026 := by
      apply Matrix.ext; unfold tripleCharges sourceA2256 sourceB2256 sourceC2256 difference raw31026; decide +kernel
    rw [ha]
    exact (canonical31026 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2256 + difference 5 2) (sourceB2256 + difference 2 5) sourceC2256) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4727) := by
    have ha : (tripleCharges (sourceA2256 + difference 5 2) (sourceB2256 + difference 2 5) sourceC2256) = raw31027 := by
      apply Matrix.ext; unfold tripleCharges sourceA2256 sourceB2256 sourceC2256 difference raw31027; decide +kernel
    rw [ha]
    exact (canonical31027 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2256 + difference 5 3) (sourceB2256 + difference 3 5) sourceC2256) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4727) := by
    have ha : (tripleCharges (sourceA2256 + difference 5 3) (sourceB2256 + difference 3 5) sourceC2256) = raw31028 := by
      apply Matrix.ext; unfold tripleCharges sourceA2256 sourceB2256 sourceC2256 difference raw31028; decide +kernel
    rw [ha]
    exact (canonical31028 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2256 + difference 5 4) (sourceB2256 + difference 4 5) sourceC2256) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4871) := by
    have ha : (tripleCharges (sourceA2256 + difference 5 4) (sourceB2256 + difference 4 5) sourceC2256) = raw10795 := by
      apply Matrix.ext; unfold tripleCharges sourceA2256 sourceB2256 sourceC2256 difference raw10795; decide +kernel
    rw [ha]
    exact (canonical10795 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2256 sourceB2256 sourceC2256
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2256, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2257 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2257 : Charge := ![3, -1, 0, 0, -2, 0]
def sourceC2257 : Charge := ![0, 2, 0, 0, 0, -2]
def sourceForm2257 : Integer.Sparse Master := [(Sum.inr 738, 2), (Sum.inr 741, 1), (Sum.inr 743, 1), (Sum.inr 830, 1), (Sum.inr 1799, 2), (Sum.inr 1814, 2), (Sum.inr 1817, 1), (Sum.inr 1819, 1), (Sum.inr 1878, 2), (Sum.inr 1881, 2), (Sum.inr 1928, 2), (Sum.inr 2101, 2), (Sum.inr 2103, 1), (Sum.inr 2110, 2), (Sum.inr 2112, 1), (Sum.inr 2276, 1), (Sum.inr 2279, 1), (Sum.inr 3732, 2), (Sum.inr 3740, 1), (Sum.inr 3886, 1), (Sum.inr 3889, 1)]

theorem sourceEq2257 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2257 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2257 + difference 0 1) (sourceB2257 + difference 1 0) sourceC2257) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3740) := by
    have ha : (tripleCharges (sourceA2257 + difference 0 1) (sourceB2257 + difference 1 0) sourceC2257) = raw31029 := by
      apply Matrix.ext; unfold tripleCharges sourceA2257 sourceB2257 sourceC2257 difference raw31029; decide +kernel
    rw [ha]
    exact (canonical31029 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2257 + difference 0 2) (sourceB2257 + difference 2 0) sourceC2257) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3732) := by
    have ha : (tripleCharges (sourceA2257 + difference 0 2) (sourceB2257 + difference 2 0) sourceC2257) = raw31030 := by
      apply Matrix.ext; unfold tripleCharges sourceA2257 sourceB2257 sourceC2257 difference raw31030; decide +kernel
    rw [ha]
    exact (canonical31030 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2257 + difference 0 3) (sourceB2257 + difference 3 0) sourceC2257) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3732) := by
    have ha : (tripleCharges (sourceA2257 + difference 0 3) (sourceB2257 + difference 3 0) sourceC2257) = raw31031 := by
      apply Matrix.ext; unfold tripleCharges sourceA2257 sourceB2257 sourceC2257 difference raw31031; decide +kernel
    rw [ha]
    exact (canonical31031 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2257 + difference 0 4) (sourceB2257 + difference 4 0) sourceC2257) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3889) := by
    have ha : (tripleCharges (sourceA2257 + difference 0 4) (sourceB2257 + difference 4 0) sourceC2257) = raw31032 := by
      apply Matrix.ext; unfold tripleCharges sourceA2257 sourceB2257 sourceC2257 difference raw31032; decide +kernel
    rw [ha]
    exact (canonical31032 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2257 + difference 0 5) (sourceB2257 + difference 5 0) sourceC2257) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3886) := by
    have ha : (tripleCharges (sourceA2257 + difference 0 5) (sourceB2257 + difference 5 0) sourceC2257) = raw31033 := by
      apply Matrix.ext; unfold tripleCharges sourceA2257 sourceB2257 sourceC2257 difference raw31033; decide +kernel
    rw [ha]
    exact (canonical31033 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2257 + difference 1 0) (sourceB2257 + difference 0 1) sourceC2257) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 830) := by
    have ha : (tripleCharges (sourceA2257 + difference 1 0) (sourceB2257 + difference 0 1) sourceC2257) = raw31034 := by
      apply Matrix.ext; unfold tripleCharges sourceA2257 sourceB2257 sourceC2257 difference raw31034; decide +kernel
    rw [ha]
    exact (canonical31034 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2257 + difference 1 2) (sourceB2257 + difference 2 1) sourceC2257) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1928) := by
    have ha : (tripleCharges (sourceA2257 + difference 1 2) (sourceB2257 + difference 2 1) sourceC2257) = raw31035 := by
      apply Matrix.ext; unfold tripleCharges sourceA2257 sourceB2257 sourceC2257 difference raw31035; decide +kernel
    rw [ha]
    exact (canonical31035 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2257 + difference 1 3) (sourceB2257 + difference 3 1) sourceC2257) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1928) := by
    have ha : (tripleCharges (sourceA2257 + difference 1 3) (sourceB2257 + difference 3 1) sourceC2257) = raw31036 := by
      apply Matrix.ext; unfold tripleCharges sourceA2257 sourceB2257 sourceC2257 difference raw31036; decide +kernel
    rw [ha]
    exact (canonical31036 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2257 + difference 1 4) (sourceB2257 + difference 4 1) sourceC2257) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2279) := by
    have ha : (tripleCharges (sourceA2257 + difference 1 4) (sourceB2257 + difference 4 1) sourceC2257) = raw31037 := by
      apply Matrix.ext; unfold tripleCharges sourceA2257 sourceB2257 sourceC2257 difference raw31037; decide +kernel
    rw [ha]
    exact (canonical31037 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2257 + difference 1 5) (sourceB2257 + difference 5 1) sourceC2257) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2276) := by
    have ha : (tripleCharges (sourceA2257 + difference 1 5) (sourceB2257 + difference 5 1) sourceC2257) = raw31038 := by
      apply Matrix.ext; unfold tripleCharges sourceA2257 sourceB2257 sourceC2257 difference raw31038; decide +kernel
    rw [ha]
    exact (canonical31038 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2257 + difference 2 0) (sourceB2257 + difference 0 2) sourceC2257) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 738) := by
    have ha : (tripleCharges (sourceA2257 + difference 2 0) (sourceB2257 + difference 0 2) sourceC2257) = raw31039 := by
      apply Matrix.ext; unfold tripleCharges sourceA2257 sourceB2257 sourceC2257 difference raw31039; decide +kernel
    rw [ha]
    exact (canonical31039 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2257 + difference 2 1) (sourceB2257 + difference 1 2) sourceC2257) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1814) := by
    have ha : (tripleCharges (sourceA2257 + difference 2 1) (sourceB2257 + difference 1 2) sourceC2257) = raw31040 := by
      apply Matrix.ext; unfold tripleCharges sourceA2257 sourceB2257 sourceC2257 difference raw31040; decide +kernel
    rw [ha]
    exact (canonical31040 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2257 + difference 2 3) (sourceB2257 + difference 3 2) sourceC2257) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1878) := by
    have ha : (tripleCharges (sourceA2257 + difference 2 3) (sourceB2257 + difference 3 2) sourceC2257) = raw31041 := by
      apply Matrix.ext; unfold tripleCharges sourceA2257 sourceB2257 sourceC2257 difference raw31041; decide +kernel
    rw [ha]
    exact (canonical31041 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2257 + difference 2 4) (sourceB2257 + difference 4 2) sourceC2257) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2110) := by
    have ha : (tripleCharges (sourceA2257 + difference 2 4) (sourceB2257 + difference 4 2) sourceC2257) = raw31042 := by
      apply Matrix.ext; unfold tripleCharges sourceA2257 sourceB2257 sourceC2257 difference raw31042; decide +kernel
    rw [ha]
    exact (canonical31042 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2257 + difference 2 5) (sourceB2257 + difference 5 2) sourceC2257) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2101) := by
    have ha : (tripleCharges (sourceA2257 + difference 2 5) (sourceB2257 + difference 5 2) sourceC2257) = raw31043 := by
      apply Matrix.ext; unfold tripleCharges sourceA2257 sourceB2257 sourceC2257 difference raw31043; decide +kernel
    rw [ha]
    exact (canonical31043 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2257 + difference 3 0) (sourceB2257 + difference 0 3) sourceC2257) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 738) := by
    have ha : (tripleCharges (sourceA2257 + difference 3 0) (sourceB2257 + difference 0 3) sourceC2257) = raw31044 := by
      apply Matrix.ext; unfold tripleCharges sourceA2257 sourceB2257 sourceC2257 difference raw31044; decide +kernel
    rw [ha]
    exact (canonical31044 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2257 + difference 3 1) (sourceB2257 + difference 1 3) sourceC2257) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1814) := by
    have ha : (tripleCharges (sourceA2257 + difference 3 1) (sourceB2257 + difference 1 3) sourceC2257) = raw31045 := by
      apply Matrix.ext; unfold tripleCharges sourceA2257 sourceB2257 sourceC2257 difference raw31045; decide +kernel
    rw [ha]
    exact (canonical31045 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2257 + difference 3 2) (sourceB2257 + difference 2 3) sourceC2257) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1878) := by
    have ha : (tripleCharges (sourceA2257 + difference 3 2) (sourceB2257 + difference 2 3) sourceC2257) = raw31046 := by
      apply Matrix.ext; unfold tripleCharges sourceA2257 sourceB2257 sourceC2257 difference raw31046; decide +kernel
    rw [ha]
    exact (canonical31046 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2257 + difference 3 4) (sourceB2257 + difference 4 3) sourceC2257) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2110) := by
    have ha : (tripleCharges (sourceA2257 + difference 3 4) (sourceB2257 + difference 4 3) sourceC2257) = raw31047 := by
      apply Matrix.ext; unfold tripleCharges sourceA2257 sourceB2257 sourceC2257 difference raw31047; decide +kernel
    rw [ha]
    exact (canonical31047 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2257 + difference 3 5) (sourceB2257 + difference 5 3) sourceC2257) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2101) := by
    have ha : (tripleCharges (sourceA2257 + difference 3 5) (sourceB2257 + difference 5 3) sourceC2257) = raw31048 := by
      apply Matrix.ext; unfold tripleCharges sourceA2257 sourceB2257 sourceC2257 difference raw31048; decide +kernel
    rw [ha]
    exact (canonical31048 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2257 + difference 4 0) (sourceB2257 + difference 0 4) sourceC2257) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 741) := by
    have ha : (tripleCharges (sourceA2257 + difference 4 0) (sourceB2257 + difference 0 4) sourceC2257) = raw31049 := by
      apply Matrix.ext; unfold tripleCharges sourceA2257 sourceB2257 sourceC2257 difference raw31049; decide +kernel
    rw [ha]
    exact (canonical31049 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2257 + difference 4 1) (sourceB2257 + difference 1 4) sourceC2257) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1817) := by
    have ha : (tripleCharges (sourceA2257 + difference 4 1) (sourceB2257 + difference 1 4) sourceC2257) = raw31050 := by
      apply Matrix.ext; unfold tripleCharges sourceA2257 sourceB2257 sourceC2257 difference raw31050; decide +kernel
    rw [ha]
    exact (canonical31050 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2257 + difference 4 2) (sourceB2257 + difference 2 4) sourceC2257) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1799) := by
    have ha : (tripleCharges (sourceA2257 + difference 4 2) (sourceB2257 + difference 2 4) sourceC2257) = raw31051 := by
      apply Matrix.ext; unfold tripleCharges sourceA2257 sourceB2257 sourceC2257 difference raw31051; decide +kernel
    rw [ha]
    exact (canonical31051 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2257 + difference 4 3) (sourceB2257 + difference 3 4) sourceC2257) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1799) := by
    have ha : (tripleCharges (sourceA2257 + difference 4 3) (sourceB2257 + difference 3 4) sourceC2257) = raw31052 := by
      apply Matrix.ext; unfold tripleCharges sourceA2257 sourceB2257 sourceC2257 difference raw31052; decide +kernel
    rw [ha]
    exact (canonical31052 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2257 + difference 4 5) (sourceB2257 + difference 5 4) sourceC2257) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2103) := by
    have ha : (tripleCharges (sourceA2257 + difference 4 5) (sourceB2257 + difference 5 4) sourceC2257) = raw31053 := by
      apply Matrix.ext; unfold tripleCharges sourceA2257 sourceB2257 sourceC2257 difference raw31053; decide +kernel
    rw [ha]
    exact (canonical31053 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2257 + difference 5 0) (sourceB2257 + difference 0 5) sourceC2257) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 743) := by
    have ha : (tripleCharges (sourceA2257 + difference 5 0) (sourceB2257 + difference 0 5) sourceC2257) = raw31054 := by
      apply Matrix.ext; unfold tripleCharges sourceA2257 sourceB2257 sourceC2257 difference raw31054; decide +kernel
    rw [ha]
    exact (canonical31054 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2257 + difference 5 1) (sourceB2257 + difference 1 5) sourceC2257) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1819) := by
    have ha : (tripleCharges (sourceA2257 + difference 5 1) (sourceB2257 + difference 1 5) sourceC2257) = raw31055 := by
      apply Matrix.ext; unfold tripleCharges sourceA2257 sourceB2257 sourceC2257 difference raw31055; decide +kernel
    rw [ha]
    exact (canonical31055 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2257 + difference 5 2) (sourceB2257 + difference 2 5) sourceC2257) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1881) := by
    have ha : (tripleCharges (sourceA2257 + difference 5 2) (sourceB2257 + difference 2 5) sourceC2257) = raw31056 := by
      apply Matrix.ext; unfold tripleCharges sourceA2257 sourceB2257 sourceC2257 difference raw31056; decide +kernel
    rw [ha]
    exact (canonical31056 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2257 + difference 5 3) (sourceB2257 + difference 3 5) sourceC2257) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1881) := by
    have ha : (tripleCharges (sourceA2257 + difference 5 3) (sourceB2257 + difference 3 5) sourceC2257) = raw31057 := by
      apply Matrix.ext; unfold tripleCharges sourceA2257 sourceB2257 sourceC2257 difference raw31057; decide +kernel
    rw [ha]
    exact (canonical31057 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2257 + difference 5 4) (sourceB2257 + difference 4 5) sourceC2257) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2112) := by
    have ha : (tripleCharges (sourceA2257 + difference 5 4) (sourceB2257 + difference 4 5) sourceC2257) = raw31058 := by
      apply Matrix.ext; unfold tripleCharges sourceA2257 sourceB2257 sourceC2257 difference raw31058; decide +kernel
    rw [ha]
    exact (canonical31058 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2257 sourceB2257 sourceC2257
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2257, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2258 : Charge := ![0, 2, 0, 0, 0, -2]
def sourceB2258 : Charge := ![3, -1, 0, 0, -2, 0]
def sourceC2258 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceForm2258 : Integer.Sparse Master := [(Sum.inr 4470, 2), (Sum.inr 4472, 1), (Sum.inr 4479, 1), (Sum.inr 4491, 1), (Sum.inr 4810, 2), (Sum.inr 4812, 2), (Sum.inr 4814, 2), (Sum.inr 4820, 2), (Sum.inr 4828, 2), (Sum.inr 4845, 1), (Sum.inr 4846, 1), (Sum.inr 4855, 2), (Sum.inr 4856, 2), (Sum.inr 4873, 1), (Sum.inr 4875, 1), (Sum.inr 4883, 1), (Sum.inr 4884, 1), (Sum.inr 5176, 1), (Sum.inr 5188, 2), (Sum.inr 5206, 1), (Sum.inr 5207, 1)]

theorem sourceEq2258 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2258 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2258 + difference 0 1) (sourceB2258 + difference 1 0) sourceC2258) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5176) := by
    have ha : (tripleCharges (sourceA2258 + difference 0 1) (sourceB2258 + difference 1 0) sourceC2258) = raw29694 := by
      apply Matrix.ext; unfold tripleCharges sourceA2258 sourceB2258 sourceC2258 difference raw29694; decide +kernel
    rw [ha]
    exact (canonical29694 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2258 + difference 0 2) (sourceB2258 + difference 2 0) sourceC2258) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5188) := by
    have ha : (tripleCharges (sourceA2258 + difference 0 2) (sourceB2258 + difference 2 0) sourceC2258) = raw31059 := by
      apply Matrix.ext; unfold tripleCharges sourceA2258 sourceB2258 sourceC2258 difference raw31059; decide +kernel
    rw [ha]
    exact (canonical31059 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2258 + difference 0 3) (sourceB2258 + difference 3 0) sourceC2258) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5188) := by
    have ha : (tripleCharges (sourceA2258 + difference 0 3) (sourceB2258 + difference 3 0) sourceC2258) = raw30172 := by
      apply Matrix.ext; unfold tripleCharges sourceA2258 sourceB2258 sourceC2258 difference raw30172; decide +kernel
    rw [ha]
    exact (canonical30172 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2258 + difference 0 4) (sourceB2258 + difference 4 0) sourceC2258) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5207) := by
    have ha : (tripleCharges (sourceA2258 + difference 0 4) (sourceB2258 + difference 4 0) sourceC2258) = raw29681 := by
      apply Matrix.ext; unfold tripleCharges sourceA2258 sourceB2258 sourceC2258 difference raw29681; decide +kernel
    rw [ha]
    exact (canonical29681 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2258 + difference 0 5) (sourceB2258 + difference 5 0) sourceC2258) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5206) := by
    have ha : (tripleCharges (sourceA2258 + difference 0 5) (sourceB2258 + difference 5 0) sourceC2258) = raw31060 := by
      apply Matrix.ext; unfold tripleCharges sourceA2258 sourceB2258 sourceC2258 difference raw31060; decide +kernel
    rw [ha]
    exact (canonical31060 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2258 + difference 1 0) (sourceB2258 + difference 0 1) sourceC2258) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4479) := by
    have ha : (tripleCharges (sourceA2258 + difference 1 0) (sourceB2258 + difference 0 1) sourceC2258) = raw31061 := by
      apply Matrix.ext; unfold tripleCharges sourceA2258 sourceB2258 sourceC2258 difference raw31061; decide +kernel
    rw [ha]
    exact (canonical31061 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2258 + difference 1 2) (sourceB2258 + difference 2 1) sourceC2258) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4820) := by
    have ha : (tripleCharges (sourceA2258 + difference 1 2) (sourceB2258 + difference 2 1) sourceC2258) = raw31062 := by
      apply Matrix.ext; unfold tripleCharges sourceA2258 sourceB2258 sourceC2258 difference raw31062; decide +kernel
    rw [ha]
    exact (canonical31062 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2258 + difference 1 3) (sourceB2258 + difference 3 1) sourceC2258) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4820) := by
    have ha : (tripleCharges (sourceA2258 + difference 1 3) (sourceB2258 + difference 3 1) sourceC2258) = raw31063 := by
      apply Matrix.ext; unfold tripleCharges sourceA2258 sourceB2258 sourceC2258 difference raw31063; decide +kernel
    rw [ha]
    exact (canonical31063 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2258 + difference 1 4) (sourceB2258 + difference 4 1) sourceC2258) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4884) := by
    have ha : (tripleCharges (sourceA2258 + difference 1 4) (sourceB2258 + difference 4 1) sourceC2258) = raw31064 := by
      apply Matrix.ext; unfold tripleCharges sourceA2258 sourceB2258 sourceC2258 difference raw31064; decide +kernel
    rw [ha]
    exact (canonical31064 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2258 + difference 1 5) (sourceB2258 + difference 5 1) sourceC2258) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4883) := by
    have ha : (tripleCharges (sourceA2258 + difference 1 5) (sourceB2258 + difference 5 1) sourceC2258) = raw31065 := by
      apply Matrix.ext; unfold tripleCharges sourceA2258 sourceB2258 sourceC2258 difference raw31065; decide +kernel
    rw [ha]
    exact (canonical31065 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2258 + difference 2 0) (sourceB2258 + difference 0 2) sourceC2258) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4470) := by
    have ha : (tripleCharges (sourceA2258 + difference 2 0) (sourceB2258 + difference 0 2) sourceC2258) = raw31066 := by
      apply Matrix.ext; unfold tripleCharges sourceA2258 sourceB2258 sourceC2258 difference raw31066; decide +kernel
    rw [ha]
    exact (canonical31066 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2258 + difference 2 1) (sourceB2258 + difference 1 2) sourceC2258) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4810) := by
    have ha : (tripleCharges (sourceA2258 + difference 2 1) (sourceB2258 + difference 1 2) sourceC2258) = raw30363 := by
      apply Matrix.ext; unfold tripleCharges sourceA2258 sourceB2258 sourceC2258 difference raw30363; decide +kernel
    rw [ha]
    exact (canonical30363 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2258 + difference 2 3) (sourceB2258 + difference 3 2) sourceC2258) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4812) := by
    have ha : (tripleCharges (sourceA2258 + difference 2 3) (sourceB2258 + difference 3 2) sourceC2258) = raw31067 := by
      apply Matrix.ext; unfold tripleCharges sourceA2258 sourceB2258 sourceC2258 difference raw31067; decide +kernel
    rw [ha]
    exact (canonical31067 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2258 + difference 2 4) (sourceB2258 + difference 4 2) sourceC2258) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4856) := by
    have ha : (tripleCharges (sourceA2258 + difference 2 4) (sourceB2258 + difference 4 2) sourceC2258) = raw31068 := by
      apply Matrix.ext; unfold tripleCharges sourceA2258 sourceB2258 sourceC2258 difference raw31068; decide +kernel
    rw [ha]
    exact (canonical31068 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2258 + difference 2 5) (sourceB2258 + difference 5 2) sourceC2258) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4855) := by
    have ha : (tripleCharges (sourceA2258 + difference 2 5) (sourceB2258 + difference 5 2) sourceC2258) = raw31069 := by
      apply Matrix.ext; unfold tripleCharges sourceA2258 sourceB2258 sourceC2258 difference raw31069; decide +kernel
    rw [ha]
    exact (canonical31069 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2258 + difference 3 0) (sourceB2258 + difference 0 3) sourceC2258) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4470) := by
    have ha : (tripleCharges (sourceA2258 + difference 3 0) (sourceB2258 + difference 0 3) sourceC2258) = raw31070 := by
      apply Matrix.ext; unfold tripleCharges sourceA2258 sourceB2258 sourceC2258 difference raw31070; decide +kernel
    rw [ha]
    exact (canonical31070 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2258 + difference 3 1) (sourceB2258 + difference 1 3) sourceC2258) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4810) := by
    have ha : (tripleCharges (sourceA2258 + difference 3 1) (sourceB2258 + difference 1 3) sourceC2258) = raw31071 := by
      apply Matrix.ext; unfold tripleCharges sourceA2258 sourceB2258 sourceC2258 difference raw31071; decide +kernel
    rw [ha]
    exact (canonical31071 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2258 + difference 3 2) (sourceB2258 + difference 2 3) sourceC2258) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4812) := by
    have ha : (tripleCharges (sourceA2258 + difference 3 2) (sourceB2258 + difference 2 3) sourceC2258) = raw31072 := by
      apply Matrix.ext; unfold tripleCharges sourceA2258 sourceB2258 sourceC2258 difference raw31072; decide +kernel
    rw [ha]
    exact (canonical31072 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2258 + difference 3 4) (sourceB2258 + difference 4 3) sourceC2258) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4856) := by
    have ha : (tripleCharges (sourceA2258 + difference 3 4) (sourceB2258 + difference 4 3) sourceC2258) = raw31073 := by
      apply Matrix.ext; unfold tripleCharges sourceA2258 sourceB2258 sourceC2258 difference raw31073; decide +kernel
    rw [ha]
    exact (canonical31073 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2258 + difference 3 5) (sourceB2258 + difference 5 3) sourceC2258) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4855) := by
    have ha : (tripleCharges (sourceA2258 + difference 3 5) (sourceB2258 + difference 5 3) sourceC2258) = raw31074 := by
      apply Matrix.ext; unfold tripleCharges sourceA2258 sourceB2258 sourceC2258 difference raw31074; decide +kernel
    rw [ha]
    exact (canonical31074 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2258 + difference 4 0) (sourceB2258 + difference 0 4) sourceC2258) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4472) := by
    have ha : (tripleCharges (sourceA2258 + difference 4 0) (sourceB2258 + difference 0 4) sourceC2258) = raw31075 := by
      apply Matrix.ext; unfold tripleCharges sourceA2258 sourceB2258 sourceC2258 difference raw31075; decide +kernel
    rw [ha]
    exact (canonical31075 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2258 + difference 4 1) (sourceB2258 + difference 1 4) sourceC2258) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4845) := by
    have ha : (tripleCharges (sourceA2258 + difference 4 1) (sourceB2258 + difference 1 4) sourceC2258) = raw30687 := by
      apply Matrix.ext; unfold tripleCharges sourceA2258 sourceB2258 sourceC2258 difference raw30687; decide +kernel
    rw [ha]
    exact (canonical30687 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2258 + difference 4 2) (sourceB2258 + difference 2 4) sourceC2258) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4814) := by
    have ha : (tripleCharges (sourceA2258 + difference 4 2) (sourceB2258 + difference 2 4) sourceC2258) = raw31076 := by
      apply Matrix.ext; unfold tripleCharges sourceA2258 sourceB2258 sourceC2258 difference raw31076; decide +kernel
    rw [ha]
    exact (canonical31076 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2258 + difference 4 3) (sourceB2258 + difference 3 4) sourceC2258) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4814) := by
    have ha : (tripleCharges (sourceA2258 + difference 4 3) (sourceB2258 + difference 3 4) sourceC2258) = raw31077 := by
      apply Matrix.ext; unfold tripleCharges sourceA2258 sourceB2258 sourceC2258 difference raw31077; decide +kernel
    rw [ha]
    exact (canonical31077 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2258 + difference 4 5) (sourceB2258 + difference 5 4) sourceC2258) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4873) := by
    have ha : (tripleCharges (sourceA2258 + difference 4 5) (sourceB2258 + difference 5 4) sourceC2258) = raw31078 := by
      apply Matrix.ext; unfold tripleCharges sourceA2258 sourceB2258 sourceC2258 difference raw31078; decide +kernel
    rw [ha]
    exact (canonical31078 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2258 + difference 5 0) (sourceB2258 + difference 0 5) sourceC2258) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4491) := by
    have ha : (tripleCharges (sourceA2258 + difference 5 0) (sourceB2258 + difference 0 5) sourceC2258) = raw31079 := by
      apply Matrix.ext; unfold tripleCharges sourceA2258 sourceB2258 sourceC2258 difference raw31079; decide +kernel
    rw [ha]
    exact (canonical31079 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2258 + difference 5 1) (sourceB2258 + difference 1 5) sourceC2258) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4846) := by
    have ha : (tripleCharges (sourceA2258 + difference 5 1) (sourceB2258 + difference 1 5) sourceC2258) = raw29690 := by
      apply Matrix.ext; unfold tripleCharges sourceA2258 sourceB2258 sourceC2258 difference raw29690; decide +kernel
    rw [ha]
    exact (canonical29690 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2258 + difference 5 2) (sourceB2258 + difference 2 5) sourceC2258) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4828) := by
    have ha : (tripleCharges (sourceA2258 + difference 5 2) (sourceB2258 + difference 2 5) sourceC2258) = raw31080 := by
      apply Matrix.ext; unfold tripleCharges sourceA2258 sourceB2258 sourceC2258 difference raw31080; decide +kernel
    rw [ha]
    exact (canonical31080 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2258 + difference 5 3) (sourceB2258 + difference 3 5) sourceC2258) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4828) := by
    have ha : (tripleCharges (sourceA2258 + difference 5 3) (sourceB2258 + difference 3 5) sourceC2258) = raw30169 := by
      apply Matrix.ext; unfold tripleCharges sourceA2258 sourceB2258 sourceC2258 difference raw30169; decide +kernel
    rw [ha]
    exact (canonical30169 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2258 + difference 5 4) (sourceB2258 + difference 4 5) sourceC2258) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4875) := by
    have ha : (tripleCharges (sourceA2258 + difference 5 4) (sourceB2258 + difference 4 5) sourceC2258) = raw29678 := by
      apply Matrix.ext; unfold tripleCharges sourceA2258 sourceB2258 sourceC2258 difference raw29678; decide +kernel
    rw [ha]
    exact (canonical29678 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2258 sourceB2258 sourceC2258
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2258, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2259 : Charge := ![0, 2, 0, 0, 0, -2]
def sourceB2259 : Charge := ![3, -1, 0, 0, -2, 0]
def sourceC2259 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceForm2259 : Integer.Sparse Master := [(Sum.inr 1640, 2), (Sum.inr 1652, 1), (Sum.inr 1653, 1), (Sum.inr 1660, 1), (Sum.inr 2028, 2), (Sum.inr 2065, 1), (Sum.inr 2066, 1), (Sum.inr 2072, 2), (Sum.inr 2081, 2), (Sum.inr 2082, 2), (Sum.inr 2093, 2), (Sum.inr 2094, 2), (Sum.inr 2114, 1), (Sum.inr 2116, 1), (Sum.inr 2122, 2), (Sum.inr 2137, 1), (Sum.inr 2138, 1), (Sum.inr 2604, 1), (Sum.inr 2620, 2), (Sum.inr 2643, 1), (Sum.inr 2644, 1)]

theorem sourceEq2259 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2259 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2259 + difference 0 1) (sourceB2259 + difference 1 0) sourceC2259) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2604) := by
    have ha : (tripleCharges (sourceA2259 + difference 0 1) (sourceB2259 + difference 1 0) sourceC2259) = raw30388 := by
      apply Matrix.ext; unfold tripleCharges sourceA2259 sourceB2259 sourceC2259 difference raw30388; decide +kernel
    rw [ha]
    exact (canonical30388 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2259 + difference 0 2) (sourceB2259 + difference 2 0) sourceC2259) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2620) := by
    have ha : (tripleCharges (sourceA2259 + difference 0 2) (sourceB2259 + difference 2 0) sourceC2259) = raw31081 := by
      apply Matrix.ext; unfold tripleCharges sourceA2259 sourceB2259 sourceC2259 difference raw31081; decide +kernel
    rw [ha]
    exact (canonical31081 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2259 + difference 0 3) (sourceB2259 + difference 3 0) sourceC2259) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2620) := by
    have ha : (tripleCharges (sourceA2259 + difference 0 3) (sourceB2259 + difference 3 0) sourceC2259) = raw31082 := by
      apply Matrix.ext; unfold tripleCharges sourceA2259 sourceB2259 sourceC2259 difference raw31082; decide +kernel
    rw [ha]
    exact (canonical31082 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2259 + difference 0 4) (sourceB2259 + difference 4 0) sourceC2259) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2644) := by
    have ha : (tripleCharges (sourceA2259 + difference 0 4) (sourceB2259 + difference 4 0) sourceC2259) = raw31083 := by
      apply Matrix.ext; unfold tripleCharges sourceA2259 sourceB2259 sourceC2259 difference raw31083; decide +kernel
    rw [ha]
    exact (canonical31083 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2259 + difference 0 5) (sourceB2259 + difference 5 0) sourceC2259) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2643) := by
    have ha : (tripleCharges (sourceA2259 + difference 0 5) (sourceB2259 + difference 5 0) sourceC2259) = raw31084 := by
      apply Matrix.ext; unfold tripleCharges sourceA2259 sourceB2259 sourceC2259 difference raw31084; decide +kernel
    rw [ha]
    exact (canonical31084 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2259 + difference 1 0) (sourceB2259 + difference 0 1) sourceC2259) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1660) := by
    have ha : (tripleCharges (sourceA2259 + difference 1 0) (sourceB2259 + difference 0 1) sourceC2259) = raw31085 := by
      apply Matrix.ext; unfold tripleCharges sourceA2259 sourceB2259 sourceC2259 difference raw31085; decide +kernel
    rw [ha]
    exact (canonical31085 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2259 + difference 1 2) (sourceB2259 + difference 2 1) sourceC2259) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2122) := by
    have ha : (tripleCharges (sourceA2259 + difference 1 2) (sourceB2259 + difference 2 1) sourceC2259) = raw31086 := by
      apply Matrix.ext; unfold tripleCharges sourceA2259 sourceB2259 sourceC2259 difference raw31086; decide +kernel
    rw [ha]
    exact (canonical31086 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2259 + difference 1 3) (sourceB2259 + difference 3 1) sourceC2259) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2122) := by
    have ha : (tripleCharges (sourceA2259 + difference 1 3) (sourceB2259 + difference 3 1) sourceC2259) = raw31087 := by
      apply Matrix.ext; unfold tripleCharges sourceA2259 sourceB2259 sourceC2259 difference raw31087; decide +kernel
    rw [ha]
    exact (canonical31087 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2259 + difference 1 4) (sourceB2259 + difference 4 1) sourceC2259) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2138) := by
    have ha : (tripleCharges (sourceA2259 + difference 1 4) (sourceB2259 + difference 4 1) sourceC2259) = raw31088 := by
      apply Matrix.ext; unfold tripleCharges sourceA2259 sourceB2259 sourceC2259 difference raw31088; decide +kernel
    rw [ha]
    exact (canonical31088 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2259 + difference 1 5) (sourceB2259 + difference 5 1) sourceC2259) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2137) := by
    have ha : (tripleCharges (sourceA2259 + difference 1 5) (sourceB2259 + difference 5 1) sourceC2259) = raw31089 := by
      apply Matrix.ext; unfold tripleCharges sourceA2259 sourceB2259 sourceC2259 difference raw31089; decide +kernel
    rw [ha]
    exact (canonical31089 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2259 + difference 2 0) (sourceB2259 + difference 0 2) sourceC2259) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1640) := by
    have ha : (tripleCharges (sourceA2259 + difference 2 0) (sourceB2259 + difference 0 2) sourceC2259) = raw31090 := by
      apply Matrix.ext; unfold tripleCharges sourceA2259 sourceB2259 sourceC2259 difference raw31090; decide +kernel
    rw [ha]
    exact (canonical31090 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2259 + difference 2 1) (sourceB2259 + difference 1 2) sourceC2259) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2028) := by
    have ha : (tripleCharges (sourceA2259 + difference 2 1) (sourceB2259 + difference 1 2) sourceC2259) = raw30387 := by
      apply Matrix.ext; unfold tripleCharges sourceA2259 sourceB2259 sourceC2259 difference raw30387; decide +kernel
    rw [ha]
    exact (canonical30387 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2259 + difference 2 3) (sourceB2259 + difference 3 2) sourceC2259) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2072) := by
    have ha : (tripleCharges (sourceA2259 + difference 2 3) (sourceB2259 + difference 3 2) sourceC2259) = raw31091 := by
      apply Matrix.ext; unfold tripleCharges sourceA2259 sourceB2259 sourceC2259 difference raw31091; decide +kernel
    rw [ha]
    exact (canonical31091 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2259 + difference 2 4) (sourceB2259 + difference 4 2) sourceC2259) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2094) := by
    have ha : (tripleCharges (sourceA2259 + difference 2 4) (sourceB2259 + difference 4 2) sourceC2259) = raw31092 := by
      apply Matrix.ext; unfold tripleCharges sourceA2259 sourceB2259 sourceC2259 difference raw31092; decide +kernel
    rw [ha]
    exact (canonical31092 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2259 + difference 2 5) (sourceB2259 + difference 5 2) sourceC2259) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2093) := by
    have ha : (tripleCharges (sourceA2259 + difference 2 5) (sourceB2259 + difference 5 2) sourceC2259) = raw31093 := by
      apply Matrix.ext; unfold tripleCharges sourceA2259 sourceB2259 sourceC2259 difference raw31093; decide +kernel
    rw [ha]
    exact (canonical31093 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2259 + difference 3 0) (sourceB2259 + difference 0 3) sourceC2259) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1640) := by
    have ha : (tripleCharges (sourceA2259 + difference 3 0) (sourceB2259 + difference 0 3) sourceC2259) = raw31094 := by
      apply Matrix.ext; unfold tripleCharges sourceA2259 sourceB2259 sourceC2259 difference raw31094; decide +kernel
    rw [ha]
    exact (canonical31094 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2259 + difference 3 1) (sourceB2259 + difference 1 3) sourceC2259) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2028) := by
    have ha : (tripleCharges (sourceA2259 + difference 3 1) (sourceB2259 + difference 1 3) sourceC2259) = raw31095 := by
      apply Matrix.ext; unfold tripleCharges sourceA2259 sourceB2259 sourceC2259 difference raw31095; decide +kernel
    rw [ha]
    exact (canonical31095 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2259 + difference 3 2) (sourceB2259 + difference 2 3) sourceC2259) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2072) := by
    have ha : (tripleCharges (sourceA2259 + difference 3 2) (sourceB2259 + difference 2 3) sourceC2259) = raw31096 := by
      apply Matrix.ext; unfold tripleCharges sourceA2259 sourceB2259 sourceC2259 difference raw31096; decide +kernel
    rw [ha]
    exact (canonical31096 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2259 + difference 3 4) (sourceB2259 + difference 4 3) sourceC2259) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2094) := by
    have ha : (tripleCharges (sourceA2259 + difference 3 4) (sourceB2259 + difference 4 3) sourceC2259) = raw31097 := by
      apply Matrix.ext; unfold tripleCharges sourceA2259 sourceB2259 sourceC2259 difference raw31097; decide +kernel
    rw [ha]
    exact (canonical31097 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2259 + difference 3 5) (sourceB2259 + difference 5 3) sourceC2259) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2093) := by
    have ha : (tripleCharges (sourceA2259 + difference 3 5) (sourceB2259 + difference 5 3) sourceC2259) = raw31098 := by
      apply Matrix.ext; unfold tripleCharges sourceA2259 sourceB2259 sourceC2259 difference raw31098; decide +kernel
    rw [ha]
    exact (canonical31098 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2259 + difference 4 0) (sourceB2259 + difference 0 4) sourceC2259) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1652) := by
    have ha : (tripleCharges (sourceA2259 + difference 4 0) (sourceB2259 + difference 0 4) sourceC2259) = raw31099 := by
      apply Matrix.ext; unfold tripleCharges sourceA2259 sourceB2259 sourceC2259 difference raw31099; decide +kernel
    rw [ha]
    exact (canonical31099 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2259 + difference 4 1) (sourceB2259 + difference 1 4) sourceC2259) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2065) := by
    have ha : (tripleCharges (sourceA2259 + difference 4 1) (sourceB2259 + difference 1 4) sourceC2259) = raw31100 := by
      apply Matrix.ext; unfold tripleCharges sourceA2259 sourceB2259 sourceC2259 difference raw31100; decide +kernel
    rw [ha]
    exact (canonical31100 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2259 + difference 4 2) (sourceB2259 + difference 2 4) sourceC2259) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2081) := by
    have ha : (tripleCharges (sourceA2259 + difference 4 2) (sourceB2259 + difference 2 4) sourceC2259) = raw31101 := by
      apply Matrix.ext; unfold tripleCharges sourceA2259 sourceB2259 sourceC2259 difference raw31101; decide +kernel
    rw [ha]
    exact (canonical31101 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2259 + difference 4 3) (sourceB2259 + difference 3 4) sourceC2259) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2081) := by
    have ha : (tripleCharges (sourceA2259 + difference 4 3) (sourceB2259 + difference 3 4) sourceC2259) = raw31102 := by
      apply Matrix.ext; unfold tripleCharges sourceA2259 sourceB2259 sourceC2259 difference raw31102; decide +kernel
    rw [ha]
    exact (canonical31102 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2259 + difference 4 5) (sourceB2259 + difference 5 4) sourceC2259) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2114) := by
    have ha : (tripleCharges (sourceA2259 + difference 4 5) (sourceB2259 + difference 5 4) sourceC2259) = raw31103 := by
      apply Matrix.ext; unfold tripleCharges sourceA2259 sourceB2259 sourceC2259 difference raw31103; decide +kernel
    rw [ha]
    exact (canonical31103 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2259 + difference 5 0) (sourceB2259 + difference 0 5) sourceC2259) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1653) := by
    have ha : (tripleCharges (sourceA2259 + difference 5 0) (sourceB2259 + difference 0 5) sourceC2259) = raw31104 := by
      apply Matrix.ext; unfold tripleCharges sourceA2259 sourceB2259 sourceC2259 difference raw31104; decide +kernel
    rw [ha]
    exact (canonical31104 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2259 + difference 5 1) (sourceB2259 + difference 1 5) sourceC2259) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2066) := by
    have ha : (tripleCharges (sourceA2259 + difference 5 1) (sourceB2259 + difference 1 5) sourceC2259) = raw31105 := by
      apply Matrix.ext; unfold tripleCharges sourceA2259 sourceB2259 sourceC2259 difference raw31105; decide +kernel
    rw [ha]
    exact (canonical31105 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2259 + difference 5 2) (sourceB2259 + difference 2 5) sourceC2259) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2082) := by
    have ha : (tripleCharges (sourceA2259 + difference 5 2) (sourceB2259 + difference 2 5) sourceC2259) = raw31106 := by
      apply Matrix.ext; unfold tripleCharges sourceA2259 sourceB2259 sourceC2259 difference raw31106; decide +kernel
    rw [ha]
    exact (canonical31106 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2259 + difference 5 3) (sourceB2259 + difference 3 5) sourceC2259) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2082) := by
    have ha : (tripleCharges (sourceA2259 + difference 5 3) (sourceB2259 + difference 3 5) sourceC2259) = raw31107 := by
      apply Matrix.ext; unfold tripleCharges sourceA2259 sourceB2259 sourceC2259 difference raw31107; decide +kernel
    rw [ha]
    exact (canonical31107 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2259 + difference 5 4) (sourceB2259 + difference 4 5) sourceC2259) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2116) := by
    have ha : (tripleCharges (sourceA2259 + difference 5 4) (sourceB2259 + difference 4 5) sourceC2259) = raw31108 := by
      apply Matrix.ext; unfold tripleCharges sourceA2259 sourceB2259 sourceC2259 difference raw31108; decide +kernel
    rw [ha]
    exact (canonical31108 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2259 sourceB2259 sourceC2259
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2259, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2260 : Charge := ![0, 2, 0, 0, 0, -2]
def sourceB2260 : Charge := ![3, -1, 0, 0, -2, 0]
def sourceC2260 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceForm2260 : Integer.Sparse Master := [(Sum.inr 1371, 2), (Sum.inr 1373, 1), (Sum.inr 1374, 1), (Sum.inr 1444, 1), (Sum.inr 2867, 2), (Sum.inr 2872, 2), (Sum.inr 2887, 1), (Sum.inr 2888, 1), (Sum.inr 2889, 1), (Sum.inr 2968, 1), (Sum.inr 3095, 1), (Sum.inr 3151, 2), (Sum.inr 3159, 2), (Sum.inr 3160, 1), (Sum.inr 3161, 1), (Sum.inr 3168, 2), (Sum.inr 3174, 2), (Sum.inr 3178, 2), (Sum.inr 3188, 1), (Sum.inr 3206, 2), (Sum.inr 3216, 1)]

theorem sourceEq2260 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2260 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2260 + difference 0 1) (sourceB2260 + difference 1 0) sourceC2260) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2968) := by
    have ha : (tripleCharges (sourceA2260 + difference 0 1) (sourceB2260 + difference 1 0) sourceC2260) = raw31109 := by
      apply Matrix.ext; unfold tripleCharges sourceA2260 sourceB2260 sourceC2260 difference raw31109; decide +kernel
    rw [ha]
    exact (canonical31109 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2260 + difference 0 2) (sourceB2260 + difference 2 0) sourceC2260) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2867) := by
    have ha : (tripleCharges (sourceA2260 + difference 0 2) (sourceB2260 + difference 2 0) sourceC2260) = raw31110 := by
      apply Matrix.ext; unfold tripleCharges sourceA2260 sourceB2260 sourceC2260 difference raw31110; decide +kernel
    rw [ha]
    exact (canonical31110 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2260 + difference 0 3) (sourceB2260 + difference 3 0) sourceC2260) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2867) := by
    have ha : (tripleCharges (sourceA2260 + difference 0 3) (sourceB2260 + difference 3 0) sourceC2260) = raw31111 := by
      apply Matrix.ext; unfold tripleCharges sourceA2260 sourceB2260 sourceC2260 difference raw31111; decide +kernel
    rw [ha]
    exact (canonical31111 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2260 + difference 0 4) (sourceB2260 + difference 4 0) sourceC2260) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2889) := by
    have ha : (tripleCharges (sourceA2260 + difference 0 4) (sourceB2260 + difference 4 0) sourceC2260) = raw31112 := by
      apply Matrix.ext; unfold tripleCharges sourceA2260 sourceB2260 sourceC2260 difference raw31112; decide +kernel
    rw [ha]
    exact (canonical31112 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2260 + difference 0 5) (sourceB2260 + difference 5 0) sourceC2260) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2888) := by
    have ha : (tripleCharges (sourceA2260 + difference 0 5) (sourceB2260 + difference 5 0) sourceC2260) = raw31113 := by
      apply Matrix.ext; unfold tripleCharges sourceA2260 sourceB2260 sourceC2260 difference raw31113; decide +kernel
    rw [ha]
    exact (canonical31113 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2260 + difference 1 0) (sourceB2260 + difference 0 1) sourceC2260) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1374) := by
    have ha : (tripleCharges (sourceA2260 + difference 1 0) (sourceB2260 + difference 0 1) sourceC2260) = raw31114 := by
      apply Matrix.ext; unfold tripleCharges sourceA2260 sourceB2260 sourceC2260 difference raw31114; decide +kernel
    rw [ha]
    exact (canonical31114 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2260 + difference 1 2) (sourceB2260 + difference 2 1) sourceC2260) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3151) := by
    have ha : (tripleCharges (sourceA2260 + difference 1 2) (sourceB2260 + difference 2 1) sourceC2260) = raw31115 := by
      apply Matrix.ext; unfold tripleCharges sourceA2260 sourceB2260 sourceC2260 difference raw31115; decide +kernel
    rw [ha]
    exact (canonical31115 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2260 + difference 1 3) (sourceB2260 + difference 3 1) sourceC2260) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3151) := by
    have ha : (tripleCharges (sourceA2260 + difference 1 3) (sourceB2260 + difference 3 1) sourceC2260) = raw31116 := by
      apply Matrix.ext; unfold tripleCharges sourceA2260 sourceB2260 sourceC2260 difference raw31116; decide +kernel
    rw [ha]
    exact (canonical31116 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2260 + difference 1 4) (sourceB2260 + difference 4 1) sourceC2260) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3161) := by
    have ha : (tripleCharges (sourceA2260 + difference 1 4) (sourceB2260 + difference 4 1) sourceC2260) = raw31117 := by
      apply Matrix.ext; unfold tripleCharges sourceA2260 sourceB2260 sourceC2260 difference raw31117; decide +kernel
    rw [ha]
    exact (canonical31117 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2260 + difference 1 5) (sourceB2260 + difference 5 1) sourceC2260) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3160) := by
    have ha : (tripleCharges (sourceA2260 + difference 1 5) (sourceB2260 + difference 5 1) sourceC2260) = raw31118 := by
      apply Matrix.ext; unfold tripleCharges sourceA2260 sourceB2260 sourceC2260 difference raw31118; decide +kernel
    rw [ha]
    exact (canonical31118 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2260 + difference 2 0) (sourceB2260 + difference 0 2) sourceC2260) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1371) := by
    have ha : (tripleCharges (sourceA2260 + difference 2 0) (sourceB2260 + difference 0 2) sourceC2260) = raw31119 := by
      apply Matrix.ext; unfold tripleCharges sourceA2260 sourceB2260 sourceC2260 difference raw31119; decide +kernel
    rw [ha]
    exact (canonical31119 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2260 + difference 2 1) (sourceB2260 + difference 1 2) sourceC2260) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3206) := by
    have ha : (tripleCharges (sourceA2260 + difference 2 1) (sourceB2260 + difference 1 2) sourceC2260) = raw31120 := by
      apply Matrix.ext; unfold tripleCharges sourceA2260 sourceB2260 sourceC2260 difference raw31120; decide +kernel
    rw [ha]
    exact (canonical31120 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2260 + difference 2 3) (sourceB2260 + difference 3 2) sourceC2260) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3168) := by
    have ha : (tripleCharges (sourceA2260 + difference 2 3) (sourceB2260 + difference 3 2) sourceC2260) = raw31121 := by
      apply Matrix.ext; unfold tripleCharges sourceA2260 sourceB2260 sourceC2260 difference raw31121; decide +kernel
    rw [ha]
    exact (canonical31121 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2260 + difference 2 4) (sourceB2260 + difference 4 2) sourceC2260) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3174) := by
    have ha : (tripleCharges (sourceA2260 + difference 2 4) (sourceB2260 + difference 4 2) sourceC2260) = raw31122 := by
      apply Matrix.ext; unfold tripleCharges sourceA2260 sourceB2260 sourceC2260 difference raw31122; decide +kernel
    rw [ha]
    exact (canonical31122 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2260 + difference 2 5) (sourceB2260 + difference 5 2) sourceC2260) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3159) := by
    have ha : (tripleCharges (sourceA2260 + difference 2 5) (sourceB2260 + difference 5 2) sourceC2260) = raw31123 := by
      apply Matrix.ext; unfold tripleCharges sourceA2260 sourceB2260 sourceC2260 difference raw31123; decide +kernel
    rw [ha]
    exact (canonical31123 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2260 + difference 3 0) (sourceB2260 + difference 0 3) sourceC2260) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1371) := by
    have ha : (tripleCharges (sourceA2260 + difference 3 0) (sourceB2260 + difference 0 3) sourceC2260) = raw31124 := by
      apply Matrix.ext; unfold tripleCharges sourceA2260 sourceB2260 sourceC2260 difference raw31124; decide +kernel
    rw [ha]
    exact (canonical31124 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2260 + difference 3 1) (sourceB2260 + difference 1 3) sourceC2260) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3206) := by
    have ha : (tripleCharges (sourceA2260 + difference 3 1) (sourceB2260 + difference 1 3) sourceC2260) = raw31125 := by
      apply Matrix.ext; unfold tripleCharges sourceA2260 sourceB2260 sourceC2260 difference raw31125; decide +kernel
    rw [ha]
    exact (canonical31125 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2260 + difference 3 2) (sourceB2260 + difference 2 3) sourceC2260) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3168) := by
    have ha : (tripleCharges (sourceA2260 + difference 3 2) (sourceB2260 + difference 2 3) sourceC2260) = raw31126 := by
      apply Matrix.ext; unfold tripleCharges sourceA2260 sourceB2260 sourceC2260 difference raw31126; decide +kernel
    rw [ha]
    exact (canonical31126 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2260 + difference 3 4) (sourceB2260 + difference 4 3) sourceC2260) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3174) := by
    have ha : (tripleCharges (sourceA2260 + difference 3 4) (sourceB2260 + difference 4 3) sourceC2260) = raw31127 := by
      apply Matrix.ext; unfold tripleCharges sourceA2260 sourceB2260 sourceC2260 difference raw31127; decide +kernel
    rw [ha]
    exact (canonical31127 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2260 + difference 3 5) (sourceB2260 + difference 5 3) sourceC2260) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3159) := by
    have ha : (tripleCharges (sourceA2260 + difference 3 5) (sourceB2260 + difference 5 3) sourceC2260) = raw31128 := by
      apply Matrix.ext; unfold tripleCharges sourceA2260 sourceB2260 sourceC2260 difference raw31128; decide +kernel
    rw [ha]
    exact (canonical31128 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2260 + difference 4 0) (sourceB2260 + difference 0 4) sourceC2260) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1373) := by
    have ha : (tripleCharges (sourceA2260 + difference 4 0) (sourceB2260 + difference 0 4) sourceC2260) = raw31129 := by
      apply Matrix.ext; unfold tripleCharges sourceA2260 sourceB2260 sourceC2260 difference raw31129; decide +kernel
    rw [ha]
    exact (canonical31129 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2260 + difference 4 1) (sourceB2260 + difference 1 4) sourceC2260) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3095) := by
    have ha : (tripleCharges (sourceA2260 + difference 4 1) (sourceB2260 + difference 1 4) sourceC2260) = raw31130 := by
      apply Matrix.ext; unfold tripleCharges sourceA2260 sourceB2260 sourceC2260 difference raw31130; decide +kernel
    rw [ha]
    exact (canonical31130 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2260 + difference 4 2) (sourceB2260 + difference 2 4) sourceC2260) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2872) := by
    have ha : (tripleCharges (sourceA2260 + difference 4 2) (sourceB2260 + difference 2 4) sourceC2260) = raw31131 := by
      apply Matrix.ext; unfold tripleCharges sourceA2260 sourceB2260 sourceC2260 difference raw31131; decide +kernel
    rw [ha]
    exact (canonical31131 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2260 + difference 4 3) (sourceB2260 + difference 3 4) sourceC2260) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2872) := by
    have ha : (tripleCharges (sourceA2260 + difference 4 3) (sourceB2260 + difference 3 4) sourceC2260) = raw31132 := by
      apply Matrix.ext; unfold tripleCharges sourceA2260 sourceB2260 sourceC2260 difference raw31132; decide +kernel
    rw [ha]
    exact (canonical31132 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2260 + difference 4 5) (sourceB2260 + difference 5 4) sourceC2260) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2887) := by
    have ha : (tripleCharges (sourceA2260 + difference 4 5) (sourceB2260 + difference 5 4) sourceC2260) = raw31133 := by
      apply Matrix.ext; unfold tripleCharges sourceA2260 sourceB2260 sourceC2260 difference raw31133; decide +kernel
    rw [ha]
    exact (canonical31133 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2260 + difference 5 0) (sourceB2260 + difference 0 5) sourceC2260) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1444) := by
    have ha : (tripleCharges (sourceA2260 + difference 5 0) (sourceB2260 + difference 0 5) sourceC2260) = raw31134 := by
      apply Matrix.ext; unfold tripleCharges sourceA2260 sourceB2260 sourceC2260 difference raw31134; decide +kernel
    rw [ha]
    exact (canonical31134 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2260 + difference 5 1) (sourceB2260 + difference 1 5) sourceC2260) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3216) := by
    have ha : (tripleCharges (sourceA2260 + difference 5 1) (sourceB2260 + difference 1 5) sourceC2260) = raw31135 := by
      apply Matrix.ext; unfold tripleCharges sourceA2260 sourceB2260 sourceC2260 difference raw31135; decide +kernel
    rw [ha]
    exact (canonical31135 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2260 + difference 5 2) (sourceB2260 + difference 2 5) sourceC2260) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3178) := by
    have ha : (tripleCharges (sourceA2260 + difference 5 2) (sourceB2260 + difference 2 5) sourceC2260) = raw31136 := by
      apply Matrix.ext; unfold tripleCharges sourceA2260 sourceB2260 sourceC2260 difference raw31136; decide +kernel
    rw [ha]
    exact (canonical31136 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2260 + difference 5 3) (sourceB2260 + difference 3 5) sourceC2260) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3178) := by
    have ha : (tripleCharges (sourceA2260 + difference 5 3) (sourceB2260 + difference 3 5) sourceC2260) = raw31137 := by
      apply Matrix.ext; unfold tripleCharges sourceA2260 sourceB2260 sourceC2260 difference raw31137; decide +kernel
    rw [ha]
    exact (canonical31137 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2260 + difference 5 4) (sourceB2260 + difference 4 5) sourceC2260) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3188) := by
    have ha : (tripleCharges (sourceA2260 + difference 5 4) (sourceB2260 + difference 4 5) sourceC2260) = raw31138 := by
      apply Matrix.ext; unfold tripleCharges sourceA2260 sourceB2260 sourceC2260 difference raw31138; decide +kernel
    rw [ha]
    exact (canonical31138 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2260 sourceB2260 sourceC2260
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2260, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2261 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2261 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceC2261 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceForm2261 : Integer.Sparse Master := [(Sum.inr 4369, 2), (Sum.inr 4374, 2), (Sum.inr 4467, 1), (Sum.inr 4701, 2), (Sum.inr 4705, 2), (Sum.inr 4774, 2), (Sum.inr 4777, 4), (Sum.inr 4811, 2), (Sum.inr 4866, 4), (Sum.inr 4871, 2), (Sum.inr 4895, 2), (Sum.inr 5269, 2), (Sum.inr 5303, 1), (Sum.inr 5304, 2)]

theorem sourceEq2261 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2261 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2261 + difference 0 1) (sourceB2261 + difference 1 0) sourceC2261) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5303) := by
    have ha : (tripleCharges (sourceA2261 + difference 0 1) (sourceB2261 + difference 1 0) sourceC2261) = raw31139 := by
      apply Matrix.ext; unfold tripleCharges sourceA2261 sourceB2261 sourceC2261 difference raw31139; decide +kernel
    rw [ha]
    exact (canonical31139 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2261 + difference 0 2) (sourceB2261 + difference 2 0) sourceC2261) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5269) := by
    have ha : (tripleCharges (sourceA2261 + difference 0 2) (sourceB2261 + difference 2 0) sourceC2261) = raw31140 := by
      apply Matrix.ext; unfold tripleCharges sourceA2261 sourceB2261 sourceC2261 difference raw31140; decide +kernel
    rw [ha]
    exact (canonical31140 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2261 + difference 0 3) (sourceB2261 + difference 3 0) sourceC2261) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5269) := by
    have ha : (tripleCharges (sourceA2261 + difference 0 3) (sourceB2261 + difference 3 0) sourceC2261) = raw31141 := by
      apply Matrix.ext; unfold tripleCharges sourceA2261 sourceB2261 sourceC2261 difference raw31141; decide +kernel
    rw [ha]
    exact (canonical31141 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2261 + difference 0 4) (sourceB2261 + difference 4 0) sourceC2261) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA2261 + difference 0 4) (sourceB2261 + difference 4 0) sourceC2261) = raw11398 := by
      apply Matrix.ext; unfold tripleCharges sourceA2261 sourceB2261 sourceC2261 difference raw11398; decide +kernel
    rw [ha]
    exact (canonical11398 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2261 + difference 0 5) (sourceB2261 + difference 5 0) sourceC2261) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA2261 + difference 0 5) (sourceB2261 + difference 5 0) sourceC2261) = raw31142 := by
      apply Matrix.ext; unfold tripleCharges sourceA2261 sourceB2261 sourceC2261 difference raw31142; decide +kernel
    rw [ha]
    exact (canonical31142 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2261 + difference 1 0) (sourceB2261 + difference 0 1) sourceC2261) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4467) := by
    have ha : (tripleCharges (sourceA2261 + difference 1 0) (sourceB2261 + difference 0 1) sourceC2261) = raw11418 := by
      apply Matrix.ext; unfold tripleCharges sourceA2261 sourceB2261 sourceC2261 difference raw11418; decide +kernel
    rw [ha]
    exact (canonical11418 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2261 + difference 1 2) (sourceB2261 + difference 2 1) sourceC2261) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4811) := by
    have ha : (tripleCharges (sourceA2261 + difference 1 2) (sourceB2261 + difference 2 1) sourceC2261) = raw11420 := by
      apply Matrix.ext; unfold tripleCharges sourceA2261 sourceB2261 sourceC2261 difference raw11420; decide +kernel
    rw [ha]
    exact (canonical11420 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2261 + difference 1 3) (sourceB2261 + difference 3 1) sourceC2261) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4811) := by
    have ha : (tripleCharges (sourceA2261 + difference 1 3) (sourceB2261 + difference 3 1) sourceC2261) = raw11421 := by
      apply Matrix.ext; unfold tripleCharges sourceA2261 sourceB2261 sourceC2261 difference raw11421; decide +kernel
    rw [ha]
    exact (canonical11421 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2261 + difference 1 4) (sourceB2261 + difference 4 1) sourceC2261) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA2261 + difference 1 4) (sourceB2261 + difference 4 1) sourceC2261) = raw21144 := by
      apply Matrix.ext; unfold tripleCharges sourceA2261 sourceB2261 sourceC2261 difference raw21144; decide +kernel
    rw [ha]
    exact (canonical21144 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2261 + difference 1 5) (sourceB2261 + difference 5 1) sourceC2261) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA2261 + difference 1 5) (sourceB2261 + difference 5 1) sourceC2261) = raw11422 := by
      apply Matrix.ext; unfold tripleCharges sourceA2261 sourceB2261 sourceC2261 difference raw11422; decide +kernel
    rw [ha]
    exact (canonical11422 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2261 + difference 2 0) (sourceB2261 + difference 0 2) sourceC2261) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4369) := by
    have ha : (tripleCharges (sourceA2261 + difference 2 0) (sourceB2261 + difference 0 2) sourceC2261) = raw23154 := by
      apply Matrix.ext; unfold tripleCharges sourceA2261 sourceB2261 sourceC2261 difference raw23154; decide +kernel
    rw [ha]
    exact (canonical23154 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2261 + difference 2 1) (sourceB2261 + difference 1 2) sourceC2261) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4701) := by
    have ha : (tripleCharges (sourceA2261 + difference 2 1) (sourceB2261 + difference 1 2) sourceC2261) = raw31143 := by
      apply Matrix.ext; unfold tripleCharges sourceA2261 sourceB2261 sourceC2261 difference raw31143; decide +kernel
    rw [ha]
    exact (canonical31143 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2261 + difference 2 3) (sourceB2261 + difference 3 2) sourceC2261) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4774) := by
    have ha : (tripleCharges (sourceA2261 + difference 2 3) (sourceB2261 + difference 3 2) sourceC2261) = raw31144 := by
      apply Matrix.ext; unfold tripleCharges sourceA2261 sourceB2261 sourceC2261 difference raw31144; decide +kernel
    rw [ha]
    exact (canonical31144 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2261 + difference 2 4) (sourceB2261 + difference 4 2) sourceC2261) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA2261 + difference 2 4) (sourceB2261 + difference 4 2) sourceC2261) = raw11409 := by
      apply Matrix.ext; unfold tripleCharges sourceA2261 sourceB2261 sourceC2261 difference raw11409; decide +kernel
    rw [ha]
    exact (canonical11409 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2261 + difference 2 5) (sourceB2261 + difference 5 2) sourceC2261) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA2261 + difference 2 5) (sourceB2261 + difference 5 2) sourceC2261) = raw31145 := by
      apply Matrix.ext; unfold tripleCharges sourceA2261 sourceB2261 sourceC2261 difference raw31145; decide +kernel
    rw [ha]
    exact (canonical31145 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2261 + difference 3 0) (sourceB2261 + difference 0 3) sourceC2261) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4369) := by
    have ha : (tripleCharges (sourceA2261 + difference 3 0) (sourceB2261 + difference 0 3) sourceC2261) = raw23158 := by
      apply Matrix.ext; unfold tripleCharges sourceA2261 sourceB2261 sourceC2261 difference raw23158; decide +kernel
    rw [ha]
    exact (canonical23158 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2261 + difference 3 1) (sourceB2261 + difference 1 3) sourceC2261) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4701) := by
    have ha : (tripleCharges (sourceA2261 + difference 3 1) (sourceB2261 + difference 1 3) sourceC2261) = raw31146 := by
      apply Matrix.ext; unfold tripleCharges sourceA2261 sourceB2261 sourceC2261 difference raw31146; decide +kernel
    rw [ha]
    exact (canonical31146 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2261 + difference 3 2) (sourceB2261 + difference 2 3) sourceC2261) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4774) := by
    have ha : (tripleCharges (sourceA2261 + difference 3 2) (sourceB2261 + difference 2 3) sourceC2261) = raw31147 := by
      apply Matrix.ext; unfold tripleCharges sourceA2261 sourceB2261 sourceC2261 difference raw31147; decide +kernel
    rw [ha]
    exact (canonical31147 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2261 + difference 3 4) (sourceB2261 + difference 4 3) sourceC2261) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA2261 + difference 3 4) (sourceB2261 + difference 4 3) sourceC2261) = raw11414 := by
      apply Matrix.ext; unfold tripleCharges sourceA2261 sourceB2261 sourceC2261 difference raw11414; decide +kernel
    rw [ha]
    exact (canonical11414 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2261 + difference 3 5) (sourceB2261 + difference 5 3) sourceC2261) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA2261 + difference 3 5) (sourceB2261 + difference 5 3) sourceC2261) = raw31148 := by
      apply Matrix.ext; unfold tripleCharges sourceA2261 sourceB2261 sourceC2261 difference raw31148; decide +kernel
    rw [ha]
    exact (canonical31148 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2261 + difference 4 0) (sourceB2261 + difference 0 4) sourceC2261) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4374) := by
    have ha : (tripleCharges (sourceA2261 + difference 4 0) (sourceB2261 + difference 0 4) sourceC2261) = raw23162 := by
      apply Matrix.ext; unfold tripleCharges sourceA2261 sourceB2261 sourceC2261 difference raw23162; decide +kernel
    rw [ha]
    exact (canonical23162 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2261 + difference 4 1) (sourceB2261 + difference 1 4) sourceC2261) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4705) := by
    have ha : (tripleCharges (sourceA2261 + difference 4 1) (sourceB2261 + difference 1 4) sourceC2261) = raw31149 := by
      apply Matrix.ext; unfold tripleCharges sourceA2261 sourceB2261 sourceC2261 difference raw31149; decide +kernel
    rw [ha]
    exact (canonical31149 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2261 + difference 4 2) (sourceB2261 + difference 2 4) sourceC2261) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4777) := by
    have ha : (tripleCharges (sourceA2261 + difference 4 2) (sourceB2261 + difference 2 4) sourceC2261) = raw31150 := by
      apply Matrix.ext; unfold tripleCharges sourceA2261 sourceB2261 sourceC2261 difference raw31150; decide +kernel
    rw [ha]
    exact (canonical31150 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2261 + difference 4 3) (sourceB2261 + difference 3 4) sourceC2261) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4777) := by
    have ha : (tripleCharges (sourceA2261 + difference 4 3) (sourceB2261 + difference 3 4) sourceC2261) = raw31151 := by
      apply Matrix.ext; unfold tripleCharges sourceA2261 sourceB2261 sourceC2261 difference raw31151; decide +kernel
    rw [ha]
    exact (canonical31151 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2261 + difference 4 5) (sourceB2261 + difference 5 4) sourceC2261) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4871) := by
    have ha : (tripleCharges (sourceA2261 + difference 4 5) (sourceB2261 + difference 5 4) sourceC2261) = raw31152 := by
      apply Matrix.ext; unfold tripleCharges sourceA2261 sourceB2261 sourceC2261 difference raw31152; decide +kernel
    rw [ha]
    exact (canonical31152 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2261 + difference 5 0) (sourceB2261 + difference 0 5) sourceC2261) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4374) := by
    have ha : (tripleCharges (sourceA2261 + difference 5 0) (sourceB2261 + difference 0 5) sourceC2261) = raw21158 := by
      apply Matrix.ext; unfold tripleCharges sourceA2261 sourceB2261 sourceC2261 difference raw21158; decide +kernel
    rw [ha]
    exact (canonical21158 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2261 + difference 5 1) (sourceB2261 + difference 1 5) sourceC2261) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4705) := by
    have ha : (tripleCharges (sourceA2261 + difference 5 1) (sourceB2261 + difference 1 5) sourceC2261) = raw31153 := by
      apply Matrix.ext; unfold tripleCharges sourceA2261 sourceB2261 sourceC2261 difference raw31153; decide +kernel
    rw [ha]
    exact (canonical31153 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2261 + difference 5 2) (sourceB2261 + difference 2 5) sourceC2261) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4777) := by
    have ha : (tripleCharges (sourceA2261 + difference 5 2) (sourceB2261 + difference 2 5) sourceC2261) = raw31154 := by
      apply Matrix.ext; unfold tripleCharges sourceA2261 sourceB2261 sourceC2261 difference raw31154; decide +kernel
    rw [ha]
    exact (canonical31154 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2261 + difference 5 3) (sourceB2261 + difference 3 5) sourceC2261) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4777) := by
    have ha : (tripleCharges (sourceA2261 + difference 5 3) (sourceB2261 + difference 3 5) sourceC2261) = raw31155 := by
      apply Matrix.ext; unfold tripleCharges sourceA2261 sourceB2261 sourceC2261 difference raw31155; decide +kernel
    rw [ha]
    exact (canonical31155 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2261 + difference 5 4) (sourceB2261 + difference 4 5) sourceC2261) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4871) := by
    have ha : (tripleCharges (sourceA2261 + difference 5 4) (sourceB2261 + difference 4 5) sourceC2261) = raw11424 := by
      apply Matrix.ext; unfold tripleCharges sourceA2261 sourceB2261 sourceC2261 difference raw11424; decide +kernel
    rw [ha]
    exact (canonical11424 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2261 sourceB2261 sourceC2261
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2261, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2262 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2262 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceC2262 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceForm2262 : Integer.Sparse Master := [(Sum.inr 1322, 2), (Sum.inr 1324, 2), (Sum.inr 1420, 1), (Sum.inr 2340, 4), (Sum.inr 2346, 2), (Sum.inr 2602, 2), (Sum.inr 3108, 2), (Sum.inr 3118, 1), (Sum.inr 3119, 2), (Sum.inr 3132, 2), (Sum.inr 3164, 2), (Sum.inr 3184, 4), (Sum.inr 3207, 2), (Sum.inr 3229, 2)]

theorem sourceEq2262 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2262 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2262 + difference 0 1) (sourceB2262 + difference 1 0) sourceC2262) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3118) := by
    have ha : (tripleCharges (sourceA2262 + difference 0 1) (sourceB2262 + difference 1 0) sourceC2262) = raw31156 := by
      apply Matrix.ext; unfold tripleCharges sourceA2262 sourceB2262 sourceC2262 difference raw31156; decide +kernel
    rw [ha]
    exact (canonical31156 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2262 + difference 0 2) (sourceB2262 + difference 2 0) sourceC2262) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3108) := by
    have ha : (tripleCharges (sourceA2262 + difference 0 2) (sourceB2262 + difference 2 0) sourceC2262) = raw31157 := by
      apply Matrix.ext; unfold tripleCharges sourceA2262 sourceB2262 sourceC2262 difference raw31157; decide +kernel
    rw [ha]
    exact (canonical31157 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2262 + difference 0 3) (sourceB2262 + difference 3 0) sourceC2262) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3108) := by
    have ha : (tripleCharges (sourceA2262 + difference 0 3) (sourceB2262 + difference 3 0) sourceC2262) = raw31158 := by
      apply Matrix.ext; unfold tripleCharges sourceA2262 sourceB2262 sourceC2262 difference raw31158; decide +kernel
    rw [ha]
    exact (canonical31158 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2262 + difference 0 4) (sourceB2262 + difference 4 0) sourceC2262) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3119) := by
    have ha : (tripleCharges (sourceA2262 + difference 0 4) (sourceB2262 + difference 4 0) sourceC2262) = raw31159 := by
      apply Matrix.ext; unfold tripleCharges sourceA2262 sourceB2262 sourceC2262 difference raw31159; decide +kernel
    rw [ha]
    exact (canonical31159 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2262 + difference 0 5) (sourceB2262 + difference 5 0) sourceC2262) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3119) := by
    have ha : (tripleCharges (sourceA2262 + difference 0 5) (sourceB2262 + difference 5 0) sourceC2262) = raw31160 := by
      apply Matrix.ext; unfold tripleCharges sourceA2262 sourceB2262 sourceC2262 difference raw31160; decide +kernel
    rw [ha]
    exact (canonical31160 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2262 + difference 1 0) (sourceB2262 + difference 0 1) sourceC2262) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1420) := by
    have ha : (tripleCharges (sourceA2262 + difference 1 0) (sourceB2262 + difference 0 1) sourceC2262) = raw21190 := by
      apply Matrix.ext; unfold tripleCharges sourceA2262 sourceB2262 sourceC2262 difference raw21190; decide +kernel
    rw [ha]
    exact (canonical21190 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2262 + difference 1 2) (sourceB2262 + difference 2 1) sourceC2262) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3207) := by
    have ha : (tripleCharges (sourceA2262 + difference 1 2) (sourceB2262 + difference 2 1) sourceC2262) = raw23167 := by
      apply Matrix.ext; unfold tripleCharges sourceA2262 sourceB2262 sourceC2262 difference raw23167; decide +kernel
    rw [ha]
    exact (canonical23167 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2262 + difference 1 3) (sourceB2262 + difference 3 1) sourceC2262) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3207) := by
    have ha : (tripleCharges (sourceA2262 + difference 1 3) (sourceB2262 + difference 3 1) sourceC2262) = raw23168 := by
      apply Matrix.ext; unfold tripleCharges sourceA2262 sourceB2262 sourceC2262 difference raw23168; decide +kernel
    rw [ha]
    exact (canonical23168 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2262 + difference 1 4) (sourceB2262 + difference 4 1) sourceC2262) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3229) := by
    have ha : (tripleCharges (sourceA2262 + difference 1 4) (sourceB2262 + difference 4 1) sourceC2262) = raw21170 := by
      apply Matrix.ext; unfold tripleCharges sourceA2262 sourceB2262 sourceC2262 difference raw21170; decide +kernel
    rw [ha]
    exact (canonical21170 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2262 + difference 1 5) (sourceB2262 + difference 5 1) sourceC2262) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3229) := by
    have ha : (tripleCharges (sourceA2262 + difference 1 5) (sourceB2262 + difference 5 1) sourceC2262) = raw23169 := by
      apply Matrix.ext; unfold tripleCharges sourceA2262 sourceB2262 sourceC2262 difference raw23169; decide +kernel
    rw [ha]
    exact (canonical23169 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2262 + difference 2 0) (sourceB2262 + difference 0 2) sourceC2262) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1322) := by
    have ha : (tripleCharges (sourceA2262 + difference 2 0) (sourceB2262 + difference 0 2) sourceC2262) = raw23175 := by
      apply Matrix.ext; unfold tripleCharges sourceA2262 sourceB2262 sourceC2262 difference raw23175; decide +kernel
    rw [ha]
    exact (canonical23175 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2262 + difference 2 1) (sourceB2262 + difference 1 2) sourceC2262) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3132) := by
    have ha : (tripleCharges (sourceA2262 + difference 2 1) (sourceB2262 + difference 1 2) sourceC2262) = raw31161 := by
      apply Matrix.ext; unfold tripleCharges sourceA2262 sourceB2262 sourceC2262 difference raw31161; decide +kernel
    rw [ha]
    exact (canonical31161 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2262 + difference 2 3) (sourceB2262 + difference 3 2) sourceC2262) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3164) := by
    have ha : (tripleCharges (sourceA2262 + difference 2 3) (sourceB2262 + difference 3 2) sourceC2262) = raw31162 := by
      apply Matrix.ext; unfold tripleCharges sourceA2262 sourceB2262 sourceC2262 difference raw31162; decide +kernel
    rw [ha]
    exact (canonical31162 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2262 + difference 2 4) (sourceB2262 + difference 4 2) sourceC2262) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3184) := by
    have ha : (tripleCharges (sourceA2262 + difference 2 4) (sourceB2262 + difference 4 2) sourceC2262) = raw31163 := by
      apply Matrix.ext; unfold tripleCharges sourceA2262 sourceB2262 sourceC2262 difference raw31163; decide +kernel
    rw [ha]
    exact (canonical31163 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2262 + difference 2 5) (sourceB2262 + difference 5 2) sourceC2262) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3184) := by
    have ha : (tripleCharges (sourceA2262 + difference 2 5) (sourceB2262 + difference 5 2) sourceC2262) = raw31164 := by
      apply Matrix.ext; unfold tripleCharges sourceA2262 sourceB2262 sourceC2262 difference raw31164; decide +kernel
    rw [ha]
    exact (canonical31164 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2262 + difference 3 0) (sourceB2262 + difference 0 3) sourceC2262) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1322) := by
    have ha : (tripleCharges (sourceA2262 + difference 3 0) (sourceB2262 + difference 0 3) sourceC2262) = raw23179 := by
      apply Matrix.ext; unfold tripleCharges sourceA2262 sourceB2262 sourceC2262 difference raw23179; decide +kernel
    rw [ha]
    exact (canonical23179 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2262 + difference 3 1) (sourceB2262 + difference 1 3) sourceC2262) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3132) := by
    have ha : (tripleCharges (sourceA2262 + difference 3 1) (sourceB2262 + difference 1 3) sourceC2262) = raw31165 := by
      apply Matrix.ext; unfold tripleCharges sourceA2262 sourceB2262 sourceC2262 difference raw31165; decide +kernel
    rw [ha]
    exact (canonical31165 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2262 + difference 3 2) (sourceB2262 + difference 2 3) sourceC2262) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3164) := by
    have ha : (tripleCharges (sourceA2262 + difference 3 2) (sourceB2262 + difference 2 3) sourceC2262) = raw31166 := by
      apply Matrix.ext; unfold tripleCharges sourceA2262 sourceB2262 sourceC2262 difference raw31166; decide +kernel
    rw [ha]
    exact (canonical31166 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2262 + difference 3 4) (sourceB2262 + difference 4 3) sourceC2262) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3184) := by
    have ha : (tripleCharges (sourceA2262 + difference 3 4) (sourceB2262 + difference 4 3) sourceC2262) = raw31167 := by
      apply Matrix.ext; unfold tripleCharges sourceA2262 sourceB2262 sourceC2262 difference raw31167; decide +kernel
    rw [ha]
    exact (canonical31167 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2262 + difference 3 5) (sourceB2262 + difference 5 3) sourceC2262) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3184) := by
    have ha : (tripleCharges (sourceA2262 + difference 3 5) (sourceB2262 + difference 5 3) sourceC2262) = raw31168 := by
      apply Matrix.ext; unfold tripleCharges sourceA2262 sourceB2262 sourceC2262 difference raw31168; decide +kernel
    rw [ha]
    exact (canonical31168 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2262 + difference 4 0) (sourceB2262 + difference 0 4) sourceC2262) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1324) := by
    have ha : (tripleCharges (sourceA2262 + difference 4 0) (sourceB2262 + difference 0 4) sourceC2262) = raw23183 := by
      apply Matrix.ext; unfold tripleCharges sourceA2262 sourceB2262 sourceC2262 difference raw23183; decide +kernel
    rw [ha]
    exact (canonical23183 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2262 + difference 4 1) (sourceB2262 + difference 1 4) sourceC2262) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2346) := by
    have ha : (tripleCharges (sourceA2262 + difference 4 1) (sourceB2262 + difference 1 4) sourceC2262) = raw31169 := by
      apply Matrix.ext; unfold tripleCharges sourceA2262 sourceB2262 sourceC2262 difference raw31169; decide +kernel
    rw [ha]
    exact (canonical31169 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2262 + difference 4 2) (sourceB2262 + difference 2 4) sourceC2262) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2340) := by
    have ha : (tripleCharges (sourceA2262 + difference 4 2) (sourceB2262 + difference 2 4) sourceC2262) = raw31170 := by
      apply Matrix.ext; unfold tripleCharges sourceA2262 sourceB2262 sourceC2262 difference raw31170; decide +kernel
    rw [ha]
    exact (canonical31170 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2262 + difference 4 3) (sourceB2262 + difference 3 4) sourceC2262) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2340) := by
    have ha : (tripleCharges (sourceA2262 + difference 4 3) (sourceB2262 + difference 3 4) sourceC2262) = raw31171 := by
      apply Matrix.ext; unfold tripleCharges sourceA2262 sourceB2262 sourceC2262 difference raw31171; decide +kernel
    rw [ha]
    exact (canonical31171 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2262 + difference 4 5) (sourceB2262 + difference 5 4) sourceC2262) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2602) := by
    have ha : (tripleCharges (sourceA2262 + difference 4 5) (sourceB2262 + difference 5 4) sourceC2262) = raw31172 := by
      apply Matrix.ext; unfold tripleCharges sourceA2262 sourceB2262 sourceC2262 difference raw31172; decide +kernel
    rw [ha]
    exact (canonical31172 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2262 + difference 5 0) (sourceB2262 + difference 0 5) sourceC2262) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1324) := by
    have ha : (tripleCharges (sourceA2262 + difference 5 0) (sourceB2262 + difference 0 5) sourceC2262) = raw21187 := by
      apply Matrix.ext; unfold tripleCharges sourceA2262 sourceB2262 sourceC2262 difference raw21187; decide +kernel
    rw [ha]
    exact (canonical21187 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2262 + difference 5 1) (sourceB2262 + difference 1 5) sourceC2262) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2346) := by
    have ha : (tripleCharges (sourceA2262 + difference 5 1) (sourceB2262 + difference 1 5) sourceC2262) = raw31173 := by
      apply Matrix.ext; unfold tripleCharges sourceA2262 sourceB2262 sourceC2262 difference raw31173; decide +kernel
    rw [ha]
    exact (canonical31173 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2262 + difference 5 2) (sourceB2262 + difference 2 5) sourceC2262) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2340) := by
    have ha : (tripleCharges (sourceA2262 + difference 5 2) (sourceB2262 + difference 2 5) sourceC2262) = raw31174 := by
      apply Matrix.ext; unfold tripleCharges sourceA2262 sourceB2262 sourceC2262 difference raw31174; decide +kernel
    rw [ha]
    exact (canonical31174 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2262 + difference 5 3) (sourceB2262 + difference 3 5) sourceC2262) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2340) := by
    have ha : (tripleCharges (sourceA2262 + difference 5 3) (sourceB2262 + difference 3 5) sourceC2262) = raw31175 := by
      apply Matrix.ext; unfold tripleCharges sourceA2262 sourceB2262 sourceC2262 difference raw31175; decide +kernel
    rw [ha]
    exact (canonical31175 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2262 + difference 5 4) (sourceB2262 + difference 4 5) sourceC2262) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2602) := by
    have ha : (tripleCharges (sourceA2262 + difference 5 4) (sourceB2262 + difference 4 5) sourceC2262) = raw21166 := by
      apply Matrix.ext; unfold tripleCharges sourceA2262 sourceB2262 sourceC2262 difference raw21166; decide +kernel
    rw [ha]
    exact (canonical21166 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2262 sourceB2262 sourceC2262
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2262, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2263 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2263 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceC2263 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceForm2263 : Integer.Sparse Master := [(Sum.inr 1721, 2), (Sum.inr 1748, 2), (Sum.inr 1751, 1), (Sum.inr 2199, 2), (Sum.inr 2223, 4), (Sum.inr 2225, 2), (Sum.inr 2257, 2), (Sum.inr 2260, 4), (Sum.inr 2286, 2), (Sum.inr 2287, 2), (Sum.inr 2291, 2), (Sum.inr 2736, 2), (Sum.inr 2779, 1), (Sum.inr 2782, 2)]

theorem sourceEq2263 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2263 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2263 + difference 0 1) (sourceB2263 + difference 1 0) sourceC2263) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2779) := by
    have ha : (tripleCharges (sourceA2263 + difference 0 1) (sourceB2263 + difference 1 0) sourceC2263) = raw31176 := by
      apply Matrix.ext; unfold tripleCharges sourceA2263 sourceB2263 sourceC2263 difference raw31176; decide +kernel
    rw [ha]
    exact (canonical31176 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2263 + difference 0 2) (sourceB2263 + difference 2 0) sourceC2263) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2736) := by
    have ha : (tripleCharges (sourceA2263 + difference 0 2) (sourceB2263 + difference 2 0) sourceC2263) = raw31177 := by
      apply Matrix.ext; unfold tripleCharges sourceA2263 sourceB2263 sourceC2263 difference raw31177; decide +kernel
    rw [ha]
    exact (canonical31177 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2263 + difference 0 3) (sourceB2263 + difference 3 0) sourceC2263) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2736) := by
    have ha : (tripleCharges (sourceA2263 + difference 0 3) (sourceB2263 + difference 3 0) sourceC2263) = raw31178 := by
      apply Matrix.ext; unfold tripleCharges sourceA2263 sourceB2263 sourceC2263 difference raw31178; decide +kernel
    rw [ha]
    exact (canonical31178 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2263 + difference 0 4) (sourceB2263 + difference 4 0) sourceC2263) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2782) := by
    have ha : (tripleCharges (sourceA2263 + difference 0 4) (sourceB2263 + difference 4 0) sourceC2263) = raw11428 := by
      apply Matrix.ext; unfold tripleCharges sourceA2263 sourceB2263 sourceC2263 difference raw11428; decide +kernel
    rw [ha]
    exact (canonical11428 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2263 + difference 0 5) (sourceB2263 + difference 5 0) sourceC2263) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2782) := by
    have ha : (tripleCharges (sourceA2263 + difference 0 5) (sourceB2263 + difference 5 0) sourceC2263) = raw31179 := by
      apply Matrix.ext; unfold tripleCharges sourceA2263 sourceB2263 sourceC2263 difference raw31179; decide +kernel
    rw [ha]
    exact (canonical31179 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2263 + difference 1 0) (sourceB2263 + difference 0 1) sourceC2263) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1751) := by
    have ha : (tripleCharges (sourceA2263 + difference 1 0) (sourceB2263 + difference 0 1) sourceC2263) = raw11448 := by
      apply Matrix.ext; unfold tripleCharges sourceA2263 sourceB2263 sourceC2263 difference raw11448; decide +kernel
    rw [ha]
    exact (canonical11448 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2263 + difference 1 2) (sourceB2263 + difference 2 1) sourceC2263) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2225) := by
    have ha : (tripleCharges (sourceA2263 + difference 1 2) (sourceB2263 + difference 2 1) sourceC2263) = raw11450 := by
      apply Matrix.ext; unfold tripleCharges sourceA2263 sourceB2263 sourceC2263 difference raw11450; decide +kernel
    rw [ha]
    exact (canonical11450 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2263 + difference 1 3) (sourceB2263 + difference 3 1) sourceC2263) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2225) := by
    have ha : (tripleCharges (sourceA2263 + difference 1 3) (sourceB2263 + difference 3 1) sourceC2263) = raw11451 := by
      apply Matrix.ext; unfold tripleCharges sourceA2263 sourceB2263 sourceC2263 difference raw11451; decide +kernel
    rw [ha]
    exact (canonical11451 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2263 + difference 1 4) (sourceB2263 + difference 4 1) sourceC2263) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2291) := by
    have ha : (tripleCharges (sourceA2263 + difference 1 4) (sourceB2263 + difference 4 1) sourceC2263) = raw21196 := by
      apply Matrix.ext; unfold tripleCharges sourceA2263 sourceB2263 sourceC2263 difference raw21196; decide +kernel
    rw [ha]
    exact (canonical21196 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2263 + difference 1 5) (sourceB2263 + difference 5 1) sourceC2263) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2291) := by
    have ha : (tripleCharges (sourceA2263 + difference 1 5) (sourceB2263 + difference 5 1) sourceC2263) = raw11452 := by
      apply Matrix.ext; unfold tripleCharges sourceA2263 sourceB2263 sourceC2263 difference raw11452; decide +kernel
    rw [ha]
    exact (canonical11452 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2263 + difference 2 0) (sourceB2263 + difference 0 2) sourceC2263) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1721) := by
    have ha : (tripleCharges (sourceA2263 + difference 2 0) (sourceB2263 + difference 0 2) sourceC2263) = raw23193 := by
      apply Matrix.ext; unfold tripleCharges sourceA2263 sourceB2263 sourceC2263 difference raw23193; decide +kernel
    rw [ha]
    exact (canonical23193 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2263 + difference 2 1) (sourceB2263 + difference 1 2) sourceC2263) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2257) := by
    have ha : (tripleCharges (sourceA2263 + difference 2 1) (sourceB2263 + difference 1 2) sourceC2263) = raw31180 := by
      apply Matrix.ext; unfold tripleCharges sourceA2263 sourceB2263 sourceC2263 difference raw31180; decide +kernel
    rw [ha]
    exact (canonical31180 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2263 + difference 2 3) (sourceB2263 + difference 3 2) sourceC2263) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2199) := by
    have ha : (tripleCharges (sourceA2263 + difference 2 3) (sourceB2263 + difference 3 2) sourceC2263) = raw31181 := by
      apply Matrix.ext; unfold tripleCharges sourceA2263 sourceB2263 sourceC2263 difference raw31181; decide +kernel
    rw [ha]
    exact (canonical31181 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2263 + difference 2 4) (sourceB2263 + difference 4 2) sourceC2263) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2260) := by
    have ha : (tripleCharges (sourceA2263 + difference 2 4) (sourceB2263 + difference 4 2) sourceC2263) = raw11439 := by
      apply Matrix.ext; unfold tripleCharges sourceA2263 sourceB2263 sourceC2263 difference raw11439; decide +kernel
    rw [ha]
    exact (canonical11439 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2263 + difference 2 5) (sourceB2263 + difference 5 2) sourceC2263) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2260) := by
    have ha : (tripleCharges (sourceA2263 + difference 2 5) (sourceB2263 + difference 5 2) sourceC2263) = raw31182 := by
      apply Matrix.ext; unfold tripleCharges sourceA2263 sourceB2263 sourceC2263 difference raw31182; decide +kernel
    rw [ha]
    exact (canonical31182 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2263 + difference 3 0) (sourceB2263 + difference 0 3) sourceC2263) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1721) := by
    have ha : (tripleCharges (sourceA2263 + difference 3 0) (sourceB2263 + difference 0 3) sourceC2263) = raw23197 := by
      apply Matrix.ext; unfold tripleCharges sourceA2263 sourceB2263 sourceC2263 difference raw23197; decide +kernel
    rw [ha]
    exact (canonical23197 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2263 + difference 3 1) (sourceB2263 + difference 1 3) sourceC2263) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2257) := by
    have ha : (tripleCharges (sourceA2263 + difference 3 1) (sourceB2263 + difference 1 3) sourceC2263) = raw31183 := by
      apply Matrix.ext; unfold tripleCharges sourceA2263 sourceB2263 sourceC2263 difference raw31183; decide +kernel
    rw [ha]
    exact (canonical31183 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2263 + difference 3 2) (sourceB2263 + difference 2 3) sourceC2263) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2199) := by
    have ha : (tripleCharges (sourceA2263 + difference 3 2) (sourceB2263 + difference 2 3) sourceC2263) = raw31184 := by
      apply Matrix.ext; unfold tripleCharges sourceA2263 sourceB2263 sourceC2263 difference raw31184; decide +kernel
    rw [ha]
    exact (canonical31184 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2263 + difference 3 4) (sourceB2263 + difference 4 3) sourceC2263) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2260) := by
    have ha : (tripleCharges (sourceA2263 + difference 3 4) (sourceB2263 + difference 4 3) sourceC2263) = raw11444 := by
      apply Matrix.ext; unfold tripleCharges sourceA2263 sourceB2263 sourceC2263 difference raw11444; decide +kernel
    rw [ha]
    exact (canonical11444 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2263 + difference 3 5) (sourceB2263 + difference 5 3) sourceC2263) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2260) := by
    have ha : (tripleCharges (sourceA2263 + difference 3 5) (sourceB2263 + difference 5 3) sourceC2263) = raw31185 := by
      apply Matrix.ext; unfold tripleCharges sourceA2263 sourceB2263 sourceC2263 difference raw31185; decide +kernel
    rw [ha]
    exact (canonical31185 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2263 + difference 4 0) (sourceB2263 + difference 0 4) sourceC2263) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1748) := by
    have ha : (tripleCharges (sourceA2263 + difference 4 0) (sourceB2263 + difference 0 4) sourceC2263) = raw23201 := by
      apply Matrix.ext; unfold tripleCharges sourceA2263 sourceB2263 sourceC2263 difference raw23201; decide +kernel
    rw [ha]
    exact (canonical23201 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2263 + difference 4 1) (sourceB2263 + difference 1 4) sourceC2263) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2286) := by
    have ha : (tripleCharges (sourceA2263 + difference 4 1) (sourceB2263 + difference 1 4) sourceC2263) = raw31186 := by
      apply Matrix.ext; unfold tripleCharges sourceA2263 sourceB2263 sourceC2263 difference raw31186; decide +kernel
    rw [ha]
    exact (canonical31186 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2263 + difference 4 2) (sourceB2263 + difference 2 4) sourceC2263) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2223) := by
    have ha : (tripleCharges (sourceA2263 + difference 4 2) (sourceB2263 + difference 2 4) sourceC2263) = raw31187 := by
      apply Matrix.ext; unfold tripleCharges sourceA2263 sourceB2263 sourceC2263 difference raw31187; decide +kernel
    rw [ha]
    exact (canonical31187 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2263 + difference 4 3) (sourceB2263 + difference 3 4) sourceC2263) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2223) := by
    have ha : (tripleCharges (sourceA2263 + difference 4 3) (sourceB2263 + difference 3 4) sourceC2263) = raw31188 := by
      apply Matrix.ext; unfold tripleCharges sourceA2263 sourceB2263 sourceC2263 difference raw31188; decide +kernel
    rw [ha]
    exact (canonical31188 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2263 + difference 4 5) (sourceB2263 + difference 5 4) sourceC2263) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2287) := by
    have ha : (tripleCharges (sourceA2263 + difference 4 5) (sourceB2263 + difference 5 4) sourceC2263) = raw31189 := by
      apply Matrix.ext; unfold tripleCharges sourceA2263 sourceB2263 sourceC2263 difference raw31189; decide +kernel
    rw [ha]
    exact (canonical31189 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2263 + difference 5 0) (sourceB2263 + difference 0 5) sourceC2263) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1748) := by
    have ha : (tripleCharges (sourceA2263 + difference 5 0) (sourceB2263 + difference 0 5) sourceC2263) = raw21210 := by
      apply Matrix.ext; unfold tripleCharges sourceA2263 sourceB2263 sourceC2263 difference raw21210; decide +kernel
    rw [ha]
    exact (canonical21210 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2263 + difference 5 1) (sourceB2263 + difference 1 5) sourceC2263) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2286) := by
    have ha : (tripleCharges (sourceA2263 + difference 5 1) (sourceB2263 + difference 1 5) sourceC2263) = raw31190 := by
      apply Matrix.ext; unfold tripleCharges sourceA2263 sourceB2263 sourceC2263 difference raw31190; decide +kernel
    rw [ha]
    exact (canonical31190 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2263 + difference 5 2) (sourceB2263 + difference 2 5) sourceC2263) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2223) := by
    have ha : (tripleCharges (sourceA2263 + difference 5 2) (sourceB2263 + difference 2 5) sourceC2263) = raw31191 := by
      apply Matrix.ext; unfold tripleCharges sourceA2263 sourceB2263 sourceC2263 difference raw31191; decide +kernel
    rw [ha]
    exact (canonical31191 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2263 + difference 5 3) (sourceB2263 + difference 3 5) sourceC2263) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2223) := by
    have ha : (tripleCharges (sourceA2263 + difference 5 3) (sourceB2263 + difference 3 5) sourceC2263) = raw31192 := by
      apply Matrix.ext; unfold tripleCharges sourceA2263 sourceB2263 sourceC2263 difference raw31192; decide +kernel
    rw [ha]
    exact (canonical31192 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2263 + difference 5 4) (sourceB2263 + difference 4 5) sourceC2263) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2287) := by
    have ha : (tripleCharges (sourceA2263 + difference 5 4) (sourceB2263 + difference 4 5) sourceC2263) = raw11454 := by
      apply Matrix.ext; unfold tripleCharges sourceA2263 sourceB2263 sourceC2263 difference raw11454; decide +kernel
    rw [ha]
    exact (canonical11454 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2263 sourceB2263 sourceC2263
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2263, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2264 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2264 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceC2264 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceForm2264 : Integer.Sparse Master := [(Sum.inr 1827, 2), (Sum.inr 1831, 2), (Sum.inr 2116, 1), (Sum.inr 3118, 1), (Sum.inr 4083, -1)]

theorem sourceEq2264 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2264 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2264 + difference 0 1) (sourceB2264 + difference 1 0) sourceC2264) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3118) := by
    have ha : (tripleCharges (sourceA2264 + difference 0 1) (sourceB2264 + difference 1 0) sourceC2264) = raw31193 := by
      apply Matrix.ext; unfold tripleCharges sourceA2264 sourceB2264 sourceC2264 difference raw31193; decide +kernel
    rw [ha]
    exact (canonical31193 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2264 + difference 1 1) (sourceB2264 + difference 1 1) sourceC2264) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2116) := by
    have ha : (tripleCharges (sourceA2264 + difference 1 1) (sourceB2264 + difference 1 1) sourceC2264) = raw11462 := by
      apply Matrix.ext; unfold tripleCharges sourceA2264 sourceB2264 sourceC2264 difference raw11462; decide +kernel
    rw [ha]
    exact (canonical11462 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2264 + difference 2 1) (sourceB2264 + difference 1 2) sourceC2264) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1827) := by
    have ha : (tripleCharges (sourceA2264 + difference 2 1) (sourceB2264 + difference 1 2) sourceC2264) = raw31194 := by
      apply Matrix.ext; unfold tripleCharges sourceA2264 sourceB2264 sourceC2264 difference raw31194; decide +kernel
    rw [ha]
    exact (canonical31194 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2264 + difference 3 1) (sourceB2264 + difference 1 3) sourceC2264) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1827) := by
    have ha : (tripleCharges (sourceA2264 + difference 3 1) (sourceB2264 + difference 1 3) sourceC2264) = raw31195 := by
      apply Matrix.ext; unfold tripleCharges sourceA2264 sourceB2264 sourceC2264 difference raw31195; decide +kernel
    rw [ha]
    exact (canonical31195 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2264 + difference 4 1) (sourceB2264 + difference 1 4) sourceC2264) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1831) := by
    have ha : (tripleCharges (sourceA2264 + difference 4 1) (sourceB2264 + difference 1 4) sourceC2264) = raw31196 := by
      apply Matrix.ext; unfold tripleCharges sourceA2264 sourceB2264 sourceC2264 difference raw31196; decide +kernel
    rw [ha]
    exact (canonical31196 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2264 + difference 5 1) (sourceB2264 + difference 1 5) sourceC2264) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1831) := by
    have ha : (tripleCharges (sourceA2264 + difference 5 1) (sourceB2264 + difference 1 5) sourceC2264) = raw31197 := by
      apply Matrix.ext; unfold tripleCharges sourceA2264 sourceB2264 sourceC2264 difference raw31197; decide +kernel
    rw [ha]
    exact (canonical31197 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2264 + sourceB2264) sourceC2264) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA2264 + sourceB2264) sourceC2264) = raw11464 := by
      apply Matrix.ext; unfold doubleCharges sourceA2264 sourceB2264 sourceC2264 raw11464; decide +kernel
    rw [ha]
    exact (canonical11464 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2264 sourceB2264 sourceC2264
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2264, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2265 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2265 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceC2265 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceForm2265 : Integer.Sparse Master := [(Sum.inr 947, 1), (Sum.inr 1827, 1), (Sum.inr 1975, 1), (Sum.inr 2107, 2), (Sum.inr 2116, 1), (Sum.inr 4083, -1)]

theorem sourceEq2265 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2265 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2265 + difference 2 0) (sourceB2265 + difference 0 2) sourceC2265) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 947) := by
    have ha : (tripleCharges (sourceA2265 + difference 2 0) (sourceB2265 + difference 0 2) sourceC2265) = raw23213 := by
      apply Matrix.ext; unfold tripleCharges sourceA2265 sourceB2265 sourceC2265 difference raw23213; decide +kernel
    rw [ha]
    exact (canonical23213 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2265 + difference 2 1) (sourceB2265 + difference 1 2) sourceC2265) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1827) := by
    have ha : (tripleCharges (sourceA2265 + difference 2 1) (sourceB2265 + difference 1 2) sourceC2265) = raw31194 := by
      apply Matrix.ext; unfold tripleCharges sourceA2265 sourceB2265 sourceC2265 difference raw31194; decide +kernel
    rw [ha]
    exact (canonical31194 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2265 + difference 2 2) (sourceB2265 + difference 2 2) sourceC2265) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2116) := by
    have ha : (tripleCharges (sourceA2265 + difference 2 2) (sourceB2265 + difference 2 2) sourceC2265) = raw11462 := by
      apply Matrix.ext; unfold tripleCharges sourceA2265 sourceB2265 sourceC2265 difference raw11462; decide +kernel
    rw [ha]
    exact (canonical11462 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2265 + difference 2 3) (sourceB2265 + difference 3 2) sourceC2265) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1975) := by
    have ha : (tripleCharges (sourceA2265 + difference 2 3) (sourceB2265 + difference 3 2) sourceC2265) = raw31198 := by
      apply Matrix.ext; unfold tripleCharges sourceA2265 sourceB2265 sourceC2265 difference raw31198; decide +kernel
    rw [ha]
    exact (canonical31198 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2265 + difference 2 4) (sourceB2265 + difference 4 2) sourceC2265) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2107) := by
    have ha : (tripleCharges (sourceA2265 + difference 2 4) (sourceB2265 + difference 4 2) sourceC2265) = raw11460 := by
      apply Matrix.ext; unfold tripleCharges sourceA2265 sourceB2265 sourceC2265 difference raw11460; decide +kernel
    rw [ha]
    exact (canonical11460 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2265 + difference 2 5) (sourceB2265 + difference 5 2) sourceC2265) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2107) := by
    have ha : (tripleCharges (sourceA2265 + difference 2 5) (sourceB2265 + difference 5 2) sourceC2265) = raw31199 := by
      apply Matrix.ext; unfold tripleCharges sourceA2265 sourceB2265 sourceC2265 difference raw31199; decide +kernel
    rw [ha]
    exact (canonical31199 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2265 + sourceB2265) sourceC2265) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA2265 + sourceB2265) sourceC2265) = raw11464 := by
      apply Matrix.ext; unfold doubleCharges sourceA2265 sourceB2265 sourceC2265 raw11464; decide +kernel
    rw [ha]
    exact (canonical11464 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2265 sourceB2265 sourceC2265
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2265, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2266 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2266 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceC2266 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceForm2266 : Integer.Sparse Master := [(Sum.inr 4239, 2), (Sum.inr 4242, 2), (Sum.inr 4279, 1), (Sum.inr 4689, 2), (Sum.inr 4692, 2), (Sum.inr 4725, 2), (Sum.inr 4726, 4), (Sum.inr 4750, 2), (Sum.inr 4866, 4), (Sum.inr 4868, 2), (Sum.inr 4896, 2), (Sum.inr 5390, 1), (Sum.inr 5404, 2), (Sum.inr 5451, 2)]

theorem sourceEq2266 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2266 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2266 + difference 0 1) (sourceB2266 + difference 1 0) sourceC2266) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5390) := by
    have ha : (tripleCharges (sourceA2266 + difference 0 1) (sourceB2266 + difference 1 0) sourceC2266) = raw16293 := by
      apply Matrix.ext; unfold tripleCharges sourceA2266 sourceB2266 sourceC2266 difference raw16293; decide +kernel
    rw [ha]
    exact (canonical16293 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2266 + difference 0 2) (sourceB2266 + difference 2 0) sourceC2266) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5404) := by
    have ha : (tripleCharges (sourceA2266 + difference 0 2) (sourceB2266 + difference 2 0) sourceC2266) = raw16294 := by
      apply Matrix.ext; unfold tripleCharges sourceA2266 sourceB2266 sourceC2266 difference raw16294; decide +kernel
    rw [ha]
    exact (canonical16294 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2266 + difference 0 3) (sourceB2266 + difference 3 0) sourceC2266) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5404) := by
    have ha : (tripleCharges (sourceA2266 + difference 0 3) (sourceB2266 + difference 3 0) sourceC2266) = raw16295 := by
      apply Matrix.ext; unfold tripleCharges sourceA2266 sourceB2266 sourceC2266 difference raw16295; decide +kernel
    rw [ha]
    exact (canonical16295 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2266 + difference 0 4) (sourceB2266 + difference 4 0) sourceC2266) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA2266 + difference 0 4) (sourceB2266 + difference 4 0) sourceC2266) = raw10900 := by
      apply Matrix.ext; unfold tripleCharges sourceA2266 sourceB2266 sourceC2266 difference raw10900; decide +kernel
    rw [ha]
    exact (canonical10900 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2266 + difference 0 5) (sourceB2266 + difference 5 0) sourceC2266) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA2266 + difference 0 5) (sourceB2266 + difference 5 0) sourceC2266) = raw16296 := by
      apply Matrix.ext; unfold tripleCharges sourceA2266 sourceB2266 sourceC2266 difference raw16296; decide +kernel
    rw [ha]
    exact (canonical16296 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2266 + difference 1 0) (sourceB2266 + difference 0 1) sourceC2266) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4279) := by
    have ha : (tripleCharges (sourceA2266 + difference 1 0) (sourceB2266 + difference 0 1) sourceC2266) = raw10920 := by
      apply Matrix.ext; unfold tripleCharges sourceA2266 sourceB2266 sourceC2266 difference raw10920; decide +kernel
    rw [ha]
    exact (canonical10920 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2266 + difference 1 2) (sourceB2266 + difference 2 1) sourceC2266) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4750) := by
    have ha : (tripleCharges (sourceA2266 + difference 1 2) (sourceB2266 + difference 2 1) sourceC2266) = raw10922 := by
      apply Matrix.ext; unfold tripleCharges sourceA2266 sourceB2266 sourceC2266 difference raw10922; decide +kernel
    rw [ha]
    exact (canonical10922 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2266 + difference 1 3) (sourceB2266 + difference 3 1) sourceC2266) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4750) := by
    have ha : (tripleCharges (sourceA2266 + difference 1 3) (sourceB2266 + difference 3 1) sourceC2266) = raw10923 := by
      apply Matrix.ext; unfold tripleCharges sourceA2266 sourceB2266 sourceC2266 difference raw10923; decide +kernel
    rw [ha]
    exact (canonical10923 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2266 + difference 1 4) (sourceB2266 + difference 4 1) sourceC2266) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4896) := by
    have ha : (tripleCharges (sourceA2266 + difference 1 4) (sourceB2266 + difference 4 1) sourceC2266) = raw16284 := by
      apply Matrix.ext; unfold tripleCharges sourceA2266 sourceB2266 sourceC2266 difference raw16284; decide +kernel
    rw [ha]
    exact (canonical16284 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2266 + difference 1 5) (sourceB2266 + difference 5 1) sourceC2266) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4896) := by
    have ha : (tripleCharges (sourceA2266 + difference 1 5) (sourceB2266 + difference 5 1) sourceC2266) = raw10924 := by
      apply Matrix.ext; unfold tripleCharges sourceA2266 sourceB2266 sourceC2266 difference raw10924; decide +kernel
    rw [ha]
    exact (canonical10924 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2266 + difference 2 0) (sourceB2266 + difference 0 2) sourceC2266) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4239) := by
    have ha : (tripleCharges (sourceA2266 + difference 2 0) (sourceB2266 + difference 0 2) sourceC2266) = raw31200 := by
      apply Matrix.ext; unfold tripleCharges sourceA2266 sourceB2266 sourceC2266 difference raw31200; decide +kernel
    rw [ha]
    exact (canonical31200 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2266 + difference 2 1) (sourceB2266 + difference 1 2) sourceC2266) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4689) := by
    have ha : (tripleCharges (sourceA2266 + difference 2 1) (sourceB2266 + difference 1 2) sourceC2266) = raw31201 := by
      apply Matrix.ext; unfold tripleCharges sourceA2266 sourceB2266 sourceC2266 difference raw31201; decide +kernel
    rw [ha]
    exact (canonical31201 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2266 + difference 2 3) (sourceB2266 + difference 3 2) sourceC2266) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4725) := by
    have ha : (tripleCharges (sourceA2266 + difference 2 3) (sourceB2266 + difference 3 2) sourceC2266) = raw31202 := by
      apply Matrix.ext; unfold tripleCharges sourceA2266 sourceB2266 sourceC2266 difference raw31202; decide +kernel
    rw [ha]
    exact (canonical31202 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2266 + difference 2 4) (sourceB2266 + difference 4 2) sourceC2266) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA2266 + difference 2 4) (sourceB2266 + difference 4 2) sourceC2266) = raw10911 := by
      apply Matrix.ext; unfold tripleCharges sourceA2266 sourceB2266 sourceC2266 difference raw10911; decide +kernel
    rw [ha]
    exact (canonical10911 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2266 + difference 2 5) (sourceB2266 + difference 5 2) sourceC2266) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA2266 + difference 2 5) (sourceB2266 + difference 5 2) sourceC2266) = raw31203 := by
      apply Matrix.ext; unfold tripleCharges sourceA2266 sourceB2266 sourceC2266 difference raw31203; decide +kernel
    rw [ha]
    exact (canonical31203 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2266 + difference 3 0) (sourceB2266 + difference 0 3) sourceC2266) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4239) := by
    have ha : (tripleCharges (sourceA2266 + difference 3 0) (sourceB2266 + difference 0 3) sourceC2266) = raw31204 := by
      apply Matrix.ext; unfold tripleCharges sourceA2266 sourceB2266 sourceC2266 difference raw31204; decide +kernel
    rw [ha]
    exact (canonical31204 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2266 + difference 3 1) (sourceB2266 + difference 1 3) sourceC2266) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4689) := by
    have ha : (tripleCharges (sourceA2266 + difference 3 1) (sourceB2266 + difference 1 3) sourceC2266) = raw31205 := by
      apply Matrix.ext; unfold tripleCharges sourceA2266 sourceB2266 sourceC2266 difference raw31205; decide +kernel
    rw [ha]
    exact (canonical31205 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2266 + difference 3 2) (sourceB2266 + difference 2 3) sourceC2266) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4725) := by
    have ha : (tripleCharges (sourceA2266 + difference 3 2) (sourceB2266 + difference 2 3) sourceC2266) = raw31206 := by
      apply Matrix.ext; unfold tripleCharges sourceA2266 sourceB2266 sourceC2266 difference raw31206; decide +kernel
    rw [ha]
    exact (canonical31206 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2266 + difference 3 4) (sourceB2266 + difference 4 3) sourceC2266) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA2266 + difference 3 4) (sourceB2266 + difference 4 3) sourceC2266) = raw10916 := by
      apply Matrix.ext; unfold tripleCharges sourceA2266 sourceB2266 sourceC2266 difference raw10916; decide +kernel
    rw [ha]
    exact (canonical10916 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2266 + difference 3 5) (sourceB2266 + difference 5 3) sourceC2266) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA2266 + difference 3 5) (sourceB2266 + difference 5 3) sourceC2266) = raw31207 := by
      apply Matrix.ext; unfold tripleCharges sourceA2266 sourceB2266 sourceC2266 difference raw31207; decide +kernel
    rw [ha]
    exact (canonical31207 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2266 + difference 4 0) (sourceB2266 + difference 0 4) sourceC2266) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4242) := by
    have ha : (tripleCharges (sourceA2266 + difference 4 0) (sourceB2266 + difference 0 4) sourceC2266) = raw31208 := by
      apply Matrix.ext; unfold tripleCharges sourceA2266 sourceB2266 sourceC2266 difference raw31208; decide +kernel
    rw [ha]
    exact (canonical31208 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2266 + difference 4 1) (sourceB2266 + difference 1 4) sourceC2266) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4692) := by
    have ha : (tripleCharges (sourceA2266 + difference 4 1) (sourceB2266 + difference 1 4) sourceC2266) = raw31209 := by
      apply Matrix.ext; unfold tripleCharges sourceA2266 sourceB2266 sourceC2266 difference raw31209; decide +kernel
    rw [ha]
    exact (canonical31209 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2266 + difference 4 2) (sourceB2266 + difference 2 4) sourceC2266) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4726) := by
    have ha : (tripleCharges (sourceA2266 + difference 4 2) (sourceB2266 + difference 2 4) sourceC2266) = raw31210 := by
      apply Matrix.ext; unfold tripleCharges sourceA2266 sourceB2266 sourceC2266 difference raw31210; decide +kernel
    rw [ha]
    exact (canonical31210 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2266 + difference 4 3) (sourceB2266 + difference 3 4) sourceC2266) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4726) := by
    have ha : (tripleCharges (sourceA2266 + difference 4 3) (sourceB2266 + difference 3 4) sourceC2266) = raw31211 := by
      apply Matrix.ext; unfold tripleCharges sourceA2266 sourceB2266 sourceC2266 difference raw31211; decide +kernel
    rw [ha]
    exact (canonical31211 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2266 + difference 4 5) (sourceB2266 + difference 5 4) sourceC2266) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4868) := by
    have ha : (tripleCharges (sourceA2266 + difference 4 5) (sourceB2266 + difference 5 4) sourceC2266) = raw31212 := by
      apply Matrix.ext; unfold tripleCharges sourceA2266 sourceB2266 sourceC2266 difference raw31212; decide +kernel
    rw [ha]
    exact (canonical31212 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2266 + difference 5 0) (sourceB2266 + difference 0 5) sourceC2266) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4242) := by
    have ha : (tripleCharges (sourceA2266 + difference 5 0) (sourceB2266 + difference 0 5) sourceC2266) = raw31213 := by
      apply Matrix.ext; unfold tripleCharges sourceA2266 sourceB2266 sourceC2266 difference raw31213; decide +kernel
    rw [ha]
    exact (canonical31213 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2266 + difference 5 1) (sourceB2266 + difference 1 5) sourceC2266) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4692) := by
    have ha : (tripleCharges (sourceA2266 + difference 5 1) (sourceB2266 + difference 1 5) sourceC2266) = raw31214 := by
      apply Matrix.ext; unfold tripleCharges sourceA2266 sourceB2266 sourceC2266 difference raw31214; decide +kernel
    rw [ha]
    exact (canonical31214 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2266 + difference 5 2) (sourceB2266 + difference 2 5) sourceC2266) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4726) := by
    have ha : (tripleCharges (sourceA2266 + difference 5 2) (sourceB2266 + difference 2 5) sourceC2266) = raw31215 := by
      apply Matrix.ext; unfold tripleCharges sourceA2266 sourceB2266 sourceC2266 difference raw31215; decide +kernel
    rw [ha]
    exact (canonical31215 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2266 + difference 5 3) (sourceB2266 + difference 3 5) sourceC2266) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4726) := by
    have ha : (tripleCharges (sourceA2266 + difference 5 3) (sourceB2266 + difference 3 5) sourceC2266) = raw31216 := by
      apply Matrix.ext; unfold tripleCharges sourceA2266 sourceB2266 sourceC2266 difference raw31216; decide +kernel
    rw [ha]
    exact (canonical31216 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2266 + difference 5 4) (sourceB2266 + difference 4 5) sourceC2266) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4868) := by
    have ha : (tripleCharges (sourceA2266 + difference 5 4) (sourceB2266 + difference 4 5) sourceC2266) = raw10926 := by
      apply Matrix.ext; unfold tripleCharges sourceA2266 sourceB2266 sourceC2266 difference raw10926; decide +kernel
    rw [ha]
    exact (canonical10926 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2266 sourceB2266 sourceC2266
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2266, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2267 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2267 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceC2267 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceForm2267 : Integer.Sparse Master := [(Sum.inr 739, 2), (Sum.inr 742, 2), (Sum.inr 831, 1), (Sum.inr 1815, 2), (Sum.inr 1818, 2), (Sum.inr 1879, 2), (Sum.inr 1880, 4), (Sum.inr 1929, 2), (Sum.inr 2107, 4), (Sum.inr 2109, 2), (Sum.inr 2278, 2), (Sum.inr 3741, 1), (Sum.inr 3790, 2), (Sum.inr 3888, 2)]

theorem sourceEq2267 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2267 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2267 + difference 0 1) (sourceB2267 + difference 1 0) sourceC2267) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3741) := by
    have ha : (tripleCharges (sourceA2267 + difference 0 1) (sourceB2267 + difference 1 0) sourceC2267) = raw16315 := by
      apply Matrix.ext; unfold tripleCharges sourceA2267 sourceB2267 sourceC2267 difference raw16315; decide +kernel
    rw [ha]
    exact (canonical16315 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2267 + difference 0 2) (sourceB2267 + difference 2 0) sourceC2267) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3790) := by
    have ha : (tripleCharges (sourceA2267 + difference 0 2) (sourceB2267 + difference 2 0) sourceC2267) = raw16316 := by
      apply Matrix.ext; unfold tripleCharges sourceA2267 sourceB2267 sourceC2267 difference raw16316; decide +kernel
    rw [ha]
    exact (canonical16316 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2267 + difference 0 3) (sourceB2267 + difference 3 0) sourceC2267) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3790) := by
    have ha : (tripleCharges (sourceA2267 + difference 0 3) (sourceB2267 + difference 3 0) sourceC2267) = raw16317 := by
      apply Matrix.ext; unfold tripleCharges sourceA2267 sourceB2267 sourceC2267 difference raw16317; decide +kernel
    rw [ha]
    exact (canonical16317 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2267 + difference 0 4) (sourceB2267 + difference 4 0) sourceC2267) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3888) := by
    have ha : (tripleCharges (sourceA2267 + difference 0 4) (sourceB2267 + difference 4 0) sourceC2267) = raw10930 := by
      apply Matrix.ext; unfold tripleCharges sourceA2267 sourceB2267 sourceC2267 difference raw10930; decide +kernel
    rw [ha]
    exact (canonical10930 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2267 + difference 0 5) (sourceB2267 + difference 5 0) sourceC2267) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3888) := by
    have ha : (tripleCharges (sourceA2267 + difference 0 5) (sourceB2267 + difference 5 0) sourceC2267) = raw16318 := by
      apply Matrix.ext; unfold tripleCharges sourceA2267 sourceB2267 sourceC2267 difference raw16318; decide +kernel
    rw [ha]
    exact (canonical16318 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2267 + difference 1 0) (sourceB2267 + difference 0 1) sourceC2267) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 831) := by
    have ha : (tripleCharges (sourceA2267 + difference 1 0) (sourceB2267 + difference 0 1) sourceC2267) = raw10950 := by
      apply Matrix.ext; unfold tripleCharges sourceA2267 sourceB2267 sourceC2267 difference raw10950; decide +kernel
    rw [ha]
    exact (canonical10950 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2267 + difference 1 2) (sourceB2267 + difference 2 1) sourceC2267) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1929) := by
    have ha : (tripleCharges (sourceA2267 + difference 1 2) (sourceB2267 + difference 2 1) sourceC2267) = raw10952 := by
      apply Matrix.ext; unfold tripleCharges sourceA2267 sourceB2267 sourceC2267 difference raw10952; decide +kernel
    rw [ha]
    exact (canonical10952 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2267 + difference 1 3) (sourceB2267 + difference 3 1) sourceC2267) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1929) := by
    have ha : (tripleCharges (sourceA2267 + difference 1 3) (sourceB2267 + difference 3 1) sourceC2267) = raw10953 := by
      apply Matrix.ext; unfold tripleCharges sourceA2267 sourceB2267 sourceC2267 difference raw10953; decide +kernel
    rw [ha]
    exact (canonical10953 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2267 + difference 1 4) (sourceB2267 + difference 4 1) sourceC2267) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2278) := by
    have ha : (tripleCharges (sourceA2267 + difference 1 4) (sourceB2267 + difference 4 1) sourceC2267) = raw16306 := by
      apply Matrix.ext; unfold tripleCharges sourceA2267 sourceB2267 sourceC2267 difference raw16306; decide +kernel
    rw [ha]
    exact (canonical16306 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2267 + difference 1 5) (sourceB2267 + difference 5 1) sourceC2267) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2278) := by
    have ha : (tripleCharges (sourceA2267 + difference 1 5) (sourceB2267 + difference 5 1) sourceC2267) = raw10954 := by
      apply Matrix.ext; unfold tripleCharges sourceA2267 sourceB2267 sourceC2267 difference raw10954; decide +kernel
    rw [ha]
    exact (canonical10954 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2267 + difference 2 0) (sourceB2267 + difference 0 2) sourceC2267) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 739) := by
    have ha : (tripleCharges (sourceA2267 + difference 2 0) (sourceB2267 + difference 0 2) sourceC2267) = raw31217 := by
      apply Matrix.ext; unfold tripleCharges sourceA2267 sourceB2267 sourceC2267 difference raw31217; decide +kernel
    rw [ha]
    exact (canonical31217 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2267 + difference 2 1) (sourceB2267 + difference 1 2) sourceC2267) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1815) := by
    have ha : (tripleCharges (sourceA2267 + difference 2 1) (sourceB2267 + difference 1 2) sourceC2267) = raw31218 := by
      apply Matrix.ext; unfold tripleCharges sourceA2267 sourceB2267 sourceC2267 difference raw31218; decide +kernel
    rw [ha]
    exact (canonical31218 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2267 + difference 2 3) (sourceB2267 + difference 3 2) sourceC2267) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1879) := by
    have ha : (tripleCharges (sourceA2267 + difference 2 3) (sourceB2267 + difference 3 2) sourceC2267) = raw31219 := by
      apply Matrix.ext; unfold tripleCharges sourceA2267 sourceB2267 sourceC2267 difference raw31219; decide +kernel
    rw [ha]
    exact (canonical31219 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2267 + difference 2 4) (sourceB2267 + difference 4 2) sourceC2267) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2107) := by
    have ha : (tripleCharges (sourceA2267 + difference 2 4) (sourceB2267 + difference 4 2) sourceC2267) = raw10941 := by
      apply Matrix.ext; unfold tripleCharges sourceA2267 sourceB2267 sourceC2267 difference raw10941; decide +kernel
    rw [ha]
    exact (canonical10941 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2267 + difference 2 5) (sourceB2267 + difference 5 2) sourceC2267) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2107) := by
    have ha : (tripleCharges (sourceA2267 + difference 2 5) (sourceB2267 + difference 5 2) sourceC2267) = raw31220 := by
      apply Matrix.ext; unfold tripleCharges sourceA2267 sourceB2267 sourceC2267 difference raw31220; decide +kernel
    rw [ha]
    exact (canonical31220 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2267 + difference 3 0) (sourceB2267 + difference 0 3) sourceC2267) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 739) := by
    have ha : (tripleCharges (sourceA2267 + difference 3 0) (sourceB2267 + difference 0 3) sourceC2267) = raw31221 := by
      apply Matrix.ext; unfold tripleCharges sourceA2267 sourceB2267 sourceC2267 difference raw31221; decide +kernel
    rw [ha]
    exact (canonical31221 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2267 + difference 3 1) (sourceB2267 + difference 1 3) sourceC2267) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1815) := by
    have ha : (tripleCharges (sourceA2267 + difference 3 1) (sourceB2267 + difference 1 3) sourceC2267) = raw31222 := by
      apply Matrix.ext; unfold tripleCharges sourceA2267 sourceB2267 sourceC2267 difference raw31222; decide +kernel
    rw [ha]
    exact (canonical31222 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2267 + difference 3 2) (sourceB2267 + difference 2 3) sourceC2267) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1879) := by
    have ha : (tripleCharges (sourceA2267 + difference 3 2) (sourceB2267 + difference 2 3) sourceC2267) = raw31223 := by
      apply Matrix.ext; unfold tripleCharges sourceA2267 sourceB2267 sourceC2267 difference raw31223; decide +kernel
    rw [ha]
    exact (canonical31223 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2267 + difference 3 4) (sourceB2267 + difference 4 3) sourceC2267) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2107) := by
    have ha : (tripleCharges (sourceA2267 + difference 3 4) (sourceB2267 + difference 4 3) sourceC2267) = raw10946 := by
      apply Matrix.ext; unfold tripleCharges sourceA2267 sourceB2267 sourceC2267 difference raw10946; decide +kernel
    rw [ha]
    exact (canonical10946 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2267 + difference 3 5) (sourceB2267 + difference 5 3) sourceC2267) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2107) := by
    have ha : (tripleCharges (sourceA2267 + difference 3 5) (sourceB2267 + difference 5 3) sourceC2267) = raw31224 := by
      apply Matrix.ext; unfold tripleCharges sourceA2267 sourceB2267 sourceC2267 difference raw31224; decide +kernel
    rw [ha]
    exact (canonical31224 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2267 + difference 4 0) (sourceB2267 + difference 0 4) sourceC2267) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 742) := by
    have ha : (tripleCharges (sourceA2267 + difference 4 0) (sourceB2267 + difference 0 4) sourceC2267) = raw31225 := by
      apply Matrix.ext; unfold tripleCharges sourceA2267 sourceB2267 sourceC2267 difference raw31225; decide +kernel
    rw [ha]
    exact (canonical31225 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2267 + difference 4 1) (sourceB2267 + difference 1 4) sourceC2267) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1818) := by
    have ha : (tripleCharges (sourceA2267 + difference 4 1) (sourceB2267 + difference 1 4) sourceC2267) = raw31226 := by
      apply Matrix.ext; unfold tripleCharges sourceA2267 sourceB2267 sourceC2267 difference raw31226; decide +kernel
    rw [ha]
    exact (canonical31226 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2267 + difference 4 2) (sourceB2267 + difference 2 4) sourceC2267) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1880) := by
    have ha : (tripleCharges (sourceA2267 + difference 4 2) (sourceB2267 + difference 2 4) sourceC2267) = raw31227 := by
      apply Matrix.ext; unfold tripleCharges sourceA2267 sourceB2267 sourceC2267 difference raw31227; decide +kernel
    rw [ha]
    exact (canonical31227 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2267 + difference 4 3) (sourceB2267 + difference 3 4) sourceC2267) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1880) := by
    have ha : (tripleCharges (sourceA2267 + difference 4 3) (sourceB2267 + difference 3 4) sourceC2267) = raw31228 := by
      apply Matrix.ext; unfold tripleCharges sourceA2267 sourceB2267 sourceC2267 difference raw31228; decide +kernel
    rw [ha]
    exact (canonical31228 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2267 + difference 4 5) (sourceB2267 + difference 5 4) sourceC2267) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2109) := by
    have ha : (tripleCharges (sourceA2267 + difference 4 5) (sourceB2267 + difference 5 4) sourceC2267) = raw31229 := by
      apply Matrix.ext; unfold tripleCharges sourceA2267 sourceB2267 sourceC2267 difference raw31229; decide +kernel
    rw [ha]
    exact (canonical31229 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2267 + difference 5 0) (sourceB2267 + difference 0 5) sourceC2267) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 742) := by
    have ha : (tripleCharges (sourceA2267 + difference 5 0) (sourceB2267 + difference 0 5) sourceC2267) = raw31230 := by
      apply Matrix.ext; unfold tripleCharges sourceA2267 sourceB2267 sourceC2267 difference raw31230; decide +kernel
    rw [ha]
    exact (canonical31230 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2267 + difference 5 1) (sourceB2267 + difference 1 5) sourceC2267) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1818) := by
    have ha : (tripleCharges (sourceA2267 + difference 5 1) (sourceB2267 + difference 1 5) sourceC2267) = raw31231 := by
      apply Matrix.ext; unfold tripleCharges sourceA2267 sourceB2267 sourceC2267 difference raw31231; decide +kernel
    rw [ha]
    exact (canonical31231 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2267 + difference 5 2) (sourceB2267 + difference 2 5) sourceC2267) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1880) := by
    have ha : (tripleCharges (sourceA2267 + difference 5 2) (sourceB2267 + difference 2 5) sourceC2267) = raw31232 := by
      apply Matrix.ext; unfold tripleCharges sourceA2267 sourceB2267 sourceC2267 difference raw31232; decide +kernel
    rw [ha]
    exact (canonical31232 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2267 + difference 5 3) (sourceB2267 + difference 3 5) sourceC2267) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1880) := by
    have ha : (tripleCharges (sourceA2267 + difference 5 3) (sourceB2267 + difference 3 5) sourceC2267) = raw31233 := by
      apply Matrix.ext; unfold tripleCharges sourceA2267 sourceB2267 sourceC2267 difference raw31233; decide +kernel
    rw [ha]
    exact (canonical31233 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2267 + difference 5 4) (sourceB2267 + difference 4 5) sourceC2267) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2109) := by
    have ha : (tripleCharges (sourceA2267 + difference 5 4) (sourceB2267 + difference 4 5) sourceC2267) = raw10956 := by
      apply Matrix.ext; unfold tripleCharges sourceA2267 sourceB2267 sourceC2267 difference raw10956; decide +kernel
    rw [ha]
    exact (canonical10956 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2267 sourceB2267 sourceC2267
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2267, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2268 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceB2268 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceC2268 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceForm2268 : Integer.Sparse Master := [(Sum.inr 4487, 2), (Sum.inr 4491, 2), (Sum.inr 4506, 1), (Sum.inr 4811, 2), (Sum.inr 4825, 2), (Sum.inr 4828, 4), (Sum.inr 4842, 2), (Sum.inr 4846, 2), (Sum.inr 4856, 4), (Sum.inr 4874, 2), (Sum.inr 4884, 2), (Sum.inr 5177, 1), (Sum.inr 5189, 2), (Sum.inr 5207, 2)]

theorem sourceEq2268 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2268 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2268 + difference 0 1) (sourceB2268 + difference 1 0) sourceC2268) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5177) := by
    have ha : (tripleCharges (sourceA2268 + difference 0 1) (sourceB2268 + difference 1 0) sourceC2268) = raw29586 := by
      apply Matrix.ext; unfold tripleCharges sourceA2268 sourceB2268 sourceC2268 difference raw29586; decide +kernel
    rw [ha]
    exact (canonical29586 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2268 + difference 0 2) (sourceB2268 + difference 2 0) sourceC2268) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5189) := by
    have ha : (tripleCharges (sourceA2268 + difference 0 2) (sourceB2268 + difference 2 0) sourceC2268) = raw29679 := by
      apply Matrix.ext; unfold tripleCharges sourceA2268 sourceB2268 sourceC2268 difference raw29679; decide +kernel
    rw [ha]
    exact (canonical29679 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2268 + difference 0 3) (sourceB2268 + difference 3 0) sourceC2268) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5189) := by
    have ha : (tripleCharges (sourceA2268 + difference 0 3) (sourceB2268 + difference 3 0) sourceC2268) = raw29680 := by
      apply Matrix.ext; unfold tripleCharges sourceA2268 sourceB2268 sourceC2268 difference raw29680; decide +kernel
    rw [ha]
    exact (canonical29680 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2268 + difference 0 4) (sourceB2268 + difference 4 0) sourceC2268) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5207) := by
    have ha : (tripleCharges (sourceA2268 + difference 0 4) (sourceB2268 + difference 4 0) sourceC2268) = raw29571 := by
      apply Matrix.ext; unfold tripleCharges sourceA2268 sourceB2268 sourceC2268 difference raw29571; decide +kernel
    rw [ha]
    exact (canonical29571 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2268 + difference 0 5) (sourceB2268 + difference 5 0) sourceC2268) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5207) := by
    have ha : (tripleCharges (sourceA2268 + difference 0 5) (sourceB2268 + difference 5 0) sourceC2268) = raw29681 := by
      apply Matrix.ext; unfold tripleCharges sourceA2268 sourceB2268 sourceC2268 difference raw29681; decide +kernel
    rw [ha]
    exact (canonical29681 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2268 + difference 1 0) (sourceB2268 + difference 0 1) sourceC2268) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4506) := by
    have ha : (tripleCharges (sourceA2268 + difference 1 0) (sourceB2268 + difference 0 1) sourceC2268) = raw31234 := by
      apply Matrix.ext; unfold tripleCharges sourceA2268 sourceB2268 sourceC2268 difference raw31234; decide +kernel
    rw [ha]
    exact (canonical31234 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2268 + difference 1 2) (sourceB2268 + difference 2 1) sourceC2268) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4842) := by
    have ha : (tripleCharges (sourceA2268 + difference 1 2) (sourceB2268 + difference 2 1) sourceC2268) = raw31235 := by
      apply Matrix.ext; unfold tripleCharges sourceA2268 sourceB2268 sourceC2268 difference raw31235; decide +kernel
    rw [ha]
    exact (canonical31235 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2268 + difference 1 3) (sourceB2268 + difference 3 1) sourceC2268) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4842) := by
    have ha : (tripleCharges (sourceA2268 + difference 1 3) (sourceB2268 + difference 3 1) sourceC2268) = raw31236 := by
      apply Matrix.ext; unfold tripleCharges sourceA2268 sourceB2268 sourceC2268 difference raw31236; decide +kernel
    rw [ha]
    exact (canonical31236 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2268 + difference 1 4) (sourceB2268 + difference 4 1) sourceC2268) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4884) := by
    have ha : (tripleCharges (sourceA2268 + difference 1 4) (sourceB2268 + difference 4 1) sourceC2268) = raw30032 := by
      apply Matrix.ext; unfold tripleCharges sourceA2268 sourceB2268 sourceC2268 difference raw30032; decide +kernel
    rw [ha]
    exact (canonical30032 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2268 + difference 1 5) (sourceB2268 + difference 5 1) sourceC2268) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4884) := by
    have ha : (tripleCharges (sourceA2268 + difference 1 5) (sourceB2268 + difference 5 1) sourceC2268) = raw31064 := by
      apply Matrix.ext; unfold tripleCharges sourceA2268 sourceB2268 sourceC2268 difference raw31064; decide +kernel
    rw [ha]
    exact (canonical31064 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2268 + difference 2 0) (sourceB2268 + difference 0 2) sourceC2268) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4487) := by
    have ha : (tripleCharges (sourceA2268 + difference 2 0) (sourceB2268 + difference 0 2) sourceC2268) = raw31237 := by
      apply Matrix.ext; unfold tripleCharges sourceA2268 sourceB2268 sourceC2268 difference raw31237; decide +kernel
    rw [ha]
    exact (canonical31237 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2268 + difference 2 1) (sourceB2268 + difference 1 2) sourceC2268) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4811) := by
    have ha : (tripleCharges (sourceA2268 + difference 2 1) (sourceB2268 + difference 1 2) sourceC2268) = raw29682 := by
      apply Matrix.ext; unfold tripleCharges sourceA2268 sourceB2268 sourceC2268 difference raw29682; decide +kernel
    rw [ha]
    exact (canonical29682 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2268 + difference 2 3) (sourceB2268 + difference 3 2) sourceC2268) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4825) := by
    have ha : (tripleCharges (sourceA2268 + difference 2 3) (sourceB2268 + difference 3 2) sourceC2268) = raw31238 := by
      apply Matrix.ext; unfold tripleCharges sourceA2268 sourceB2268 sourceC2268 difference raw31238; decide +kernel
    rw [ha]
    exact (canonical31238 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2268 + difference 2 4) (sourceB2268 + difference 4 2) sourceC2268) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4856) := by
    have ha : (tripleCharges (sourceA2268 + difference 2 4) (sourceB2268 + difference 4 2) sourceC2268) = raw30037 := by
      apply Matrix.ext; unfold tripleCharges sourceA2268 sourceB2268 sourceC2268 difference raw30037; decide +kernel
    rw [ha]
    exact (canonical30037 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2268 + difference 2 5) (sourceB2268 + difference 5 2) sourceC2268) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4856) := by
    have ha : (tripleCharges (sourceA2268 + difference 2 5) (sourceB2268 + difference 5 2) sourceC2268) = raw31068 := by
      apply Matrix.ext; unfold tripleCharges sourceA2268 sourceB2268 sourceC2268 difference raw31068; decide +kernel
    rw [ha]
    exact (canonical31068 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2268 + difference 3 0) (sourceB2268 + difference 0 3) sourceC2268) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4487) := by
    have ha : (tripleCharges (sourceA2268 + difference 3 0) (sourceB2268 + difference 0 3) sourceC2268) = raw31239 := by
      apply Matrix.ext; unfold tripleCharges sourceA2268 sourceB2268 sourceC2268 difference raw31239; decide +kernel
    rw [ha]
    exact (canonical31239 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2268 + difference 3 1) (sourceB2268 + difference 1 3) sourceC2268) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4811) := by
    have ha : (tripleCharges (sourceA2268 + difference 3 1) (sourceB2268 + difference 1 3) sourceC2268) = raw29686 := by
      apply Matrix.ext; unfold tripleCharges sourceA2268 sourceB2268 sourceC2268 difference raw29686; decide +kernel
    rw [ha]
    exact (canonical29686 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2268 + difference 3 2) (sourceB2268 + difference 2 3) sourceC2268) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4825) := by
    have ha : (tripleCharges (sourceA2268 + difference 3 2) (sourceB2268 + difference 2 3) sourceC2268) = raw31240 := by
      apply Matrix.ext; unfold tripleCharges sourceA2268 sourceB2268 sourceC2268 difference raw31240; decide +kernel
    rw [ha]
    exact (canonical31240 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2268 + difference 3 4) (sourceB2268 + difference 4 3) sourceC2268) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4856) := by
    have ha : (tripleCharges (sourceA2268 + difference 3 4) (sourceB2268 + difference 4 3) sourceC2268) = raw29825 := by
      apply Matrix.ext; unfold tripleCharges sourceA2268 sourceB2268 sourceC2268 difference raw29825; decide +kernel
    rw [ha]
    exact (canonical29825 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2268 + difference 3 5) (sourceB2268 + difference 5 3) sourceC2268) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4856) := by
    have ha : (tripleCharges (sourceA2268 + difference 3 5) (sourceB2268 + difference 5 3) sourceC2268) = raw31073 := by
      apply Matrix.ext; unfold tripleCharges sourceA2268 sourceB2268 sourceC2268 difference raw31073; decide +kernel
    rw [ha]
    exact (canonical31073 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2268 + difference 4 0) (sourceB2268 + difference 0 4) sourceC2268) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4491) := by
    have ha : (tripleCharges (sourceA2268 + difference 4 0) (sourceB2268 + difference 0 4) sourceC2268) = raw31079 := by
      apply Matrix.ext; unfold tripleCharges sourceA2268 sourceB2268 sourceC2268 difference raw31079; decide +kernel
    rw [ha]
    exact (canonical31079 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2268 + difference 4 1) (sourceB2268 + difference 1 4) sourceC2268) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4846) := by
    have ha : (tripleCharges (sourceA2268 + difference 4 1) (sourceB2268 + difference 1 4) sourceC2268) = raw29690 := by
      apply Matrix.ext; unfold tripleCharges sourceA2268 sourceB2268 sourceC2268 difference raw29690; decide +kernel
    rw [ha]
    exact (canonical29690 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2268 + difference 4 2) (sourceB2268 + difference 2 4) sourceC2268) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4828) := by
    have ha : (tripleCharges (sourceA2268 + difference 4 2) (sourceB2268 + difference 2 4) sourceC2268) = raw31080 := by
      apply Matrix.ext; unfold tripleCharges sourceA2268 sourceB2268 sourceC2268 difference raw31080; decide +kernel
    rw [ha]
    exact (canonical31080 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2268 + difference 4 3) (sourceB2268 + difference 3 4) sourceC2268) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4828) := by
    have ha : (tripleCharges (sourceA2268 + difference 4 3) (sourceB2268 + difference 3 4) sourceC2268) = raw30169 := by
      apply Matrix.ext; unfold tripleCharges sourceA2268 sourceB2268 sourceC2268 difference raw30169; decide +kernel
    rw [ha]
    exact (canonical30169 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2268 + difference 4 5) (sourceB2268 + difference 5 4) sourceC2268) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4874) := by
    have ha : (tripleCharges (sourceA2268 + difference 4 5) (sourceB2268 + difference 5 4) sourceC2268) = raw31241 := by
      apply Matrix.ext; unfold tripleCharges sourceA2268 sourceB2268 sourceC2268 difference raw31241; decide +kernel
    rw [ha]
    exact (canonical31241 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2268 + difference 5 0) (sourceB2268 + difference 0 5) sourceC2268) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4491) := by
    have ha : (tripleCharges (sourceA2268 + difference 5 0) (sourceB2268 + difference 0 5) sourceC2268) = raw31242 := by
      apply Matrix.ext; unfold tripleCharges sourceA2268 sourceB2268 sourceC2268 difference raw31242; decide +kernel
    rw [ha]
    exact (canonical31242 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2268 + difference 5 1) (sourceB2268 + difference 1 5) sourceC2268) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4846) := by
    have ha : (tripleCharges (sourceA2268 + difference 5 1) (sourceB2268 + difference 1 5) sourceC2268) = raw29582 := by
      apply Matrix.ext; unfold tripleCharges sourceA2268 sourceB2268 sourceC2268 difference raw29582; decide +kernel
    rw [ha]
    exact (canonical29582 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2268 + difference 5 2) (sourceB2268 + difference 2 5) sourceC2268) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4828) := by
    have ha : (tripleCharges (sourceA2268 + difference 5 2) (sourceB2268 + difference 2 5) sourceC2268) = raw31243 := by
      apply Matrix.ext; unfold tripleCharges sourceA2268 sourceB2268 sourceC2268 difference raw31243; decide +kernel
    rw [ha]
    exact (canonical31243 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2268 + difference 5 3) (sourceB2268 + difference 3 5) sourceC2268) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4828) := by
    have ha : (tripleCharges (sourceA2268 + difference 5 3) (sourceB2268 + difference 3 5) sourceC2268) = raw31244 := by
      apply Matrix.ext; unfold tripleCharges sourceA2268 sourceB2268 sourceC2268 difference raw31244; decide +kernel
    rw [ha]
    exact (canonical31244 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2268 + difference 5 4) (sourceB2268 + difference 4 5) sourceC2268) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4874) := by
    have ha : (tripleCharges (sourceA2268 + difference 5 4) (sourceB2268 + difference 4 5) sourceC2268) = raw29567 := by
      apply Matrix.ext; unfold tripleCharges sourceA2268 sourceB2268 sourceC2268 difference raw29567; decide +kernel
    rw [ha]
    exact (canonical29567 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2268 sourceB2268 sourceC2268
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2268, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2269 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceB2269 : Charge := ![3, -1, 0, 0, -1, -1]
def sourceC2269 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceForm2269 : Integer.Sparse Master := [(Sum.inr 1641, 2), (Sum.inr 1653, 2), (Sum.inr 1661, 1), (Sum.inr 2029, 2), (Sum.inr 2066, 2), (Sum.inr 2073, 2), (Sum.inr 2082, 4), (Sum.inr 2094, 4), (Sum.inr 2115, 2), (Sum.inr 2123, 2), (Sum.inr 2138, 2), (Sum.inr 2605, 1), (Sum.inr 2621, 2), (Sum.inr 2644, 2)]

theorem sourceEq2269 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2269 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2269 + difference 0 1) (sourceB2269 + difference 1 0) sourceC2269) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2605) := by
    have ha : (tripleCharges (sourceA2269 + difference 0 1) (sourceB2269 + difference 1 0) sourceC2269) = raw30556 := by
      apply Matrix.ext; unfold tripleCharges sourceA2269 sourceB2269 sourceC2269 difference raw30556; decide +kernel
    rw [ha]
    exact (canonical30556 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2269 + difference 0 2) (sourceB2269 + difference 2 0) sourceC2269) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2621) := by
    have ha : (tripleCharges (sourceA2269 + difference 0 2) (sourceB2269 + difference 2 0) sourceC2269) = raw31245 := by
      apply Matrix.ext; unfold tripleCharges sourceA2269 sourceB2269 sourceC2269 difference raw31245; decide +kernel
    rw [ha]
    exact (canonical31245 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2269 + difference 0 3) (sourceB2269 + difference 3 0) sourceC2269) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2621) := by
    have ha : (tripleCharges (sourceA2269 + difference 0 3) (sourceB2269 + difference 3 0) sourceC2269) = raw31246 := by
      apply Matrix.ext; unfold tripleCharges sourceA2269 sourceB2269 sourceC2269 difference raw31246; decide +kernel
    rw [ha]
    exact (canonical31246 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2269 + difference 0 4) (sourceB2269 + difference 4 0) sourceC2269) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2644) := by
    have ha : (tripleCharges (sourceA2269 + difference 0 4) (sourceB2269 + difference 4 0) sourceC2269) = raw31247 := by
      apply Matrix.ext; unfold tripleCharges sourceA2269 sourceB2269 sourceC2269 difference raw31247; decide +kernel
    rw [ha]
    exact (canonical31247 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2269 + difference 0 5) (sourceB2269 + difference 5 0) sourceC2269) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2644) := by
    have ha : (tripleCharges (sourceA2269 + difference 0 5) (sourceB2269 + difference 5 0) sourceC2269) = raw31083 := by
      apply Matrix.ext; unfold tripleCharges sourceA2269 sourceB2269 sourceC2269 difference raw31083; decide +kernel
    rw [ha]
    exact (canonical31083 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2269 + difference 1 0) (sourceB2269 + difference 0 1) sourceC2269) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1661) := by
    have ha : (tripleCharges (sourceA2269 + difference 1 0) (sourceB2269 + difference 0 1) sourceC2269) = raw31248 := by
      apply Matrix.ext; unfold tripleCharges sourceA2269 sourceB2269 sourceC2269 difference raw31248; decide +kernel
    rw [ha]
    exact (canonical31248 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2269 + difference 1 2) (sourceB2269 + difference 2 1) sourceC2269) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2123) := by
    have ha : (tripleCharges (sourceA2269 + difference 1 2) (sourceB2269 + difference 2 1) sourceC2269) = raw31249 := by
      apply Matrix.ext; unfold tripleCharges sourceA2269 sourceB2269 sourceC2269 difference raw31249; decide +kernel
    rw [ha]
    exact (canonical31249 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2269 + difference 1 3) (sourceB2269 + difference 3 1) sourceC2269) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2123) := by
    have ha : (tripleCharges (sourceA2269 + difference 1 3) (sourceB2269 + difference 3 1) sourceC2269) = raw31250 := by
      apply Matrix.ext; unfold tripleCharges sourceA2269 sourceB2269 sourceC2269 difference raw31250; decide +kernel
    rw [ha]
    exact (canonical31250 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2269 + difference 1 4) (sourceB2269 + difference 4 1) sourceC2269) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2138) := by
    have ha : (tripleCharges (sourceA2269 + difference 1 4) (sourceB2269 + difference 4 1) sourceC2269) = raw31251 := by
      apply Matrix.ext; unfold tripleCharges sourceA2269 sourceB2269 sourceC2269 difference raw31251; decide +kernel
    rw [ha]
    exact (canonical31251 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2269 + difference 1 5) (sourceB2269 + difference 5 1) sourceC2269) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2138) := by
    have ha : (tripleCharges (sourceA2269 + difference 1 5) (sourceB2269 + difference 5 1) sourceC2269) = raw31088 := by
      apply Matrix.ext; unfold tripleCharges sourceA2269 sourceB2269 sourceC2269 difference raw31088; decide +kernel
    rw [ha]
    exact (canonical31088 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2269 + difference 2 0) (sourceB2269 + difference 0 2) sourceC2269) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1641) := by
    have ha : (tripleCharges (sourceA2269 + difference 2 0) (sourceB2269 + difference 0 2) sourceC2269) = raw31252 := by
      apply Matrix.ext; unfold tripleCharges sourceA2269 sourceB2269 sourceC2269 difference raw31252; decide +kernel
    rw [ha]
    exact (canonical31252 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2269 + difference 2 1) (sourceB2269 + difference 1 2) sourceC2269) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2029) := by
    have ha : (tripleCharges (sourceA2269 + difference 2 1) (sourceB2269 + difference 1 2) sourceC2269) = raw30555 := by
      apply Matrix.ext; unfold tripleCharges sourceA2269 sourceB2269 sourceC2269 difference raw30555; decide +kernel
    rw [ha]
    exact (canonical30555 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2269 + difference 2 3) (sourceB2269 + difference 3 2) sourceC2269) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2073) := by
    have ha : (tripleCharges (sourceA2269 + difference 2 3) (sourceB2269 + difference 3 2) sourceC2269) = raw31253 := by
      apply Matrix.ext; unfold tripleCharges sourceA2269 sourceB2269 sourceC2269 difference raw31253; decide +kernel
    rw [ha]
    exact (canonical31253 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2269 + difference 2 4) (sourceB2269 + difference 4 2) sourceC2269) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2094) := by
    have ha : (tripleCharges (sourceA2269 + difference 2 4) (sourceB2269 + difference 4 2) sourceC2269) = raw31254 := by
      apply Matrix.ext; unfold tripleCharges sourceA2269 sourceB2269 sourceC2269 difference raw31254; decide +kernel
    rw [ha]
    exact (canonical31254 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2269 + difference 2 5) (sourceB2269 + difference 5 2) sourceC2269) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2094) := by
    have ha : (tripleCharges (sourceA2269 + difference 2 5) (sourceB2269 + difference 5 2) sourceC2269) = raw31092 := by
      apply Matrix.ext; unfold tripleCharges sourceA2269 sourceB2269 sourceC2269 difference raw31092; decide +kernel
    rw [ha]
    exact (canonical31092 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2269 + difference 3 0) (sourceB2269 + difference 0 3) sourceC2269) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1641) := by
    have ha : (tripleCharges (sourceA2269 + difference 3 0) (sourceB2269 + difference 0 3) sourceC2269) = raw31255 := by
      apply Matrix.ext; unfold tripleCharges sourceA2269 sourceB2269 sourceC2269 difference raw31255; decide +kernel
    rw [ha]
    exact (canonical31255 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2269 + difference 3 1) (sourceB2269 + difference 1 3) sourceC2269) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2029) := by
    have ha : (tripleCharges (sourceA2269 + difference 3 1) (sourceB2269 + difference 1 3) sourceC2269) = raw31256 := by
      apply Matrix.ext; unfold tripleCharges sourceA2269 sourceB2269 sourceC2269 difference raw31256; decide +kernel
    rw [ha]
    exact (canonical31256 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2269 + difference 3 2) (sourceB2269 + difference 2 3) sourceC2269) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2073) := by
    have ha : (tripleCharges (sourceA2269 + difference 3 2) (sourceB2269 + difference 2 3) sourceC2269) = raw31257 := by
      apply Matrix.ext; unfold tripleCharges sourceA2269 sourceB2269 sourceC2269 difference raw31257; decide +kernel
    rw [ha]
    exact (canonical31257 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2269 + difference 3 4) (sourceB2269 + difference 4 3) sourceC2269) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2094) := by
    have ha : (tripleCharges (sourceA2269 + difference 3 4) (sourceB2269 + difference 4 3) sourceC2269) = raw31258 := by
      apply Matrix.ext; unfold tripleCharges sourceA2269 sourceB2269 sourceC2269 difference raw31258; decide +kernel
    rw [ha]
    exact (canonical31258 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2269 + difference 3 5) (sourceB2269 + difference 5 3) sourceC2269) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2094) := by
    have ha : (tripleCharges (sourceA2269 + difference 3 5) (sourceB2269 + difference 5 3) sourceC2269) = raw31097 := by
      apply Matrix.ext; unfold tripleCharges sourceA2269 sourceB2269 sourceC2269 difference raw31097; decide +kernel
    rw [ha]
    exact (canonical31097 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2269 + difference 4 0) (sourceB2269 + difference 0 4) sourceC2269) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1653) := by
    have ha : (tripleCharges (sourceA2269 + difference 4 0) (sourceB2269 + difference 0 4) sourceC2269) = raw31104 := by
      apply Matrix.ext; unfold tripleCharges sourceA2269 sourceB2269 sourceC2269 difference raw31104; decide +kernel
    rw [ha]
    exact (canonical31104 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2269 + difference 4 1) (sourceB2269 + difference 1 4) sourceC2269) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2066) := by
    have ha : (tripleCharges (sourceA2269 + difference 4 1) (sourceB2269 + difference 1 4) sourceC2269) = raw31105 := by
      apply Matrix.ext; unfold tripleCharges sourceA2269 sourceB2269 sourceC2269 difference raw31105; decide +kernel
    rw [ha]
    exact (canonical31105 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2269 + difference 4 2) (sourceB2269 + difference 2 4) sourceC2269) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2082) := by
    have ha : (tripleCharges (sourceA2269 + difference 4 2) (sourceB2269 + difference 2 4) sourceC2269) = raw31106 := by
      apply Matrix.ext; unfold tripleCharges sourceA2269 sourceB2269 sourceC2269 difference raw31106; decide +kernel
    rw [ha]
    exact (canonical31106 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2269 + difference 4 3) (sourceB2269 + difference 3 4) sourceC2269) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2082) := by
    have ha : (tripleCharges (sourceA2269 + difference 4 3) (sourceB2269 + difference 3 4) sourceC2269) = raw31107 := by
      apply Matrix.ext; unfold tripleCharges sourceA2269 sourceB2269 sourceC2269 difference raw31107; decide +kernel
    rw [ha]
    exact (canonical31107 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2269 + difference 4 5) (sourceB2269 + difference 5 4) sourceC2269) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2115) := by
    have ha : (tripleCharges (sourceA2269 + difference 4 5) (sourceB2269 + difference 5 4) sourceC2269) = raw31259 := by
      apply Matrix.ext; unfold tripleCharges sourceA2269 sourceB2269 sourceC2269 difference raw31259; decide +kernel
    rw [ha]
    exact (canonical31259 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2269 + difference 5 0) (sourceB2269 + difference 0 5) sourceC2269) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1653) := by
    have ha : (tripleCharges (sourceA2269 + difference 5 0) (sourceB2269 + difference 0 5) sourceC2269) = raw31260 := by
      apply Matrix.ext; unfold tripleCharges sourceA2269 sourceB2269 sourceC2269 difference raw31260; decide +kernel
    rw [ha]
    exact (canonical31260 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2269 + difference 5 1) (sourceB2269 + difference 1 5) sourceC2269) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2066) := by
    have ha : (tripleCharges (sourceA2269 + difference 5 1) (sourceB2269 + difference 1 5) sourceC2269) = raw31261 := by
      apply Matrix.ext; unfold tripleCharges sourceA2269 sourceB2269 sourceC2269 difference raw31261; decide +kernel
    rw [ha]
    exact (canonical31261 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2269 + difference 5 2) (sourceB2269 + difference 2 5) sourceC2269) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2082) := by
    have ha : (tripleCharges (sourceA2269 + difference 5 2) (sourceB2269 + difference 2 5) sourceC2269) = raw31262 := by
      apply Matrix.ext; unfold tripleCharges sourceA2269 sourceB2269 sourceC2269 difference raw31262; decide +kernel
    rw [ha]
    exact (canonical31262 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2269 + difference 5 3) (sourceB2269 + difference 3 5) sourceC2269) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2082) := by
    have ha : (tripleCharges (sourceA2269 + difference 5 3) (sourceB2269 + difference 3 5) sourceC2269) = raw31263 := by
      apply Matrix.ext; unfold tripleCharges sourceA2269 sourceB2269 sourceC2269 difference raw31263; decide +kernel
    rw [ha]
    exact (canonical31263 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2269 + difference 5 4) (sourceB2269 + difference 4 5) sourceC2269) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2115) := by
    have ha : (tripleCharges (sourceA2269 + difference 5 4) (sourceB2269 + difference 4 5) sourceC2269) = raw31264 := by
      apply Matrix.ext; unfold tripleCharges sourceA2269 sourceB2269 sourceC2269 difference raw31264; decide +kernel
    rw [ha]
    exact (canonical31264 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2269 sourceB2269 sourceC2269
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2269, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2270 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2270 : Charge := ![0, 2, 0, -1, 0, -1]
def sourceC2270 : Charge := ![3, -1, 0, 1, -2, -1]
def sourceForm2270 : Integer.Sparse Master := [(Sum.inr 2082, 1), (Sum.inr 3047, 1), (Sum.inr 3448, 1), (Sum.inr 3499, 1), (Sum.inr 3564, 1), (Sum.inr 3565, 1), (Sum.inr 4080, -1)]

theorem sourceEq2270 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2270 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2270 + difference 0 0) (sourceB2270 + difference 0 0) sourceC2270) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2082) := by
    have ha : (tripleCharges (sourceA2270 + difference 0 0) (sourceB2270 + difference 0 0) sourceC2270) = raw23315 := by
      apply Matrix.ext; unfold tripleCharges sourceA2270 sourceB2270 sourceC2270 difference raw23315; decide +kernel
    rw [ha]
    exact (canonical23315 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2270 + difference 0 1) (sourceB2270 + difference 1 0) sourceC2270) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3047) := by
    have ha : (tripleCharges (sourceA2270 + difference 0 1) (sourceB2270 + difference 1 0) sourceC2270) = raw31265 := by
      apply Matrix.ext; unfold tripleCharges sourceA2270 sourceB2270 sourceC2270 difference raw31265; decide +kernel
    rw [ha]
    exact (canonical31265 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2270 + difference 0 2) (sourceB2270 + difference 2 0) sourceC2270) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3499) := by
    have ha : (tripleCharges (sourceA2270 + difference 0 2) (sourceB2270 + difference 2 0) sourceC2270) = raw31266 := by
      apply Matrix.ext; unfold tripleCharges sourceA2270 sourceB2270 sourceC2270 difference raw31266; decide +kernel
    rw [ha]
    exact (canonical31266 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2270 + difference 0 3) (sourceB2270 + difference 3 0) sourceC2270) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3448) := by
    have ha : (tripleCharges (sourceA2270 + difference 0 3) (sourceB2270 + difference 3 0) sourceC2270) = raw31267 := by
      apply Matrix.ext; unfold tripleCharges sourceA2270 sourceB2270 sourceC2270 difference raw31267; decide +kernel
    rw [ha]
    exact (canonical31267 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2270 + difference 0 4) (sourceB2270 + difference 4 0) sourceC2270) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3565) := by
    have ha : (tripleCharges (sourceA2270 + difference 0 4) (sourceB2270 + difference 4 0) sourceC2270) = raw31268 := by
      apply Matrix.ext; unfold tripleCharges sourceA2270 sourceB2270 sourceC2270 difference raw31268; decide +kernel
    rw [ha]
    exact (canonical31268 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2270 + difference 0 5) (sourceB2270 + difference 5 0) sourceC2270) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3564) := by
    have ha : (tripleCharges (sourceA2270 + difference 0 5) (sourceB2270 + difference 5 0) sourceC2270) = raw31269 := by
      apply Matrix.ext; unfold tripleCharges sourceA2270 sourceB2270 sourceC2270 difference raw31269; decide +kernel
    rw [ha]
    exact (canonical31269 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2270 + sourceB2270) sourceC2270) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA2270 + sourceB2270) sourceC2270) = raw21586 := by
      apply Matrix.ext; unfold doubleCharges sourceA2270 sourceB2270 sourceC2270 raw21586; decide +kernel
    rw [ha]
    exact (canonical21586 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2270 sourceB2270 sourceC2270
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2270, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2271 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2271 : Charge := ![0, 2, 0, -1, 0, -1]
def sourceC2271 : Charge := ![3, -1, 0, 1, -2, -1]
def sourceForm2271 : Integer.Sparse Master := [(Sum.inr 1876, 1), (Sum.inr 1880, 1), (Sum.inr 1881, 1), (Sum.inr 1918, 1), (Sum.inr 2082, 1), (Sum.inr 3448, 1), (Sum.inr 4080, -1)]

theorem sourceEq2271 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2271 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2271 + difference 0 3) (sourceB2271 + difference 3 0) sourceC2271) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3448) := by
    have ha : (tripleCharges (sourceA2271 + difference 0 3) (sourceB2271 + difference 3 0) sourceC2271) = raw31267 := by
      apply Matrix.ext; unfold tripleCharges sourceA2271 sourceB2271 sourceC2271 difference raw31267; decide +kernel
    rw [ha]
    exact (canonical31267 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2271 + difference 1 3) (sourceB2271 + difference 3 1) sourceC2271) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1918) := by
    have ha : (tripleCharges (sourceA2271 + difference 1 3) (sourceB2271 + difference 3 1) sourceC2271) = raw23317 := by
      apply Matrix.ext; unfold tripleCharges sourceA2271 sourceB2271 sourceC2271 difference raw23317; decide +kernel
    rw [ha]
    exact (canonical23317 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2271 + difference 2 3) (sourceB2271 + difference 3 2) sourceC2271) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1876) := by
    have ha : (tripleCharges (sourceA2271 + difference 2 3) (sourceB2271 + difference 3 2) sourceC2271) = raw31270 := by
      apply Matrix.ext; unfold tripleCharges sourceA2271 sourceB2271 sourceC2271 difference raw31270; decide +kernel
    rw [ha]
    exact (canonical31270 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2271 + difference 3 3) (sourceB2271 + difference 3 3) sourceC2271) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2082) := by
    have ha : (tripleCharges (sourceA2271 + difference 3 3) (sourceB2271 + difference 3 3) sourceC2271) = raw23315 := by
      apply Matrix.ext; unfold tripleCharges sourceA2271 sourceB2271 sourceC2271 difference raw23315; decide +kernel
    rw [ha]
    exact (canonical23315 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2271 + difference 4 3) (sourceB2271 + difference 3 4) sourceC2271) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1880) := by
    have ha : (tripleCharges (sourceA2271 + difference 4 3) (sourceB2271 + difference 3 4) sourceC2271) = raw31271 := by
      apply Matrix.ext; unfold tripleCharges sourceA2271 sourceB2271 sourceC2271 difference raw31271; decide +kernel
    rw [ha]
    exact (canonical31271 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2271 + difference 5 3) (sourceB2271 + difference 3 5) sourceC2271) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1881) := by
    have ha : (tripleCharges (sourceA2271 + difference 5 3) (sourceB2271 + difference 3 5) sourceC2271) = raw31272 := by
      apply Matrix.ext; unfold tripleCharges sourceA2271 sourceB2271 sourceC2271 difference raw31272; decide +kernel
    rw [ha]
    exact (canonical31272 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2271 + sourceB2271) sourceC2271) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA2271 + sourceB2271) sourceC2271) = raw21586 := by
      apply Matrix.ext; unfold doubleCharges sourceA2271 sourceB2271 sourceC2271 raw21586; decide +kernel
    rw [ha]
    exact (canonical21586 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2271 sourceB2271 sourceC2271
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2271, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
