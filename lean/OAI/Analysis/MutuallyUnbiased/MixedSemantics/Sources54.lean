import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical89
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical138
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical155
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical166
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical167
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical168
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical181
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical185
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical188
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical189
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical192
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical193
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical194
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical195
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical196
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical197
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical198
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical199

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA1728 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1728 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1728 : Charge := ![3, -1, 0, -1, 0, -1]
def sourceForm1728 : Integer.Sparse Master := [(Sum.inr 603, 1), (Sum.inr 922, 1), (Sum.inr 1041, 2), (Sum.inr 1081, 1), (Sum.inr 1086, 1), (Sum.inr 4083, -1)]

theorem sourceEq1728 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1728 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1728 + difference 1 0) (sourceB1728 + difference 0 1) sourceC1728) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 603) := by
    have ha : (tripleCharges (sourceA1728 + difference 1 0) (sourceB1728 + difference 0 1) sourceC1728) = raw25226 := by
      apply Matrix.ext; unfold tripleCharges sourceA1728 sourceB1728 sourceC1728 difference raw25226; decide +kernel
    rw [ha]
    exact (canonical25226 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1728 + difference 1 1) (sourceB1728 + difference 1 1) sourceC1728) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1041) := by
    have ha : (tripleCharges (sourceA1728 + difference 1 1) (sourceB1728 + difference 1 1) sourceC1728) = raw25225 := by
      apply Matrix.ext; unfold tripleCharges sourceA1728 sourceB1728 sourceC1728 difference raw25225; decide +kernel
    rw [ha]
    exact (canonical25225 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1728 + difference 1 2) (sourceB1728 + difference 2 1) sourceC1728) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 922) := by
    have ha : (tripleCharges (sourceA1728 + difference 1 2) (sourceB1728 + difference 2 1) sourceC1728) = raw25232 := by
      apply Matrix.ext; unfold tripleCharges sourceA1728 sourceB1728 sourceC1728 difference raw25232; decide +kernel
    rw [ha]
    exact (canonical25232 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1728 + difference 1 3) (sourceB1728 + difference 3 1) sourceC1728) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1041) := by
    have ha : (tripleCharges (sourceA1728 + difference 1 3) (sourceB1728 + difference 3 1) sourceC1728) = raw25233 := by
      apply Matrix.ext; unfold tripleCharges sourceA1728 sourceB1728 sourceC1728 difference raw25233; decide +kernel
    rw [ha]
    exact (canonical25233 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1728 + difference 1 4) (sourceB1728 + difference 4 1) sourceC1728) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1086) := by
    have ha : (tripleCharges (sourceA1728 + difference 1 4) (sourceB1728 + difference 4 1) sourceC1728) = raw25234 := by
      apply Matrix.ext; unfold tripleCharges sourceA1728 sourceB1728 sourceC1728 difference raw25234; decide +kernel
    rw [ha]
    exact (canonical25234 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1728 + difference 1 5) (sourceB1728 + difference 5 1) sourceC1728) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1081) := by
    have ha : (tripleCharges (sourceA1728 + difference 1 5) (sourceB1728 + difference 5 1) sourceC1728) = raw25235 := by
      apply Matrix.ext; unfold tripleCharges sourceA1728 sourceB1728 sourceC1728 difference raw25235; decide +kernel
    rw [ha]
    exact (canonical25235 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1728 + sourceB1728) sourceC1728) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA1728 + sourceB1728) sourceC1728) = raw25231 := by
      apply Matrix.ext; unfold doubleCharges sourceA1728 sourceB1728 sourceC1728 raw25231; decide +kernel
    rw [ha]
    exact (canonical25231 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1728 sourceB1728 sourceC1728
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1728, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1729 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1729 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1729 : Charge := ![3, -1, 0, -1, 0, -1]
def sourceForm1729 : Integer.Sparse Master := [(Sum.inr 942, 1), (Sum.inr 945, 1), (Sum.inr 947, 1), (Sum.inr 950, 1), (Sum.inr 1041, 1), (Sum.inr 2107, 1), (Sum.inr 4083, -1)]

theorem sourceEq1729 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1729 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1729 + difference 0 1) (sourceB1729 + difference 1 0) sourceC1729) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2107) := by
    have ha : (tripleCharges (sourceA1729 + difference 0 1) (sourceB1729 + difference 1 0) sourceC1729) = raw25236 := by
      apply Matrix.ext; unfold tripleCharges sourceA1729 sourceB1729 sourceC1729 difference raw25236; decide +kernel
    rw [ha]
    exact (canonical25236 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1729 + difference 1 1) (sourceB1729 + difference 1 1) sourceC1729) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1041) := by
    have ha : (tripleCharges (sourceA1729 + difference 1 1) (sourceB1729 + difference 1 1) sourceC1729) = raw25225 := by
      apply Matrix.ext; unfold tripleCharges sourceA1729 sourceB1729 sourceC1729 difference raw25225; decide +kernel
    rw [ha]
    exact (canonical25225 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1729 + difference 2 1) (sourceB1729 + difference 1 2) sourceC1729) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 942) := by
    have ha : (tripleCharges (sourceA1729 + difference 2 1) (sourceB1729 + difference 1 2) sourceC1729) = raw25237 := by
      apply Matrix.ext; unfold tripleCharges sourceA1729 sourceB1729 sourceC1729 difference raw25237; decide +kernel
    rw [ha]
    exact (canonical25237 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1729 + difference 3 1) (sourceB1729 + difference 1 3) sourceC1729) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 947) := by
    have ha : (tripleCharges (sourceA1729 + difference 3 1) (sourceB1729 + difference 1 3) sourceC1729) = raw25238 := by
      apply Matrix.ext; unfold tripleCharges sourceA1729 sourceB1729 sourceC1729 difference raw25238; decide +kernel
    rw [ha]
    exact (canonical25238 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1729 + difference 4 1) (sourceB1729 + difference 1 4) sourceC1729) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 950) := by
    have ha : (tripleCharges (sourceA1729 + difference 4 1) (sourceB1729 + difference 1 4) sourceC1729) = raw25239 := by
      apply Matrix.ext; unfold tripleCharges sourceA1729 sourceB1729 sourceC1729 difference raw25239; decide +kernel
    rw [ha]
    exact (canonical25239 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1729 + difference 5 1) (sourceB1729 + difference 1 5) sourceC1729) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 945) := by
    have ha : (tripleCharges (sourceA1729 + difference 5 1) (sourceB1729 + difference 1 5) sourceC1729) = raw25240 := by
      apply Matrix.ext; unfold tripleCharges sourceA1729 sourceB1729 sourceC1729 difference raw25240; decide +kernel
    rw [ha]
    exact (canonical25240 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1729 + sourceB1729) sourceC1729) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA1729 + sourceB1729) sourceC1729) = raw25231 := by
      apply Matrix.ext; unfold doubleCharges sourceA1729 sourceB1729 sourceC1729 raw25231; decide +kernel
    rw [ha]
    exact (canonical25231 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1729 sourceB1729 sourceC1729
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1729, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1730 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1730 : Charge := ![3, -1, 0, -1, 0, -1]
def sourceC1730 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceForm1730 : Integer.Sparse Master := [(Sum.inr 4100, 1), (Sum.inr 4101, 1), (Sum.inr 4102, 1), (Sum.inr 4107, 1), (Sum.inr 4119, 1), (Sum.inr 4287, 1), (Sum.inr 4288, 1), (Sum.inr 4292, 1), (Sum.inr 4301, 1), (Sum.inr 4344, 1), (Sum.inr 4346, 1), (Sum.inr 4349, 1), (Sum.inr 4355, 1), (Sum.inr 4399, 1), (Sum.inr 4401, 1), (Sum.inr 4404, 1), (Sum.inr 4424, 1), (Sum.inr 4456, 1), (Sum.inr 4457, 1), (Sum.inr 4458, 2), (Sum.inr 4460, 1), (Sum.inr 4467, 1), (Sum.inr 4495, 1), (Sum.inr 4499, 1), (Sum.inr 5073, 1), (Sum.inr 5169, 1), (Sum.inr 5259, 1), (Sum.inr 5292, 1), (Sum.inr 5293, 1)]

theorem sourceEq1730 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1730 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1730 + difference 0 1) (sourceB1730 + difference 1 0) sourceC1730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA1730 + difference 0 1) (sourceB1730 + difference 1 0) sourceC1730) = raw17671 := by
      apply Matrix.ext; unfold tripleCharges sourceA1730 sourceB1730 sourceC1730 difference raw17671; decide +kernel
    rw [ha]
    exact (canonical17671 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1730 + difference 0 2) (sourceB1730 + difference 2 0) sourceC1730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5073) := by
    have ha : (tripleCharges (sourceA1730 + difference 0 2) (sourceB1730 + difference 2 0) sourceC1730) = raw25241 := by
      apply Matrix.ext; unfold tripleCharges sourceA1730 sourceB1730 sourceC1730 difference raw25241; decide +kernel
    rw [ha]
    exact (canonical25241 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1730 + difference 0 3) (sourceB1730 + difference 3 0) sourceC1730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA1730 + difference 0 3) (sourceB1730 + difference 3 0) sourceC1730) = raw2771 := by
      apply Matrix.ext; unfold tripleCharges sourceA1730 sourceB1730 sourceC1730 difference raw2771; decide +kernel
    rw [ha]
    exact (canonical2771 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1730 + difference 0 4) (sourceB1730 + difference 4 0) sourceC1730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA1730 + difference 0 4) (sourceB1730 + difference 4 0) sourceC1730) = raw2766 := by
      apply Matrix.ext; unfold tripleCharges sourceA1730 sourceB1730 sourceC1730 difference raw2766; decide +kernel
    rw [ha]
    exact (canonical2766 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1730 + difference 0 5) (sourceB1730 + difference 5 0) sourceC1730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA1730 + difference 0 5) (sourceB1730 + difference 5 0) sourceC1730) = raw25242 := by
      apply Matrix.ext; unfold tripleCharges sourceA1730 sourceB1730 sourceC1730 difference raw25242; decide +kernel
    rw [ha]
    exact (canonical25242 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1730 + difference 1 0) (sourceB1730 + difference 0 1) sourceC1730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4119) := by
    have ha : (tripleCharges (sourceA1730 + difference 1 0) (sourceB1730 + difference 0 1) sourceC1730) = raw25243 := by
      apply Matrix.ext; unfold tripleCharges sourceA1730 sourceB1730 sourceC1730 difference raw25243; decide +kernel
    rw [ha]
    exact (canonical25243 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1730 + difference 1 2) (sourceB1730 + difference 2 1) sourceC1730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4301) := by
    have ha : (tripleCharges (sourceA1730 + difference 1 2) (sourceB1730 + difference 2 1) sourceC1730) = raw25244 := by
      apply Matrix.ext; unfold tripleCharges sourceA1730 sourceB1730 sourceC1730 difference raw25244; decide +kernel
    rw [ha]
    exact (canonical25244 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1730 + difference 1 3) (sourceB1730 + difference 3 1) sourceC1730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4499) := by
    have ha : (tripleCharges (sourceA1730 + difference 1 3) (sourceB1730 + difference 3 1) sourceC1730) = raw21481 := by
      apply Matrix.ext; unfold tripleCharges sourceA1730 sourceB1730 sourceC1730 difference raw21481; decide +kernel
    rw [ha]
    exact (canonical21481 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1730 + difference 1 4) (sourceB1730 + difference 4 1) sourceC1730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4424) := by
    have ha : (tripleCharges (sourceA1730 + difference 1 4) (sourceB1730 + difference 4 1) sourceC1730) = raw25245 := by
      apply Matrix.ext; unfold tripleCharges sourceA1730 sourceB1730 sourceC1730 difference raw25245; decide +kernel
    rw [ha]
    exact (canonical25245 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1730 + difference 1 5) (sourceB1730 + difference 5 1) sourceC1730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4495) := by
    have ha : (tripleCharges (sourceA1730 + difference 1 5) (sourceB1730 + difference 5 1) sourceC1730) = raw25246 := by
      apply Matrix.ext; unfold tripleCharges sourceA1730 sourceB1730 sourceC1730 difference raw25246; decide +kernel
    rw [ha]
    exact (canonical25246 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1730 + difference 2 0) (sourceB1730 + difference 0 2) sourceC1730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4100) := by
    have ha : (tripleCharges (sourceA1730 + difference 2 0) (sourceB1730 + difference 0 2) sourceC1730) = raw25247 := by
      apply Matrix.ext; unfold tripleCharges sourceA1730 sourceB1730 sourceC1730 difference raw25247; decide +kernel
    rw [ha]
    exact (canonical25247 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1730 + difference 2 1) (sourceB1730 + difference 1 2) sourceC1730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4344) := by
    have ha : (tripleCharges (sourceA1730 + difference 2 1) (sourceB1730 + difference 1 2) sourceC1730) = raw25248 := by
      apply Matrix.ext; unfold tripleCharges sourceA1730 sourceB1730 sourceC1730 difference raw25248; decide +kernel
    rw [ha]
    exact (canonical25248 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1730 + difference 2 3) (sourceB1730 + difference 3 2) sourceC1730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1730 + difference 2 3) (sourceB1730 + difference 3 2) sourceC1730) = raw21485 := by
      apply Matrix.ext; unfold tripleCharges sourceA1730 sourceB1730 sourceC1730 difference raw21485; decide +kernel
    rw [ha]
    exact (canonical21485 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1730 + difference 2 4) (sourceB1730 + difference 4 2) sourceC1730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4399) := by
    have ha : (tripleCharges (sourceA1730 + difference 2 4) (sourceB1730 + difference 4 2) sourceC1730) = raw25249 := by
      apply Matrix.ext; unfold tripleCharges sourceA1730 sourceB1730 sourceC1730 difference raw25249; decide +kernel
    rw [ha]
    exact (canonical25249 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1730 + difference 2 5) (sourceB1730 + difference 5 2) sourceC1730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4456) := by
    have ha : (tripleCharges (sourceA1730 + difference 2 5) (sourceB1730 + difference 5 2) sourceC1730) = raw25250 := by
      apply Matrix.ext; unfold tripleCharges sourceA1730 sourceB1730 sourceC1730 difference raw25250; decide +kernel
    rw [ha]
    exact (canonical25250 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1730 + difference 3 0) (sourceB1730 + difference 0 3) sourceC1730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4102) := by
    have ha : (tripleCharges (sourceA1730 + difference 3 0) (sourceB1730 + difference 0 3) sourceC1730) = raw25251 := by
      apply Matrix.ext; unfold tripleCharges sourceA1730 sourceB1730 sourceC1730 difference raw25251; decide +kernel
    rw [ha]
    exact (canonical25251 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1730 + difference 3 1) (sourceB1730 + difference 1 3) sourceC1730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4349) := by
    have ha : (tripleCharges (sourceA1730 + difference 3 1) (sourceB1730 + difference 1 3) sourceC1730) = raw25252 := by
      apply Matrix.ext; unfold tripleCharges sourceA1730 sourceB1730 sourceC1730 difference raw25252; decide +kernel
    rw [ha]
    exact (canonical25252 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1730 + difference 3 2) (sourceB1730 + difference 2 3) sourceC1730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4288) := by
    have ha : (tripleCharges (sourceA1730 + difference 3 2) (sourceB1730 + difference 2 3) sourceC1730) = raw25253 := by
      apply Matrix.ext; unfold tripleCharges sourceA1730 sourceB1730 sourceC1730 difference raw25253; decide +kernel
    rw [ha]
    exact (canonical25253 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1730 + difference 3 4) (sourceB1730 + difference 4 3) sourceC1730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4404) := by
    have ha : (tripleCharges (sourceA1730 + difference 3 4) (sourceB1730 + difference 4 3) sourceC1730) = raw25254 := by
      apply Matrix.ext; unfold tripleCharges sourceA1730 sourceB1730 sourceC1730 difference raw25254; decide +kernel
    rw [ha]
    exact (canonical25254 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1730 + difference 3 5) (sourceB1730 + difference 5 3) sourceC1730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4457) := by
    have ha : (tripleCharges (sourceA1730 + difference 3 5) (sourceB1730 + difference 5 3) sourceC1730) = raw25255 := by
      apply Matrix.ext; unfold tripleCharges sourceA1730 sourceB1730 sourceC1730 difference raw25255; decide +kernel
    rw [ha]
    exact (canonical25255 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1730 + difference 4 0) (sourceB1730 + difference 0 4) sourceC1730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4107) := by
    have ha : (tripleCharges (sourceA1730 + difference 4 0) (sourceB1730 + difference 0 4) sourceC1730) = raw23230 := by
      apply Matrix.ext; unfold tripleCharges sourceA1730 sourceB1730 sourceC1730 difference raw23230; decide +kernel
    rw [ha]
    exact (canonical23230 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1730 + difference 4 1) (sourceB1730 + difference 1 4) sourceC1730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4355) := by
    have ha : (tripleCharges (sourceA1730 + difference 4 1) (sourceB1730 + difference 1 4) sourceC1730) = raw23231 := by
      apply Matrix.ext; unfold tripleCharges sourceA1730 sourceB1730 sourceC1730 difference raw23231; decide +kernel
    rw [ha]
    exact (canonical23231 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1730 + difference 4 2) (sourceB1730 + difference 2 4) sourceC1730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4292) := by
    have ha : (tripleCharges (sourceA1730 + difference 4 2) (sourceB1730 + difference 2 4) sourceC1730) = raw23232 := by
      apply Matrix.ext; unfold tripleCharges sourceA1730 sourceB1730 sourceC1730 difference raw23232; decide +kernel
    rw [ha]
    exact (canonical23232 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1730 + difference 4 3) (sourceB1730 + difference 3 4) sourceC1730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4467) := by
    have ha : (tripleCharges (sourceA1730 + difference 4 3) (sourceB1730 + difference 3 4) sourceC1730) = raw21494 := by
      apply Matrix.ext; unfold tripleCharges sourceA1730 sourceB1730 sourceC1730 difference raw21494; decide +kernel
    rw [ha]
    exact (canonical21494 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1730 + difference 4 5) (sourceB1730 + difference 5 4) sourceC1730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1730 + difference 4 5) (sourceB1730 + difference 5 4) sourceC1730) = raw23233 := by
      apply Matrix.ext; unfold tripleCharges sourceA1730 sourceB1730 sourceC1730 difference raw23233; decide +kernel
    rw [ha]
    exact (canonical23233 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1730 + difference 5 0) (sourceB1730 + difference 0 5) sourceC1730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4101) := by
    have ha : (tripleCharges (sourceA1730 + difference 5 0) (sourceB1730 + difference 0 5) sourceC1730) = raw21486 := by
      apply Matrix.ext; unfold tripleCharges sourceA1730 sourceB1730 sourceC1730 difference raw21486; decide +kernel
    rw [ha]
    exact (canonical21486 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1730 + difference 5 1) (sourceB1730 + difference 1 5) sourceC1730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4346) := by
    have ha : (tripleCharges (sourceA1730 + difference 5 1) (sourceB1730 + difference 1 5) sourceC1730) = raw21487 := by
      apply Matrix.ext; unfold tripleCharges sourceA1730 sourceB1730 sourceC1730 difference raw21487; decide +kernel
    rw [ha]
    exact (canonical21487 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1730 + difference 5 2) (sourceB1730 + difference 2 5) sourceC1730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4287) := by
    have ha : (tripleCharges (sourceA1730 + difference 5 2) (sourceB1730 + difference 2 5) sourceC1730) = raw21488 := by
      apply Matrix.ext; unfold tripleCharges sourceA1730 sourceB1730 sourceC1730 difference raw21488; decide +kernel
    rw [ha]
    exact (canonical21488 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1730 + difference 5 3) (sourceB1730 + difference 3 5) sourceC1730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4460) := by
    have ha : (tripleCharges (sourceA1730 + difference 5 3) (sourceB1730 + difference 3 5) sourceC1730) = raw4935 := by
      apply Matrix.ext; unfold tripleCharges sourceA1730 sourceB1730 sourceC1730 difference raw4935; decide +kernel
    rw [ha]
    exact (canonical4935 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1730 + difference 5 4) (sourceB1730 + difference 4 5) sourceC1730) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4401) := by
    have ha : (tripleCharges (sourceA1730 + difference 5 4) (sourceB1730 + difference 4 5) sourceC1730) = raw4931 := by
      apply Matrix.ext; unfold tripleCharges sourceA1730 sourceB1730 sourceC1730 difference raw4931; decide +kernel
    rw [ha]
    exact (canonical4931 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1730 sourceB1730 sourceC1730
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1730, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1731 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1731 : Charge := ![3, -1, 0, -1, 0, -1]
def sourceC1731 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceForm1731 : Integer.Sparse Master := [(Sum.inr 537, 1), (Sum.inr 538, 1), (Sum.inr 539, 1), (Sum.inr 544, 1), (Sum.inr 554, 1), (Sum.inr 865, 1), (Sum.inr 866, 1), (Sum.inr 870, 1), (Sum.inr 879, 1), (Sum.inr 922, 1), (Sum.inr 924, 1), (Sum.inr 927, 1), (Sum.inr 933, 1), (Sum.inr 980, 1), (Sum.inr 982, 1), (Sum.inr 985, 1), (Sum.inr 1005, 1), (Sum.inr 1039, 1), (Sum.inr 1040, 1), (Sum.inr 1041, 2), (Sum.inr 1043, 1), (Sum.inr 1050, 1), (Sum.inr 1079, 1), (Sum.inr 1083, 1), (Sum.inr 2480, 1), (Sum.inr 2595, 1), (Sum.inr 2723, 1), (Sum.inr 2766, 1), (Sum.inr 2767, 1)]

theorem sourceEq1731 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1731 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1731 + difference 0 1) (sourceB1731 + difference 1 0) sourceC1731) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2595) := by
    have ha : (tripleCharges (sourceA1731 + difference 0 1) (sourceB1731 + difference 1 0) sourceC1731) = raw25256 := by
      apply Matrix.ext; unfold tripleCharges sourceA1731 sourceB1731 sourceC1731 difference raw25256; decide +kernel
    rw [ha]
    exact (canonical25256 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1731 + difference 0 2) (sourceB1731 + difference 2 0) sourceC1731) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2480) := by
    have ha : (tripleCharges (sourceA1731 + difference 0 2) (sourceB1731 + difference 2 0) sourceC1731) = raw25257 := by
      apply Matrix.ext; unfold tripleCharges sourceA1731 sourceB1731 sourceC1731 difference raw25257; decide +kernel
    rw [ha]
    exact (canonical25257 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1731 + difference 0 3) (sourceB1731 + difference 3 0) sourceC1731) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2767) := by
    have ha : (tripleCharges (sourceA1731 + difference 0 3) (sourceB1731 + difference 3 0) sourceC1731) = raw2801 := by
      apply Matrix.ext; unfold tripleCharges sourceA1731 sourceB1731 sourceC1731 difference raw2801; decide +kernel
    rw [ha]
    exact (canonical2801 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1731 + difference 0 4) (sourceB1731 + difference 4 0) sourceC1731) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA1731 + difference 0 4) (sourceB1731 + difference 4 0) sourceC1731) = raw2796 := by
      apply Matrix.ext; unfold tripleCharges sourceA1731 sourceB1731 sourceC1731 difference raw2796; decide +kernel
    rw [ha]
    exact (canonical2796 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1731 + difference 0 5) (sourceB1731 + difference 5 0) sourceC1731) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2766) := by
    have ha : (tripleCharges (sourceA1731 + difference 0 5) (sourceB1731 + difference 5 0) sourceC1731) = raw25258 := by
      apply Matrix.ext; unfold tripleCharges sourceA1731 sourceB1731 sourceC1731 difference raw25258; decide +kernel
    rw [ha]
    exact (canonical25258 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1731 + difference 1 0) (sourceB1731 + difference 0 1) sourceC1731) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 554) := by
    have ha : (tripleCharges (sourceA1731 + difference 1 0) (sourceB1731 + difference 0 1) sourceC1731) = raw25259 := by
      apply Matrix.ext; unfold tripleCharges sourceA1731 sourceB1731 sourceC1731 difference raw25259; decide +kernel
    rw [ha]
    exact (canonical25259 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1731 + difference 1 2) (sourceB1731 + difference 2 1) sourceC1731) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 879) := by
    have ha : (tripleCharges (sourceA1731 + difference 1 2) (sourceB1731 + difference 2 1) sourceC1731) = raw25260 := by
      apply Matrix.ext; unfold tripleCharges sourceA1731 sourceB1731 sourceC1731 difference raw25260; decide +kernel
    rw [ha]
    exact (canonical25260 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1731 + difference 1 3) (sourceB1731 + difference 3 1) sourceC1731) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1083) := by
    have ha : (tripleCharges (sourceA1731 + difference 1 3) (sourceB1731 + difference 3 1) sourceC1731) = raw21502 := by
      apply Matrix.ext; unfold tripleCharges sourceA1731 sourceB1731 sourceC1731 difference raw21502; decide +kernel
    rw [ha]
    exact (canonical21502 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1731 + difference 1 4) (sourceB1731 + difference 4 1) sourceC1731) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1005) := by
    have ha : (tripleCharges (sourceA1731 + difference 1 4) (sourceB1731 + difference 4 1) sourceC1731) = raw25261 := by
      apply Matrix.ext; unfold tripleCharges sourceA1731 sourceB1731 sourceC1731 difference raw25261; decide +kernel
    rw [ha]
    exact (canonical25261 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1731 + difference 1 5) (sourceB1731 + difference 5 1) sourceC1731) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1079) := by
    have ha : (tripleCharges (sourceA1731 + difference 1 5) (sourceB1731 + difference 5 1) sourceC1731) = raw25262 := by
      apply Matrix.ext; unfold tripleCharges sourceA1731 sourceB1731 sourceC1731 difference raw25262; decide +kernel
    rw [ha]
    exact (canonical25262 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1731 + difference 2 0) (sourceB1731 + difference 0 2) sourceC1731) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 537) := by
    have ha : (tripleCharges (sourceA1731 + difference 2 0) (sourceB1731 + difference 0 2) sourceC1731) = raw25263 := by
      apply Matrix.ext; unfold tripleCharges sourceA1731 sourceB1731 sourceC1731 difference raw25263; decide +kernel
    rw [ha]
    exact (canonical25263 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1731 + difference 2 1) (sourceB1731 + difference 1 2) sourceC1731) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 922) := by
    have ha : (tripleCharges (sourceA1731 + difference 2 1) (sourceB1731 + difference 1 2) sourceC1731) = raw25264 := by
      apply Matrix.ext; unfold tripleCharges sourceA1731 sourceB1731 sourceC1731 difference raw25264; decide +kernel
    rw [ha]
    exact (canonical25264 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1731 + difference 2 3) (sourceB1731 + difference 3 2) sourceC1731) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1041) := by
    have ha : (tripleCharges (sourceA1731 + difference 2 3) (sourceB1731 + difference 3 2) sourceC1731) = raw21506 := by
      apply Matrix.ext; unfold tripleCharges sourceA1731 sourceB1731 sourceC1731 difference raw21506; decide +kernel
    rw [ha]
    exact (canonical21506 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1731 + difference 2 4) (sourceB1731 + difference 4 2) sourceC1731) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 980) := by
    have ha : (tripleCharges (sourceA1731 + difference 2 4) (sourceB1731 + difference 4 2) sourceC1731) = raw25265 := by
      apply Matrix.ext; unfold tripleCharges sourceA1731 sourceB1731 sourceC1731 difference raw25265; decide +kernel
    rw [ha]
    exact (canonical25265 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1731 + difference 2 5) (sourceB1731 + difference 5 2) sourceC1731) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1039) := by
    have ha : (tripleCharges (sourceA1731 + difference 2 5) (sourceB1731 + difference 5 2) sourceC1731) = raw25266 := by
      apply Matrix.ext; unfold tripleCharges sourceA1731 sourceB1731 sourceC1731 difference raw25266; decide +kernel
    rw [ha]
    exact (canonical25266 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1731 + difference 3 0) (sourceB1731 + difference 0 3) sourceC1731) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 539) := by
    have ha : (tripleCharges (sourceA1731 + difference 3 0) (sourceB1731 + difference 0 3) sourceC1731) = raw25267 := by
      apply Matrix.ext; unfold tripleCharges sourceA1731 sourceB1731 sourceC1731 difference raw25267; decide +kernel
    rw [ha]
    exact (canonical25267 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1731 + difference 3 1) (sourceB1731 + difference 1 3) sourceC1731) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 927) := by
    have ha : (tripleCharges (sourceA1731 + difference 3 1) (sourceB1731 + difference 1 3) sourceC1731) = raw25268 := by
      apply Matrix.ext; unfold tripleCharges sourceA1731 sourceB1731 sourceC1731 difference raw25268; decide +kernel
    rw [ha]
    exact (canonical25268 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1731 + difference 3 2) (sourceB1731 + difference 2 3) sourceC1731) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 866) := by
    have ha : (tripleCharges (sourceA1731 + difference 3 2) (sourceB1731 + difference 2 3) sourceC1731) = raw25269 := by
      apply Matrix.ext; unfold tripleCharges sourceA1731 sourceB1731 sourceC1731 difference raw25269; decide +kernel
    rw [ha]
    exact (canonical25269 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1731 + difference 3 4) (sourceB1731 + difference 4 3) sourceC1731) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 985) := by
    have ha : (tripleCharges (sourceA1731 + difference 3 4) (sourceB1731 + difference 4 3) sourceC1731) = raw25270 := by
      apply Matrix.ext; unfold tripleCharges sourceA1731 sourceB1731 sourceC1731 difference raw25270; decide +kernel
    rw [ha]
    exact (canonical25270 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1731 + difference 3 5) (sourceB1731 + difference 5 3) sourceC1731) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1040) := by
    have ha : (tripleCharges (sourceA1731 + difference 3 5) (sourceB1731 + difference 5 3) sourceC1731) = raw25271 := by
      apply Matrix.ext; unfold tripleCharges sourceA1731 sourceB1731 sourceC1731 difference raw25271; decide +kernel
    rw [ha]
    exact (canonical25271 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1731 + difference 4 0) (sourceB1731 + difference 0 4) sourceC1731) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 544) := by
    have ha : (tripleCharges (sourceA1731 + difference 4 0) (sourceB1731 + difference 0 4) sourceC1731) = raw23251 := by
      apply Matrix.ext; unfold tripleCharges sourceA1731 sourceB1731 sourceC1731 difference raw23251; decide +kernel
    rw [ha]
    exact (canonical23251 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1731 + difference 4 1) (sourceB1731 + difference 1 4) sourceC1731) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 933) := by
    have ha : (tripleCharges (sourceA1731 + difference 4 1) (sourceB1731 + difference 1 4) sourceC1731) = raw23252 := by
      apply Matrix.ext; unfold tripleCharges sourceA1731 sourceB1731 sourceC1731 difference raw23252; decide +kernel
    rw [ha]
    exact (canonical23252 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1731 + difference 4 2) (sourceB1731 + difference 2 4) sourceC1731) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 870) := by
    have ha : (tripleCharges (sourceA1731 + difference 4 2) (sourceB1731 + difference 2 4) sourceC1731) = raw23253 := by
      apply Matrix.ext; unfold tripleCharges sourceA1731 sourceB1731 sourceC1731 difference raw23253; decide +kernel
    rw [ha]
    exact (canonical23253 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1731 + difference 4 3) (sourceB1731 + difference 3 4) sourceC1731) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1050) := by
    have ha : (tripleCharges (sourceA1731 + difference 4 3) (sourceB1731 + difference 3 4) sourceC1731) = raw21515 := by
      apply Matrix.ext; unfold tripleCharges sourceA1731 sourceB1731 sourceC1731 difference raw21515; decide +kernel
    rw [ha]
    exact (canonical21515 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1731 + difference 4 5) (sourceB1731 + difference 5 4) sourceC1731) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1041) := by
    have ha : (tripleCharges (sourceA1731 + difference 4 5) (sourceB1731 + difference 5 4) sourceC1731) = raw23254 := by
      apply Matrix.ext; unfold tripleCharges sourceA1731 sourceB1731 sourceC1731 difference raw23254; decide +kernel
    rw [ha]
    exact (canonical23254 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1731 + difference 5 0) (sourceB1731 + difference 0 5) sourceC1731) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 538) := by
    have ha : (tripleCharges (sourceA1731 + difference 5 0) (sourceB1731 + difference 0 5) sourceC1731) = raw21507 := by
      apply Matrix.ext; unfold tripleCharges sourceA1731 sourceB1731 sourceC1731 difference raw21507; decide +kernel
    rw [ha]
    exact (canonical21507 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1731 + difference 5 1) (sourceB1731 + difference 1 5) sourceC1731) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 924) := by
    have ha : (tripleCharges (sourceA1731 + difference 5 1) (sourceB1731 + difference 1 5) sourceC1731) = raw21508 := by
      apply Matrix.ext; unfold tripleCharges sourceA1731 sourceB1731 sourceC1731 difference raw21508; decide +kernel
    rw [ha]
    exact (canonical21508 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1731 + difference 5 2) (sourceB1731 + difference 2 5) sourceC1731) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 865) := by
    have ha : (tripleCharges (sourceA1731 + difference 5 2) (sourceB1731 + difference 2 5) sourceC1731) = raw21509 := by
      apply Matrix.ext; unfold tripleCharges sourceA1731 sourceB1731 sourceC1731 difference raw21509; decide +kernel
    rw [ha]
    exact (canonical21509 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1731 + difference 5 3) (sourceB1731 + difference 3 5) sourceC1731) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1043) := by
    have ha : (tripleCharges (sourceA1731 + difference 5 3) (sourceB1731 + difference 3 5) sourceC1731) = raw4957 := by
      apply Matrix.ext; unfold tripleCharges sourceA1731 sourceB1731 sourceC1731 difference raw4957; decide +kernel
    rw [ha]
    exact (canonical4957 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1731 + difference 5 4) (sourceB1731 + difference 4 5) sourceC1731) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 982) := by
    have ha : (tripleCharges (sourceA1731 + difference 5 4) (sourceB1731 + difference 4 5) sourceC1731) = raw4953 := by
      apply Matrix.ext; unfold tripleCharges sourceA1731 sourceB1731 sourceC1731 difference raw4953; decide +kernel
    rw [ha]
    exact (canonical4953 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1731 sourceB1731 sourceC1731
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1731, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1732 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceB1732 : Charge := ![3, -1, 0, -1, 0, -1]
def sourceC1732 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1732 : Integer.Sparse Master := [(Sum.inr 4249, 1), (Sum.inr 4264, 1), (Sum.inr 4265, 1), (Sum.inr 4267, 1), (Sum.inr 4268, 1), (Sum.inr 4396, 1), (Sum.inr 4397, 1), (Sum.inr 4399, 1), (Sum.inr 4407, 1), (Sum.inr 4436, 1), (Sum.inr 4438, 1), (Sum.inr 4439, 1), (Sum.inr 4452, 1), (Sum.inr 4453, 1), (Sum.inr 4457, 1), (Sum.inr 4458, 2), (Sum.inr 4459, 1), (Sum.inr 4461, 1), (Sum.inr 4471, 1), (Sum.inr 4474, 1), (Sum.inr 4475, 1), (Sum.inr 4498, 1), (Sum.inr 4499, 1), (Sum.inr 4502, 1), (Sum.inr 4590, 1), (Sum.inr 4602, 1), (Sum.inr 4603, 1), (Sum.inr 4606, 1), (Sum.inr 4624, 1)]

theorem sourceEq1732 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1732 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1732 + difference 0 1) (sourceB1732 + difference 1 0) sourceC1732) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4624) := by
    have ha : (tripleCharges (sourceA1732 + difference 0 1) (sourceB1732 + difference 1 0) sourceC1732) = raw24171 := by
      apply Matrix.ext; unfold tripleCharges sourceA1732 sourceB1732 sourceC1732 difference raw24171; decide +kernel
    rw [ha]
    exact (canonical24171 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1732 + difference 0 2) (sourceB1732 + difference 2 0) sourceC1732) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4590) := by
    have ha : (tripleCharges (sourceA1732 + difference 0 2) (sourceB1732 + difference 2 0) sourceC1732) = raw24607 := by
      apply Matrix.ext; unfold tripleCharges sourceA1732 sourceB1732 sourceC1732 difference raw24607; decide +kernel
    rw [ha]
    exact (canonical24607 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1732 + difference 0 3) (sourceB1732 + difference 3 0) sourceC1732) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4606) := by
    have ha : (tripleCharges (sourceA1732 + difference 0 3) (sourceB1732 + difference 3 0) sourceC1732) = raw24161 := by
      apply Matrix.ext; unfold tripleCharges sourceA1732 sourceB1732 sourceC1732 difference raw24161; decide +kernel
    rw [ha]
    exact (canonical24161 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1732 + difference 0 4) (sourceB1732 + difference 4 0) sourceC1732) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4603) := by
    have ha : (tripleCharges (sourceA1732 + difference 0 4) (sourceB1732 + difference 4 0) sourceC1732) = raw25272 := by
      apply Matrix.ext; unfold tripleCharges sourceA1732 sourceB1732 sourceC1732 difference raw25272; decide +kernel
    rw [ha]
    exact (canonical25272 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1732 + difference 0 5) (sourceB1732 + difference 5 0) sourceC1732) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1732 + difference 0 5) (sourceB1732 + difference 5 0) sourceC1732) = raw25087 := by
      apply Matrix.ext; unfold tripleCharges sourceA1732 sourceB1732 sourceC1732 difference raw25087; decide +kernel
    rw [ha]
    exact (canonical25087 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1732 + difference 1 0) (sourceB1732 + difference 0 1) sourceC1732) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4268) := by
    have ha : (tripleCharges (sourceA1732 + difference 1 0) (sourceB1732 + difference 0 1) sourceC1732) = raw25273 := by
      apply Matrix.ext; unfold tripleCharges sourceA1732 sourceB1732 sourceC1732 difference raw25273; decide +kernel
    rw [ha]
    exact (canonical25273 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1732 + difference 1 2) (sourceB1732 + difference 2 1) sourceC1732) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4407) := by
    have ha : (tripleCharges (sourceA1732 + difference 1 2) (sourceB1732 + difference 2 1) sourceC1732) = raw25274 := by
      apply Matrix.ext; unfold tripleCharges sourceA1732 sourceB1732 sourceC1732 difference raw25274; decide +kernel
    rw [ha]
    exact (canonical25274 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1732 + difference 1 3) (sourceB1732 + difference 3 1) sourceC1732) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4474) := by
    have ha : (tripleCharges (sourceA1732 + difference 1 3) (sourceB1732 + difference 3 1) sourceC1732) = raw25275 := by
      apply Matrix.ext; unfold tripleCharges sourceA1732 sourceB1732 sourceC1732 difference raw25275; decide +kernel
    rw [ha]
    exact (canonical25275 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1732 + difference 1 4) (sourceB1732 + difference 4 1) sourceC1732) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4471) := by
    have ha : (tripleCharges (sourceA1732 + difference 1 4) (sourceB1732 + difference 4 1) sourceC1732) = raw25276 := by
      apply Matrix.ext; unfold tripleCharges sourceA1732 sourceB1732 sourceC1732 difference raw25276; decide +kernel
    rw [ha]
    exact (canonical25276 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1732 + difference 1 5) (sourceB1732 + difference 5 1) sourceC1732) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4475) := by
    have ha : (tripleCharges (sourceA1732 + difference 1 5) (sourceB1732 + difference 5 1) sourceC1732) = raw25092 := by
      apply Matrix.ext; unfold tripleCharges sourceA1732 sourceB1732 sourceC1732 difference raw25092; decide +kernel
    rw [ha]
    exact (canonical25092 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1732 + difference 2 0) (sourceB1732 + difference 0 2) sourceC1732) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4249) := by
    have ha : (tripleCharges (sourceA1732 + difference 2 0) (sourceB1732 + difference 0 2) sourceC1732) = raw25277 := by
      apply Matrix.ext; unfold tripleCharges sourceA1732 sourceB1732 sourceC1732 difference raw25277; decide +kernel
    rw [ha]
    exact (canonical25277 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1732 + difference 2 1) (sourceB1732 + difference 1 2) sourceC1732) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1732 + difference 2 1) (sourceB1732 + difference 1 2) sourceC1732) = raw25278 := by
      apply Matrix.ext; unfold tripleCharges sourceA1732 sourceB1732 sourceC1732 difference raw25278; decide +kernel
    rw [ha]
    exact (canonical25278 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1732 + difference 2 3) (sourceB1732 + difference 3 2) sourceC1732) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4438) := by
    have ha : (tripleCharges (sourceA1732 + difference 2 3) (sourceB1732 + difference 3 2) sourceC1732) = raw25279 := by
      apply Matrix.ext; unfold tripleCharges sourceA1732 sourceB1732 sourceC1732 difference raw25279; decide +kernel
    rw [ha]
    exact (canonical25279 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1732 + difference 2 4) (sourceB1732 + difference 4 2) sourceC1732) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4436) := by
    have ha : (tripleCharges (sourceA1732 + difference 2 4) (sourceB1732 + difference 4 2) sourceC1732) = raw25280 := by
      apply Matrix.ext; unfold tripleCharges sourceA1732 sourceB1732 sourceC1732 difference raw25280; decide +kernel
    rw [ha]
    exact (canonical25280 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1732 + difference 2 5) (sourceB1732 + difference 5 2) sourceC1732) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4439) := by
    have ha : (tripleCharges (sourceA1732 + difference 2 5) (sourceB1732 + difference 5 2) sourceC1732) = raw25097 := by
      apply Matrix.ext; unfold tripleCharges sourceA1732 sourceB1732 sourceC1732 difference raw25097; decide +kernel
    rw [ha]
    exact (canonical25097 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1732 + difference 3 0) (sourceB1732 + difference 0 3) sourceC1732) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4265) := by
    have ha : (tripleCharges (sourceA1732 + difference 3 0) (sourceB1732 + difference 0 3) sourceC1732) = raw25281 := by
      apply Matrix.ext; unfold tripleCharges sourceA1732 sourceB1732 sourceC1732 difference raw25281; decide +kernel
    rw [ha]
    exact (canonical25281 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1732 + difference 3 1) (sourceB1732 + difference 1 3) sourceC1732) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4499) := by
    have ha : (tripleCharges (sourceA1732 + difference 3 1) (sourceB1732 + difference 1 3) sourceC1732) = raw25282 := by
      apply Matrix.ext; unfold tripleCharges sourceA1732 sourceB1732 sourceC1732 difference raw25282; decide +kernel
    rw [ha]
    exact (canonical25282 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1732 + difference 3 2) (sourceB1732 + difference 2 3) sourceC1732) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4397) := by
    have ha : (tripleCharges (sourceA1732 + difference 3 2) (sourceB1732 + difference 2 3) sourceC1732) = raw25283 := by
      apply Matrix.ext; unfold tripleCharges sourceA1732 sourceB1732 sourceC1732 difference raw25283; decide +kernel
    rw [ha]
    exact (canonical25283 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1732 + difference 3 4) (sourceB1732 + difference 4 3) sourceC1732) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4453) := by
    have ha : (tripleCharges (sourceA1732 + difference 3 4) (sourceB1732 + difference 4 3) sourceC1732) = raw25284 := by
      apply Matrix.ext; unfold tripleCharges sourceA1732 sourceB1732 sourceC1732 difference raw25284; decide +kernel
    rw [ha]
    exact (canonical25284 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1732 + difference 3 5) (sourceB1732 + difference 5 3) sourceC1732) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4459) := by
    have ha : (tripleCharges (sourceA1732 + difference 3 5) (sourceB1732 + difference 5 3) sourceC1732) = raw25102 := by
      apply Matrix.ext; unfold tripleCharges sourceA1732 sourceB1732 sourceC1732 difference raw25102; decide +kernel
    rw [ha]
    exact (canonical25102 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1732 + difference 4 0) (sourceB1732 + difference 0 4) sourceC1732) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4267) := by
    have ha : (tripleCharges (sourceA1732 + difference 4 0) (sourceB1732 + difference 0 4) sourceC1732) = raw25107 := by
      apply Matrix.ext; unfold tripleCharges sourceA1732 sourceB1732 sourceC1732 difference raw25107; decide +kernel
    rw [ha]
    exact (canonical25107 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1732 + difference 4 1) (sourceB1732 + difference 1 4) sourceC1732) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4502) := by
    have ha : (tripleCharges (sourceA1732 + difference 4 1) (sourceB1732 + difference 1 4) sourceC1732) = raw24260 := by
      apply Matrix.ext; unfold tripleCharges sourceA1732 sourceB1732 sourceC1732 difference raw24260; decide +kernel
    rw [ha]
    exact (canonical24260 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1732 + difference 4 2) (sourceB1732 + difference 2 4) sourceC1732) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4399) := by
    have ha : (tripleCharges (sourceA1732 + difference 4 2) (sourceB1732 + difference 2 4) sourceC1732) = raw24605 := by
      apply Matrix.ext; unfold tripleCharges sourceA1732 sourceB1732 sourceC1732 difference raw24605; decide +kernel
    rw [ha]
    exact (canonical24605 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1732 + difference 4 3) (sourceB1732 + difference 3 4) sourceC1732) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1732 + difference 4 3) (sourceB1732 + difference 3 4) sourceC1732) = raw24252 := by
      apply Matrix.ext; unfold tripleCharges sourceA1732 sourceB1732 sourceC1732 difference raw24252; decide +kernel
    rw [ha]
    exact (canonical24252 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1732 + difference 4 5) (sourceB1732 + difference 5 4) sourceC1732) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4461) := by
    have ha : (tripleCharges (sourceA1732 + difference 4 5) (sourceB1732 + difference 5 4) sourceC1732) = raw25285 := by
      apply Matrix.ext; unfold tripleCharges sourceA1732 sourceB1732 sourceC1732 difference raw25285; decide +kernel
    rw [ha]
    exact (canonical25285 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1732 + difference 5 0) (sourceB1732 + difference 0 5) sourceC1732) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4264) := by
    have ha : (tripleCharges (sourceA1732 + difference 5 0) (sourceB1732 + difference 0 5) sourceC1732) = raw25286 := by
      apply Matrix.ext; unfold tripleCharges sourceA1732 sourceB1732 sourceC1732 difference raw25286; decide +kernel
    rw [ha]
    exact (canonical25286 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1732 + difference 5 1) (sourceB1732 + difference 1 5) sourceC1732) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4498) := by
    have ha : (tripleCharges (sourceA1732 + difference 5 1) (sourceB1732 + difference 1 5) sourceC1732) = raw24167 := by
      apply Matrix.ext; unfold tripleCharges sourceA1732 sourceB1732 sourceC1732 difference raw24167; decide +kernel
    rw [ha]
    exact (canonical24167 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1732 + difference 5 2) (sourceB1732 + difference 2 5) sourceC1732) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4396) := by
    have ha : (tripleCharges (sourceA1732 + difference 5 2) (sourceB1732 + difference 2 5) sourceC1732) = raw24815 := by
      apply Matrix.ext; unfold tripleCharges sourceA1732 sourceB1732 sourceC1732 difference raw24815; decide +kernel
    rw [ha]
    exact (canonical24815 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1732 + difference 5 3) (sourceB1732 + difference 3 5) sourceC1732) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4457) := by
    have ha : (tripleCharges (sourceA1732 + difference 5 3) (sourceB1732 + difference 3 5) sourceC1732) = raw24157 := by
      apply Matrix.ext; unfold tripleCharges sourceA1732 sourceB1732 sourceC1732 difference raw24157; decide +kernel
    rw [ha]
    exact (canonical24157 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1732 + difference 5 4) (sourceB1732 + difference 4 5) sourceC1732) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4452) := by
    have ha : (tripleCharges (sourceA1732 + difference 5 4) (sourceB1732 + difference 4 5) sourceC1732) = raw25287 := by
      apply Matrix.ext; unfold tripleCharges sourceA1732 sourceB1732 sourceC1732 difference raw25287; decide +kernel
    rw [ha]
    exact (canonical25287 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1732 sourceB1732 sourceC1732
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1732, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1733 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceB1733 : Charge := ![3, -1, 0, -1, 0, -1]
def sourceC1733 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1733 : Integer.Sparse Master := [(Sum.inr 783, 1), (Sum.inr 806, 1), (Sum.inr 807, 1), (Sum.inr 810, 1), (Sum.inr 824, 1), (Sum.inr 977, 1), (Sum.inr 978, 1), (Sum.inr 980, 1), (Sum.inr 988, 1), (Sum.inr 1018, 1), (Sum.inr 1020, 1), (Sum.inr 1021, 1), (Sum.inr 1035, 1), (Sum.inr 1036, 1), (Sum.inr 1040, 1), (Sum.inr 1041, 2), (Sum.inr 1042, 1), (Sum.inr 1044, 1), (Sum.inr 1054, 1), (Sum.inr 1057, 1), (Sum.inr 1058, 1), (Sum.inr 1082, 1), (Sum.inr 1083, 1), (Sum.inr 1086, 1), (Sum.inr 1213, 1), (Sum.inr 1262, 1), (Sum.inr 1266, 1), (Sum.inr 1267, 1), (Sum.inr 1301, 1)]

theorem sourceEq1733 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1733 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1733 + difference 0 1) (sourceB1733 + difference 1 0) sourceC1733) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1301) := by
    have ha : (tripleCharges (sourceA1733 + difference 0 1) (sourceB1733 + difference 1 0) sourceC1733) = raw24633 := by
      apply Matrix.ext; unfold tripleCharges sourceA1733 sourceB1733 sourceC1733 difference raw24633; decide +kernel
    rw [ha]
    exact (canonical24633 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1733 + difference 0 2) (sourceB1733 + difference 2 0) sourceC1733) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1213) := by
    have ha : (tripleCharges (sourceA1733 + difference 0 2) (sourceB1733 + difference 2 0) sourceC1733) = raw24628 := by
      apply Matrix.ext; unfold tripleCharges sourceA1733 sourceB1733 sourceC1733 difference raw24628; decide +kernel
    rw [ha]
    exact (canonical24628 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1733 + difference 0 3) (sourceB1733 + difference 3 0) sourceC1733) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1266) := by
    have ha : (tripleCharges (sourceA1733 + difference 0 3) (sourceB1733 + difference 3 0) sourceC1733) = raw25288 := by
      apply Matrix.ext; unfold tripleCharges sourceA1733 sourceB1733 sourceC1733 difference raw25288; decide +kernel
    rw [ha]
    exact (canonical25288 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1733 + difference 0 4) (sourceB1733 + difference 4 0) sourceC1733) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1262) := by
    have ha : (tripleCharges (sourceA1733 + difference 0 4) (sourceB1733 + difference 4 0) sourceC1733) = raw25289 := by
      apply Matrix.ext; unfold tripleCharges sourceA1733 sourceB1733 sourceC1733 difference raw25289; decide +kernel
    rw [ha]
    exact (canonical25289 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1733 + difference 0 5) (sourceB1733 + difference 5 0) sourceC1733) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1267) := by
    have ha : (tripleCharges (sourceA1733 + difference 0 5) (sourceB1733 + difference 5 0) sourceC1733) = raw25110 := by
      apply Matrix.ext; unfold tripleCharges sourceA1733 sourceB1733 sourceC1733 difference raw25110; decide +kernel
    rw [ha]
    exact (canonical25110 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1733 + difference 1 0) (sourceB1733 + difference 0 1) sourceC1733) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 824) := by
    have ha : (tripleCharges (sourceA1733 + difference 1 0) (sourceB1733 + difference 0 1) sourceC1733) = raw25290 := by
      apply Matrix.ext; unfold tripleCharges sourceA1733 sourceB1733 sourceC1733 difference raw25290; decide +kernel
    rw [ha]
    exact (canonical25290 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1733 + difference 1 2) (sourceB1733 + difference 2 1) sourceC1733) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 988) := by
    have ha : (tripleCharges (sourceA1733 + difference 1 2) (sourceB1733 + difference 2 1) sourceC1733) = raw25291 := by
      apply Matrix.ext; unfold tripleCharges sourceA1733 sourceB1733 sourceC1733 difference raw25291; decide +kernel
    rw [ha]
    exact (canonical25291 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1733 + difference 1 3) (sourceB1733 + difference 3 1) sourceC1733) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1057) := by
    have ha : (tripleCharges (sourceA1733 + difference 1 3) (sourceB1733 + difference 3 1) sourceC1733) = raw25292 := by
      apply Matrix.ext; unfold tripleCharges sourceA1733 sourceB1733 sourceC1733 difference raw25292; decide +kernel
    rw [ha]
    exact (canonical25292 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1733 + difference 1 4) (sourceB1733 + difference 4 1) sourceC1733) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1054) := by
    have ha : (tripleCharges (sourceA1733 + difference 1 4) (sourceB1733 + difference 4 1) sourceC1733) = raw25293 := by
      apply Matrix.ext; unfold tripleCharges sourceA1733 sourceB1733 sourceC1733 difference raw25293; decide +kernel
    rw [ha]
    exact (canonical25293 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1733 + difference 1 5) (sourceB1733 + difference 5 1) sourceC1733) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1058) := by
    have ha : (tripleCharges (sourceA1733 + difference 1 5) (sourceB1733 + difference 5 1) sourceC1733) = raw25115 := by
      apply Matrix.ext; unfold tripleCharges sourceA1733 sourceB1733 sourceC1733 difference raw25115; decide +kernel
    rw [ha]
    exact (canonical25115 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1733 + difference 2 0) (sourceB1733 + difference 0 2) sourceC1733) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 783) := by
    have ha : (tripleCharges (sourceA1733 + difference 2 0) (sourceB1733 + difference 0 2) sourceC1733) = raw25294 := by
      apply Matrix.ext; unfold tripleCharges sourceA1733 sourceB1733 sourceC1733 difference raw25294; decide +kernel
    rw [ha]
    exact (canonical25294 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1733 + difference 2 1) (sourceB1733 + difference 1 2) sourceC1733) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1041) := by
    have ha : (tripleCharges (sourceA1733 + difference 2 1) (sourceB1733 + difference 1 2) sourceC1733) = raw25295 := by
      apply Matrix.ext; unfold tripleCharges sourceA1733 sourceB1733 sourceC1733 difference raw25295; decide +kernel
    rw [ha]
    exact (canonical25295 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1733 + difference 2 3) (sourceB1733 + difference 3 2) sourceC1733) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1020) := by
    have ha : (tripleCharges (sourceA1733 + difference 2 3) (sourceB1733 + difference 3 2) sourceC1733) = raw25296 := by
      apply Matrix.ext; unfold tripleCharges sourceA1733 sourceB1733 sourceC1733 difference raw25296; decide +kernel
    rw [ha]
    exact (canonical25296 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1733 + difference 2 4) (sourceB1733 + difference 4 2) sourceC1733) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1018) := by
    have ha : (tripleCharges (sourceA1733 + difference 2 4) (sourceB1733 + difference 4 2) sourceC1733) = raw25297 := by
      apply Matrix.ext; unfold tripleCharges sourceA1733 sourceB1733 sourceC1733 difference raw25297; decide +kernel
    rw [ha]
    exact (canonical25297 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1733 + difference 2 5) (sourceB1733 + difference 5 2) sourceC1733) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1021) := by
    have ha : (tripleCharges (sourceA1733 + difference 2 5) (sourceB1733 + difference 5 2) sourceC1733) = raw25120 := by
      apply Matrix.ext; unfold tripleCharges sourceA1733 sourceB1733 sourceC1733 difference raw25120; decide +kernel
    rw [ha]
    exact (canonical25120 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1733 + difference 3 0) (sourceB1733 + difference 0 3) sourceC1733) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 807) := by
    have ha : (tripleCharges (sourceA1733 + difference 3 0) (sourceB1733 + difference 0 3) sourceC1733) = raw25298 := by
      apply Matrix.ext; unfold tripleCharges sourceA1733 sourceB1733 sourceC1733 difference raw25298; decide +kernel
    rw [ha]
    exact (canonical25298 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1733 + difference 3 1) (sourceB1733 + difference 1 3) sourceC1733) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1083) := by
    have ha : (tripleCharges (sourceA1733 + difference 3 1) (sourceB1733 + difference 1 3) sourceC1733) = raw25299 := by
      apply Matrix.ext; unfold tripleCharges sourceA1733 sourceB1733 sourceC1733 difference raw25299; decide +kernel
    rw [ha]
    exact (canonical25299 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1733 + difference 3 2) (sourceB1733 + difference 2 3) sourceC1733) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 978) := by
    have ha : (tripleCharges (sourceA1733 + difference 3 2) (sourceB1733 + difference 2 3) sourceC1733) = raw25300 := by
      apply Matrix.ext; unfold tripleCharges sourceA1733 sourceB1733 sourceC1733 difference raw25300; decide +kernel
    rw [ha]
    exact (canonical25300 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1733 + difference 3 4) (sourceB1733 + difference 4 3) sourceC1733) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1036) := by
    have ha : (tripleCharges (sourceA1733 + difference 3 4) (sourceB1733 + difference 4 3) sourceC1733) = raw25301 := by
      apply Matrix.ext; unfold tripleCharges sourceA1733 sourceB1733 sourceC1733 difference raw25301; decide +kernel
    rw [ha]
    exact (canonical25301 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1733 + difference 3 5) (sourceB1733 + difference 5 3) sourceC1733) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1042) := by
    have ha : (tripleCharges (sourceA1733 + difference 3 5) (sourceB1733 + difference 5 3) sourceC1733) = raw25125 := by
      apply Matrix.ext; unfold tripleCharges sourceA1733 sourceB1733 sourceC1733 difference raw25125; decide +kernel
    rw [ha]
    exact (canonical25125 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1733 + difference 4 0) (sourceB1733 + difference 0 4) sourceC1733) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 810) := by
    have ha : (tripleCharges (sourceA1733 + difference 4 0) (sourceB1733 + difference 0 4) sourceC1733) = raw25132 := by
      apply Matrix.ext; unfold tripleCharges sourceA1733 sourceB1733 sourceC1733 difference raw25132; decide +kernel
    rw [ha]
    exact (canonical25132 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1733 + difference 4 1) (sourceB1733 + difference 1 4) sourceC1733) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1086) := by
    have ha : (tripleCharges (sourceA1733 + difference 4 1) (sourceB1733 + difference 1 4) sourceC1733) = raw24630 := by
      apply Matrix.ext; unfold tripleCharges sourceA1733 sourceB1733 sourceC1733 difference raw24630; decide +kernel
    rw [ha]
    exact (canonical24630 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1733 + difference 4 2) (sourceB1733 + difference 2 4) sourceC1733) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 980) := by
    have ha : (tripleCharges (sourceA1733 + difference 4 2) (sourceB1733 + difference 2 4) sourceC1733) = raw24625 := by
      apply Matrix.ext; unfold tripleCharges sourceA1733 sourceB1733 sourceC1733 difference raw24625; decide +kernel
    rw [ha]
    exact (canonical24625 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1733 + difference 4 3) (sourceB1733 + difference 3 4) sourceC1733) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1041) := by
    have ha : (tripleCharges (sourceA1733 + difference 4 3) (sourceB1733 + difference 3 4) sourceC1733) = raw25133 := by
      apply Matrix.ext; unfold tripleCharges sourceA1733 sourceB1733 sourceC1733 difference raw25133; decide +kernel
    rw [ha]
    exact (canonical25133 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1733 + difference 4 5) (sourceB1733 + difference 5 4) sourceC1733) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1044) := by
    have ha : (tripleCharges (sourceA1733 + difference 4 5) (sourceB1733 + difference 5 4) sourceC1733) = raw25302 := by
      apply Matrix.ext; unfold tripleCharges sourceA1733 sourceB1733 sourceC1733 difference raw25302; decide +kernel
    rw [ha]
    exact (canonical25302 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1733 + difference 5 0) (sourceB1733 + difference 0 5) sourceC1733) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 806) := by
    have ha : (tripleCharges (sourceA1733 + difference 5 0) (sourceB1733 + difference 0 5) sourceC1733) = raw25303 := by
      apply Matrix.ext; unfold tripleCharges sourceA1733 sourceB1733 sourceC1733 difference raw25303; decide +kernel
    rw [ha]
    exact (canonical25303 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1733 + difference 5 1) (sourceB1733 + difference 1 5) sourceC1733) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1082) := by
    have ha : (tripleCharges (sourceA1733 + difference 5 1) (sourceB1733 + difference 1 5) sourceC1733) = raw25304 := by
      apply Matrix.ext; unfold tripleCharges sourceA1733 sourceB1733 sourceC1733 difference raw25304; decide +kernel
    rw [ha]
    exact (canonical25304 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1733 + difference 5 2) (sourceB1733 + difference 2 5) sourceC1733) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 977) := by
    have ha : (tripleCharges (sourceA1733 + difference 5 2) (sourceB1733 + difference 2 5) sourceC1733) = raw25305 := by
      apply Matrix.ext; unfold tripleCharges sourceA1733 sourceB1733 sourceC1733 difference raw25305; decide +kernel
    rw [ha]
    exact (canonical25305 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1733 + difference 5 3) (sourceB1733 + difference 3 5) sourceC1733) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1040) := by
    have ha : (tripleCharges (sourceA1733 + difference 5 3) (sourceB1733 + difference 3 5) sourceC1733) = raw25306 := by
      apply Matrix.ext; unfold tripleCharges sourceA1733 sourceB1733 sourceC1733 difference raw25306; decide +kernel
    rw [ha]
    exact (canonical25306 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1733 + difference 5 4) (sourceB1733 + difference 4 5) sourceC1733) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1035) := by
    have ha : (tripleCharges (sourceA1733 + difference 5 4) (sourceB1733 + difference 4 5) sourceC1733) = raw25307 := by
      apply Matrix.ext; unfold tripleCharges sourceA1733 sourceB1733 sourceC1733 difference raw25307; decide +kernel
    rw [ha]
    exact (canonical25307 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1733 sourceB1733 sourceC1733
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1733, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1734 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceB1734 : Charge := ![3, -1, 0, -1, 0, -1]
def sourceC1734 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1734 : Integer.Sparse Master := [(Sum.inr 1213, 1), (Sum.inr 1236, 1), (Sum.inr 1237, 1), (Sum.inr 1240, 1), (Sum.inr 1301, 1), (Sum.inr 1358, 1), (Sum.inr 1367, 1), (Sum.inr 1368, 1), (Sum.inr 1370, 1), (Sum.inr 1383, 1), (Sum.inr 1384, 1), (Sum.inr 1386, 1), (Sum.inr 1393, 1), (Sum.inr 1395, 1), (Sum.inr 1396, 1), (Sum.inr 1406, 1), (Sum.inr 1407, 1), (Sum.inr 1410, 1), (Sum.inr 1411, 2), (Sum.inr 1412, 1), (Sum.inr 1414, 1), (Sum.inr 1443, 1), (Sum.inr 1447, 1), (Sum.inr 1448, 1), (Sum.inr 1468, 1), (Sum.inr 1475, 1), (Sum.inr 1480, 1), (Sum.inr 1482, 1), (Sum.inr 1483, 1)]

theorem sourceEq1734 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1734 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1734 + difference 0 1) (sourceB1734 + difference 1 0) sourceC1734) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1301) := by
    have ha : (tripleCharges (sourceA1734 + difference 0 1) (sourceB1734 + difference 1 0) sourceC1734) = raw24201 := by
      apply Matrix.ext; unfold tripleCharges sourceA1734 sourceB1734 sourceC1734 difference raw24201; decide +kernel
    rw [ha]
    exact (canonical24201 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1734 + difference 0 2) (sourceB1734 + difference 2 0) sourceC1734) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1213) := by
    have ha : (tripleCharges (sourceA1734 + difference 0 2) (sourceB1734 + difference 2 0) sourceC1734) = raw25308 := by
      apply Matrix.ext; unfold tripleCharges sourceA1734 sourceB1734 sourceC1734 difference raw25308; decide +kernel
    rw [ha]
    exact (canonical25308 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1734 + difference 0 3) (sourceB1734 + difference 3 0) sourceC1734) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1240) := by
    have ha : (tripleCharges (sourceA1734 + difference 0 3) (sourceB1734 + difference 3 0) sourceC1734) = raw24191 := by
      apply Matrix.ext; unfold tripleCharges sourceA1734 sourceB1734 sourceC1734 difference raw24191; decide +kernel
    rw [ha]
    exact (canonical24191 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1734 + difference 0 4) (sourceB1734 + difference 4 0) sourceC1734) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1237) := by
    have ha : (tripleCharges (sourceA1734 + difference 0 4) (sourceB1734 + difference 4 0) sourceC1734) = raw25309 := by
      apply Matrix.ext; unfold tripleCharges sourceA1734 sourceB1734 sourceC1734 difference raw25309; decide +kernel
    rw [ha]
    exact (canonical25309 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1734 + difference 0 5) (sourceB1734 + difference 5 0) sourceC1734) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1236) := by
    have ha : (tripleCharges (sourceA1734 + difference 0 5) (sourceB1734 + difference 5 0) sourceC1734) = raw25310 := by
      apply Matrix.ext; unfold tripleCharges sourceA1734 sourceB1734 sourceC1734 difference raw25310; decide +kernel
    rw [ha]
    exact (canonical25310 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1734 + difference 1 0) (sourceB1734 + difference 0 1) sourceC1734) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1468) := by
    have ha : (tripleCharges (sourceA1734 + difference 1 0) (sourceB1734 + difference 0 1) sourceC1734) = raw25311 := by
      apply Matrix.ext; unfold tripleCharges sourceA1734 sourceB1734 sourceC1734 difference raw25311; decide +kernel
    rw [ha]
    exact (canonical25311 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1734 + difference 1 2) (sourceB1734 + difference 2 1) sourceC1734) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1358) := by
    have ha : (tripleCharges (sourceA1734 + difference 1 2) (sourceB1734 + difference 2 1) sourceC1734) = raw25312 := by
      apply Matrix.ext; unfold tripleCharges sourceA1734 sourceB1734 sourceC1734 difference raw25312; decide +kernel
    rw [ha]
    exact (canonical25312 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1734 + difference 1 3) (sourceB1734 + difference 3 1) sourceC1734) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1370) := by
    have ha : (tripleCharges (sourceA1734 + difference 1 3) (sourceB1734 + difference 3 1) sourceC1734) = raw25313 := by
      apply Matrix.ext; unfold tripleCharges sourceA1734 sourceB1734 sourceC1734 difference raw25313; decide +kernel
    rw [ha]
    exact (canonical25313 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1734 + difference 1 4) (sourceB1734 + difference 4 1) sourceC1734) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1368) := by
    have ha : (tripleCharges (sourceA1734 + difference 1 4) (sourceB1734 + difference 4 1) sourceC1734) = raw25314 := by
      apply Matrix.ext; unfold tripleCharges sourceA1734 sourceB1734 sourceC1734 difference raw25314; decide +kernel
    rw [ha]
    exact (canonical25314 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1734 + difference 1 5) (sourceB1734 + difference 5 1) sourceC1734) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1367) := by
    have ha : (tripleCharges (sourceA1734 + difference 1 5) (sourceB1734 + difference 5 1) sourceC1734) = raw25315 := by
      apply Matrix.ext; unfold tripleCharges sourceA1734 sourceB1734 sourceC1734 difference raw25315; decide +kernel
    rw [ha]
    exact (canonical25315 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1734 + difference 2 0) (sourceB1734 + difference 0 2) sourceC1734) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1475) := by
    have ha : (tripleCharges (sourceA1734 + difference 2 0) (sourceB1734 + difference 0 2) sourceC1734) = raw25316 := by
      apply Matrix.ext; unfold tripleCharges sourceA1734 sourceB1734 sourceC1734 difference raw25316; decide +kernel
    rw [ha]
    exact (canonical25316 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1734 + difference 2 1) (sourceB1734 + difference 1 2) sourceC1734) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1411) := by
    have ha : (tripleCharges (sourceA1734 + difference 2 1) (sourceB1734 + difference 1 2) sourceC1734) = raw25317 := by
      apply Matrix.ext; unfold tripleCharges sourceA1734 sourceB1734 sourceC1734 difference raw25317; decide +kernel
    rw [ha]
    exact (canonical25317 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1734 + difference 2 3) (sourceB1734 + difference 3 2) sourceC1734) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1386) := by
    have ha : (tripleCharges (sourceA1734 + difference 2 3) (sourceB1734 + difference 3 2) sourceC1734) = raw25318 := by
      apply Matrix.ext; unfold tripleCharges sourceA1734 sourceB1734 sourceC1734 difference raw25318; decide +kernel
    rw [ha]
    exact (canonical25318 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1734 + difference 2 4) (sourceB1734 + difference 4 2) sourceC1734) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1384) := by
    have ha : (tripleCharges (sourceA1734 + difference 2 4) (sourceB1734 + difference 4 2) sourceC1734) = raw25319 := by
      apply Matrix.ext; unfold tripleCharges sourceA1734 sourceB1734 sourceC1734 difference raw25319; decide +kernel
    rw [ha]
    exact (canonical25319 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1734 + difference 2 5) (sourceB1734 + difference 5 2) sourceC1734) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1383) := by
    have ha : (tripleCharges (sourceA1734 + difference 2 5) (sourceB1734 + difference 5 2) sourceC1734) = raw25320 := by
      apply Matrix.ext; unfold tripleCharges sourceA1734 sourceB1734 sourceC1734 difference raw25320; decide +kernel
    rw [ha]
    exact (canonical25320 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1734 + difference 3 0) (sourceB1734 + difference 0 3) sourceC1734) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1480) := by
    have ha : (tripleCharges (sourceA1734 + difference 3 0) (sourceB1734 + difference 0 3) sourceC1734) = raw25321 := by
      apply Matrix.ext; unfold tripleCharges sourceA1734 sourceB1734 sourceC1734 difference raw25321; decide +kernel
    rw [ha]
    exact (canonical25321 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1734 + difference 3 1) (sourceB1734 + difference 1 3) sourceC1734) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1443) := by
    have ha : (tripleCharges (sourceA1734 + difference 3 1) (sourceB1734 + difference 1 3) sourceC1734) = raw25322 := by
      apply Matrix.ext; unfold tripleCharges sourceA1734 sourceB1734 sourceC1734 difference raw25322; decide +kernel
    rw [ha]
    exact (canonical25322 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1734 + difference 3 2) (sourceB1734 + difference 2 3) sourceC1734) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1393) := by
    have ha : (tripleCharges (sourceA1734 + difference 3 2) (sourceB1734 + difference 2 3) sourceC1734) = raw25323 := by
      apply Matrix.ext; unfold tripleCharges sourceA1734 sourceB1734 sourceC1734 difference raw25323; decide +kernel
    rw [ha]
    exact (canonical25323 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1734 + difference 3 4) (sourceB1734 + difference 4 3) sourceC1734) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1407) := by
    have ha : (tripleCharges (sourceA1734 + difference 3 4) (sourceB1734 + difference 4 3) sourceC1734) = raw25324 := by
      apply Matrix.ext; unfold tripleCharges sourceA1734 sourceB1734 sourceC1734 difference raw25324; decide +kernel
    rw [ha]
    exact (canonical25324 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1734 + difference 3 5) (sourceB1734 + difference 5 3) sourceC1734) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1406) := by
    have ha : (tripleCharges (sourceA1734 + difference 3 5) (sourceB1734 + difference 5 3) sourceC1734) = raw25325 := by
      apply Matrix.ext; unfold tripleCharges sourceA1734 sourceB1734 sourceC1734 difference raw25325; decide +kernel
    rw [ha]
    exact (canonical25325 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1734 + difference 4 0) (sourceB1734 + difference 0 4) sourceC1734) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1482) := by
    have ha : (tripleCharges (sourceA1734 + difference 4 0) (sourceB1734 + difference 0 4) sourceC1734) = raw25326 := by
      apply Matrix.ext; unfold tripleCharges sourceA1734 sourceB1734 sourceC1734 difference raw25326; decide +kernel
    rw [ha]
    exact (canonical25326 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1734 + difference 4 1) (sourceB1734 + difference 1 4) sourceC1734) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1447) := by
    have ha : (tripleCharges (sourceA1734 + difference 4 1) (sourceB1734 + difference 1 4) sourceC1734) = raw25327 := by
      apply Matrix.ext; unfold tripleCharges sourceA1734 sourceB1734 sourceC1734 difference raw25327; decide +kernel
    rw [ha]
    exact (canonical25327 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1734 + difference 4 2) (sourceB1734 + difference 2 4) sourceC1734) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1395) := by
    have ha : (tripleCharges (sourceA1734 + difference 4 2) (sourceB1734 + difference 2 4) sourceC1734) = raw25328 := by
      apply Matrix.ext; unfold tripleCharges sourceA1734 sourceB1734 sourceC1734 difference raw25328; decide +kernel
    rw [ha]
    exact (canonical25328 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1734 + difference 4 3) (sourceB1734 + difference 3 4) sourceC1734) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1411) := by
    have ha : (tripleCharges (sourceA1734 + difference 4 3) (sourceB1734 + difference 3 4) sourceC1734) = raw25329 := by
      apply Matrix.ext; unfold tripleCharges sourceA1734 sourceB1734 sourceC1734 difference raw25329; decide +kernel
    rw [ha]
    exact (canonical25329 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1734 + difference 4 5) (sourceB1734 + difference 5 4) sourceC1734) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1410) := by
    have ha : (tripleCharges (sourceA1734 + difference 4 5) (sourceB1734 + difference 5 4) sourceC1734) = raw25330 := by
      apply Matrix.ext; unfold tripleCharges sourceA1734 sourceB1734 sourceC1734 difference raw25330; decide +kernel
    rw [ha]
    exact (canonical25330 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1734 + difference 5 0) (sourceB1734 + difference 0 5) sourceC1734) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1483) := by
    have ha : (tripleCharges (sourceA1734 + difference 5 0) (sourceB1734 + difference 0 5) sourceC1734) = raw25331 := by
      apply Matrix.ext; unfold tripleCharges sourceA1734 sourceB1734 sourceC1734 difference raw25331; decide +kernel
    rw [ha]
    exact (canonical25331 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1734 + difference 5 1) (sourceB1734 + difference 1 5) sourceC1734) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1448) := by
    have ha : (tripleCharges (sourceA1734 + difference 5 1) (sourceB1734 + difference 1 5) sourceC1734) = raw24197 := by
      apply Matrix.ext; unfold tripleCharges sourceA1734 sourceB1734 sourceC1734 difference raw24197; decide +kernel
    rw [ha]
    exact (canonical24197 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1734 + difference 5 2) (sourceB1734 + difference 2 5) sourceC1734) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1396) := by
    have ha : (tripleCharges (sourceA1734 + difference 5 2) (sourceB1734 + difference 2 5) sourceC1734) = raw25332 := by
      apply Matrix.ext; unfold tripleCharges sourceA1734 sourceB1734 sourceC1734 difference raw25332; decide +kernel
    rw [ha]
    exact (canonical25332 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1734 + difference 5 3) (sourceB1734 + difference 3 5) sourceC1734) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1414) := by
    have ha : (tripleCharges (sourceA1734 + difference 5 3) (sourceB1734 + difference 3 5) sourceC1734) = raw24187 := by
      apply Matrix.ext; unfold tripleCharges sourceA1734 sourceB1734 sourceC1734 difference raw24187; decide +kernel
    rw [ha]
    exact (canonical24187 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1734 + difference 5 4) (sourceB1734 + difference 4 5) sourceC1734) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1412) := by
    have ha : (tripleCharges (sourceA1734 + difference 5 4) (sourceB1734 + difference 4 5) sourceC1734) = raw25333 := by
      apply Matrix.ext; unfold tripleCharges sourceA1734 sourceB1734 sourceC1734 difference raw25333; decide +kernel
    rw [ha]
    exact (canonical25333 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1734 sourceB1734 sourceC1734
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1734, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1735 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1735 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC1735 : Charge := ![3, -1, 0, -1, 1, -2]
def sourceForm1735 : Integer.Sparse Master := [(Sum.inr 1035, 1), (Sum.inr 2016, 1), (Sum.inr 2101, 1), (Sum.inr 2205, 1), (Sum.inr 2242, 1), (Sum.inr 2260, 1), (Sum.inr 4080, -1)]

theorem sourceEq1735 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1735 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1735 + difference 0 0) (sourceB1735 + difference 0 0) sourceC1735) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1035) := by
    have ha : (tripleCharges (sourceA1735 + difference 0 0) (sourceB1735 + difference 0 0) sourceC1735) = raw25334 := by
      apply Matrix.ext; unfold tripleCharges sourceA1735 sourceB1735 sourceC1735 difference raw25334; decide +kernel
    rw [ha]
    exact (canonical25334 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1735 + difference 0 1) (sourceB1735 + difference 1 0) sourceC1735) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2101) := by
    have ha : (tripleCharges (sourceA1735 + difference 0 1) (sourceB1735 + difference 1 0) sourceC1735) = raw25335 := by
      apply Matrix.ext; unfold tripleCharges sourceA1735 sourceB1735 sourceC1735 difference raw25335; decide +kernel
    rw [ha]
    exact (canonical25335 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1735 + difference 0 2) (sourceB1735 + difference 2 0) sourceC1735) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2016) := by
    have ha : (tripleCharges (sourceA1735 + difference 0 2) (sourceB1735 + difference 2 0) sourceC1735) = raw25336 := by
      apply Matrix.ext; unfold tripleCharges sourceA1735 sourceB1735 sourceC1735 difference raw25336; decide +kernel
    rw [ha]
    exact (canonical25336 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1735 + difference 0 3) (sourceB1735 + difference 3 0) sourceC1735) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2242) := by
    have ha : (tripleCharges (sourceA1735 + difference 0 3) (sourceB1735 + difference 3 0) sourceC1735) = raw25337 := by
      apply Matrix.ext; unfold tripleCharges sourceA1735 sourceB1735 sourceC1735 difference raw25337; decide +kernel
    rw [ha]
    exact (canonical25337 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1735 + difference 0 4) (sourceB1735 + difference 4 0) sourceC1735) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2205) := by
    have ha : (tripleCharges (sourceA1735 + difference 0 4) (sourceB1735 + difference 4 0) sourceC1735) = raw25338 := by
      apply Matrix.ext; unfold tripleCharges sourceA1735 sourceB1735 sourceC1735 difference raw25338; decide +kernel
    rw [ha]
    exact (canonical25338 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1735 + difference 0 5) (sourceB1735 + difference 5 0) sourceC1735) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2260) := by
    have ha : (tripleCharges (sourceA1735 + difference 0 5) (sourceB1735 + difference 5 0) sourceC1735) = raw25339 := by
      apply Matrix.ext; unfold tripleCharges sourceA1735 sourceB1735 sourceC1735 difference raw25339; decide +kernel
    rw [ha]
    exact (canonical25339 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1735 + sourceB1735) sourceC1735) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1735 + sourceB1735) sourceC1735) = raw25340 := by
      apply Matrix.ext; unfold doubleCharges sourceA1735 sourceB1735 sourceC1735 raw25340; decide +kernel
    rw [ha]
    exact (canonical25340 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1735 sourceB1735 sourceC1735
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1735, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1736 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1736 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceC1736 : Charge := ![3, -1, 0, -1, 1, -2]
def sourceForm1736 : Integer.Sparse Master := [(Sum.inr 593, 1), (Sum.inr 915, 1), (Sum.inr 1004, 1), (Sum.inr 1035, 2), (Sum.inr 1073, 1), (Sum.inr 4080, -1)]

theorem sourceEq1736 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1736 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1736 + difference 1 0) (sourceB1736 + difference 0 1) sourceC1736) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 593) := by
    have ha : (tripleCharges (sourceA1736 + difference 1 0) (sourceB1736 + difference 0 1) sourceC1736) = raw25341 := by
      apply Matrix.ext; unfold tripleCharges sourceA1736 sourceB1736 sourceC1736 difference raw25341; decide +kernel
    rw [ha]
    exact (canonical25341 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1736 + difference 1 1) (sourceB1736 + difference 1 1) sourceC1736) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1035) := by
    have ha : (tripleCharges (sourceA1736 + difference 1 1) (sourceB1736 + difference 1 1) sourceC1736) = raw25334 := by
      apply Matrix.ext; unfold tripleCharges sourceA1736 sourceB1736 sourceC1736 difference raw25334; decide +kernel
    rw [ha]
    exact (canonical25334 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1736 + difference 1 2) (sourceB1736 + difference 2 1) sourceC1736) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 915) := by
    have ha : (tripleCharges (sourceA1736 + difference 1 2) (sourceB1736 + difference 2 1) sourceC1736) = raw25342 := by
      apply Matrix.ext; unfold tripleCharges sourceA1736 sourceB1736 sourceC1736 difference raw25342; decide +kernel
    rw [ha]
    exact (canonical25342 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1736 + difference 1 3) (sourceB1736 + difference 3 1) sourceC1736) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1035) := by
    have ha : (tripleCharges (sourceA1736 + difference 1 3) (sourceB1736 + difference 3 1) sourceC1736) = raw25343 := by
      apply Matrix.ext; unfold tripleCharges sourceA1736 sourceB1736 sourceC1736 difference raw25343; decide +kernel
    rw [ha]
    exact (canonical25343 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1736 + difference 1 4) (sourceB1736 + difference 4 1) sourceC1736) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1004) := by
    have ha : (tripleCharges (sourceA1736 + difference 1 4) (sourceB1736 + difference 4 1) sourceC1736) = raw25344 := by
      apply Matrix.ext; unfold tripleCharges sourceA1736 sourceB1736 sourceC1736 difference raw25344; decide +kernel
    rw [ha]
    exact (canonical25344 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1736 + difference 1 5) (sourceB1736 + difference 5 1) sourceC1736) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1073) := by
    have ha : (tripleCharges (sourceA1736 + difference 1 5) (sourceB1736 + difference 5 1) sourceC1736) = raw25345 := by
      apply Matrix.ext; unfold tripleCharges sourceA1736 sourceB1736 sourceC1736 difference raw25345; decide +kernel
    rw [ha]
    exact (canonical25345 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1736 + sourceB1736) sourceC1736) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1736 + sourceB1736) sourceC1736) = raw25340 := by
      apply Matrix.ext; unfold doubleCharges sourceA1736 sourceB1736 sourceC1736 raw25340; decide +kernel
    rw [ha]
    exact (canonical25340 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1736 sourceB1736 sourceC1736
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1736, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1737 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceB1737 : Charge := ![3, -1, 0, -1, 1, -2]
def sourceC1737 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1737 : Integer.Sparse Master := [(Sum.inr 730, 1), (Sum.inr 733, 1), (Sum.inr 734, 1), (Sum.inr 738, 1), (Sum.inr 806, 1), (Sum.inr 1645, 1), (Sum.inr 4069, -1)]

theorem sourceEq1737 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1737 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1737 + difference 0 0) (sourceB1737 + difference 0 0) sourceC1737) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1645) := by
    have ha : (tripleCharges (sourceA1737 + difference 0 0) (sourceB1737 + difference 0 0) sourceC1737) = raw25346 := by
      apply Matrix.ext; unfold tripleCharges sourceA1737 sourceB1737 sourceC1737 difference raw25346; decide +kernel
    rw [ha]
    exact (canonical25346 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1737 + difference 1 0) (sourceB1737 + difference 0 1) sourceC1737) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 738) := by
    have ha : (tripleCharges (sourceA1737 + difference 1 0) (sourceB1737 + difference 0 1) sourceC1737) = raw25347 := by
      apply Matrix.ext; unfold tripleCharges sourceA1737 sourceB1737 sourceC1737 difference raw25347; decide +kernel
    rw [ha]
    exact (canonical25347 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1737 + difference 2 0) (sourceB1737 + difference 0 2) sourceC1737) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 730) := by
    have ha : (tripleCharges (sourceA1737 + difference 2 0) (sourceB1737 + difference 0 2) sourceC1737) = raw25348 := by
      apply Matrix.ext; unfold tripleCharges sourceA1737 sourceB1737 sourceC1737 difference raw25348; decide +kernel
    rw [ha]
    exact (canonical25348 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1737 + difference 3 0) (sourceB1737 + difference 0 3) sourceC1737) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 734) := by
    have ha : (tripleCharges (sourceA1737 + difference 3 0) (sourceB1737 + difference 0 3) sourceC1737) = raw25349 := by
      apply Matrix.ext; unfold tripleCharges sourceA1737 sourceB1737 sourceC1737 difference raw25349; decide +kernel
    rw [ha]
    exact (canonical25349 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1737 + difference 4 0) (sourceB1737 + difference 0 4) sourceC1737) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 806) := by
    have ha : (tripleCharges (sourceA1737 + difference 4 0) (sourceB1737 + difference 0 4) sourceC1737) = raw25350 := by
      apply Matrix.ext; unfold tripleCharges sourceA1737 sourceB1737 sourceC1737 difference raw25350; decide +kernel
    rw [ha]
    exact (canonical25350 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1737 + difference 5 0) (sourceB1737 + difference 0 5) sourceC1737) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 733) := by
    have ha : (tripleCharges (sourceA1737 + difference 5 0) (sourceB1737 + difference 0 5) sourceC1737) = raw25351 := by
      apply Matrix.ext; unfold tripleCharges sourceA1737 sourceB1737 sourceC1737 difference raw25351; decide +kernel
    rw [ha]
    exact (canonical25351 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1737 + sourceB1737) sourceC1737) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1737 + sourceB1737) sourceC1737) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1737 sourceB1737 sourceC1737 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1737 sourceB1737 sourceC1737
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1737, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1738 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1738 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC1738 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceForm1738 : Integer.Sparse Master := [(Sum.inr 4149, 1), (Sum.inr 4151, 1), (Sum.inr 4154, 2), (Sum.inr 4172, 1), (Sum.inr 4326, 1), (Sum.inr 4328, 2), (Sum.inr 4341, 1), (Sum.inr 4363, 1), (Sum.inr 4365, 1), (Sum.inr 4368, 2), (Sum.inr 4455, 1), (Sum.inr 4457, 2), (Sum.inr 4459, 2), (Sum.inr 4460, 2), (Sum.inr 4466, 2), (Sum.inr 4495, 1), (Sum.inr 4498, 2), (Sum.inr 4801, 1), (Sum.inr 4865, 1), (Sum.inr 4888, 1), (Sum.inr 4894, 2)]

theorem sourceEq1738 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1738 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1738 + difference 0 1) (sourceB1738 + difference 1 0) sourceC1738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4865) := by
    have ha : (tripleCharges (sourceA1738 + difference 0 1) (sourceB1738 + difference 1 0) sourceC1738) = raw11487 := by
      apply Matrix.ext; unfold tripleCharges sourceA1738 sourceB1738 sourceC1738 difference raw11487; decide +kernel
    rw [ha]
    exact (canonical11487 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1738 + difference 0 2) (sourceB1738 + difference 2 0) sourceC1738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4801) := by
    have ha : (tripleCharges (sourceA1738 + difference 0 2) (sourceB1738 + difference 2 0) sourceC1738) = raw11488 := by
      apply Matrix.ext; unfold tripleCharges sourceA1738 sourceB1738 sourceC1738 difference raw11488; decide +kernel
    rw [ha]
    exact (canonical11488 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1738 + difference 0 3) (sourceB1738 + difference 3 0) sourceC1738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4894) := by
    have ha : (tripleCharges (sourceA1738 + difference 0 3) (sourceB1738 + difference 3 0) sourceC1738) = raw21373 := by
      apply Matrix.ext; unfold tripleCharges sourceA1738 sourceB1738 sourceC1738 difference raw21373; decide +kernel
    rw [ha]
    exact (canonical21373 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1738 + difference 0 4) (sourceB1738 + difference 4 0) sourceC1738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4894) := by
    have ha : (tripleCharges (sourceA1738 + difference 0 4) (sourceB1738 + difference 4 0) sourceC1738) = raw11489 := by
      apply Matrix.ext; unfold tripleCharges sourceA1738 sourceB1738 sourceC1738 difference raw11489; decide +kernel
    rw [ha]
    exact (canonical11489 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1738 + difference 0 5) (sourceB1738 + difference 5 0) sourceC1738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA1738 + difference 0 5) (sourceB1738 + difference 5 0) sourceC1738) = raw11490 := by
      apply Matrix.ext; unfold tripleCharges sourceA1738 sourceB1738 sourceC1738 difference raw11490; decide +kernel
    rw [ha]
    exact (canonical11490 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1738 + difference 1 0) (sourceB1738 + difference 0 1) sourceC1738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4172) := by
    have ha : (tripleCharges (sourceA1738 + difference 1 0) (sourceB1738 + difference 0 1) sourceC1738) = raw25352 := by
      apply Matrix.ext; unfold tripleCharges sourceA1738 sourceB1738 sourceC1738 difference raw25352; decide +kernel
    rw [ha]
    exact (canonical25352 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1738 + difference 1 2) (sourceB1738 + difference 2 1) sourceC1738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4341) := by
    have ha : (tripleCharges (sourceA1738 + difference 1 2) (sourceB1738 + difference 2 1) sourceC1738) = raw25353 := by
      apply Matrix.ext; unfold tripleCharges sourceA1738 sourceB1738 sourceC1738 difference raw25353; decide +kernel
    rw [ha]
    exact (canonical25353 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1738 + difference 1 3) (sourceB1738 + difference 3 1) sourceC1738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4498) := by
    have ha : (tripleCharges (sourceA1738 + difference 1 3) (sourceB1738 + difference 3 1) sourceC1738) = raw11476 := by
      apply Matrix.ext; unfold tripleCharges sourceA1738 sourceB1738 sourceC1738 difference raw11476; decide +kernel
    rw [ha]
    exact (canonical11476 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1738 + difference 1 4) (sourceB1738 + difference 4 1) sourceC1738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4498) := by
    have ha : (tripleCharges (sourceA1738 + difference 1 4) (sourceB1738 + difference 4 1) sourceC1738) = raw25354 := by
      apply Matrix.ext; unfold tripleCharges sourceA1738 sourceB1738 sourceC1738 difference raw25354; decide +kernel
    rw [ha]
    exact (canonical25354 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1738 + difference 1 5) (sourceB1738 + difference 5 1) sourceC1738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4495) := by
    have ha : (tripleCharges (sourceA1738 + difference 1 5) (sourceB1738 + difference 5 1) sourceC1738) = raw25355 := by
      apply Matrix.ext; unfold tripleCharges sourceA1738 sourceB1738 sourceC1738 difference raw25355; decide +kernel
    rw [ha]
    exact (canonical25355 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1738 + difference 2 0) (sourceB1738 + difference 0 2) sourceC1738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4149) := by
    have ha : (tripleCharges (sourceA1738 + difference 2 0) (sourceB1738 + difference 0 2) sourceC1738) = raw25356 := by
      apply Matrix.ext; unfold tripleCharges sourceA1738 sourceB1738 sourceC1738 difference raw25356; decide +kernel
    rw [ha]
    exact (canonical25356 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1738 + difference 2 1) (sourceB1738 + difference 1 2) sourceC1738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4363) := by
    have ha : (tripleCharges (sourceA1738 + difference 2 1) (sourceB1738 + difference 1 2) sourceC1738) = raw25357 := by
      apply Matrix.ext; unfold tripleCharges sourceA1738 sourceB1738 sourceC1738 difference raw25357; decide +kernel
    rw [ha]
    exact (canonical25357 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1738 + difference 2 3) (sourceB1738 + difference 3 2) sourceC1738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4457) := by
    have ha : (tripleCharges (sourceA1738 + difference 2 3) (sourceB1738 + difference 3 2) sourceC1738) = raw11481 := by
      apply Matrix.ext; unfold tripleCharges sourceA1738 sourceB1738 sourceC1738 difference raw11481; decide +kernel
    rw [ha]
    exact (canonical11481 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1738 + difference 2 4) (sourceB1738 + difference 4 2) sourceC1738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4457) := by
    have ha : (tripleCharges (sourceA1738 + difference 2 4) (sourceB1738 + difference 4 2) sourceC1738) = raw25358 := by
      apply Matrix.ext; unfold tripleCharges sourceA1738 sourceB1738 sourceC1738 difference raw25358; decide +kernel
    rw [ha]
    exact (canonical25358 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1738 + difference 2 5) (sourceB1738 + difference 5 2) sourceC1738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4455) := by
    have ha : (tripleCharges (sourceA1738 + difference 2 5) (sourceB1738 + difference 5 2) sourceC1738) = raw25359 := by
      apply Matrix.ext; unfold tripleCharges sourceA1738 sourceB1738 sourceC1738 difference raw25359; decide +kernel
    rw [ha]
    exact (canonical25359 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1738 + difference 3 0) (sourceB1738 + difference 0 3) sourceC1738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4154) := by
    have ha : (tripleCharges (sourceA1738 + difference 3 0) (sourceB1738 + difference 0 3) sourceC1738) = raw25360 := by
      apply Matrix.ext; unfold tripleCharges sourceA1738 sourceB1738 sourceC1738 difference raw25360; decide +kernel
    rw [ha]
    exact (canonical25360 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1738 + difference 3 1) (sourceB1738 + difference 1 3) sourceC1738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4368) := by
    have ha : (tripleCharges (sourceA1738 + difference 3 1) (sourceB1738 + difference 1 3) sourceC1738) = raw25361 := by
      apply Matrix.ext; unfold tripleCharges sourceA1738 sourceB1738 sourceC1738 difference raw25361; decide +kernel
    rw [ha]
    exact (canonical25361 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1738 + difference 3 2) (sourceB1738 + difference 2 3) sourceC1738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4328) := by
    have ha : (tripleCharges (sourceA1738 + difference 3 2) (sourceB1738 + difference 2 3) sourceC1738) = raw25362 := by
      apply Matrix.ext; unfold tripleCharges sourceA1738 sourceB1738 sourceC1738 difference raw25362; decide +kernel
    rw [ha]
    exact (canonical25362 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1738 + difference 3 4) (sourceB1738 + difference 4 3) sourceC1738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4466) := by
    have ha : (tripleCharges (sourceA1738 + difference 3 4) (sourceB1738 + difference 4 3) sourceC1738) = raw25363 := by
      apply Matrix.ext; unfold tripleCharges sourceA1738 sourceB1738 sourceC1738 difference raw25363; decide +kernel
    rw [ha]
    exact (canonical25363 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1738 + difference 3 5) (sourceB1738 + difference 5 3) sourceC1738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4459) := by
    have ha : (tripleCharges (sourceA1738 + difference 3 5) (sourceB1738 + difference 5 3) sourceC1738) = raw25364 := by
      apply Matrix.ext; unfold tripleCharges sourceA1738 sourceB1738 sourceC1738 difference raw25364; decide +kernel
    rw [ha]
    exact (canonical25364 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1738 + difference 4 0) (sourceB1738 + difference 0 4) sourceC1738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4154) := by
    have ha : (tripleCharges (sourceA1738 + difference 4 0) (sourceB1738 + difference 0 4) sourceC1738) = raw25365 := by
      apply Matrix.ext; unfold tripleCharges sourceA1738 sourceB1738 sourceC1738 difference raw25365; decide +kernel
    rw [ha]
    exact (canonical25365 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1738 + difference 4 1) (sourceB1738 + difference 1 4) sourceC1738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4368) := by
    have ha : (tripleCharges (sourceA1738 + difference 4 1) (sourceB1738 + difference 1 4) sourceC1738) = raw25366 := by
      apply Matrix.ext; unfold tripleCharges sourceA1738 sourceB1738 sourceC1738 difference raw25366; decide +kernel
    rw [ha]
    exact (canonical25366 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1738 + difference 4 2) (sourceB1738 + difference 2 4) sourceC1738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4328) := by
    have ha : (tripleCharges (sourceA1738 + difference 4 2) (sourceB1738 + difference 2 4) sourceC1738) = raw25367 := by
      apply Matrix.ext; unfold tripleCharges sourceA1738 sourceB1738 sourceC1738 difference raw25367; decide +kernel
    rw [ha]
    exact (canonical25367 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1738 + difference 4 3) (sourceB1738 + difference 3 4) sourceC1738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4466) := by
    have ha : (tripleCharges (sourceA1738 + difference 4 3) (sourceB1738 + difference 3 4) sourceC1738) = raw11491 := by
      apply Matrix.ext; unfold tripleCharges sourceA1738 sourceB1738 sourceC1738 difference raw11491; decide +kernel
    rw [ha]
    exact (canonical11491 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1738 + difference 4 5) (sourceB1738 + difference 5 4) sourceC1738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4459) := by
    have ha : (tripleCharges (sourceA1738 + difference 4 5) (sourceB1738 + difference 5 4) sourceC1738) = raw25368 := by
      apply Matrix.ext; unfold tripleCharges sourceA1738 sourceB1738 sourceC1738 difference raw25368; decide +kernel
    rw [ha]
    exact (canonical25368 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1738 + difference 5 0) (sourceB1738 + difference 0 5) sourceC1738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4151) := by
    have ha : (tripleCharges (sourceA1738 + difference 5 0) (sourceB1738 + difference 0 5) sourceC1738) = raw21382 := by
      apply Matrix.ext; unfold tripleCharges sourceA1738 sourceB1738 sourceC1738 difference raw21382; decide +kernel
    rw [ha]
    exact (canonical21382 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1738 + difference 5 1) (sourceB1738 + difference 1 5) sourceC1738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4365) := by
    have ha : (tripleCharges (sourceA1738 + difference 5 1) (sourceB1738 + difference 1 5) sourceC1738) = raw21383 := by
      apply Matrix.ext; unfold tripleCharges sourceA1738 sourceB1738 sourceC1738 difference raw21383; decide +kernel
    rw [ha]
    exact (canonical21383 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1738 + difference 5 2) (sourceB1738 + difference 2 5) sourceC1738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4326) := by
    have ha : (tripleCharges (sourceA1738 + difference 5 2) (sourceB1738 + difference 2 5) sourceC1738) = raw21384 := by
      apply Matrix.ext; unfold tripleCharges sourceA1738 sourceB1738 sourceC1738 difference raw21384; decide +kernel
    rw [ha]
    exact (canonical21384 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1738 + difference 5 3) (sourceB1738 + difference 3 5) sourceC1738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4460) := by
    have ha : (tripleCharges (sourceA1738 + difference 5 3) (sourceB1738 + difference 3 5) sourceC1738) = raw11496 := by
      apply Matrix.ext; unfold tripleCharges sourceA1738 sourceB1738 sourceC1738 difference raw11496; decide +kernel
    rw [ha]
    exact (canonical11496 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1738 + difference 5 4) (sourceB1738 + difference 4 5) sourceC1738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4460) := by
    have ha : (tripleCharges (sourceA1738 + difference 5 4) (sourceB1738 + difference 4 5) sourceC1738) = raw21385 := by
      apply Matrix.ext; unfold tripleCharges sourceA1738 sourceB1738 sourceC1738 difference raw21385; decide +kernel
    rw [ha]
    exact (canonical21385 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1738 sourceB1738 sourceC1738
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1738, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1739 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1739 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC1739 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceForm1739 : Integer.Sparse Master := [(Sum.inr 629, 1), (Sum.inr 630, 1), (Sum.inr 631, 2), (Sum.inr 646, 1), (Sum.inr 1319, 1), (Sum.inr 1320, 1), (Sum.inr 1321, 2), (Sum.inr 1329, 1), (Sum.inr 1330, 2), (Sum.inr 1341, 1), (Sum.inr 1405, 1), (Sum.inr 1406, 2), (Sum.inr 1414, 2), (Sum.inr 1416, 2), (Sum.inr 1419, 2), (Sum.inr 1441, 1), (Sum.inr 1448, 2), (Sum.inr 3185, 1), (Sum.inr 3205, 1), (Sum.inr 3227, 1), (Sum.inr 3230, 2)]

theorem sourceEq1739 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1739 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1739 + difference 0 1) (sourceB1739 + difference 1 0) sourceC1739) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3185) := by
    have ha : (tripleCharges (sourceA1739 + difference 0 1) (sourceB1739 + difference 1 0) sourceC1739) = raw25369 := by
      apply Matrix.ext; unfold tripleCharges sourceA1739 sourceB1739 sourceC1739 difference raw25369; decide +kernel
    rw [ha]
    exact (canonical25369 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1739 + difference 0 2) (sourceB1739 + difference 2 0) sourceC1739) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3205) := by
    have ha : (tripleCharges (sourceA1739 + difference 0 2) (sourceB1739 + difference 2 0) sourceC1739) = raw25370 := by
      apply Matrix.ext; unfold tripleCharges sourceA1739 sourceB1739 sourceC1739 difference raw25370; decide +kernel
    rw [ha]
    exact (canonical25370 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1739 + difference 0 3) (sourceB1739 + difference 3 0) sourceC1739) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3230) := by
    have ha : (tripleCharges (sourceA1739 + difference 0 3) (sourceB1739 + difference 3 0) sourceC1739) = raw21399 := by
      apply Matrix.ext; unfold tripleCharges sourceA1739 sourceB1739 sourceC1739 difference raw21399; decide +kernel
    rw [ha]
    exact (canonical21399 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1739 + difference 0 4) (sourceB1739 + difference 4 0) sourceC1739) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3230) := by
    have ha : (tripleCharges (sourceA1739 + difference 0 4) (sourceB1739 + difference 4 0) sourceC1739) = raw25371 := by
      apply Matrix.ext; unfold tripleCharges sourceA1739 sourceB1739 sourceC1739 difference raw25371; decide +kernel
    rw [ha]
    exact (canonical25371 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1739 + difference 0 5) (sourceB1739 + difference 5 0) sourceC1739) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3227) := by
    have ha : (tripleCharges (sourceA1739 + difference 0 5) (sourceB1739 + difference 5 0) sourceC1739) = raw25372 := by
      apply Matrix.ext; unfold tripleCharges sourceA1739 sourceB1739 sourceC1739 difference raw25372; decide +kernel
    rw [ha]
    exact (canonical25372 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1739 + difference 1 0) (sourceB1739 + difference 0 1) sourceC1739) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 646) := by
    have ha : (tripleCharges (sourceA1739 + difference 1 0) (sourceB1739 + difference 0 1) sourceC1739) = raw25373 := by
      apply Matrix.ext; unfold tripleCharges sourceA1739 sourceB1739 sourceC1739 difference raw25373; decide +kernel
    rw [ha]
    exact (canonical25373 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1739 + difference 1 2) (sourceB1739 + difference 2 1) sourceC1739) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1341) := by
    have ha : (tripleCharges (sourceA1739 + difference 1 2) (sourceB1739 + difference 2 1) sourceC1739) = raw25374 := by
      apply Matrix.ext; unfold tripleCharges sourceA1739 sourceB1739 sourceC1739 difference raw25374; decide +kernel
    rw [ha]
    exact (canonical25374 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1739 + difference 1 3) (sourceB1739 + difference 3 1) sourceC1739) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1448) := by
    have ha : (tripleCharges (sourceA1739 + difference 1 3) (sourceB1739 + difference 3 1) sourceC1739) = raw21404 := by
      apply Matrix.ext; unfold tripleCharges sourceA1739 sourceB1739 sourceC1739 difference raw21404; decide +kernel
    rw [ha]
    exact (canonical21404 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1739 + difference 1 4) (sourceB1739 + difference 4 1) sourceC1739) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1448) := by
    have ha : (tripleCharges (sourceA1739 + difference 1 4) (sourceB1739 + difference 4 1) sourceC1739) = raw25375 := by
      apply Matrix.ext; unfold tripleCharges sourceA1739 sourceB1739 sourceC1739 difference raw25375; decide +kernel
    rw [ha]
    exact (canonical25375 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1739 + difference 1 5) (sourceB1739 + difference 5 1) sourceC1739) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1441) := by
    have ha : (tripleCharges (sourceA1739 + difference 1 5) (sourceB1739 + difference 5 1) sourceC1739) = raw25376 := by
      apply Matrix.ext; unfold tripleCharges sourceA1739 sourceB1739 sourceC1739 difference raw25376; decide +kernel
    rw [ha]
    exact (canonical25376 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1739 + difference 2 0) (sourceB1739 + difference 0 2) sourceC1739) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 629) := by
    have ha : (tripleCharges (sourceA1739 + difference 2 0) (sourceB1739 + difference 0 2) sourceC1739) = raw25377 := by
      apply Matrix.ext; unfold tripleCharges sourceA1739 sourceB1739 sourceC1739 difference raw25377; decide +kernel
    rw [ha]
    exact (canonical25377 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1739 + difference 2 1) (sourceB1739 + difference 1 2) sourceC1739) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1319) := by
    have ha : (tripleCharges (sourceA1739 + difference 2 1) (sourceB1739 + difference 1 2) sourceC1739) = raw25378 := by
      apply Matrix.ext; unfold tripleCharges sourceA1739 sourceB1739 sourceC1739 difference raw25378; decide +kernel
    rw [ha]
    exact (canonical25378 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1739 + difference 2 3) (sourceB1739 + difference 3 2) sourceC1739) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1414) := by
    have ha : (tripleCharges (sourceA1739 + difference 2 3) (sourceB1739 + difference 3 2) sourceC1739) = raw21409 := by
      apply Matrix.ext; unfold tripleCharges sourceA1739 sourceB1739 sourceC1739 difference raw21409; decide +kernel
    rw [ha]
    exact (canonical21409 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1739 + difference 2 4) (sourceB1739 + difference 4 2) sourceC1739) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1414) := by
    have ha : (tripleCharges (sourceA1739 + difference 2 4) (sourceB1739 + difference 4 2) sourceC1739) = raw25379 := by
      apply Matrix.ext; unfold tripleCharges sourceA1739 sourceB1739 sourceC1739 difference raw25379; decide +kernel
    rw [ha]
    exact (canonical25379 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1739 + difference 2 5) (sourceB1739 + difference 5 2) sourceC1739) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1405) := by
    have ha : (tripleCharges (sourceA1739 + difference 2 5) (sourceB1739 + difference 5 2) sourceC1739) = raw25380 := by
      apply Matrix.ext; unfold tripleCharges sourceA1739 sourceB1739 sourceC1739 difference raw25380; decide +kernel
    rw [ha]
    exact (canonical25380 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1739 + difference 3 0) (sourceB1739 + difference 0 3) sourceC1739) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 631) := by
    have ha : (tripleCharges (sourceA1739 + difference 3 0) (sourceB1739 + difference 0 3) sourceC1739) = raw25381 := by
      apply Matrix.ext; unfold tripleCharges sourceA1739 sourceB1739 sourceC1739 difference raw25381; decide +kernel
    rw [ha]
    exact (canonical25381 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1739 + difference 3 1) (sourceB1739 + difference 1 3) sourceC1739) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1321) := by
    have ha : (tripleCharges (sourceA1739 + difference 3 1) (sourceB1739 + difference 1 3) sourceC1739) = raw25382 := by
      apply Matrix.ext; unfold tripleCharges sourceA1739 sourceB1739 sourceC1739 difference raw25382; decide +kernel
    rw [ha]
    exact (canonical25382 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1739 + difference 3 2) (sourceB1739 + difference 2 3) sourceC1739) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1330) := by
    have ha : (tripleCharges (sourceA1739 + difference 3 2) (sourceB1739 + difference 2 3) sourceC1739) = raw25383 := by
      apply Matrix.ext; unfold tripleCharges sourceA1739 sourceB1739 sourceC1739 difference raw25383; decide +kernel
    rw [ha]
    exact (canonical25383 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1739 + difference 3 4) (sourceB1739 + difference 4 3) sourceC1739) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1419) := by
    have ha : (tripleCharges (sourceA1739 + difference 3 4) (sourceB1739 + difference 4 3) sourceC1739) = raw25384 := by
      apply Matrix.ext; unfold tripleCharges sourceA1739 sourceB1739 sourceC1739 difference raw25384; decide +kernel
    rw [ha]
    exact (canonical25384 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1739 + difference 3 5) (sourceB1739 + difference 5 3) sourceC1739) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1406) := by
    have ha : (tripleCharges (sourceA1739 + difference 3 5) (sourceB1739 + difference 5 3) sourceC1739) = raw25385 := by
      apply Matrix.ext; unfold tripleCharges sourceA1739 sourceB1739 sourceC1739 difference raw25385; decide +kernel
    rw [ha]
    exact (canonical25385 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1739 + difference 4 0) (sourceB1739 + difference 0 4) sourceC1739) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 631) := by
    have ha : (tripleCharges (sourceA1739 + difference 4 0) (sourceB1739 + difference 0 4) sourceC1739) = raw25386 := by
      apply Matrix.ext; unfold tripleCharges sourceA1739 sourceB1739 sourceC1739 difference raw25386; decide +kernel
    rw [ha]
    exact (canonical25386 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1739 + difference 4 1) (sourceB1739 + difference 1 4) sourceC1739) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1321) := by
    have ha : (tripleCharges (sourceA1739 + difference 4 1) (sourceB1739 + difference 1 4) sourceC1739) = raw25387 := by
      apply Matrix.ext; unfold tripleCharges sourceA1739 sourceB1739 sourceC1739 difference raw25387; decide +kernel
    rw [ha]
    exact (canonical25387 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1739 + difference 4 2) (sourceB1739 + difference 2 4) sourceC1739) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1330) := by
    have ha : (tripleCharges (sourceA1739 + difference 4 2) (sourceB1739 + difference 2 4) sourceC1739) = raw25388 := by
      apply Matrix.ext; unfold tripleCharges sourceA1739 sourceB1739 sourceC1739 difference raw25388; decide +kernel
    rw [ha]
    exact (canonical25388 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1739 + difference 4 3) (sourceB1739 + difference 3 4) sourceC1739) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1419) := by
    have ha : (tripleCharges (sourceA1739 + difference 4 3) (sourceB1739 + difference 3 4) sourceC1739) = raw21419 := by
      apply Matrix.ext; unfold tripleCharges sourceA1739 sourceB1739 sourceC1739 difference raw21419; decide +kernel
    rw [ha]
    exact (canonical21419 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1739 + difference 4 5) (sourceB1739 + difference 5 4) sourceC1739) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1406) := by
    have ha : (tripleCharges (sourceA1739 + difference 4 5) (sourceB1739 + difference 5 4) sourceC1739) = raw25389 := by
      apply Matrix.ext; unfold tripleCharges sourceA1739 sourceB1739 sourceC1739 difference raw25389; decide +kernel
    rw [ha]
    exact (canonical25389 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1739 + difference 5 0) (sourceB1739 + difference 0 5) sourceC1739) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 630) := by
    have ha : (tripleCharges (sourceA1739 + difference 5 0) (sourceB1739 + difference 0 5) sourceC1739) = raw21410 := by
      apply Matrix.ext; unfold tripleCharges sourceA1739 sourceB1739 sourceC1739 difference raw21410; decide +kernel
    rw [ha]
    exact (canonical21410 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1739 + difference 5 1) (sourceB1739 + difference 1 5) sourceC1739) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1320) := by
    have ha : (tripleCharges (sourceA1739 + difference 5 1) (sourceB1739 + difference 1 5) sourceC1739) = raw21411 := by
      apply Matrix.ext; unfold tripleCharges sourceA1739 sourceB1739 sourceC1739 difference raw21411; decide +kernel
    rw [ha]
    exact (canonical21411 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1739 + difference 5 2) (sourceB1739 + difference 2 5) sourceC1739) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1329) := by
    have ha : (tripleCharges (sourceA1739 + difference 5 2) (sourceB1739 + difference 2 5) sourceC1739) = raw21412 := by
      apply Matrix.ext; unfold tripleCharges sourceA1739 sourceB1739 sourceC1739 difference raw21412; decide +kernel
    rw [ha]
    exact (canonical21412 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1739 + difference 5 3) (sourceB1739 + difference 3 5) sourceC1739) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1416) := by
    have ha : (tripleCharges (sourceA1739 + difference 5 3) (sourceB1739 + difference 3 5) sourceC1739) = raw25390 := by
      apply Matrix.ext; unfold tripleCharges sourceA1739 sourceB1739 sourceC1739 difference raw25390; decide +kernel
    rw [ha]
    exact (canonical25390 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1739 + difference 5 4) (sourceB1739 + difference 4 5) sourceC1739) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1416) := by
    have ha : (tripleCharges (sourceA1739 + difference 5 4) (sourceB1739 + difference 4 5) sourceC1739) = raw21413 := by
      apply Matrix.ext; unfold tripleCharges sourceA1739 sourceB1739 sourceC1739 difference raw21413; decide +kernel
    rw [ha]
    exact (canonical21413 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1739 sourceB1739 sourceC1739
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1739, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1740 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1740 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC1740 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceForm1740 : Integer.Sparse Master := [(Sum.inr 1501, 1), (Sum.inr 1505, 1), (Sum.inr 1507, 1), (Sum.inr 1511, 2), (Sum.inr 1663, 1), (Sum.inr 1664, 1), (Sum.inr 1667, 2), (Sum.inr 1697, 1), (Sum.inr 1698, 1), (Sum.inr 1704, 1), (Sum.inr 1707, 2), (Sum.inr 1708, 1), (Sum.inr 1712, 2), (Sum.inr 1714, 2), (Sum.inr 1725, 2), (Sum.inr 1727, 2), (Sum.inr 1738, 2), (Sum.inr 2190, 1), (Sum.inr 2242, 1), (Sum.inr 2244, 1), (Sum.inr 2264, 2)]

theorem sourceEq1740 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1740 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1740 + difference 0 1) (sourceB1740 + difference 1 0) sourceC1740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2242) := by
    have ha : (tripleCharges (sourceA1740 + difference 0 1) (sourceB1740 + difference 1 0) sourceC1740) = raw25391 := by
      apply Matrix.ext; unfold tripleCharges sourceA1740 sourceB1740 sourceC1740 difference raw25391; decide +kernel
    rw [ha]
    exact (canonical25391 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1740 + difference 0 2) (sourceB1740 + difference 2 0) sourceC1740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2190) := by
    have ha : (tripleCharges (sourceA1740 + difference 0 2) (sourceB1740 + difference 2 0) sourceC1740) = raw25392 := by
      apply Matrix.ext; unfold tripleCharges sourceA1740 sourceB1740 sourceC1740 difference raw25392; decide +kernel
    rw [ha]
    exact (canonical25392 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1740 + difference 0 3) (sourceB1740 + difference 3 0) sourceC1740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2264) := by
    have ha : (tripleCharges (sourceA1740 + difference 0 3) (sourceB1740 + difference 3 0) sourceC1740) = raw21429 := by
      apply Matrix.ext; unfold tripleCharges sourceA1740 sourceB1740 sourceC1740 difference raw21429; decide +kernel
    rw [ha]
    exact (canonical21429 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1740 + difference 0 4) (sourceB1740 + difference 4 0) sourceC1740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2264) := by
    have ha : (tripleCharges (sourceA1740 + difference 0 4) (sourceB1740 + difference 4 0) sourceC1740) = raw25393 := by
      apply Matrix.ext; unfold tripleCharges sourceA1740 sourceB1740 sourceC1740 difference raw25393; decide +kernel
    rw [ha]
    exact (canonical25393 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1740 + difference 0 5) (sourceB1740 + difference 5 0) sourceC1740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2244) := by
    have ha : (tripleCharges (sourceA1740 + difference 0 5) (sourceB1740 + difference 5 0) sourceC1740) = raw25394 := by
      apply Matrix.ext; unfold tripleCharges sourceA1740 sourceB1740 sourceC1740 difference raw25394; decide +kernel
    rw [ha]
    exact (canonical25394 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1740 + difference 1 0) (sourceB1740 + difference 0 1) sourceC1740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1507) := by
    have ha : (tripleCharges (sourceA1740 + difference 1 0) (sourceB1740 + difference 0 1) sourceC1740) = raw25395 := by
      apply Matrix.ext; unfold tripleCharges sourceA1740 sourceB1740 sourceC1740 difference raw25395; decide +kernel
    rw [ha]
    exact (canonical25395 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1740 + difference 1 2) (sourceB1740 + difference 2 1) sourceC1740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1664) := by
    have ha : (tripleCharges (sourceA1740 + difference 1 2) (sourceB1740 + difference 2 1) sourceC1740) = raw25396 := by
      apply Matrix.ext; unfold tripleCharges sourceA1740 sourceB1740 sourceC1740 difference raw25396; decide +kernel
    rw [ha]
    exact (canonical25396 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1740 + difference 1 3) (sourceB1740 + difference 3 1) sourceC1740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1727) := by
    have ha : (tripleCharges (sourceA1740 + difference 1 3) (sourceB1740 + difference 3 1) sourceC1740) = raw21434 := by
      apply Matrix.ext; unfold tripleCharges sourceA1740 sourceB1740 sourceC1740 difference raw21434; decide +kernel
    rw [ha]
    exact (canonical21434 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1740 + difference 1 4) (sourceB1740 + difference 4 1) sourceC1740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1727) := by
    have ha : (tripleCharges (sourceA1740 + difference 1 4) (sourceB1740 + difference 4 1) sourceC1740) = raw25397 := by
      apply Matrix.ext; unfold tripleCharges sourceA1740 sourceB1740 sourceC1740 difference raw25397; decide +kernel
    rw [ha]
    exact (canonical25397 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1740 + difference 1 5) (sourceB1740 + difference 5 1) sourceC1740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1708) := by
    have ha : (tripleCharges (sourceA1740 + difference 1 5) (sourceB1740 + difference 5 1) sourceC1740) = raw25398 := by
      apply Matrix.ext; unfold tripleCharges sourceA1740 sourceB1740 sourceC1740 difference raw25398; decide +kernel
    rw [ha]
    exact (canonical25398 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1740 + difference 2 0) (sourceB1740 + difference 0 2) sourceC1740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1501) := by
    have ha : (tripleCharges (sourceA1740 + difference 2 0) (sourceB1740 + difference 0 2) sourceC1740) = raw25399 := by
      apply Matrix.ext; unfold tripleCharges sourceA1740 sourceB1740 sourceC1740 difference raw25399; decide +kernel
    rw [ha]
    exact (canonical25399 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1740 + difference 2 1) (sourceB1740 + difference 1 2) sourceC1740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1697) := by
    have ha : (tripleCharges (sourceA1740 + difference 2 1) (sourceB1740 + difference 1 2) sourceC1740) = raw25400 := by
      apply Matrix.ext; unfold tripleCharges sourceA1740 sourceB1740 sourceC1740 difference raw25400; decide +kernel
    rw [ha]
    exact (canonical25400 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1740 + difference 2 3) (sourceB1740 + difference 3 2) sourceC1740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1707) := by
    have ha : (tripleCharges (sourceA1740 + difference 2 3) (sourceB1740 + difference 3 2) sourceC1740) = raw21439 := by
      apply Matrix.ext; unfold tripleCharges sourceA1740 sourceB1740 sourceC1740 difference raw21439; decide +kernel
    rw [ha]
    exact (canonical21439 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1740 + difference 2 4) (sourceB1740 + difference 4 2) sourceC1740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1707) := by
    have ha : (tripleCharges (sourceA1740 + difference 2 4) (sourceB1740 + difference 4 2) sourceC1740) = raw25401 := by
      apply Matrix.ext; unfold tripleCharges sourceA1740 sourceB1740 sourceC1740 difference raw25401; decide +kernel
    rw [ha]
    exact (canonical25401 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1740 + difference 2 5) (sourceB1740 + difference 5 2) sourceC1740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1698) := by
    have ha : (tripleCharges (sourceA1740 + difference 2 5) (sourceB1740 + difference 5 2) sourceC1740) = raw25402 := by
      apply Matrix.ext; unfold tripleCharges sourceA1740 sourceB1740 sourceC1740 difference raw25402; decide +kernel
    rw [ha]
    exact (canonical25402 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1740 + difference 3 0) (sourceB1740 + difference 0 3) sourceC1740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1511) := by
    have ha : (tripleCharges (sourceA1740 + difference 3 0) (sourceB1740 + difference 0 3) sourceC1740) = raw25403 := by
      apply Matrix.ext; unfold tripleCharges sourceA1740 sourceB1740 sourceC1740 difference raw25403; decide +kernel
    rw [ha]
    exact (canonical25403 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1740 + difference 3 1) (sourceB1740 + difference 1 3) sourceC1740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1712) := by
    have ha : (tripleCharges (sourceA1740 + difference 3 1) (sourceB1740 + difference 1 3) sourceC1740) = raw25404 := by
      apply Matrix.ext; unfold tripleCharges sourceA1740 sourceB1740 sourceC1740 difference raw25404; decide +kernel
    rw [ha]
    exact (canonical25404 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1740 + difference 3 2) (sourceB1740 + difference 2 3) sourceC1740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1667) := by
    have ha : (tripleCharges (sourceA1740 + difference 3 2) (sourceB1740 + difference 2 3) sourceC1740) = raw25405 := by
      apply Matrix.ext; unfold tripleCharges sourceA1740 sourceB1740 sourceC1740 difference raw25405; decide +kernel
    rw [ha]
    exact (canonical25405 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1740 + difference 3 4) (sourceB1740 + difference 4 3) sourceC1740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1738) := by
    have ha : (tripleCharges (sourceA1740 + difference 3 4) (sourceB1740 + difference 4 3) sourceC1740) = raw25406 := by
      apply Matrix.ext; unfold tripleCharges sourceA1740 sourceB1740 sourceC1740 difference raw25406; decide +kernel
    rw [ha]
    exact (canonical25406 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1740 + difference 3 5) (sourceB1740 + difference 5 3) sourceC1740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1714) := by
    have ha : (tripleCharges (sourceA1740 + difference 3 5) (sourceB1740 + difference 5 3) sourceC1740) = raw25407 := by
      apply Matrix.ext; unfold tripleCharges sourceA1740 sourceB1740 sourceC1740 difference raw25407; decide +kernel
    rw [ha]
    exact (canonical25407 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1740 + difference 4 0) (sourceB1740 + difference 0 4) sourceC1740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1511) := by
    have ha : (tripleCharges (sourceA1740 + difference 4 0) (sourceB1740 + difference 0 4) sourceC1740) = raw25408 := by
      apply Matrix.ext; unfold tripleCharges sourceA1740 sourceB1740 sourceC1740 difference raw25408; decide +kernel
    rw [ha]
    exact (canonical25408 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1740 + difference 4 1) (sourceB1740 + difference 1 4) sourceC1740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1712) := by
    have ha : (tripleCharges (sourceA1740 + difference 4 1) (sourceB1740 + difference 1 4) sourceC1740) = raw25409 := by
      apply Matrix.ext; unfold tripleCharges sourceA1740 sourceB1740 sourceC1740 difference raw25409; decide +kernel
    rw [ha]
    exact (canonical25409 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1740 + difference 4 2) (sourceB1740 + difference 2 4) sourceC1740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1667) := by
    have ha : (tripleCharges (sourceA1740 + difference 4 2) (sourceB1740 + difference 2 4) sourceC1740) = raw25410 := by
      apply Matrix.ext; unfold tripleCharges sourceA1740 sourceB1740 sourceC1740 difference raw25410; decide +kernel
    rw [ha]
    exact (canonical25410 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1740 + difference 4 3) (sourceB1740 + difference 3 4) sourceC1740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1738) := by
    have ha : (tripleCharges (sourceA1740 + difference 4 3) (sourceB1740 + difference 3 4) sourceC1740) = raw21449 := by
      apply Matrix.ext; unfold tripleCharges sourceA1740 sourceB1740 sourceC1740 difference raw21449; decide +kernel
    rw [ha]
    exact (canonical21449 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1740 + difference 4 5) (sourceB1740 + difference 5 4) sourceC1740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1714) := by
    have ha : (tripleCharges (sourceA1740 + difference 4 5) (sourceB1740 + difference 5 4) sourceC1740) = raw25411 := by
      apply Matrix.ext; unfold tripleCharges sourceA1740 sourceB1740 sourceC1740 difference raw25411; decide +kernel
    rw [ha]
    exact (canonical25411 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1740 + difference 5 0) (sourceB1740 + difference 0 5) sourceC1740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1505) := by
    have ha : (tripleCharges (sourceA1740 + difference 5 0) (sourceB1740 + difference 0 5) sourceC1740) = raw21440 := by
      apply Matrix.ext; unfold tripleCharges sourceA1740 sourceB1740 sourceC1740 difference raw21440; decide +kernel
    rw [ha]
    exact (canonical21440 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1740 + difference 5 1) (sourceB1740 + difference 1 5) sourceC1740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1704) := by
    have ha : (tripleCharges (sourceA1740 + difference 5 1) (sourceB1740 + difference 1 5) sourceC1740) = raw21441 := by
      apply Matrix.ext; unfold tripleCharges sourceA1740 sourceB1740 sourceC1740 difference raw21441; decide +kernel
    rw [ha]
    exact (canonical21441 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1740 + difference 5 2) (sourceB1740 + difference 2 5) sourceC1740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1663) := by
    have ha : (tripleCharges (sourceA1740 + difference 5 2) (sourceB1740 + difference 2 5) sourceC1740) = raw21442 := by
      apply Matrix.ext; unfold tripleCharges sourceA1740 sourceB1740 sourceC1740 difference raw21442; decide +kernel
    rw [ha]
    exact (canonical21442 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1740 + difference 5 3) (sourceB1740 + difference 3 5) sourceC1740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1725) := by
    have ha : (tripleCharges (sourceA1740 + difference 5 3) (sourceB1740 + difference 3 5) sourceC1740) = raw25412 := by
      apply Matrix.ext; unfold tripleCharges sourceA1740 sourceB1740 sourceC1740 difference raw25412; decide +kernel
    rw [ha]
    exact (canonical25412 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1740 + difference 5 4) (sourceB1740 + difference 4 5) sourceC1740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1725) := by
    have ha : (tripleCharges (sourceA1740 + difference 5 4) (sourceB1740 + difference 4 5) sourceC1740) = raw21443 := by
      apply Matrix.ext; unfold tripleCharges sourceA1740 sourceB1740 sourceC1740 difference raw21443; decide +kernel
    rw [ha]
    exact (canonical21443 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1740 sourceB1740 sourceC1740
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1740, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1741 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1741 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC1741 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceForm1741 : Integer.Sparse Master := [(Sum.inr 577, 1), (Sum.inr 579, 1), (Sum.inr 582, 2), (Sum.inr 600, 1), (Sum.inr 1040, 1), (Sum.inr 4084, -1)]

theorem sourceEq1741 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1741 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1741 + difference 0 0) (sourceB1741 + difference 0 0) sourceC1741) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1040) := by
    have ha : (tripleCharges (sourceA1741 + difference 0 0) (sourceB1741 + difference 0 0) sourceC1741) = raw25413 := by
      apply Matrix.ext; unfold tripleCharges sourceA1741 sourceB1741 sourceC1741 difference raw25413; decide +kernel
    rw [ha]
    exact (canonical25413 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1741 + difference 1 0) (sourceB1741 + difference 0 1) sourceC1741) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 600) := by
    have ha : (tripleCharges (sourceA1741 + difference 1 0) (sourceB1741 + difference 0 1) sourceC1741) = raw25414 := by
      apply Matrix.ext; unfold tripleCharges sourceA1741 sourceB1741 sourceC1741 difference raw25414; decide +kernel
    rw [ha]
    exact (canonical25414 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1741 + difference 2 0) (sourceB1741 + difference 0 2) sourceC1741) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 577) := by
    have ha : (tripleCharges (sourceA1741 + difference 2 0) (sourceB1741 + difference 0 2) sourceC1741) = raw25415 := by
      apply Matrix.ext; unfold tripleCharges sourceA1741 sourceB1741 sourceC1741 difference raw25415; decide +kernel
    rw [ha]
    exact (canonical25415 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1741 + difference 3 0) (sourceB1741 + difference 0 3) sourceC1741) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 582) := by
    have ha : (tripleCharges (sourceA1741 + difference 3 0) (sourceB1741 + difference 0 3) sourceC1741) = raw25416 := by
      apply Matrix.ext; unfold tripleCharges sourceA1741 sourceB1741 sourceC1741 difference raw25416; decide +kernel
    rw [ha]
    exact (canonical25416 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1741 + difference 4 0) (sourceB1741 + difference 0 4) sourceC1741) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 582) := by
    have ha : (tripleCharges (sourceA1741 + difference 4 0) (sourceB1741 + difference 0 4) sourceC1741) = raw25417 := by
      apply Matrix.ext; unfold tripleCharges sourceA1741 sourceB1741 sourceC1741 difference raw25417; decide +kernel
    rw [ha]
    exact (canonical25417 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1741 + difference 5 0) (sourceB1741 + difference 0 5) sourceC1741) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 579) := by
    have ha : (tripleCharges (sourceA1741 + difference 5 0) (sourceB1741 + difference 0 5) sourceC1741) = raw21458 := by
      apply Matrix.ext; unfold tripleCharges sourceA1741 sourceB1741 sourceC1741 difference raw21458; decide +kernel
    rw [ha]
    exact (canonical21458 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1741 + sourceB1741) sourceC1741) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1741 + sourceB1741) sourceC1741) = raw21461 := by
      apply Matrix.ext; unfold doubleCharges sourceA1741 sourceB1741 sourceC1741 raw21461; decide +kernel
    rw [ha]
    exact (canonical21461 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1741 sourceB1741 sourceC1741
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1741, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1742 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1742 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC1742 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceForm1742 : Integer.Sparse Master := [(Sum.inr 600, 1), (Sum.inr 919, 1), (Sum.inr 1040, 1), (Sum.inr 1079, 1), (Sum.inr 1082, 2), (Sum.inr 4084, -1)]

theorem sourceEq1742 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1742 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1742 + difference 1 0) (sourceB1742 + difference 0 1) sourceC1742) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 600) := by
    have ha : (tripleCharges (sourceA1742 + difference 1 0) (sourceB1742 + difference 0 1) sourceC1742) = raw25414 := by
      apply Matrix.ext; unfold tripleCharges sourceA1742 sourceB1742 sourceC1742 difference raw25414; decide +kernel
    rw [ha]
    exact (canonical25414 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1742 + difference 1 1) (sourceB1742 + difference 1 1) sourceC1742) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1040) := by
    have ha : (tripleCharges (sourceA1742 + difference 1 1) (sourceB1742 + difference 1 1) sourceC1742) = raw25413 := by
      apply Matrix.ext; unfold tripleCharges sourceA1742 sourceB1742 sourceC1742 difference raw25413; decide +kernel
    rw [ha]
    exact (canonical25413 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1742 + difference 1 2) (sourceB1742 + difference 2 1) sourceC1742) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 919) := by
    have ha : (tripleCharges (sourceA1742 + difference 1 2) (sourceB1742 + difference 2 1) sourceC1742) = raw25418 := by
      apply Matrix.ext; unfold tripleCharges sourceA1742 sourceB1742 sourceC1742 difference raw25418; decide +kernel
    rw [ha]
    exact (canonical25418 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1742 + difference 1 3) (sourceB1742 + difference 3 1) sourceC1742) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1082) := by
    have ha : (tripleCharges (sourceA1742 + difference 1 3) (sourceB1742 + difference 3 1) sourceC1742) = raw21465 := by
      apply Matrix.ext; unfold tripleCharges sourceA1742 sourceB1742 sourceC1742 difference raw21465; decide +kernel
    rw [ha]
    exact (canonical21465 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1742 + difference 1 4) (sourceB1742 + difference 4 1) sourceC1742) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1082) := by
    have ha : (tripleCharges (sourceA1742 + difference 1 4) (sourceB1742 + difference 4 1) sourceC1742) = raw25419 := by
      apply Matrix.ext; unfold tripleCharges sourceA1742 sourceB1742 sourceC1742 difference raw25419; decide +kernel
    rw [ha]
    exact (canonical25419 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1742 + difference 1 5) (sourceB1742 + difference 5 1) sourceC1742) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1079) := by
    have ha : (tripleCharges (sourceA1742 + difference 1 5) (sourceB1742 + difference 5 1) sourceC1742) = raw25420 := by
      apply Matrix.ext; unfold tripleCharges sourceA1742 sourceB1742 sourceC1742 difference raw25420; decide +kernel
    rw [ha]
    exact (canonical25420 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1742 + sourceB1742) sourceC1742) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1742 + sourceB1742) sourceC1742) = raw21461 := by
      apply Matrix.ext; unfold doubleCharges sourceA1742 sourceB1742 sourceC1742 raw21461; decide +kernel
    rw [ha]
    exact (canonical21461 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1742 sourceB1742 sourceC1742
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1742, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1743 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1743 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC1743 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceForm1743 : Integer.Sparse Master := [(Sum.inr 941, 1), (Sum.inr 943, 1), (Sum.inr 946, 2), (Sum.inr 1040, 1), (Sum.inr 2106, 1), (Sum.inr 4084, -1)]

theorem sourceEq1743 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1743 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1743 + difference 0 1) (sourceB1743 + difference 1 0) sourceC1743) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2106) := by
    have ha : (tripleCharges (sourceA1743 + difference 0 1) (sourceB1743 + difference 1 0) sourceC1743) = raw25421 := by
      apply Matrix.ext; unfold tripleCharges sourceA1743 sourceB1743 sourceC1743 difference raw25421; decide +kernel
    rw [ha]
    exact (canonical25421 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1743 + difference 1 1) (sourceB1743 + difference 1 1) sourceC1743) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1040) := by
    have ha : (tripleCharges (sourceA1743 + difference 1 1) (sourceB1743 + difference 1 1) sourceC1743) = raw25413 := by
      apply Matrix.ext; unfold tripleCharges sourceA1743 sourceB1743 sourceC1743 difference raw25413; decide +kernel
    rw [ha]
    exact (canonical25413 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1743 + difference 2 1) (sourceB1743 + difference 1 2) sourceC1743) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 941) := by
    have ha : (tripleCharges (sourceA1743 + difference 2 1) (sourceB1743 + difference 1 2) sourceC1743) = raw25422 := by
      apply Matrix.ext; unfold tripleCharges sourceA1743 sourceB1743 sourceC1743 difference raw25422; decide +kernel
    rw [ha]
    exact (canonical25422 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1743 + difference 3 1) (sourceB1743 + difference 1 3) sourceC1743) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 946) := by
    have ha : (tripleCharges (sourceA1743 + difference 3 1) (sourceB1743 + difference 1 3) sourceC1743) = raw25423 := by
      apply Matrix.ext; unfold tripleCharges sourceA1743 sourceB1743 sourceC1743 difference raw25423; decide +kernel
    rw [ha]
    exact (canonical25423 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1743 + difference 4 1) (sourceB1743 + difference 1 4) sourceC1743) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 946) := by
    have ha : (tripleCharges (sourceA1743 + difference 4 1) (sourceB1743 + difference 1 4) sourceC1743) = raw25424 := by
      apply Matrix.ext; unfold tripleCharges sourceA1743 sourceB1743 sourceC1743 difference raw25424; decide +kernel
    rw [ha]
    exact (canonical25424 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1743 + difference 5 1) (sourceB1743 + difference 1 5) sourceC1743) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 943) := by
    have ha : (tripleCharges (sourceA1743 + difference 5 1) (sourceB1743 + difference 1 5) sourceC1743) = raw21468 := by
      apply Matrix.ext; unfold tripleCharges sourceA1743 sourceB1743 sourceC1743 difference raw21468; decide +kernel
    rw [ha]
    exact (canonical21468 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1743 + sourceB1743) sourceC1743) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1743 + sourceB1743) sourceC1743) = raw21461 := by
      apply Matrix.ext; unfold doubleCharges sourceA1743 sourceB1743 sourceC1743 raw21461; decide +kernel
    rw [ha]
    exact (canonical21461 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1743 sourceB1743 sourceC1743
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1743, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1744 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1744 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceC1744 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceForm1744 : Integer.Sparse Master := [(Sum.inr 577, 1), (Sum.inr 941, 1), (Sum.inr 1038, 1), (Sum.inr 1040, 3), (Sum.inr 4084, -1)]

theorem sourceEq1744 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1744 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1744 + difference 2 0) (sourceB1744 + difference 0 2) sourceC1744) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 577) := by
    have ha : (tripleCharges (sourceA1744 + difference 2 0) (sourceB1744 + difference 0 2) sourceC1744) = raw25415 := by
      apply Matrix.ext; unfold tripleCharges sourceA1744 sourceB1744 sourceC1744 difference raw25415; decide +kernel
    rw [ha]
    exact (canonical25415 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1744 + difference 2 1) (sourceB1744 + difference 1 2) sourceC1744) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 941) := by
    have ha : (tripleCharges (sourceA1744 + difference 2 1) (sourceB1744 + difference 1 2) sourceC1744) = raw25422 := by
      apply Matrix.ext; unfold tripleCharges sourceA1744 sourceB1744 sourceC1744 difference raw25422; decide +kernel
    rw [ha]
    exact (canonical25422 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1744 + difference 2 2) (sourceB1744 + difference 2 2) sourceC1744) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1040) := by
    have ha : (tripleCharges (sourceA1744 + difference 2 2) (sourceB1744 + difference 2 2) sourceC1744) = raw25413 := by
      apply Matrix.ext; unfold tripleCharges sourceA1744 sourceB1744 sourceC1744 difference raw25413; decide +kernel
    rw [ha]
    exact (canonical25413 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1744 + difference 2 3) (sourceB1744 + difference 3 2) sourceC1744) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1040) := by
    have ha : (tripleCharges (sourceA1744 + difference 2 3) (sourceB1744 + difference 3 2) sourceC1744) = raw21473 := by
      apply Matrix.ext; unfold tripleCharges sourceA1744 sourceB1744 sourceC1744 difference raw21473; decide +kernel
    rw [ha]
    exact (canonical21473 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1744 + difference 2 4) (sourceB1744 + difference 4 2) sourceC1744) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1040) := by
    have ha : (tripleCharges (sourceA1744 + difference 2 4) (sourceB1744 + difference 4 2) sourceC1744) = raw25425 := by
      apply Matrix.ext; unfold tripleCharges sourceA1744 sourceB1744 sourceC1744 difference raw25425; decide +kernel
    rw [ha]
    exact (canonical25425 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1744 + difference 2 5) (sourceB1744 + difference 5 2) sourceC1744) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1038) := by
    have ha : (tripleCharges (sourceA1744 + difference 2 5) (sourceB1744 + difference 5 2) sourceC1744) = raw25426 := by
      apply Matrix.ext; unfold tripleCharges sourceA1744 sourceB1744 sourceC1744 difference raw25426; decide +kernel
    rw [ha]
    exact (canonical25426 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1744 + sourceB1744) sourceC1744) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1744 + sourceB1744) sourceC1744) = raw21461 := by
      apply Matrix.ext; unfold doubleCharges sourceA1744 sourceB1744 sourceC1744 raw21461; decide +kernel
    rw [ha]
    exact (canonical21461 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1744 sourceB1744 sourceC1744
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1744, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1745 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1745 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceC1745 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceForm1745 : Integer.Sparse Master := [(Sum.inr 4098, 1), (Sum.inr 4099, 1), (Sum.inr 4102, 2), (Sum.inr 4115, 1), (Sum.inr 4286, 1), (Sum.inr 4288, 2), (Sum.inr 4298, 1), (Sum.inr 4341, 1), (Sum.inr 4343, 1), (Sum.inr 4349, 2), (Sum.inr 4396, 2), (Sum.inr 4398, 2), (Sum.inr 4404, 2), (Sum.inr 4419, 2), (Sum.inr 4456, 1), (Sum.inr 4458, 2), (Sum.inr 4495, 1), (Sum.inr 5072, 1), (Sum.inr 5168, 1), (Sum.inr 5258, 2), (Sum.inr 5292, 1)]

theorem sourceEq1745 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1745 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1745 + difference 0 1) (sourceB1745 + difference 1 0) sourceC1745) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5168) := by
    have ha : (tripleCharges (sourceA1745 + difference 0 1) (sourceB1745 + difference 1 0) sourceC1745) = raw10101 := by
      apply Matrix.ext; unfold tripleCharges sourceA1745 sourceB1745 sourceC1745 difference raw10101; decide +kernel
    rw [ha]
    exact (canonical10101 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1745 + difference 0 2) (sourceB1745 + difference 2 0) sourceC1745) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5072) := by
    have ha : (tripleCharges (sourceA1745 + difference 0 2) (sourceB1745 + difference 2 0) sourceC1745) = raw10102 := by
      apply Matrix.ext; unfold tripleCharges sourceA1745 sourceB1745 sourceC1745 difference raw10102; decide +kernel
    rw [ha]
    exact (canonical10102 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1745 + difference 0 3) (sourceB1745 + difference 3 0) sourceC1745) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA1745 + difference 0 3) (sourceB1745 + difference 3 0) sourceC1745) = raw25427 := by
      apply Matrix.ext; unfold tripleCharges sourceA1745 sourceB1745 sourceC1745 difference raw25427; decide +kernel
    rw [ha]
    exact (canonical25427 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1745 + difference 0 4) (sourceB1745 + difference 4 0) sourceC1745) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA1745 + difference 0 4) (sourceB1745 + difference 4 0) sourceC1745) = raw10103 := by
      apply Matrix.ext; unfold tripleCharges sourceA1745 sourceB1745 sourceC1745 difference raw10103; decide +kernel
    rw [ha]
    exact (canonical10103 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1745 + difference 0 5) (sourceB1745 + difference 5 0) sourceC1745) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA1745 + difference 0 5) (sourceB1745 + difference 5 0) sourceC1745) = raw10104 := by
      apply Matrix.ext; unfold tripleCharges sourceA1745 sourceB1745 sourceC1745 difference raw10104; decide +kernel
    rw [ha]
    exact (canonical10104 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1745 + difference 1 0) (sourceB1745 + difference 0 1) sourceC1745) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4115) := by
    have ha : (tripleCharges (sourceA1745 + difference 1 0) (sourceB1745 + difference 0 1) sourceC1745) = raw25428 := by
      apply Matrix.ext; unfold tripleCharges sourceA1745 sourceB1745 sourceC1745 difference raw25428; decide +kernel
    rw [ha]
    exact (canonical25428 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1745 + difference 1 2) (sourceB1745 + difference 2 1) sourceC1745) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4298) := by
    have ha : (tripleCharges (sourceA1745 + difference 1 2) (sourceB1745 + difference 2 1) sourceC1745) = raw25429 := by
      apply Matrix.ext; unfold tripleCharges sourceA1745 sourceB1745 sourceC1745 difference raw25429; decide +kernel
    rw [ha]
    exact (canonical25429 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1745 + difference 1 3) (sourceB1745 + difference 3 1) sourceC1745) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4419) := by
    have ha : (tripleCharges (sourceA1745 + difference 1 3) (sourceB1745 + difference 3 1) sourceC1745) = raw10090 := by
      apply Matrix.ext; unfold tripleCharges sourceA1745 sourceB1745 sourceC1745 difference raw10090; decide +kernel
    rw [ha]
    exact (canonical10090 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1745 + difference 1 4) (sourceB1745 + difference 4 1) sourceC1745) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4419) := by
    have ha : (tripleCharges (sourceA1745 + difference 1 4) (sourceB1745 + difference 4 1) sourceC1745) = raw25430 := by
      apply Matrix.ext; unfold tripleCharges sourceA1745 sourceB1745 sourceC1745 difference raw25430; decide +kernel
    rw [ha]
    exact (canonical25430 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1745 + difference 1 5) (sourceB1745 + difference 5 1) sourceC1745) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4495) := by
    have ha : (tripleCharges (sourceA1745 + difference 1 5) (sourceB1745 + difference 5 1) sourceC1745) = raw25431 := by
      apply Matrix.ext; unfold tripleCharges sourceA1745 sourceB1745 sourceC1745 difference raw25431; decide +kernel
    rw [ha]
    exact (canonical25431 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1745 + difference 2 0) (sourceB1745 + difference 0 2) sourceC1745) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4098) := by
    have ha : (tripleCharges (sourceA1745 + difference 2 0) (sourceB1745 + difference 0 2) sourceC1745) = raw25432 := by
      apply Matrix.ext; unfold tripleCharges sourceA1745 sourceB1745 sourceC1745 difference raw25432; decide +kernel
    rw [ha]
    exact (canonical25432 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1745 + difference 2 1) (sourceB1745 + difference 1 2) sourceC1745) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4341) := by
    have ha : (tripleCharges (sourceA1745 + difference 2 1) (sourceB1745 + difference 1 2) sourceC1745) = raw25433 := by
      apply Matrix.ext; unfold tripleCharges sourceA1745 sourceB1745 sourceC1745 difference raw25433; decide +kernel
    rw [ha]
    exact (canonical25433 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1745 + difference 2 3) (sourceB1745 + difference 3 2) sourceC1745) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4396) := by
    have ha : (tripleCharges (sourceA1745 + difference 2 3) (sourceB1745 + difference 3 2) sourceC1745) = raw10095 := by
      apply Matrix.ext; unfold tripleCharges sourceA1745 sourceB1745 sourceC1745 difference raw10095; decide +kernel
    rw [ha]
    exact (canonical10095 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1745 + difference 2 4) (sourceB1745 + difference 4 2) sourceC1745) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4396) := by
    have ha : (tripleCharges (sourceA1745 + difference 2 4) (sourceB1745 + difference 4 2) sourceC1745) = raw25434 := by
      apply Matrix.ext; unfold tripleCharges sourceA1745 sourceB1745 sourceC1745 difference raw25434; decide +kernel
    rw [ha]
    exact (canonical25434 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1745 + difference 2 5) (sourceB1745 + difference 5 2) sourceC1745) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4456) := by
    have ha : (tripleCharges (sourceA1745 + difference 2 5) (sourceB1745 + difference 5 2) sourceC1745) = raw25435 := by
      apply Matrix.ext; unfold tripleCharges sourceA1745 sourceB1745 sourceC1745 difference raw25435; decide +kernel
    rw [ha]
    exact (canonical25435 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1745 + difference 3 0) (sourceB1745 + difference 0 3) sourceC1745) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4102) := by
    have ha : (tripleCharges (sourceA1745 + difference 3 0) (sourceB1745 + difference 0 3) sourceC1745) = raw25436 := by
      apply Matrix.ext; unfold tripleCharges sourceA1745 sourceB1745 sourceC1745 difference raw25436; decide +kernel
    rw [ha]
    exact (canonical25436 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1745 + difference 3 1) (sourceB1745 + difference 1 3) sourceC1745) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4349) := by
    have ha : (tripleCharges (sourceA1745 + difference 3 1) (sourceB1745 + difference 1 3) sourceC1745) = raw25437 := by
      apply Matrix.ext; unfold tripleCharges sourceA1745 sourceB1745 sourceC1745 difference raw25437; decide +kernel
    rw [ha]
    exact (canonical25437 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1745 + difference 3 2) (sourceB1745 + difference 2 3) sourceC1745) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4288) := by
    have ha : (tripleCharges (sourceA1745 + difference 3 2) (sourceB1745 + difference 2 3) sourceC1745) = raw25438 := by
      apply Matrix.ext; unfold tripleCharges sourceA1745 sourceB1745 sourceC1745 difference raw25438; decide +kernel
    rw [ha]
    exact (canonical25438 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1745 + difference 3 4) (sourceB1745 + difference 4 3) sourceC1745) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4404) := by
    have ha : (tripleCharges (sourceA1745 + difference 3 4) (sourceB1745 + difference 4 3) sourceC1745) = raw25439 := by
      apply Matrix.ext; unfold tripleCharges sourceA1745 sourceB1745 sourceC1745 difference raw25439; decide +kernel
    rw [ha]
    exact (canonical25439 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1745 + difference 3 5) (sourceB1745 + difference 5 3) sourceC1745) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1745 + difference 3 5) (sourceB1745 + difference 5 3) sourceC1745) = raw25440 := by
      apply Matrix.ext; unfold tripleCharges sourceA1745 sourceB1745 sourceC1745 difference raw25440; decide +kernel
    rw [ha]
    exact (canonical25440 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1745 + difference 4 0) (sourceB1745 + difference 0 4) sourceC1745) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4102) := by
    have ha : (tripleCharges (sourceA1745 + difference 4 0) (sourceB1745 + difference 0 4) sourceC1745) = raw25441 := by
      apply Matrix.ext; unfold tripleCharges sourceA1745 sourceB1745 sourceC1745 difference raw25441; decide +kernel
    rw [ha]
    exact (canonical25441 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1745 + difference 4 1) (sourceB1745 + difference 1 4) sourceC1745) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4349) := by
    have ha : (tripleCharges (sourceA1745 + difference 4 1) (sourceB1745 + difference 1 4) sourceC1745) = raw25442 := by
      apply Matrix.ext; unfold tripleCharges sourceA1745 sourceB1745 sourceC1745 difference raw25442; decide +kernel
    rw [ha]
    exact (canonical25442 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1745 + difference 4 2) (sourceB1745 + difference 2 4) sourceC1745) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4288) := by
    have ha : (tripleCharges (sourceA1745 + difference 4 2) (sourceB1745 + difference 2 4) sourceC1745) = raw25443 := by
      apply Matrix.ext; unfold tripleCharges sourceA1745 sourceB1745 sourceC1745 difference raw25443; decide +kernel
    rw [ha]
    exact (canonical25443 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1745 + difference 4 3) (sourceB1745 + difference 3 4) sourceC1745) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4404) := by
    have ha : (tripleCharges (sourceA1745 + difference 4 3) (sourceB1745 + difference 3 4) sourceC1745) = raw10105 := by
      apply Matrix.ext; unfold tripleCharges sourceA1745 sourceB1745 sourceC1745 difference raw10105; decide +kernel
    rw [ha]
    exact (canonical10105 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1745 + difference 4 5) (sourceB1745 + difference 5 4) sourceC1745) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1745 + difference 4 5) (sourceB1745 + difference 5 4) sourceC1745) = raw25444 := by
      apply Matrix.ext; unfold tripleCharges sourceA1745 sourceB1745 sourceC1745 difference raw25444; decide +kernel
    rw [ha]
    exact (canonical25444 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1745 + difference 5 0) (sourceB1745 + difference 0 5) sourceC1745) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4099) := by
    have ha : (tripleCharges (sourceA1745 + difference 5 0) (sourceB1745 + difference 0 5) sourceC1745) = raw25445 := by
      apply Matrix.ext; unfold tripleCharges sourceA1745 sourceB1745 sourceC1745 difference raw25445; decide +kernel
    rw [ha]
    exact (canonical25445 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1745 + difference 5 1) (sourceB1745 + difference 1 5) sourceC1745) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4343) := by
    have ha : (tripleCharges (sourceA1745 + difference 5 1) (sourceB1745 + difference 1 5) sourceC1745) = raw25446 := by
      apply Matrix.ext; unfold tripleCharges sourceA1745 sourceB1745 sourceC1745 difference raw25446; decide +kernel
    rw [ha]
    exact (canonical25446 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1745 + difference 5 2) (sourceB1745 + difference 2 5) sourceC1745) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4286) := by
    have ha : (tripleCharges (sourceA1745 + difference 5 2) (sourceB1745 + difference 2 5) sourceC1745) = raw25447 := by
      apply Matrix.ext; unfold tripleCharges sourceA1745 sourceB1745 sourceC1745 difference raw25447; decide +kernel
    rw [ha]
    exact (canonical25447 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1745 + difference 5 3) (sourceB1745 + difference 3 5) sourceC1745) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4398) := by
    have ha : (tripleCharges (sourceA1745 + difference 5 3) (sourceB1745 + difference 3 5) sourceC1745) = raw10110 := by
      apply Matrix.ext; unfold tripleCharges sourceA1745 sourceB1745 sourceC1745 difference raw10110; decide +kernel
    rw [ha]
    exact (canonical10110 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1745 + difference 5 4) (sourceB1745 + difference 4 5) sourceC1745) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4398) := by
    have ha : (tripleCharges (sourceA1745 + difference 5 4) (sourceB1745 + difference 4 5) sourceC1745) = raw25448 := by
      apply Matrix.ext; unfold tripleCharges sourceA1745 sourceB1745 sourceC1745 difference raw25448; decide +kernel
    rw [ha]
    exact (canonical25448 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1745 sourceB1745 sourceC1745
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1745, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1746 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1746 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceC1746 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceForm1746 : Integer.Sparse Master := [(Sum.inr 535, 1), (Sum.inr 536, 1), (Sum.inr 539, 2), (Sum.inr 552, 1), (Sum.inr 864, 1), (Sum.inr 866, 2), (Sum.inr 876, 1), (Sum.inr 919, 1), (Sum.inr 921, 1), (Sum.inr 927, 2), (Sum.inr 977, 2), (Sum.inr 979, 2), (Sum.inr 985, 2), (Sum.inr 1000, 2), (Sum.inr 1039, 1), (Sum.inr 1041, 2), (Sum.inr 1079, 1), (Sum.inr 2479, 1), (Sum.inr 2594, 1), (Sum.inr 2722, 2), (Sum.inr 2766, 1)]

theorem sourceEq1746 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1746 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1746 + difference 0 1) (sourceB1746 + difference 1 0) sourceC1746) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2594) := by
    have ha : (tripleCharges (sourceA1746 + difference 0 1) (sourceB1746 + difference 1 0) sourceC1746) = raw10131 := by
      apply Matrix.ext; unfold tripleCharges sourceA1746 sourceB1746 sourceC1746 difference raw10131; decide +kernel
    rw [ha]
    exact (canonical10131 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1746 + difference 0 2) (sourceB1746 + difference 2 0) sourceC1746) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2479) := by
    have ha : (tripleCharges (sourceA1746 + difference 0 2) (sourceB1746 + difference 2 0) sourceC1746) = raw10132 := by
      apply Matrix.ext; unfold tripleCharges sourceA1746 sourceB1746 sourceC1746 difference raw10132; decide +kernel
    rw [ha]
    exact (canonical10132 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1746 + difference 0 3) (sourceB1746 + difference 3 0) sourceC1746) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA1746 + difference 0 3) (sourceB1746 + difference 3 0) sourceC1746) = raw25449 := by
      apply Matrix.ext; unfold tripleCharges sourceA1746 sourceB1746 sourceC1746 difference raw25449; decide +kernel
    rw [ha]
    exact (canonical25449 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1746 + difference 0 4) (sourceB1746 + difference 4 0) sourceC1746) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA1746 + difference 0 4) (sourceB1746 + difference 4 0) sourceC1746) = raw10133 := by
      apply Matrix.ext; unfold tripleCharges sourceA1746 sourceB1746 sourceC1746 difference raw10133; decide +kernel
    rw [ha]
    exact (canonical10133 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1746 + difference 0 5) (sourceB1746 + difference 5 0) sourceC1746) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2766) := by
    have ha : (tripleCharges (sourceA1746 + difference 0 5) (sourceB1746 + difference 5 0) sourceC1746) = raw10134 := by
      apply Matrix.ext; unfold tripleCharges sourceA1746 sourceB1746 sourceC1746 difference raw10134; decide +kernel
    rw [ha]
    exact (canonical10134 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1746 + difference 1 0) (sourceB1746 + difference 0 1) sourceC1746) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 552) := by
    have ha : (tripleCharges (sourceA1746 + difference 1 0) (sourceB1746 + difference 0 1) sourceC1746) = raw25450 := by
      apply Matrix.ext; unfold tripleCharges sourceA1746 sourceB1746 sourceC1746 difference raw25450; decide +kernel
    rw [ha]
    exact (canonical25450 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1746 + difference 1 2) (sourceB1746 + difference 2 1) sourceC1746) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 876) := by
    have ha : (tripleCharges (sourceA1746 + difference 1 2) (sourceB1746 + difference 2 1) sourceC1746) = raw25451 := by
      apply Matrix.ext; unfold tripleCharges sourceA1746 sourceB1746 sourceC1746 difference raw25451; decide +kernel
    rw [ha]
    exact (canonical25451 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1746 + difference 1 3) (sourceB1746 + difference 3 1) sourceC1746) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1000) := by
    have ha : (tripleCharges (sourceA1746 + difference 1 3) (sourceB1746 + difference 3 1) sourceC1746) = raw10120 := by
      apply Matrix.ext; unfold tripleCharges sourceA1746 sourceB1746 sourceC1746 difference raw10120; decide +kernel
    rw [ha]
    exact (canonical10120 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1746 + difference 1 4) (sourceB1746 + difference 4 1) sourceC1746) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1000) := by
    have ha : (tripleCharges (sourceA1746 + difference 1 4) (sourceB1746 + difference 4 1) sourceC1746) = raw25452 := by
      apply Matrix.ext; unfold tripleCharges sourceA1746 sourceB1746 sourceC1746 difference raw25452; decide +kernel
    rw [ha]
    exact (canonical25452 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1746 + difference 1 5) (sourceB1746 + difference 5 1) sourceC1746) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1079) := by
    have ha : (tripleCharges (sourceA1746 + difference 1 5) (sourceB1746 + difference 5 1) sourceC1746) = raw25453 := by
      apply Matrix.ext; unfold tripleCharges sourceA1746 sourceB1746 sourceC1746 difference raw25453; decide +kernel
    rw [ha]
    exact (canonical25453 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1746 + difference 2 0) (sourceB1746 + difference 0 2) sourceC1746) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 535) := by
    have ha : (tripleCharges (sourceA1746 + difference 2 0) (sourceB1746 + difference 0 2) sourceC1746) = raw25454 := by
      apply Matrix.ext; unfold tripleCharges sourceA1746 sourceB1746 sourceC1746 difference raw25454; decide +kernel
    rw [ha]
    exact (canonical25454 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1746 + difference 2 1) (sourceB1746 + difference 1 2) sourceC1746) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 919) := by
    have ha : (tripleCharges (sourceA1746 + difference 2 1) (sourceB1746 + difference 1 2) sourceC1746) = raw25455 := by
      apply Matrix.ext; unfold tripleCharges sourceA1746 sourceB1746 sourceC1746 difference raw25455; decide +kernel
    rw [ha]
    exact (canonical25455 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1746 + difference 2 3) (sourceB1746 + difference 3 2) sourceC1746) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 977) := by
    have ha : (tripleCharges (sourceA1746 + difference 2 3) (sourceB1746 + difference 3 2) sourceC1746) = raw10125 := by
      apply Matrix.ext; unfold tripleCharges sourceA1746 sourceB1746 sourceC1746 difference raw10125; decide +kernel
    rw [ha]
    exact (canonical10125 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1746 + difference 2 4) (sourceB1746 + difference 4 2) sourceC1746) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 977) := by
    have ha : (tripleCharges (sourceA1746 + difference 2 4) (sourceB1746 + difference 4 2) sourceC1746) = raw25456 := by
      apply Matrix.ext; unfold tripleCharges sourceA1746 sourceB1746 sourceC1746 difference raw25456; decide +kernel
    rw [ha]
    exact (canonical25456 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1746 + difference 2 5) (sourceB1746 + difference 5 2) sourceC1746) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1039) := by
    have ha : (tripleCharges (sourceA1746 + difference 2 5) (sourceB1746 + difference 5 2) sourceC1746) = raw25457 := by
      apply Matrix.ext; unfold tripleCharges sourceA1746 sourceB1746 sourceC1746 difference raw25457; decide +kernel
    rw [ha]
    exact (canonical25457 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1746 + difference 3 0) (sourceB1746 + difference 0 3) sourceC1746) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 539) := by
    have ha : (tripleCharges (sourceA1746 + difference 3 0) (sourceB1746 + difference 0 3) sourceC1746) = raw25458 := by
      apply Matrix.ext; unfold tripleCharges sourceA1746 sourceB1746 sourceC1746 difference raw25458; decide +kernel
    rw [ha]
    exact (canonical25458 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1746 + difference 3 1) (sourceB1746 + difference 1 3) sourceC1746) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 927) := by
    have ha : (tripleCharges (sourceA1746 + difference 3 1) (sourceB1746 + difference 1 3) sourceC1746) = raw25459 := by
      apply Matrix.ext; unfold tripleCharges sourceA1746 sourceB1746 sourceC1746 difference raw25459; decide +kernel
    rw [ha]
    exact (canonical25459 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1746 + difference 3 2) (sourceB1746 + difference 2 3) sourceC1746) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 866) := by
    have ha : (tripleCharges (sourceA1746 + difference 3 2) (sourceB1746 + difference 2 3) sourceC1746) = raw25460 := by
      apply Matrix.ext; unfold tripleCharges sourceA1746 sourceB1746 sourceC1746 difference raw25460; decide +kernel
    rw [ha]
    exact (canonical25460 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1746 + difference 3 4) (sourceB1746 + difference 4 3) sourceC1746) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 985) := by
    have ha : (tripleCharges (sourceA1746 + difference 3 4) (sourceB1746 + difference 4 3) sourceC1746) = raw25461 := by
      apply Matrix.ext; unfold tripleCharges sourceA1746 sourceB1746 sourceC1746 difference raw25461; decide +kernel
    rw [ha]
    exact (canonical25461 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1746 + difference 3 5) (sourceB1746 + difference 5 3) sourceC1746) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1041) := by
    have ha : (tripleCharges (sourceA1746 + difference 3 5) (sourceB1746 + difference 5 3) sourceC1746) = raw25462 := by
      apply Matrix.ext; unfold tripleCharges sourceA1746 sourceB1746 sourceC1746 difference raw25462; decide +kernel
    rw [ha]
    exact (canonical25462 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1746 + difference 4 0) (sourceB1746 + difference 0 4) sourceC1746) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 539) := by
    have ha : (tripleCharges (sourceA1746 + difference 4 0) (sourceB1746 + difference 0 4) sourceC1746) = raw25463 := by
      apply Matrix.ext; unfold tripleCharges sourceA1746 sourceB1746 sourceC1746 difference raw25463; decide +kernel
    rw [ha]
    exact (canonical25463 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1746 + difference 4 1) (sourceB1746 + difference 1 4) sourceC1746) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 927) := by
    have ha : (tripleCharges (sourceA1746 + difference 4 1) (sourceB1746 + difference 1 4) sourceC1746) = raw25464 := by
      apply Matrix.ext; unfold tripleCharges sourceA1746 sourceB1746 sourceC1746 difference raw25464; decide +kernel
    rw [ha]
    exact (canonical25464 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1746 + difference 4 2) (sourceB1746 + difference 2 4) sourceC1746) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 866) := by
    have ha : (tripleCharges (sourceA1746 + difference 4 2) (sourceB1746 + difference 2 4) sourceC1746) = raw25465 := by
      apply Matrix.ext; unfold tripleCharges sourceA1746 sourceB1746 sourceC1746 difference raw25465; decide +kernel
    rw [ha]
    exact (canonical25465 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1746 + difference 4 3) (sourceB1746 + difference 3 4) sourceC1746) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 985) := by
    have ha : (tripleCharges (sourceA1746 + difference 4 3) (sourceB1746 + difference 3 4) sourceC1746) = raw10135 := by
      apply Matrix.ext; unfold tripleCharges sourceA1746 sourceB1746 sourceC1746 difference raw10135; decide +kernel
    rw [ha]
    exact (canonical10135 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1746 + difference 4 5) (sourceB1746 + difference 5 4) sourceC1746) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1041) := by
    have ha : (tripleCharges (sourceA1746 + difference 4 5) (sourceB1746 + difference 5 4) sourceC1746) = raw25466 := by
      apply Matrix.ext; unfold tripleCharges sourceA1746 sourceB1746 sourceC1746 difference raw25466; decide +kernel
    rw [ha]
    exact (canonical25466 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1746 + difference 5 0) (sourceB1746 + difference 0 5) sourceC1746) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 536) := by
    have ha : (tripleCharges (sourceA1746 + difference 5 0) (sourceB1746 + difference 0 5) sourceC1746) = raw25467 := by
      apply Matrix.ext; unfold tripleCharges sourceA1746 sourceB1746 sourceC1746 difference raw25467; decide +kernel
    rw [ha]
    exact (canonical25467 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1746 + difference 5 1) (sourceB1746 + difference 1 5) sourceC1746) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 921) := by
    have ha : (tripleCharges (sourceA1746 + difference 5 1) (sourceB1746 + difference 1 5) sourceC1746) = raw25468 := by
      apply Matrix.ext; unfold tripleCharges sourceA1746 sourceB1746 sourceC1746 difference raw25468; decide +kernel
    rw [ha]
    exact (canonical25468 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1746 + difference 5 2) (sourceB1746 + difference 2 5) sourceC1746) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 864) := by
    have ha : (tripleCharges (sourceA1746 + difference 5 2) (sourceB1746 + difference 2 5) sourceC1746) = raw25469 := by
      apply Matrix.ext; unfold tripleCharges sourceA1746 sourceB1746 sourceC1746 difference raw25469; decide +kernel
    rw [ha]
    exact (canonical25469 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1746 + difference 5 3) (sourceB1746 + difference 3 5) sourceC1746) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 979) := by
    have ha : (tripleCharges (sourceA1746 + difference 5 3) (sourceB1746 + difference 3 5) sourceC1746) = raw10140 := by
      apply Matrix.ext; unfold tripleCharges sourceA1746 sourceB1746 sourceC1746 difference raw10140; decide +kernel
    rw [ha]
    exact (canonical10140 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1746 + difference 5 4) (sourceB1746 + difference 4 5) sourceC1746) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 979) := by
    have ha : (tripleCharges (sourceA1746 + difference 5 4) (sourceB1746 + difference 4 5) sourceC1746) = raw25470 := by
      apply Matrix.ext; unfold tripleCharges sourceA1746 sourceB1746 sourceC1746 difference raw25470; decide +kernel
    rw [ha]
    exact (canonical25470 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1746 sourceB1746 sourceC1746
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1746, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1747 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceB1747 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceC1747 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1747 : Integer.Sparse Master := [(Sum.inr 4248, 1), (Sum.inr 4251, 1), (Sum.inr 4255, 1), (Sum.inr 4264, 2), (Sum.inr 4395, 1), (Sum.inr 4396, 2), (Sum.inr 4406, 1), (Sum.inr 4435, 2), (Sum.inr 4438, 1), (Sum.inr 4450, 2), (Sum.inr 4452, 2), (Sum.inr 4457, 1), (Sum.inr 4458, 2), (Sum.inr 4470, 2), (Sum.inr 4474, 1), (Sum.inr 4496, 1), (Sum.inr 4498, 2), (Sum.inr 4589, 1), (Sum.inr 4606, 1), (Sum.inr 4607, 2), (Sum.inr 4623, 1)]

theorem sourceEq1747 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1747 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1747 + difference 0 1) (sourceB1747 + difference 1 0) sourceC1747) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4623) := by
    have ha : (tripleCharges (sourceA1747 + difference 0 1) (sourceB1747 + difference 1 0) sourceC1747) = raw24269 := by
      apply Matrix.ext; unfold tripleCharges sourceA1747 sourceB1747 sourceC1747 difference raw24269; decide +kernel
    rw [ha]
    exact (canonical24269 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1747 + difference 0 2) (sourceB1747 + difference 2 0) sourceC1747) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4589) := by
    have ha : (tripleCharges (sourceA1747 + difference 0 2) (sourceB1747 + difference 2 0) sourceC1747) = raw24158 := by
      apply Matrix.ext; unfold tripleCharges sourceA1747 sourceB1747 sourceC1747 difference raw24158; decide +kernel
    rw [ha]
    exact (canonical24158 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1747 + difference 0 3) (sourceB1747 + difference 3 0) sourceC1747) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4607) := by
    have ha : (tripleCharges (sourceA1747 + difference 0 3) (sourceB1747 + difference 3 0) sourceC1747) = raw24159 := by
      apply Matrix.ext; unfold tripleCharges sourceA1747 sourceB1747 sourceC1747 difference raw24159; decide +kernel
    rw [ha]
    exact (canonical24159 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1747 + difference 0 4) (sourceB1747 + difference 4 0) sourceC1747) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4607) := by
    have ha : (tripleCharges (sourceA1747 + difference 0 4) (sourceB1747 + difference 4 0) sourceC1747) = raw24160 := by
      apply Matrix.ext; unfold tripleCharges sourceA1747 sourceB1747 sourceC1747 difference raw24160; decide +kernel
    rw [ha]
    exact (canonical24160 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1747 + difference 0 5) (sourceB1747 + difference 5 0) sourceC1747) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4606) := by
    have ha : (tripleCharges (sourceA1747 + difference 0 5) (sourceB1747 + difference 5 0) sourceC1747) = raw24161 := by
      apply Matrix.ext; unfold tripleCharges sourceA1747 sourceB1747 sourceC1747 difference raw24161; decide +kernel
    rw [ha]
    exact (canonical24161 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1747 + difference 1 0) (sourceB1747 + difference 0 1) sourceC1747) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4255) := by
    have ha : (tripleCharges (sourceA1747 + difference 1 0) (sourceB1747 + difference 0 1) sourceC1747) = raw25471 := by
      apply Matrix.ext; unfold tripleCharges sourceA1747 sourceB1747 sourceC1747 difference raw25471; decide +kernel
    rw [ha]
    exact (canonical25471 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1747 + difference 1 2) (sourceB1747 + difference 2 1) sourceC1747) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4406) := by
    have ha : (tripleCharges (sourceA1747 + difference 1 2) (sourceB1747 + difference 2 1) sourceC1747) = raw25472 := by
      apply Matrix.ext; unfold tripleCharges sourceA1747 sourceB1747 sourceC1747 difference raw25472; decide +kernel
    rw [ha]
    exact (canonical25472 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1747 + difference 1 3) (sourceB1747 + difference 3 1) sourceC1747) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4470) := by
    have ha : (tripleCharges (sourceA1747 + difference 1 3) (sourceB1747 + difference 3 1) sourceC1747) = raw25473 := by
      apply Matrix.ext; unfold tripleCharges sourceA1747 sourceB1747 sourceC1747 difference raw25473; decide +kernel
    rw [ha]
    exact (canonical25473 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1747 + difference 1 4) (sourceB1747 + difference 4 1) sourceC1747) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4470) := by
    have ha : (tripleCharges (sourceA1747 + difference 1 4) (sourceB1747 + difference 4 1) sourceC1747) = raw25474 := by
      apply Matrix.ext; unfold tripleCharges sourceA1747 sourceB1747 sourceC1747 difference raw25474; decide +kernel
    rw [ha]
    exact (canonical25474 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1747 + difference 1 5) (sourceB1747 + difference 5 1) sourceC1747) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4474) := by
    have ha : (tripleCharges (sourceA1747 + difference 1 5) (sourceB1747 + difference 5 1) sourceC1747) = raw25275 := by
      apply Matrix.ext; unfold tripleCharges sourceA1747 sourceB1747 sourceC1747 difference raw25275; decide +kernel
    rw [ha]
    exact (canonical25275 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1747 + difference 2 0) (sourceB1747 + difference 0 2) sourceC1747) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4248) := by
    have ha : (tripleCharges (sourceA1747 + difference 2 0) (sourceB1747 + difference 0 2) sourceC1747) = raw25475 := by
      apply Matrix.ext; unfold tripleCharges sourceA1747 sourceB1747 sourceC1747 difference raw25475; decide +kernel
    rw [ha]
    exact (canonical25475 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1747 + difference 2 1) (sourceB1747 + difference 1 2) sourceC1747) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4457) := by
    have ha : (tripleCharges (sourceA1747 + difference 2 1) (sourceB1747 + difference 1 2) sourceC1747) = raw24162 := by
      apply Matrix.ext; unfold tripleCharges sourceA1747 sourceB1747 sourceC1747 difference raw24162; decide +kernel
    rw [ha]
    exact (canonical24162 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1747 + difference 2 3) (sourceB1747 + difference 3 2) sourceC1747) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4435) := by
    have ha : (tripleCharges (sourceA1747 + difference 2 3) (sourceB1747 + difference 3 2) sourceC1747) = raw25476 := by
      apply Matrix.ext; unfold tripleCharges sourceA1747 sourceB1747 sourceC1747 difference raw25476; decide +kernel
    rw [ha]
    exact (canonical25476 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1747 + difference 2 4) (sourceB1747 + difference 4 2) sourceC1747) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4435) := by
    have ha : (tripleCharges (sourceA1747 + difference 2 4) (sourceB1747 + difference 4 2) sourceC1747) = raw25477 := by
      apply Matrix.ext; unfold tripleCharges sourceA1747 sourceB1747 sourceC1747 difference raw25477; decide +kernel
    rw [ha]
    exact (canonical25477 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1747 + difference 2 5) (sourceB1747 + difference 5 2) sourceC1747) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4438) := by
    have ha : (tripleCharges (sourceA1747 + difference 2 5) (sourceB1747 + difference 5 2) sourceC1747) = raw25279 := by
      apply Matrix.ext; unfold tripleCharges sourceA1747 sourceB1747 sourceC1747 difference raw25279; decide +kernel
    rw [ha]
    exact (canonical25279 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1747 + difference 3 0) (sourceB1747 + difference 0 3) sourceC1747) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4264) := by
    have ha : (tripleCharges (sourceA1747 + difference 3 0) (sourceB1747 + difference 0 3) sourceC1747) = raw25286 := by
      apply Matrix.ext; unfold tripleCharges sourceA1747 sourceB1747 sourceC1747 difference raw25286; decide +kernel
    rw [ha]
    exact (canonical25286 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1747 + difference 3 1) (sourceB1747 + difference 1 3) sourceC1747) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4498) := by
    have ha : (tripleCharges (sourceA1747 + difference 3 1) (sourceB1747 + difference 1 3) sourceC1747) = raw24167 := by
      apply Matrix.ext; unfold tripleCharges sourceA1747 sourceB1747 sourceC1747 difference raw24167; decide +kernel
    rw [ha]
    exact (canonical24167 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1747 + difference 3 2) (sourceB1747 + difference 2 3) sourceC1747) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4396) := by
    have ha : (tripleCharges (sourceA1747 + difference 3 2) (sourceB1747 + difference 2 3) sourceC1747) = raw24815 := by
      apply Matrix.ext; unfold tripleCharges sourceA1747 sourceB1747 sourceC1747 difference raw24815; decide +kernel
    rw [ha]
    exact (canonical24815 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1747 + difference 3 4) (sourceB1747 + difference 4 3) sourceC1747) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4452) := by
    have ha : (tripleCharges (sourceA1747 + difference 3 4) (sourceB1747 + difference 4 3) sourceC1747) = raw25287 := by
      apply Matrix.ext; unfold tripleCharges sourceA1747 sourceB1747 sourceC1747 difference raw25287; decide +kernel
    rw [ha]
    exact (canonical25287 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1747 + difference 3 5) (sourceB1747 + difference 5 3) sourceC1747) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1747 + difference 3 5) (sourceB1747 + difference 5 3) sourceC1747) = raw25108 := by
      apply Matrix.ext; unfold tripleCharges sourceA1747 sourceB1747 sourceC1747 difference raw25108; decide +kernel
    rw [ha]
    exact (canonical25108 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1747 + difference 4 0) (sourceB1747 + difference 0 4) sourceC1747) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4264) := by
    have ha : (tripleCharges (sourceA1747 + difference 4 0) (sourceB1747 + difference 0 4) sourceC1747) = raw25478 := by
      apply Matrix.ext; unfold tripleCharges sourceA1747 sourceB1747 sourceC1747 difference raw25478; decide +kernel
    rw [ha]
    exact (canonical25478 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1747 + difference 4 1) (sourceB1747 + difference 1 4) sourceC1747) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4498) := by
    have ha : (tripleCharges (sourceA1747 + difference 4 1) (sourceB1747 + difference 1 4) sourceC1747) = raw24172 := by
      apply Matrix.ext; unfold tripleCharges sourceA1747 sourceB1747 sourceC1747 difference raw24172; decide +kernel
    rw [ha]
    exact (canonical24172 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1747 + difference 4 2) (sourceB1747 + difference 2 4) sourceC1747) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4396) := by
    have ha : (tripleCharges (sourceA1747 + difference 4 2) (sourceB1747 + difference 2 4) sourceC1747) = raw25479 := by
      apply Matrix.ext; unfold tripleCharges sourceA1747 sourceB1747 sourceC1747 difference raw25479; decide +kernel
    rw [ha]
    exact (canonical25479 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1747 + difference 4 3) (sourceB1747 + difference 3 4) sourceC1747) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4452) := by
    have ha : (tripleCharges (sourceA1747 + difference 4 3) (sourceB1747 + difference 3 4) sourceC1747) = raw25480 := by
      apply Matrix.ext; unfold tripleCharges sourceA1747 sourceB1747 sourceC1747 difference raw25480; decide +kernel
    rw [ha]
    exact (canonical25480 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1747 + difference 4 5) (sourceB1747 + difference 5 4) sourceC1747) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1747 + difference 4 5) (sourceB1747 + difference 5 4) sourceC1747) = raw24252 := by
      apply Matrix.ext; unfold tripleCharges sourceA1747 sourceB1747 sourceC1747 difference raw24252; decide +kernel
    rw [ha]
    exact (canonical24252 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1747 + difference 5 0) (sourceB1747 + difference 0 5) sourceC1747) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4251) := by
    have ha : (tripleCharges (sourceA1747 + difference 5 0) (sourceB1747 + difference 0 5) sourceC1747) = raw25481 := by
      apply Matrix.ext; unfold tripleCharges sourceA1747 sourceB1747 sourceC1747 difference raw25481; decide +kernel
    rw [ha]
    exact (canonical25481 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1747 + difference 5 1) (sourceB1747 + difference 1 5) sourceC1747) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4496) := by
    have ha : (tripleCharges (sourceA1747 + difference 5 1) (sourceB1747 + difference 1 5) sourceC1747) = raw24177 := by
      apply Matrix.ext; unfold tripleCharges sourceA1747 sourceB1747 sourceC1747 difference raw24177; decide +kernel
    rw [ha]
    exact (canonical24177 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1747 + difference 5 2) (sourceB1747 + difference 2 5) sourceC1747) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4395) := by
    have ha : (tripleCharges (sourceA1747 + difference 5 2) (sourceB1747 + difference 2 5) sourceC1747) = raw25482 := by
      apply Matrix.ext; unfold tripleCharges sourceA1747 sourceB1747 sourceC1747 difference raw25482; decide +kernel
    rw [ha]
    exact (canonical25482 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1747 + difference 5 3) (sourceB1747 + difference 3 5) sourceC1747) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4450) := by
    have ha : (tripleCharges (sourceA1747 + difference 5 3) (sourceB1747 + difference 3 5) sourceC1747) = raw25483 := by
      apply Matrix.ext; unfold tripleCharges sourceA1747 sourceB1747 sourceC1747 difference raw25483; decide +kernel
    rw [ha]
    exact (canonical25483 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1747 + difference 5 4) (sourceB1747 + difference 4 5) sourceC1747) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4450) := by
    have ha : (tripleCharges (sourceA1747 + difference 5 4) (sourceB1747 + difference 4 5) sourceC1747) = raw25484 := by
      apply Matrix.ext; unfold tripleCharges sourceA1747 sourceB1747 sourceC1747 difference raw25484; decide +kernel
    rw [ha]
    exact (canonical25484 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1747 sourceB1747 sourceC1747
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1747, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1748 : Charge := ![1, 1, 0, -1, -1, 0]
def sourceB1748 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceC1748 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1748 : Integer.Sparse Master := [(Sum.inr 1216, 1), (Sum.inr 1240, 1), (Sum.inr 1241, 2), (Sum.inr 1305, 1), (Sum.inr 1360, 1), (Sum.inr 1370, 1), (Sum.inr 1371, 2), (Sum.inr 1386, 1), (Sum.inr 1387, 2), (Sum.inr 1396, 2), (Sum.inr 1398, 1), (Sum.inr 1411, 2), (Sum.inr 1412, 2), (Sum.inr 1414, 1), (Sum.inr 1415, 2), (Sum.inr 1448, 2), (Sum.inr 1451, 1), (Sum.inr 1470, 1), (Sum.inr 1477, 1), (Sum.inr 1478, 1), (Sum.inr 1483, 2)]

theorem sourceEq1748 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1748 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1748 + difference 0 1) (sourceB1748 + difference 1 0) sourceC1748) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1305) := by
    have ha : (tripleCharges (sourceA1748 + difference 0 1) (sourceB1748 + difference 1 0) sourceC1748) = raw25485 := by
      apply Matrix.ext; unfold tripleCharges sourceA1748 sourceB1748 sourceC1748 difference raw25485; decide +kernel
    rw [ha]
    exact (canonical25485 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1748 + difference 0 2) (sourceB1748 + difference 2 0) sourceC1748) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1216) := by
    have ha : (tripleCharges (sourceA1748 + difference 0 2) (sourceB1748 + difference 2 0) sourceC1748) = raw24188 := by
      apply Matrix.ext; unfold tripleCharges sourceA1748 sourceB1748 sourceC1748 difference raw24188; decide +kernel
    rw [ha]
    exact (canonical24188 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1748 + difference 0 3) (sourceB1748 + difference 3 0) sourceC1748) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1241) := by
    have ha : (tripleCharges (sourceA1748 + difference 0 3) (sourceB1748 + difference 3 0) sourceC1748) = raw24189 := by
      apply Matrix.ext; unfold tripleCharges sourceA1748 sourceB1748 sourceC1748 difference raw24189; decide +kernel
    rw [ha]
    exact (canonical24189 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1748 + difference 0 4) (sourceB1748 + difference 4 0) sourceC1748) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1241) := by
    have ha : (tripleCharges (sourceA1748 + difference 0 4) (sourceB1748 + difference 4 0) sourceC1748) = raw24190 := by
      apply Matrix.ext; unfold tripleCharges sourceA1748 sourceB1748 sourceC1748 difference raw24190; decide +kernel
    rw [ha]
    exact (canonical24190 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1748 + difference 0 5) (sourceB1748 + difference 5 0) sourceC1748) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1240) := by
    have ha : (tripleCharges (sourceA1748 + difference 0 5) (sourceB1748 + difference 5 0) sourceC1748) = raw24191 := by
      apply Matrix.ext; unfold tripleCharges sourceA1748 sourceB1748 sourceC1748 difference raw24191; decide +kernel
    rw [ha]
    exact (canonical24191 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1748 + difference 1 0) (sourceB1748 + difference 0 1) sourceC1748) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1470) := by
    have ha : (tripleCharges (sourceA1748 + difference 1 0) (sourceB1748 + difference 0 1) sourceC1748) = raw25486 := by
      apply Matrix.ext; unfold tripleCharges sourceA1748 sourceB1748 sourceC1748 difference raw25486; decide +kernel
    rw [ha]
    exact (canonical25486 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1748 + difference 1 2) (sourceB1748 + difference 2 1) sourceC1748) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1360) := by
    have ha : (tripleCharges (sourceA1748 + difference 1 2) (sourceB1748 + difference 2 1) sourceC1748) = raw25487 := by
      apply Matrix.ext; unfold tripleCharges sourceA1748 sourceB1748 sourceC1748 difference raw25487; decide +kernel
    rw [ha]
    exact (canonical25487 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1748 + difference 1 3) (sourceB1748 + difference 3 1) sourceC1748) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1371) := by
    have ha : (tripleCharges (sourceA1748 + difference 1 3) (sourceB1748 + difference 3 1) sourceC1748) = raw25488 := by
      apply Matrix.ext; unfold tripleCharges sourceA1748 sourceB1748 sourceC1748 difference raw25488; decide +kernel
    rw [ha]
    exact (canonical25488 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1748 + difference 1 4) (sourceB1748 + difference 4 1) sourceC1748) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1371) := by
    have ha : (tripleCharges (sourceA1748 + difference 1 4) (sourceB1748 + difference 4 1) sourceC1748) = raw25489 := by
      apply Matrix.ext; unfold tripleCharges sourceA1748 sourceB1748 sourceC1748 difference raw25489; decide +kernel
    rw [ha]
    exact (canonical25489 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1748 + difference 1 5) (sourceB1748 + difference 5 1) sourceC1748) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1370) := by
    have ha : (tripleCharges (sourceA1748 + difference 1 5) (sourceB1748 + difference 5 1) sourceC1748) = raw25313 := by
      apply Matrix.ext; unfold tripleCharges sourceA1748 sourceB1748 sourceC1748 difference raw25313; decide +kernel
    rw [ha]
    exact (canonical25313 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1748 + difference 2 0) (sourceB1748 + difference 0 2) sourceC1748) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1477) := by
    have ha : (tripleCharges (sourceA1748 + difference 2 0) (sourceB1748 + difference 0 2) sourceC1748) = raw25490 := by
      apply Matrix.ext; unfold tripleCharges sourceA1748 sourceB1748 sourceC1748 difference raw25490; decide +kernel
    rw [ha]
    exact (canonical25490 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1748 + difference 2 1) (sourceB1748 + difference 1 2) sourceC1748) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1414) := by
    have ha : (tripleCharges (sourceA1748 + difference 2 1) (sourceB1748 + difference 1 2) sourceC1748) = raw24192 := by
      apply Matrix.ext; unfold tripleCharges sourceA1748 sourceB1748 sourceC1748 difference raw24192; decide +kernel
    rw [ha]
    exact (canonical24192 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1748 + difference 2 3) (sourceB1748 + difference 3 2) sourceC1748) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1387) := by
    have ha : (tripleCharges (sourceA1748 + difference 2 3) (sourceB1748 + difference 3 2) sourceC1748) = raw25491 := by
      apply Matrix.ext; unfold tripleCharges sourceA1748 sourceB1748 sourceC1748 difference raw25491; decide +kernel
    rw [ha]
    exact (canonical25491 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1748 + difference 2 4) (sourceB1748 + difference 4 2) sourceC1748) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1387) := by
    have ha : (tripleCharges (sourceA1748 + difference 2 4) (sourceB1748 + difference 4 2) sourceC1748) = raw25492 := by
      apply Matrix.ext; unfold tripleCharges sourceA1748 sourceB1748 sourceC1748 difference raw25492; decide +kernel
    rw [ha]
    exact (canonical25492 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1748 + difference 2 5) (sourceB1748 + difference 5 2) sourceC1748) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1386) := by
    have ha : (tripleCharges (sourceA1748 + difference 2 5) (sourceB1748 + difference 5 2) sourceC1748) = raw25318 := by
      apply Matrix.ext; unfold tripleCharges sourceA1748 sourceB1748 sourceC1748 difference raw25318; decide +kernel
    rw [ha]
    exact (canonical25318 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1748 + difference 3 0) (sourceB1748 + difference 0 3) sourceC1748) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1483) := by
    have ha : (tripleCharges (sourceA1748 + difference 3 0) (sourceB1748 + difference 0 3) sourceC1748) = raw25331 := by
      apply Matrix.ext; unfold tripleCharges sourceA1748 sourceB1748 sourceC1748 difference raw25331; decide +kernel
    rw [ha]
    exact (canonical25331 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1748 + difference 3 1) (sourceB1748 + difference 1 3) sourceC1748) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1448) := by
    have ha : (tripleCharges (sourceA1748 + difference 3 1) (sourceB1748 + difference 1 3) sourceC1748) = raw24197 := by
      apply Matrix.ext; unfold tripleCharges sourceA1748 sourceB1748 sourceC1748 difference raw24197; decide +kernel
    rw [ha]
    exact (canonical24197 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1748 + difference 3 2) (sourceB1748 + difference 2 3) sourceC1748) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1396) := by
    have ha : (tripleCharges (sourceA1748 + difference 3 2) (sourceB1748 + difference 2 3) sourceC1748) = raw25332 := by
      apply Matrix.ext; unfold tripleCharges sourceA1748 sourceB1748 sourceC1748 difference raw25332; decide +kernel
    rw [ha]
    exact (canonical25332 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1748 + difference 3 4) (sourceB1748 + difference 4 3) sourceC1748) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1412) := by
    have ha : (tripleCharges (sourceA1748 + difference 3 4) (sourceB1748 + difference 4 3) sourceC1748) = raw25333 := by
      apply Matrix.ext; unfold tripleCharges sourceA1748 sourceB1748 sourceC1748 difference raw25333; decide +kernel
    rw [ha]
    exact (canonical25333 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1748 + difference 3 5) (sourceB1748 + difference 5 3) sourceC1748) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1411) := by
    have ha : (tripleCharges (sourceA1748 + difference 3 5) (sourceB1748 + difference 5 3) sourceC1748) = raw25493 := by
      apply Matrix.ext; unfold tripleCharges sourceA1748 sourceB1748 sourceC1748 difference raw25493; decide +kernel
    rw [ha]
    exact (canonical25493 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1748 + difference 4 0) (sourceB1748 + difference 0 4) sourceC1748) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1483) := by
    have ha : (tripleCharges (sourceA1748 + difference 4 0) (sourceB1748 + difference 0 4) sourceC1748) = raw25494 := by
      apply Matrix.ext; unfold tripleCharges sourceA1748 sourceB1748 sourceC1748 difference raw25494; decide +kernel
    rw [ha]
    exact (canonical25494 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1748 + difference 4 1) (sourceB1748 + difference 1 4) sourceC1748) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1448) := by
    have ha : (tripleCharges (sourceA1748 + difference 4 1) (sourceB1748 + difference 1 4) sourceC1748) = raw24202 := by
      apply Matrix.ext; unfold tripleCharges sourceA1748 sourceB1748 sourceC1748 difference raw24202; decide +kernel
    rw [ha]
    exact (canonical24202 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1748 + difference 4 2) (sourceB1748 + difference 2 4) sourceC1748) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1396) := by
    have ha : (tripleCharges (sourceA1748 + difference 4 2) (sourceB1748 + difference 2 4) sourceC1748) = raw25495 := by
      apply Matrix.ext; unfold tripleCharges sourceA1748 sourceB1748 sourceC1748 difference raw25495; decide +kernel
    rw [ha]
    exact (canonical25495 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1748 + difference 4 3) (sourceB1748 + difference 3 4) sourceC1748) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1412) := by
    have ha : (tripleCharges (sourceA1748 + difference 4 3) (sourceB1748 + difference 3 4) sourceC1748) = raw25496 := by
      apply Matrix.ext; unfold tripleCharges sourceA1748 sourceB1748 sourceC1748 difference raw25496; decide +kernel
    rw [ha]
    exact (canonical25496 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1748 + difference 4 5) (sourceB1748 + difference 5 4) sourceC1748) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1411) := by
    have ha : (tripleCharges (sourceA1748 + difference 4 5) (sourceB1748 + difference 5 4) sourceC1748) = raw25329 := by
      apply Matrix.ext; unfold tripleCharges sourceA1748 sourceB1748 sourceC1748 difference raw25329; decide +kernel
    rw [ha]
    exact (canonical25329 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1748 + difference 5 0) (sourceB1748 + difference 0 5) sourceC1748) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1478) := by
    have ha : (tripleCharges (sourceA1748 + difference 5 0) (sourceB1748 + difference 0 5) sourceC1748) = raw25497 := by
      apply Matrix.ext; unfold tripleCharges sourceA1748 sourceB1748 sourceC1748 difference raw25497; decide +kernel
    rw [ha]
    exact (canonical25497 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1748 + difference 5 1) (sourceB1748 + difference 1 5) sourceC1748) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1451) := by
    have ha : (tripleCharges (sourceA1748 + difference 5 1) (sourceB1748 + difference 1 5) sourceC1748) = raw24207 := by
      apply Matrix.ext; unfold tripleCharges sourceA1748 sourceB1748 sourceC1748 difference raw24207; decide +kernel
    rw [ha]
    exact (canonical24207 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1748 + difference 5 2) (sourceB1748 + difference 2 5) sourceC1748) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1398) := by
    have ha : (tripleCharges (sourceA1748 + difference 5 2) (sourceB1748 + difference 2 5) sourceC1748) = raw25498 := by
      apply Matrix.ext; unfold tripleCharges sourceA1748 sourceB1748 sourceC1748 difference raw25498; decide +kernel
    rw [ha]
    exact (canonical25498 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1748 + difference 5 3) (sourceB1748 + difference 3 5) sourceC1748) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1415) := by
    have ha : (tripleCharges (sourceA1748 + difference 5 3) (sourceB1748 + difference 3 5) sourceC1748) = raw25499 := by
      apply Matrix.ext; unfold tripleCharges sourceA1748 sourceB1748 sourceC1748 difference raw25499; decide +kernel
    rw [ha]
    exact (canonical25499 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1748 + difference 5 4) (sourceB1748 + difference 4 5) sourceC1748) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1415) := by
    have ha : (tripleCharges (sourceA1748 + difference 5 4) (sourceB1748 + difference 4 5) sourceC1748) = raw25500 := by
      apply Matrix.ext; unfold tripleCharges sourceA1748 sourceB1748 sourceC1748 difference raw25500; decide +kernel
    rw [ha]
    exact (canonical25500 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1748 sourceB1748 sourceC1748
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1748, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1749 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1749 : Charge := ![1, 1, 0, -1, -2, 1]
def sourceC1749 : Charge := ![3, -1, 0, 0, 1, -3]
def sourceForm1749 : Integer.Sparse Master := [(Sum.inr 1033, 1), (Sum.inr 2015, 1), (Sum.inr 2099, 1), (Sum.inr 2203, 1), (Sum.inr 2259, 1), (Sum.inr 2261, 1), (Sum.inr 4081, -1)]

theorem sourceEq1749 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1749 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1749 + difference 0 0) (sourceB1749 + difference 0 0) sourceC1749) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1033) := by
    have ha : (tripleCharges (sourceA1749 + difference 0 0) (sourceB1749 + difference 0 0) sourceC1749) = raw21573 := by
      apply Matrix.ext; unfold tripleCharges sourceA1749 sourceB1749 sourceC1749 difference raw21573; decide +kernel
    rw [ha]
    exact (canonical21573 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1749 + difference 0 1) (sourceB1749 + difference 1 0) sourceC1749) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2099) := by
    have ha : (tripleCharges (sourceA1749 + difference 0 1) (sourceB1749 + difference 1 0) sourceC1749) = raw25501 := by
      apply Matrix.ext; unfold tripleCharges sourceA1749 sourceB1749 sourceC1749 difference raw25501; decide +kernel
    rw [ha]
    exact (canonical25501 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1749 + difference 0 2) (sourceB1749 + difference 2 0) sourceC1749) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2015) := by
    have ha : (tripleCharges (sourceA1749 + difference 0 2) (sourceB1749 + difference 2 0) sourceC1749) = raw25502 := by
      apply Matrix.ext; unfold tripleCharges sourceA1749 sourceB1749 sourceC1749 difference raw25502; decide +kernel
    rw [ha]
    exact (canonical25502 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1749 + difference 0 3) (sourceB1749 + difference 3 0) sourceC1749) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2261) := by
    have ha : (tripleCharges (sourceA1749 + difference 0 3) (sourceB1749 + difference 3 0) sourceC1749) = raw21567 := by
      apply Matrix.ext; unfold tripleCharges sourceA1749 sourceB1749 sourceC1749 difference raw21567; decide +kernel
    rw [ha]
    exact (canonical21567 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1749 + difference 0 4) (sourceB1749 + difference 4 0) sourceC1749) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2203) := by
    have ha : (tripleCharges (sourceA1749 + difference 0 4) (sourceB1749 + difference 4 0) sourceC1749) = raw25503 := by
      apply Matrix.ext; unfold tripleCharges sourceA1749 sourceB1749 sourceC1749 difference raw25503; decide +kernel
    rw [ha]
    exact (canonical25503 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1749 + difference 0 5) (sourceB1749 + difference 5 0) sourceC1749) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2259) := by
    have ha : (tripleCharges (sourceA1749 + difference 0 5) (sourceB1749 + difference 5 0) sourceC1749) = raw25504 := by
      apply Matrix.ext; unfold tripleCharges sourceA1749 sourceB1749 sourceC1749 difference raw25504; decide +kernel
    rw [ha]
    exact (canonical25504 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1749 + sourceB1749) sourceC1749) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1749 + sourceB1749) sourceC1749) = raw19876 := by
      apply Matrix.ext; unfold doubleCharges sourceA1749 sourceB1749 sourceC1749 raw19876; decide +kernel
    rw [ha]
    exact (canonical19876 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1749 sourceB1749 sourceC1749
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1749, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1750 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1750 : Charge := ![1, 1, -1, 1, 0, -2]
def sourceC1750 : Charge := ![3, -1, 1, -2, -1, 0]
def sourceForm1750 : Integer.Sparse Master := [(Sum.inr 981, 1), (Sum.inr 1913, 1), (Sum.inr 2078, 1), (Sum.inr 2192, 1), (Sum.inr 2196, 1), (Sum.inr 2202, 1), (Sum.inr 4080, -1)]

theorem sourceEq1750 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1750 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1750 + difference 0 0) (sourceB1750 + difference 0 0) sourceC1750) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 981) := by
    have ha : (tripleCharges (sourceA1750 + difference 0 0) (sourceB1750 + difference 0 0) sourceC1750) = raw25505 := by
      apply Matrix.ext; unfold tripleCharges sourceA1750 sourceB1750 sourceC1750 difference raw25505; decide +kernel
    rw [ha]
    exact (canonical25505 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1750 + difference 0 1) (sourceB1750 + difference 1 0) sourceC1750) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2078) := by
    have ha : (tripleCharges (sourceA1750 + difference 0 1) (sourceB1750 + difference 1 0) sourceC1750) = raw25506 := by
      apply Matrix.ext; unfold tripleCharges sourceA1750 sourceB1750 sourceC1750 difference raw25506; decide +kernel
    rw [ha]
    exact (canonical25506 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1750 + difference 0 2) (sourceB1750 + difference 2 0) sourceC1750) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1913) := by
    have ha : (tripleCharges (sourceA1750 + difference 0 2) (sourceB1750 + difference 2 0) sourceC1750) = raw25507 := by
      apply Matrix.ext; unfold tripleCharges sourceA1750 sourceB1750 sourceC1750 difference raw25507; decide +kernel
    rw [ha]
    exact (canonical25507 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1750 + difference 0 3) (sourceB1750 + difference 3 0) sourceC1750) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2196) := by
    have ha : (tripleCharges (sourceA1750 + difference 0 3) (sourceB1750 + difference 3 0) sourceC1750) = raw25508 := by
      apply Matrix.ext; unfold tripleCharges sourceA1750 sourceB1750 sourceC1750 difference raw25508; decide +kernel
    rw [ha]
    exact (canonical25508 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1750 + difference 0 4) (sourceB1750 + difference 4 0) sourceC1750) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2192) := by
    have ha : (tripleCharges (sourceA1750 + difference 0 4) (sourceB1750 + difference 4 0) sourceC1750) = raw25509 := by
      apply Matrix.ext; unfold tripleCharges sourceA1750 sourceB1750 sourceC1750 difference raw25509; decide +kernel
    rw [ha]
    exact (canonical25509 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1750 + difference 0 5) (sourceB1750 + difference 5 0) sourceC1750) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2202) := by
    have ha : (tripleCharges (sourceA1750 + difference 0 5) (sourceB1750 + difference 5 0) sourceC1750) = raw25510 := by
      apply Matrix.ext; unfold tripleCharges sourceA1750 sourceB1750 sourceC1750 difference raw25510; decide +kernel
    rw [ha]
    exact (canonical25510 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1750 + sourceB1750) sourceC1750) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1750 + sourceB1750) sourceC1750) = raw25511 := by
      apply Matrix.ext; unfold doubleCharges sourceA1750 sourceB1750 sourceC1750 raw25511; decide +kernel
    rw [ha]
    exact (canonical25511 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1750 sourceB1750 sourceC1750
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1750, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1751 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1751 : Charge := ![1, 1, -1, 1, 0, -2]
def sourceC1751 : Charge := ![3, -1, 1, -2, -1, 0]
def sourceForm1751 : Integer.Sparse Master := [(Sum.inr 977, 1), (Sum.inr 978, 1), (Sum.inr 981, 1), (Sum.inr 998, 1), (Sum.inr 1032, 1), (Sum.inr 2202, 1), (Sum.inr 4080, -1)]

theorem sourceEq1751 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1751 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1751 + difference 0 5) (sourceB1751 + difference 5 0) sourceC1751) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2202) := by
    have ha : (tripleCharges (sourceA1751 + difference 0 5) (sourceB1751 + difference 5 0) sourceC1751) = raw25510 := by
      apply Matrix.ext; unfold tripleCharges sourceA1751 sourceB1751 sourceC1751 difference raw25510; decide +kernel
    rw [ha]
    exact (canonical25510 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1751 + difference 1 5) (sourceB1751 + difference 5 1) sourceC1751) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 998) := by
    have ha : (tripleCharges (sourceA1751 + difference 1 5) (sourceB1751 + difference 5 1) sourceC1751) = raw25512 := by
      apply Matrix.ext; unfold tripleCharges sourceA1751 sourceB1751 sourceC1751 difference raw25512; decide +kernel
    rw [ha]
    exact (canonical25512 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1751 + difference 2 5) (sourceB1751 + difference 5 2) sourceC1751) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1032) := by
    have ha : (tripleCharges (sourceA1751 + difference 2 5) (sourceB1751 + difference 5 2) sourceC1751) = raw25513 := by
      apply Matrix.ext; unfold tripleCharges sourceA1751 sourceB1751 sourceC1751 difference raw25513; decide +kernel
    rw [ha]
    exact (canonical25513 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1751 + difference 3 5) (sourceB1751 + difference 5 3) sourceC1751) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 977) := by
    have ha : (tripleCharges (sourceA1751 + difference 3 5) (sourceB1751 + difference 5 3) sourceC1751) = raw25514 := by
      apply Matrix.ext; unfold tripleCharges sourceA1751 sourceB1751 sourceC1751 difference raw25514; decide +kernel
    rw [ha]
    exact (canonical25514 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1751 + difference 4 5) (sourceB1751 + difference 5 4) sourceC1751) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 978) := by
    have ha : (tripleCharges (sourceA1751 + difference 4 5) (sourceB1751 + difference 5 4) sourceC1751) = raw25515 := by
      apply Matrix.ext; unfold tripleCharges sourceA1751 sourceB1751 sourceC1751 difference raw25515; decide +kernel
    rw [ha]
    exact (canonical25515 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1751 + difference 5 5) (sourceB1751 + difference 5 5) sourceC1751) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 981) := by
    have ha : (tripleCharges (sourceA1751 + difference 5 5) (sourceB1751 + difference 5 5) sourceC1751) = raw25505 := by
      apply Matrix.ext; unfold tripleCharges sourceA1751 sourceB1751 sourceC1751 difference raw25505; decide +kernel
    rw [ha]
    exact (canonical25505 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1751 + sourceB1751) sourceC1751) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1751 + sourceB1751) sourceC1751) = raw25511 := by
      apply Matrix.ext; unfold doubleCharges sourceA1751 sourceB1751 sourceC1751 raw25511; decide +kernel
    rw [ha]
    exact (canonical25511 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1751 sourceB1751 sourceC1751
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1751, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1752 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1752 : Charge := ![1, 1, -1, 1, -1, -1]
def sourceC1752 : Charge := ![3, -1, 1, -2, 0, -1]
def sourceForm1752 : Integer.Sparse Master := [(Sum.inr 978, 1), (Sum.inr 1909, 1), (Sum.inr 2076, 1), (Sum.inr 2195, 1), (Sum.inr 2202, 1), (Sum.inr 2206, 1), (Sum.inr 4080, -1)]

theorem sourceEq1752 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1752 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1752 + difference 0 0) (sourceB1752 + difference 0 0) sourceC1752) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 978) := by
    have ha : (tripleCharges (sourceA1752 + difference 0 0) (sourceB1752 + difference 0 0) sourceC1752) = raw25516 := by
      apply Matrix.ext; unfold tripleCharges sourceA1752 sourceB1752 sourceC1752 difference raw25516; decide +kernel
    rw [ha]
    exact (canonical25516 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1752 + difference 0 1) (sourceB1752 + difference 1 0) sourceC1752) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2076) := by
    have ha : (tripleCharges (sourceA1752 + difference 0 1) (sourceB1752 + difference 1 0) sourceC1752) = raw25517 := by
      apply Matrix.ext; unfold tripleCharges sourceA1752 sourceB1752 sourceC1752 difference raw25517; decide +kernel
    rw [ha]
    exact (canonical25517 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1752 + difference 0 2) (sourceB1752 + difference 2 0) sourceC1752) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1909) := by
    have ha : (tripleCharges (sourceA1752 + difference 0 2) (sourceB1752 + difference 2 0) sourceC1752) = raw25518 := by
      apply Matrix.ext; unfold tripleCharges sourceA1752 sourceB1752 sourceC1752 difference raw25518; decide +kernel
    rw [ha]
    exact (canonical25518 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1752 + difference 0 3) (sourceB1752 + difference 3 0) sourceC1752) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2195) := by
    have ha : (tripleCharges (sourceA1752 + difference 0 3) (sourceB1752 + difference 3 0) sourceC1752) = raw25519 := by
      apply Matrix.ext; unfold tripleCharges sourceA1752 sourceB1752 sourceC1752 difference raw25519; decide +kernel
    rw [ha]
    exact (canonical25519 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1752 + difference 0 4) (sourceB1752 + difference 4 0) sourceC1752) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2206) := by
    have ha : (tripleCharges (sourceA1752 + difference 0 4) (sourceB1752 + difference 4 0) sourceC1752) = raw25520 := by
      apply Matrix.ext; unfold tripleCharges sourceA1752 sourceB1752 sourceC1752 difference raw25520; decide +kernel
    rw [ha]
    exact (canonical25520 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1752 + difference 0 5) (sourceB1752 + difference 5 0) sourceC1752) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2202) := by
    have ha : (tripleCharges (sourceA1752 + difference 0 5) (sourceB1752 + difference 5 0) sourceC1752) = raw25521 := by
      apply Matrix.ext; unfold tripleCharges sourceA1752 sourceB1752 sourceC1752 difference raw25521; decide +kernel
    rw [ha]
    exact (canonical25521 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1752 + sourceB1752) sourceC1752) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1752 + sourceB1752) sourceC1752) = raw25522 := by
      apply Matrix.ext; unfold doubleCharges sourceA1752 sourceB1752 sourceC1752 raw25522; decide +kernel
    rw [ha]
    exact (canonical25522 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1752 sourceB1752 sourceC1752
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1752, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1753 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1753 : Charge := ![1, 1, -1, 0, 0, -1]
def sourceC1753 : Charge := ![3, -1, 1, -1, -1, -1]
def sourceForm1753 : Integer.Sparse Master := [(Sum.inr 980, 1), (Sum.inr 1912, 1), (Sum.inr 2077, 1), (Sum.inr 2191, 2), (Sum.inr 2204, 1), (Sum.inr 4079, -1)]

theorem sourceEq1753 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1753 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1753 + difference 0 0) (sourceB1753 + difference 0 0) sourceC1753) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 980) := by
    have ha : (tripleCharges (sourceA1753 + difference 0 0) (sourceB1753 + difference 0 0) sourceC1753) = raw25523 := by
      apply Matrix.ext; unfold tripleCharges sourceA1753 sourceB1753 sourceC1753 difference raw25523; decide +kernel
    rw [ha]
    exact (canonical25523 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1753 + difference 0 1) (sourceB1753 + difference 1 0) sourceC1753) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2077) := by
    have ha : (tripleCharges (sourceA1753 + difference 0 1) (sourceB1753 + difference 1 0) sourceC1753) = raw25524 := by
      apply Matrix.ext; unfold tripleCharges sourceA1753 sourceB1753 sourceC1753 difference raw25524; decide +kernel
    rw [ha]
    exact (canonical25524 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1753 + difference 0 2) (sourceB1753 + difference 2 0) sourceC1753) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1912) := by
    have ha : (tripleCharges (sourceA1753 + difference 0 2) (sourceB1753 + difference 2 0) sourceC1753) = raw25525 := by
      apply Matrix.ext; unfold tripleCharges sourceA1753 sourceB1753 sourceC1753 difference raw25525; decide +kernel
    rw [ha]
    exact (canonical25525 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1753 + difference 0 3) (sourceB1753 + difference 3 0) sourceC1753) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2191) := by
    have ha : (tripleCharges (sourceA1753 + difference 0 3) (sourceB1753 + difference 3 0) sourceC1753) = raw25526 := by
      apply Matrix.ext; unfold tripleCharges sourceA1753 sourceB1753 sourceC1753 difference raw25526; decide +kernel
    rw [ha]
    exact (canonical25526 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1753 + difference 0 4) (sourceB1753 + difference 4 0) sourceC1753) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2191) := by
    have ha : (tripleCharges (sourceA1753 + difference 0 4) (sourceB1753 + difference 4 0) sourceC1753) = raw25527 := by
      apply Matrix.ext; unfold tripleCharges sourceA1753 sourceB1753 sourceC1753 difference raw25527; decide +kernel
    rw [ha]
    exact (canonical25527 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1753 + difference 0 5) (sourceB1753 + difference 5 0) sourceC1753) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2204) := by
    have ha : (tripleCharges (sourceA1753 + difference 0 5) (sourceB1753 + difference 5 0) sourceC1753) = raw25528 := by
      apply Matrix.ext; unfold tripleCharges sourceA1753 sourceB1753 sourceC1753 difference raw25528; decide +kernel
    rw [ha]
    exact (canonical25528 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1753 + sourceB1753) sourceC1753) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4079) := by
    have ha : (doubleCharges (sourceA1753 + sourceB1753) sourceC1753) = raw25529 := by
      apply Matrix.ext; unfold doubleCharges sourceA1753 sourceB1753 sourceC1753 raw25529; decide +kernel
    rw [ha]
    exact (canonical25529 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1753 sourceB1753 sourceC1753
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1753, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1754 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1754 : Charge := ![1, 1, -1, 0, 0, -1]
def sourceC1754 : Charge := ![3, -1, 1, -1, -1, -1]
def sourceForm1754 : Integer.Sparse Master := [(Sum.inr 571, 1), (Sum.inr 884, 1), (Sum.inr 980, 3), (Sum.inr 1003, 1), (Sum.inr 4079, -1)]

theorem sourceEq1754 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1754 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1754 + difference 1 0) (sourceB1754 + difference 0 1) sourceC1754) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 571) := by
    have ha : (tripleCharges (sourceA1754 + difference 1 0) (sourceB1754 + difference 0 1) sourceC1754) = raw25530 := by
      apply Matrix.ext; unfold tripleCharges sourceA1754 sourceB1754 sourceC1754 difference raw25530; decide +kernel
    rw [ha]
    exact (canonical25530 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1754 + difference 1 1) (sourceB1754 + difference 1 1) sourceC1754) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 980) := by
    have ha : (tripleCharges (sourceA1754 + difference 1 1) (sourceB1754 + difference 1 1) sourceC1754) = raw25523 := by
      apply Matrix.ext; unfold tripleCharges sourceA1754 sourceB1754 sourceC1754 difference raw25523; decide +kernel
    rw [ha]
    exact (canonical25523 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1754 + difference 1 2) (sourceB1754 + difference 2 1) sourceC1754) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 884) := by
    have ha : (tripleCharges (sourceA1754 + difference 1 2) (sourceB1754 + difference 2 1) sourceC1754) = raw25531 := by
      apply Matrix.ext; unfold tripleCharges sourceA1754 sourceB1754 sourceC1754 difference raw25531; decide +kernel
    rw [ha]
    exact (canonical25531 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1754 + difference 1 3) (sourceB1754 + difference 3 1) sourceC1754) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 980) := by
    have ha : (tripleCharges (sourceA1754 + difference 1 3) (sourceB1754 + difference 3 1) sourceC1754) = raw25532 := by
      apply Matrix.ext; unfold tripleCharges sourceA1754 sourceB1754 sourceC1754 difference raw25532; decide +kernel
    rw [ha]
    exact (canonical25532 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1754 + difference 1 4) (sourceB1754 + difference 4 1) sourceC1754) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 980) := by
    have ha : (tripleCharges (sourceA1754 + difference 1 4) (sourceB1754 + difference 4 1) sourceC1754) = raw25533 := by
      apply Matrix.ext; unfold tripleCharges sourceA1754 sourceB1754 sourceC1754 difference raw25533; decide +kernel
    rw [ha]
    exact (canonical25533 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1754 + difference 1 5) (sourceB1754 + difference 5 1) sourceC1754) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1003) := by
    have ha : (tripleCharges (sourceA1754 + difference 1 5) (sourceB1754 + difference 5 1) sourceC1754) = raw25534 := by
      apply Matrix.ext; unfold tripleCharges sourceA1754 sourceB1754 sourceC1754 difference raw25534; decide +kernel
    rw [ha]
    exact (canonical25534 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1754 + sourceB1754) sourceC1754) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4079) := by
    have ha : (doubleCharges (sourceA1754 + sourceB1754) sourceC1754) = raw25529 := by
      apply Matrix.ext; unfold doubleCharges sourceA1754 sourceB1754 sourceC1754 raw25529; decide +kernel
    rw [ha]
    exact (canonical25529 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1754 sourceB1754 sourceC1754
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1754, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1755 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1755 : Charge := ![1, 1, -1, 0, 0, -1]
def sourceC1755 : Charge := ![3, -1, 1, -1, -1, -1]
def sourceForm1755 : Integer.Sparse Master := [(Sum.inr 868, 1), (Sum.inr 870, 2), (Sum.inr 884, 1), (Sum.inr 980, 1), (Sum.inr 1912, 1), (Sum.inr 4079, -1)]

theorem sourceEq1755 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1755 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1755 + difference 0 2) (sourceB1755 + difference 2 0) sourceC1755) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1912) := by
    have ha : (tripleCharges (sourceA1755 + difference 0 2) (sourceB1755 + difference 2 0) sourceC1755) = raw25525 := by
      apply Matrix.ext; unfold tripleCharges sourceA1755 sourceB1755 sourceC1755 difference raw25525; decide +kernel
    rw [ha]
    exact (canonical25525 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1755 + difference 1 2) (sourceB1755 + difference 2 1) sourceC1755) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 884) := by
    have ha : (tripleCharges (sourceA1755 + difference 1 2) (sourceB1755 + difference 2 1) sourceC1755) = raw25531 := by
      apply Matrix.ext; unfold tripleCharges sourceA1755 sourceB1755 sourceC1755 difference raw25531; decide +kernel
    rw [ha]
    exact (canonical25531 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1755 + difference 2 2) (sourceB1755 + difference 2 2) sourceC1755) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 980) := by
    have ha : (tripleCharges (sourceA1755 + difference 2 2) (sourceB1755 + difference 2 2) sourceC1755) = raw25523 := by
      apply Matrix.ext; unfold tripleCharges sourceA1755 sourceB1755 sourceC1755 difference raw25523; decide +kernel
    rw [ha]
    exact (canonical25523 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1755 + difference 3 2) (sourceB1755 + difference 2 3) sourceC1755) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 870) := by
    have ha : (tripleCharges (sourceA1755 + difference 3 2) (sourceB1755 + difference 2 3) sourceC1755) = raw25535 := by
      apply Matrix.ext; unfold tripleCharges sourceA1755 sourceB1755 sourceC1755 difference raw25535; decide +kernel
    rw [ha]
    exact (canonical25535 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1755 + difference 4 2) (sourceB1755 + difference 2 4) sourceC1755) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 870) := by
    have ha : (tripleCharges (sourceA1755 + difference 4 2) (sourceB1755 + difference 2 4) sourceC1755) = raw25536 := by
      apply Matrix.ext; unfold tripleCharges sourceA1755 sourceB1755 sourceC1755 difference raw25536; decide +kernel
    rw [ha]
    exact (canonical25536 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1755 + difference 5 2) (sourceB1755 + difference 2 5) sourceC1755) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 868) := by
    have ha : (tripleCharges (sourceA1755 + difference 5 2) (sourceB1755 + difference 2 5) sourceC1755) = raw25537 := by
      apply Matrix.ext; unfold tripleCharges sourceA1755 sourceB1755 sourceC1755 difference raw25537; decide +kernel
    rw [ha]
    exact (canonical25537 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1755 + sourceB1755) sourceC1755) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4079) := by
    have ha : (doubleCharges (sourceA1755 + sourceB1755) sourceC1755) = raw25529 := by
      apply Matrix.ext; unfold doubleCharges sourceA1755 sourceB1755 sourceC1755 raw25529; decide +kernel
    rw [ha]
    exact (canonical25529 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1755 sourceB1755 sourceC1755
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1755, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1756 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1756 : Charge := ![1, 1, -1, 0, 0, -1]
def sourceC1756 : Charge := ![3, -1, 1, -1, -1, -1]
def sourceForm1756 : Integer.Sparse Master := [(Sum.inr 980, 3), (Sum.inr 1003, 1), (Sum.inr 1034, 1), (Sum.inr 2204, 1), (Sum.inr 4079, -1)]

theorem sourceEq1756 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1756 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1756 + difference 0 5) (sourceB1756 + difference 5 0) sourceC1756) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2204) := by
    have ha : (tripleCharges (sourceA1756 + difference 0 5) (sourceB1756 + difference 5 0) sourceC1756) = raw25528 := by
      apply Matrix.ext; unfold tripleCharges sourceA1756 sourceB1756 sourceC1756 difference raw25528; decide +kernel
    rw [ha]
    exact (canonical25528 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1756 + difference 1 5) (sourceB1756 + difference 5 1) sourceC1756) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1003) := by
    have ha : (tripleCharges (sourceA1756 + difference 1 5) (sourceB1756 + difference 5 1) sourceC1756) = raw25534 := by
      apply Matrix.ext; unfold tripleCharges sourceA1756 sourceB1756 sourceC1756 difference raw25534; decide +kernel
    rw [ha]
    exact (canonical25534 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1756 + difference 2 5) (sourceB1756 + difference 5 2) sourceC1756) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1034) := by
    have ha : (tripleCharges (sourceA1756 + difference 2 5) (sourceB1756 + difference 5 2) sourceC1756) = raw25538 := by
      apply Matrix.ext; unfold tripleCharges sourceA1756 sourceB1756 sourceC1756 difference raw25538; decide +kernel
    rw [ha]
    exact (canonical25538 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1756 + difference 3 5) (sourceB1756 + difference 5 3) sourceC1756) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 980) := by
    have ha : (tripleCharges (sourceA1756 + difference 3 5) (sourceB1756 + difference 5 3) sourceC1756) = raw25539 := by
      apply Matrix.ext; unfold tripleCharges sourceA1756 sourceB1756 sourceC1756 difference raw25539; decide +kernel
    rw [ha]
    exact (canonical25539 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1756 + difference 4 5) (sourceB1756 + difference 5 4) sourceC1756) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 980) := by
    have ha : (tripleCharges (sourceA1756 + difference 4 5) (sourceB1756 + difference 5 4) sourceC1756) = raw25540 := by
      apply Matrix.ext; unfold tripleCharges sourceA1756 sourceB1756 sourceC1756 difference raw25540; decide +kernel
    rw [ha]
    exact (canonical25540 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1756 + difference 5 5) (sourceB1756 + difference 5 5) sourceC1756) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 980) := by
    have ha : (tripleCharges (sourceA1756 + difference 5 5) (sourceB1756 + difference 5 5) sourceC1756) = raw25523 := by
      apply Matrix.ext; unfold tripleCharges sourceA1756 sourceB1756 sourceC1756 difference raw25523; decide +kernel
    rw [ha]
    exact (canonical25523 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1756 + sourceB1756) sourceC1756) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4079) := by
    have ha : (doubleCharges (sourceA1756 + sourceB1756) sourceC1756) = raw25529 := by
      apply Matrix.ext; unfold doubleCharges sourceA1756 sourceB1756 sourceC1756 raw25529; decide +kernel
    rw [ha]
    exact (canonical25529 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1756 sourceB1756 sourceC1756
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1756, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1757 : Charge := ![1, 1, -1, 0, 0, -1]
def sourceB1757 : Charge := ![3, -1, 1, -1, -1, -1]
def sourceC1757 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1757 : Integer.Sparse Master := [(Sum.inr 712, 1), (Sum.inr 713, 2), (Sum.inr 719, 1), (Sum.inr 850, 1), (Sum.inr 1616, 1), (Sum.inr 4069, -1)]

theorem sourceEq1757 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1757 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1757 + difference 0 0) (sourceB1757 + difference 0 0) sourceC1757) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1616) := by
    have ha : (tripleCharges (sourceA1757 + difference 0 0) (sourceB1757 + difference 0 0) sourceC1757) = raw25541 := by
      apply Matrix.ext; unfold tripleCharges sourceA1757 sourceB1757 sourceC1757 difference raw25541; decide +kernel
    rw [ha]
    exact (canonical25541 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1757 + difference 1 0) (sourceB1757 + difference 0 1) sourceC1757) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 719) := by
    have ha : (tripleCharges (sourceA1757 + difference 1 0) (sourceB1757 + difference 0 1) sourceC1757) = raw25542 := by
      apply Matrix.ext; unfold tripleCharges sourceA1757 sourceB1757 sourceC1757 difference raw25542; decide +kernel
    rw [ha]
    exact (canonical25542 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1757 + difference 2 0) (sourceB1757 + difference 0 2) sourceC1757) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 850) := by
    have ha : (tripleCharges (sourceA1757 + difference 2 0) (sourceB1757 + difference 0 2) sourceC1757) = raw25543 := by
      apply Matrix.ext; unfold tripleCharges sourceA1757 sourceB1757 sourceC1757 difference raw25543; decide +kernel
    rw [ha]
    exact (canonical25543 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1757 + difference 3 0) (sourceB1757 + difference 0 3) sourceC1757) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 713) := by
    have ha : (tripleCharges (sourceA1757 + difference 3 0) (sourceB1757 + difference 0 3) sourceC1757) = raw25544 := by
      apply Matrix.ext; unfold tripleCharges sourceA1757 sourceB1757 sourceC1757 difference raw25544; decide +kernel
    rw [ha]
    exact (canonical25544 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1757 + difference 4 0) (sourceB1757 + difference 0 4) sourceC1757) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 713) := by
    have ha : (tripleCharges (sourceA1757 + difference 4 0) (sourceB1757 + difference 0 4) sourceC1757) = raw25545 := by
      apply Matrix.ext; unfold tripleCharges sourceA1757 sourceB1757 sourceC1757 difference raw25545; decide +kernel
    rw [ha]
    exact (canonical25545 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1757 + difference 5 0) (sourceB1757 + difference 0 5) sourceC1757) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 712) := by
    have ha : (tripleCharges (sourceA1757 + difference 5 0) (sourceB1757 + difference 0 5) sourceC1757) = raw25546 := by
      apply Matrix.ext; unfold tripleCharges sourceA1757 sourceB1757 sourceC1757 difference raw25546; decide +kernel
    rw [ha]
    exact (canonical25546 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1757 + sourceB1757) sourceC1757) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1757 + sourceB1757) sourceC1757) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1757 sourceB1757 sourceC1757 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1757 sourceB1757 sourceC1757
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1757, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1758 : Charge := ![1, 1, -1, 0, 0, -1]
def sourceB1758 : Charge := ![3, -1, 1, -1, -1, -1]
def sourceC1758 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1758 : Integer.Sparse Master := [(Sum.inr 712, 1), (Sum.inr 1542, 1), (Sum.inr 1597, 2), (Sum.inr 1616, 1), (Sum.inr 1622, 1), (Sum.inr 4069, -1)]

theorem sourceEq1758 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1758 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1758 + difference 5 0) (sourceB1758 + difference 0 5) sourceC1758) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 712) := by
    have ha : (tripleCharges (sourceA1758 + difference 5 0) (sourceB1758 + difference 0 5) sourceC1758) = raw25546 := by
      apply Matrix.ext; unfold tripleCharges sourceA1758 sourceB1758 sourceC1758 difference raw25546; decide +kernel
    rw [ha]
    exact (canonical25546 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1758 + difference 5 1) (sourceB1758 + difference 1 5) sourceC1758) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1622) := by
    have ha : (tripleCharges (sourceA1758 + difference 5 1) (sourceB1758 + difference 1 5) sourceC1758) = raw24864 := by
      apply Matrix.ext; unfold tripleCharges sourceA1758 sourceB1758 sourceC1758 difference raw24864; decide +kernel
    rw [ha]
    exact (canonical24864 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1758 + difference 5 2) (sourceB1758 + difference 2 5) sourceC1758) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1542) := by
    have ha : (tripleCharges (sourceA1758 + difference 5 2) (sourceB1758 + difference 2 5) sourceC1758) = raw24863 := by
      apply Matrix.ext; unfold tripleCharges sourceA1758 sourceB1758 sourceC1758 difference raw24863; decide +kernel
    rw [ha]
    exact (canonical24863 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1758 + difference 5 3) (sourceB1758 + difference 3 5) sourceC1758) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1597) := by
    have ha : (tripleCharges (sourceA1758 + difference 5 3) (sourceB1758 + difference 3 5) sourceC1758) = raw25547 := by
      apply Matrix.ext; unfold tripleCharges sourceA1758 sourceB1758 sourceC1758 difference raw25547; decide +kernel
    rw [ha]
    exact (canonical25547 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1758 + difference 5 4) (sourceB1758 + difference 4 5) sourceC1758) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1597) := by
    have ha : (tripleCharges (sourceA1758 + difference 5 4) (sourceB1758 + difference 4 5) sourceC1758) = raw25548 := by
      apply Matrix.ext; unfold tripleCharges sourceA1758 sourceB1758 sourceC1758 difference raw25548; decide +kernel
    rw [ha]
    exact (canonical25548 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1758 + difference 5 5) (sourceB1758 + difference 5 5) sourceC1758) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1616) := by
    have ha : (tripleCharges (sourceA1758 + difference 5 5) (sourceB1758 + difference 5 5) sourceC1758) = raw25541 := by
      apply Matrix.ext; unfold tripleCharges sourceA1758 sourceB1758 sourceC1758 difference raw25541; decide +kernel
    rw [ha]
    exact (canonical25541 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1758 + sourceB1758) sourceC1758) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1758 + sourceB1758) sourceC1758) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1758 sourceB1758 sourceC1758 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1758 sourceB1758 sourceC1758
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1758, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1759 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1759 : Charge := ![1, 1, -1, 0, -1, 0]
def sourceC1759 : Charge := ![3, -1, 1, -1, 0, -2]
def sourceForm1759 : Integer.Sparse Master := [(Sum.inr 977, 1), (Sum.inr 1908, 1), (Sum.inr 2075, 1), (Sum.inr 2190, 1), (Sum.inr 2202, 1), (Sum.inr 2205, 1), (Sum.inr 4080, -1)]

theorem sourceEq1759 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1759 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1759 + difference 0 0) (sourceB1759 + difference 0 0) sourceC1759) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 977) := by
    have ha : (tripleCharges (sourceA1759 + difference 0 0) (sourceB1759 + difference 0 0) sourceC1759) = raw25549 := by
      apply Matrix.ext; unfold tripleCharges sourceA1759 sourceB1759 sourceC1759 difference raw25549; decide +kernel
    rw [ha]
    exact (canonical25549 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1759 + difference 0 1) (sourceB1759 + difference 1 0) sourceC1759) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2075) := by
    have ha : (tripleCharges (sourceA1759 + difference 0 1) (sourceB1759 + difference 1 0) sourceC1759) = raw25550 := by
      apply Matrix.ext; unfold tripleCharges sourceA1759 sourceB1759 sourceC1759 difference raw25550; decide +kernel
    rw [ha]
    exact (canonical25550 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1759 + difference 0 2) (sourceB1759 + difference 2 0) sourceC1759) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1908) := by
    have ha : (tripleCharges (sourceA1759 + difference 0 2) (sourceB1759 + difference 2 0) sourceC1759) = raw25551 := by
      apply Matrix.ext; unfold tripleCharges sourceA1759 sourceB1759 sourceC1759 difference raw25551; decide +kernel
    rw [ha]
    exact (canonical25551 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1759 + difference 0 3) (sourceB1759 + difference 3 0) sourceC1759) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2190) := by
    have ha : (tripleCharges (sourceA1759 + difference 0 3) (sourceB1759 + difference 3 0) sourceC1759) = raw25552 := by
      apply Matrix.ext; unfold tripleCharges sourceA1759 sourceB1759 sourceC1759 difference raw25552; decide +kernel
    rw [ha]
    exact (canonical25552 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1759 + difference 0 4) (sourceB1759 + difference 4 0) sourceC1759) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2205) := by
    have ha : (tripleCharges (sourceA1759 + difference 0 4) (sourceB1759 + difference 4 0) sourceC1759) = raw25553 := by
      apply Matrix.ext; unfold tripleCharges sourceA1759 sourceB1759 sourceC1759 difference raw25553; decide +kernel
    rw [ha]
    exact (canonical25553 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1759 + difference 0 5) (sourceB1759 + difference 5 0) sourceC1759) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2202) := by
    have ha : (tripleCharges (sourceA1759 + difference 0 5) (sourceB1759 + difference 5 0) sourceC1759) = raw25554 := by
      apply Matrix.ext; unfold tripleCharges sourceA1759 sourceB1759 sourceC1759 difference raw25554; decide +kernel
    rw [ha]
    exact (canonical25554 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1759 + sourceB1759) sourceC1759) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1759 + sourceB1759) sourceC1759) = raw25555 := by
      apply Matrix.ext; unfold doubleCharges sourceA1759 sourceB1759 sourceC1759 raw25555; decide +kernel
    rw [ha]
    exact (canonical25555 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1759 sourceB1759 sourceC1759
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1759, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
