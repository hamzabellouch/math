import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical147
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical169
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical183
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical187
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical229
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical231
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical233
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical235
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical236
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical237
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical238
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical239
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical240

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA2208 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2208 : Charge := ![1, 0, 1, 1, 0, -3]
def sourceC2208 : Charge := ![2, 1, -1, -1, -2, 1]
def sourceForm2208 : Integer.Sparse Master := [(Sum.inr 2472, 1), (Sum.inr 3019, 2), (Sum.inr 3023, 1), (Sum.inr 3041, 1), (Sum.inr 3799, 1), (Sum.inr 4090, -1)]

theorem sourceEq2208 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2208 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2208 + difference 0 0) (sourceB2208 + difference 0 0) sourceC2208) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2472) := by
    have ha : (tripleCharges (sourceA2208 + difference 0 0) (sourceB2208 + difference 0 0) sourceC2208) = raw30225 := by
      apply Matrix.ext; unfold tripleCharges sourceA2208 sourceB2208 sourceC2208 difference raw30225; decide +kernel
    rw [ha]
    exact (canonical30225 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2208 + difference 0 1) (sourceB2208 + difference 1 0) sourceC2208) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3041) := by
    have ha : (tripleCharges (sourceA2208 + difference 0 1) (sourceB2208 + difference 1 0) sourceC2208) = raw30226 := by
      apply Matrix.ext; unfold tripleCharges sourceA2208 sourceB2208 sourceC2208 difference raw30226; decide +kernel
    rw [ha]
    exact (canonical30226 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2208 + difference 0 2) (sourceB2208 + difference 2 0) sourceC2208) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3019) := by
    have ha : (tripleCharges (sourceA2208 + difference 0 2) (sourceB2208 + difference 2 0) sourceC2208) = raw30227 := by
      apply Matrix.ext; unfold tripleCharges sourceA2208 sourceB2208 sourceC2208 difference raw30227; decide +kernel
    rw [ha]
    exact (canonical30227 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2208 + difference 0 3) (sourceB2208 + difference 3 0) sourceC2208) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3019) := by
    have ha : (tripleCharges (sourceA2208 + difference 0 3) (sourceB2208 + difference 3 0) sourceC2208) = raw30228 := by
      apply Matrix.ext; unfold tripleCharges sourceA2208 sourceB2208 sourceC2208 difference raw30228; decide +kernel
    rw [ha]
    exact (canonical30228 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2208 + difference 0 4) (sourceB2208 + difference 4 0) sourceC2208) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3023) := by
    have ha : (tripleCharges (sourceA2208 + difference 0 4) (sourceB2208 + difference 4 0) sourceC2208) = raw30229 := by
      apply Matrix.ext; unfold tripleCharges sourceA2208 sourceB2208 sourceC2208 difference raw30229; decide +kernel
    rw [ha]
    exact (canonical30229 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2208 + difference 0 5) (sourceB2208 + difference 5 0) sourceC2208) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3799) := by
    have ha : (tripleCharges (sourceA2208 + difference 0 5) (sourceB2208 + difference 5 0) sourceC2208) = raw30230 := by
      apply Matrix.ext; unfold tripleCharges sourceA2208 sourceB2208 sourceC2208 difference raw30230; decide +kernel
    rw [ha]
    exact (canonical30230 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2208 + sourceB2208) sourceC2208) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (doubleCharges (sourceA2208 + sourceB2208) sourceC2208) = raw30231 := by
      apply Matrix.ext; unfold doubleCharges sourceA2208 sourceB2208 sourceC2208 raw30231; decide +kernel
    rw [ha]
    exact (canonical30231 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2208 sourceB2208 sourceC2208
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2208, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2209 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2209 : Charge := ![1, 0, 1, 0, 1, -3]
def sourceC2209 : Charge := ![2, 1, -1, 0, -3, 1]
def sourceForm2209 : Integer.Sparse Master := [(Sum.inr 2487, 1), (Sum.inr 3020, 1), (Sum.inr 3024, 1), (Sum.inr 3026, 1), (Sum.inr 3047, 1), (Sum.inr 3564, 1), (Sum.inr 4080, -1)]

theorem sourceEq2209 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2209 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2209 + difference 0 0) (sourceB2209 + difference 0 0) sourceC2209) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2487) := by
    have ha : (tripleCharges (sourceA2209 + difference 0 0) (sourceB2209 + difference 0 0) sourceC2209) = raw30232 := by
      apply Matrix.ext; unfold tripleCharges sourceA2209 sourceB2209 sourceC2209 difference raw30232; decide +kernel
    rw [ha]
    exact (canonical30232 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2209 + difference 0 1) (sourceB2209 + difference 1 0) sourceC2209) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3047) := by
    have ha : (tripleCharges (sourceA2209 + difference 0 1) (sourceB2209 + difference 1 0) sourceC2209) = raw30233 := by
      apply Matrix.ext; unfold tripleCharges sourceA2209 sourceB2209 sourceC2209 difference raw30233; decide +kernel
    rw [ha]
    exact (canonical30233 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2209 + difference 0 2) (sourceB2209 + difference 2 0) sourceC2209) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3026) := by
    have ha : (tripleCharges (sourceA2209 + difference 0 2) (sourceB2209 + difference 2 0) sourceC2209) = raw30234 := by
      apply Matrix.ext; unfold tripleCharges sourceA2209 sourceB2209 sourceC2209 difference raw30234; decide +kernel
    rw [ha]
    exact (canonical30234 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2209 + difference 0 3) (sourceB2209 + difference 3 0) sourceC2209) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3020) := by
    have ha : (tripleCharges (sourceA2209 + difference 0 3) (sourceB2209 + difference 3 0) sourceC2209) = raw30235 := by
      apply Matrix.ext; unfold tripleCharges sourceA2209 sourceB2209 sourceC2209 difference raw30235; decide +kernel
    rw [ha]
    exact (canonical30235 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2209 + difference 0 4) (sourceB2209 + difference 4 0) sourceC2209) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3024) := by
    have ha : (tripleCharges (sourceA2209 + difference 0 4) (sourceB2209 + difference 4 0) sourceC2209) = raw30236 := by
      apply Matrix.ext; unfold tripleCharges sourceA2209 sourceB2209 sourceC2209 difference raw30236; decide +kernel
    rw [ha]
    exact (canonical30236 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2209 + difference 0 5) (sourceB2209 + difference 5 0) sourceC2209) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3564) := by
    have ha : (tripleCharges (sourceA2209 + difference 0 5) (sourceB2209 + difference 5 0) sourceC2209) = raw30237 := by
      apply Matrix.ext; unfold tripleCharges sourceA2209 sourceB2209 sourceC2209 difference raw30237; decide +kernel
    rw [ha]
    exact (canonical30237 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2209 + sourceB2209) sourceC2209) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA2209 + sourceB2209) sourceC2209) = raw30238 := by
      apply Matrix.ext; unfold doubleCharges sourceA2209 sourceB2209 sourceC2209 raw30238; decide +kernel
    rw [ha]
    exact (canonical30238 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2209 sourceB2209 sourceC2209
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2209, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2210 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2210 : Charge := ![1, 0, 1, 0, 0, -2]
def sourceC2210 : Charge := ![2, 1, -1, 0, -2, 0]
def sourceForm2210 : Integer.Sparse Master := [(Sum.inr 4529, 1), (Sum.inr 4534, 1), (Sum.inr 4536, 1), (Sum.inr 4553, 1), (Sum.inr 4592, 1), (Sum.inr 4664, 1), (Sum.inr 4670, 1), (Sum.inr 4682, 1), (Sum.inr 4853, 1), (Sum.inr 4931, 1), (Sum.inr 4934, 1), (Sum.inr 4949, 1), (Sum.inr 4954, 1), (Sum.inr 4965, 1), (Sum.inr 5038, 1), (Sum.inr 5042, 1), (Sum.inr 5072, 1), (Sum.inr 5074, 1), (Sum.inr 5075, 1), (Sum.inr 5101, 1), (Sum.inr 5105, 1), (Sum.inr 5129, 1), (Sum.inr 5188, 1), (Sum.inr 5258, 1), (Sum.inr 5260, 1), (Sum.inr 5355, 1), (Sum.inr 5378, 1), (Sum.inr 5384, 1), (Sum.inr 5409, 1), (Sum.inr 5411, 1)]

theorem sourceEq2210 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2210 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2210 + difference 0 1) (sourceB2210 + difference 1 0) sourceC2210) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5355) := by
    have ha : (tripleCharges (sourceA2210 + difference 0 1) (sourceB2210 + difference 1 0) sourceC2210) = raw30239 := by
      apply Matrix.ext; unfold tripleCharges sourceA2210 sourceB2210 sourceC2210 difference raw30239; decide +kernel
    rw [ha]
    exact (canonical30239 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2210 + difference 0 2) (sourceB2210 + difference 2 0) sourceC2210) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5384) := by
    have ha : (tripleCharges (sourceA2210 + difference 0 2) (sourceB2210 + difference 2 0) sourceC2210) = raw30240 := by
      apply Matrix.ext; unfold tripleCharges sourceA2210 sourceB2210 sourceC2210 difference raw30240; decide +kernel
    rw [ha]
    exact (canonical30240 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2210 + difference 0 3) (sourceB2210 + difference 3 0) sourceC2210) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA2210 + difference 0 3) (sourceB2210 + difference 3 0) sourceC2210) = raw30241 := by
      apply Matrix.ext; unfold tripleCharges sourceA2210 sourceB2210 sourceC2210 difference raw30241; decide +kernel
    rw [ha]
    exact (canonical30241 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2210 + difference 0 4) (sourceB2210 + difference 4 0) sourceC2210) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA2210 + difference 0 4) (sourceB2210 + difference 4 0) sourceC2210) = raw30242 := by
      apply Matrix.ext; unfold tripleCharges sourceA2210 sourceB2210 sourceC2210 difference raw30242; decide +kernel
    rw [ha]
    exact (canonical30242 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2210 + difference 0 5) (sourceB2210 + difference 5 0) sourceC2210) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5409) := by
    have ha : (tripleCharges (sourceA2210 + difference 0 5) (sourceB2210 + difference 5 0) sourceC2210) = raw30243 := by
      apply Matrix.ext; unfold tripleCharges sourceA2210 sourceB2210 sourceC2210 difference raw30243; decide +kernel
    rw [ha]
    exact (canonical30243 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2210 + difference 1 0) (sourceB2210 + difference 0 1) sourceC2210) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4592) := by
    have ha : (tripleCharges (sourceA2210 + difference 1 0) (sourceB2210 + difference 0 1) sourceC2210) = raw30244 := by
      apply Matrix.ext; unfold tripleCharges sourceA2210 sourceB2210 sourceC2210 difference raw30244; decide +kernel
    rw [ha]
    exact (canonical30244 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2210 + difference 1 2) (sourceB2210 + difference 2 1) sourceC2210) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5188) := by
    have ha : (tripleCharges (sourceA2210 + difference 1 2) (sourceB2210 + difference 2 1) sourceC2210) = raw30245 := by
      apply Matrix.ext; unfold tripleCharges sourceA2210 sourceB2210 sourceC2210 difference raw30245; decide +kernel
    rw [ha]
    exact (canonical30245 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2210 + difference 1 3) (sourceB2210 + difference 3 1) sourceC2210) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5129) := by
    have ha : (tripleCharges (sourceA2210 + difference 1 3) (sourceB2210 + difference 3 1) sourceC2210) = raw30246 := by
      apply Matrix.ext; unfold tripleCharges sourceA2210 sourceB2210 sourceC2210 difference raw30246; decide +kernel
    rw [ha]
    exact (canonical30246 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2210 + difference 1 4) (sourceB2210 + difference 4 1) sourceC2210) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5260) := by
    have ha : (tripleCharges (sourceA2210 + difference 1 4) (sourceB2210 + difference 4 1) sourceC2210) = raw30247 := by
      apply Matrix.ext; unfold tripleCharges sourceA2210 sourceB2210 sourceC2210 difference raw30247; decide +kernel
    rw [ha]
    exact (canonical30247 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2210 + difference 1 5) (sourceB2210 + difference 5 1) sourceC2210) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA2210 + difference 1 5) (sourceB2210 + difference 5 1) sourceC2210) = raw30248 := by
      apply Matrix.ext; unfold tripleCharges sourceA2210 sourceB2210 sourceC2210 difference raw30248; decide +kernel
    rw [ha]
    exact (canonical30248 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2210 + difference 2 0) (sourceB2210 + difference 0 2) sourceC2210) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4553) := by
    have ha : (tripleCharges (sourceA2210 + difference 2 0) (sourceB2210 + difference 0 2) sourceC2210) = raw30249 := by
      apply Matrix.ext; unfold tripleCharges sourceA2210 sourceB2210 sourceC2210 difference raw30249; decide +kernel
    rw [ha]
    exact (canonical30249 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2210 + difference 2 1) (sourceB2210 + difference 1 2) sourceC2210) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4949) := by
    have ha : (tripleCharges (sourceA2210 + difference 2 1) (sourceB2210 + difference 1 2) sourceC2210) = raw30250 := by
      apply Matrix.ext; unfold tripleCharges sourceA2210 sourceB2210 sourceC2210 difference raw30250; decide +kernel
    rw [ha]
    exact (canonical30250 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2210 + difference 2 3) (sourceB2210 + difference 3 2) sourceC2210) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5038) := by
    have ha : (tripleCharges (sourceA2210 + difference 2 3) (sourceB2210 + difference 3 2) sourceC2210) = raw30251 := by
      apply Matrix.ext; unfold tripleCharges sourceA2210 sourceB2210 sourceC2210 difference raw30251; decide +kernel
    rw [ha]
    exact (canonical30251 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2210 + difference 2 4) (sourceB2210 + difference 4 2) sourceC2210) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5105) := by
    have ha : (tripleCharges (sourceA2210 + difference 2 4) (sourceB2210 + difference 4 2) sourceC2210) = raw30252 := by
      apply Matrix.ext; unfold tripleCharges sourceA2210 sourceB2210 sourceC2210 difference raw30252; decide +kernel
    rw [ha]
    exact (canonical30252 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2210 + difference 2 5) (sourceB2210 + difference 5 2) sourceC2210) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5101) := by
    have ha : (tripleCharges (sourceA2210 + difference 2 5) (sourceB2210 + difference 5 2) sourceC2210) = raw30253 := by
      apply Matrix.ext; unfold tripleCharges sourceA2210 sourceB2210 sourceC2210 difference raw30253; decide +kernel
    rw [ha]
    exact (canonical30253 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2210 + difference 3 0) (sourceB2210 + difference 0 3) sourceC2210) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4529) := by
    have ha : (tripleCharges (sourceA2210 + difference 3 0) (sourceB2210 + difference 0 3) sourceC2210) = raw30254 := by
      apply Matrix.ext; unfold tripleCharges sourceA2210 sourceB2210 sourceC2210 difference raw30254; decide +kernel
    rw [ha]
    exact (canonical30254 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2210 + difference 3 1) (sourceB2210 + difference 1 3) sourceC2210) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4931) := by
    have ha : (tripleCharges (sourceA2210 + difference 3 1) (sourceB2210 + difference 1 3) sourceC2210) = raw30255 := by
      apply Matrix.ext; unfold tripleCharges sourceA2210 sourceB2210 sourceC2210 difference raw30255; decide +kernel
    rw [ha]
    exact (canonical30255 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2210 + difference 3 2) (sourceB2210 + difference 2 3) sourceC2210) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5042) := by
    have ha : (tripleCharges (sourceA2210 + difference 3 2) (sourceB2210 + difference 2 3) sourceC2210) = raw30256 := by
      apply Matrix.ext; unfold tripleCharges sourceA2210 sourceB2210 sourceC2210 difference raw30256; decide +kernel
    rw [ha]
    exact (canonical30256 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2210 + difference 3 4) (sourceB2210 + difference 4 3) sourceC2210) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5074) := by
    have ha : (tripleCharges (sourceA2210 + difference 3 4) (sourceB2210 + difference 4 3) sourceC2210) = raw30257 := by
      apply Matrix.ext; unfold tripleCharges sourceA2210 sourceB2210 sourceC2210 difference raw30257; decide +kernel
    rw [ha]
    exact (canonical30257 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2210 + difference 3 5) (sourceB2210 + difference 5 3) sourceC2210) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5072) := by
    have ha : (tripleCharges (sourceA2210 + difference 3 5) (sourceB2210 + difference 5 3) sourceC2210) = raw30258 := by
      apply Matrix.ext; unfold tripleCharges sourceA2210 sourceB2210 sourceC2210 difference raw30258; decide +kernel
    rw [ha]
    exact (canonical30258 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2210 + difference 4 0) (sourceB2210 + difference 0 4) sourceC2210) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4534) := by
    have ha : (tripleCharges (sourceA2210 + difference 4 0) (sourceB2210 + difference 0 4) sourceC2210) = raw30259 := by
      apply Matrix.ext; unfold tripleCharges sourceA2210 sourceB2210 sourceC2210 difference raw30259; decide +kernel
    rw [ha]
    exact (canonical30259 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2210 + difference 4 1) (sourceB2210 + difference 1 4) sourceC2210) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4934) := by
    have ha : (tripleCharges (sourceA2210 + difference 4 1) (sourceB2210 + difference 1 4) sourceC2210) = raw30260 := by
      apply Matrix.ext; unfold tripleCharges sourceA2210 sourceB2210 sourceC2210 difference raw30260; decide +kernel
    rw [ha]
    exact (canonical30260 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2210 + difference 4 2) (sourceB2210 + difference 2 4) sourceC2210) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4965) := by
    have ha : (tripleCharges (sourceA2210 + difference 4 2) (sourceB2210 + difference 2 4) sourceC2210) = raw30261 := by
      apply Matrix.ext; unfold tripleCharges sourceA2210 sourceB2210 sourceC2210 difference raw30261; decide +kernel
    rw [ha]
    exact (canonical30261 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2210 + difference 4 3) (sourceB2210 + difference 3 4) sourceC2210) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4954) := by
    have ha : (tripleCharges (sourceA2210 + difference 4 3) (sourceB2210 + difference 3 4) sourceC2210) = raw30262 := by
      apply Matrix.ext; unfold tripleCharges sourceA2210 sourceB2210 sourceC2210 difference raw30262; decide +kernel
    rw [ha]
    exact (canonical30262 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2210 + difference 4 5) (sourceB2210 + difference 5 4) sourceC2210) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA2210 + difference 4 5) (sourceB2210 + difference 5 4) sourceC2210) = raw30263 := by
      apply Matrix.ext; unfold tripleCharges sourceA2210 sourceB2210 sourceC2210 difference raw30263; decide +kernel
    rw [ha]
    exact (canonical30263 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2210 + difference 5 0) (sourceB2210 + difference 0 5) sourceC2210) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4536) := by
    have ha : (tripleCharges (sourceA2210 + difference 5 0) (sourceB2210 + difference 0 5) sourceC2210) = raw30264 := by
      apply Matrix.ext; unfold tripleCharges sourceA2210 sourceB2210 sourceC2210 difference raw30264; decide +kernel
    rw [ha]
    exact (canonical30264 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2210 + difference 5 1) (sourceB2210 + difference 1 5) sourceC2210) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4670) := by
    have ha : (tripleCharges (sourceA2210 + difference 5 1) (sourceB2210 + difference 1 5) sourceC2210) = raw30265 := by
      apply Matrix.ext; unfold tripleCharges sourceA2210 sourceB2210 sourceC2210 difference raw30265; decide +kernel
    rw [ha]
    exact (canonical30265 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2210 + difference 5 2) (sourceB2210 + difference 2 5) sourceC2210) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4682) := by
    have ha : (tripleCharges (sourceA2210 + difference 5 2) (sourceB2210 + difference 2 5) sourceC2210) = raw30266 := by
      apply Matrix.ext; unfold tripleCharges sourceA2210 sourceB2210 sourceC2210 difference raw30266; decide +kernel
    rw [ha]
    exact (canonical30266 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2210 + difference 5 3) (sourceB2210 + difference 3 5) sourceC2210) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4664) := by
    have ha : (tripleCharges (sourceA2210 + difference 5 3) (sourceB2210 + difference 3 5) sourceC2210) = raw30267 := by
      apply Matrix.ext; unfold tripleCharges sourceA2210 sourceB2210 sourceC2210 difference raw30267; decide +kernel
    rw [ha]
    exact (canonical30267 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2210 + difference 5 4) (sourceB2210 + difference 4 5) sourceC2210) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4853) := by
    have ha : (tripleCharges (sourceA2210 + difference 5 4) (sourceB2210 + difference 4 5) sourceC2210) = raw30268 := by
      apply Matrix.ext; unfold tripleCharges sourceA2210 sourceB2210 sourceC2210 difference raw30268; decide +kernel
    rw [ha]
    exact (canonical30268 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2210 sourceB2210 sourceC2210
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2210, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2211 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2211 : Charge := ![1, 0, 1, 0, 0, -2]
def sourceC2211 : Charge := ![2, 1, -1, 0, -2, 0]
def sourceForm2211 : Integer.Sparse Master := [(Sum.inr 2147, 1), (Sum.inr 2149, 1), (Sum.inr 2153, 1), (Sum.inr 2164, 1), (Sum.inr 2259, 1), (Sum.inr 3258, 1), (Sum.inr 3268, 1), (Sum.inr 3270, 1), (Sum.inr 3295, 1), (Sum.inr 3406, 1), (Sum.inr 3415, 1), (Sum.inr 3417, 1), (Sum.inr 3452, 1), (Sum.inr 3453, 1), (Sum.inr 3459, 1), (Sum.inr 3462, 1), (Sum.inr 3463, 1), (Sum.inr 3468, 1), (Sum.inr 3470, 1), (Sum.inr 3475, 1), (Sum.inr 3479, 1), (Sum.inr 3516, 1), (Sum.inr 3533, 1), (Sum.inr 3538, 1), (Sum.inr 3540, 1), (Sum.inr 3770, 1), (Sum.inr 3795, 1), (Sum.inr 3807, 1), (Sum.inr 3811, 1), (Sum.inr 3813, 1)]

theorem sourceEq2211 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2211 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2211 + difference 0 1) (sourceB2211 + difference 1 0) sourceC2211) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3770) := by
    have ha : (tripleCharges (sourceA2211 + difference 0 1) (sourceB2211 + difference 1 0) sourceC2211) = raw30269 := by
      apply Matrix.ext; unfold tripleCharges sourceA2211 sourceB2211 sourceC2211 difference raw30269; decide +kernel
    rw [ha]
    exact (canonical30269 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2211 + difference 0 2) (sourceB2211 + difference 2 0) sourceC2211) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3811) := by
    have ha : (tripleCharges (sourceA2211 + difference 0 2) (sourceB2211 + difference 2 0) sourceC2211) = raw30270 := by
      apply Matrix.ext; unfold tripleCharges sourceA2211 sourceB2211 sourceC2211 difference raw30270; decide +kernel
    rw [ha]
    exact (canonical30270 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2211 + difference 0 3) (sourceB2211 + difference 3 0) sourceC2211) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3795) := by
    have ha : (tripleCharges (sourceA2211 + difference 0 3) (sourceB2211 + difference 3 0) sourceC2211) = raw30271 := by
      apply Matrix.ext; unfold tripleCharges sourceA2211 sourceB2211 sourceC2211 difference raw30271; decide +kernel
    rw [ha]
    exact (canonical30271 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2211 + difference 0 4) (sourceB2211 + difference 4 0) sourceC2211) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3813) := by
    have ha : (tripleCharges (sourceA2211 + difference 0 4) (sourceB2211 + difference 4 0) sourceC2211) = raw30272 := by
      apply Matrix.ext; unfold tripleCharges sourceA2211 sourceB2211 sourceC2211 difference raw30272; decide +kernel
    rw [ha]
    exact (canonical30272 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2211 + difference 0 5) (sourceB2211 + difference 5 0) sourceC2211) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3807) := by
    have ha : (tripleCharges (sourceA2211 + difference 0 5) (sourceB2211 + difference 5 0) sourceC2211) = raw30273 := by
      apply Matrix.ext; unfold tripleCharges sourceA2211 sourceB2211 sourceC2211 difference raw30273; decide +kernel
    rw [ha]
    exact (canonical30273 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2211 + difference 1 0) (sourceB2211 + difference 0 1) sourceC2211) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3295) := by
    have ha : (tripleCharges (sourceA2211 + difference 1 0) (sourceB2211 + difference 0 1) sourceC2211) = raw30274 := by
      apply Matrix.ext; unfold tripleCharges sourceA2211 sourceB2211 sourceC2211 difference raw30274; decide +kernel
    rw [ha]
    exact (canonical30274 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2211 + difference 1 2) (sourceB2211 + difference 2 1) sourceC2211) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3538) := by
    have ha : (tripleCharges (sourceA2211 + difference 1 2) (sourceB2211 + difference 2 1) sourceC2211) = raw30275 := by
      apply Matrix.ext; unfold tripleCharges sourceA2211 sourceB2211 sourceC2211 difference raw30275; decide +kernel
    rw [ha]
    exact (canonical30275 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2211 + difference 1 3) (sourceB2211 + difference 3 1) sourceC2211) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3516) := by
    have ha : (tripleCharges (sourceA2211 + difference 1 3) (sourceB2211 + difference 3 1) sourceC2211) = raw30276 := by
      apply Matrix.ext; unfold tripleCharges sourceA2211 sourceB2211 sourceC2211 difference raw30276; decide +kernel
    rw [ha]
    exact (canonical30276 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2211 + difference 1 4) (sourceB2211 + difference 4 1) sourceC2211) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3540) := by
    have ha : (tripleCharges (sourceA2211 + difference 1 4) (sourceB2211 + difference 4 1) sourceC2211) = raw30277 := by
      apply Matrix.ext; unfold tripleCharges sourceA2211 sourceB2211 sourceC2211 difference raw30277; decide +kernel
    rw [ha]
    exact (canonical30277 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2211 + difference 1 5) (sourceB2211 + difference 5 1) sourceC2211) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3533) := by
    have ha : (tripleCharges (sourceA2211 + difference 1 5) (sourceB2211 + difference 5 1) sourceC2211) = raw30278 := by
      apply Matrix.ext; unfold tripleCharges sourceA2211 sourceB2211 sourceC2211 difference raw30278; decide +kernel
    rw [ha]
    exact (canonical30278 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2211 + difference 2 0) (sourceB2211 + difference 0 2) sourceC2211) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3270) := by
    have ha : (tripleCharges (sourceA2211 + difference 2 0) (sourceB2211 + difference 0 2) sourceC2211) = raw30279 := by
      apply Matrix.ext; unfold tripleCharges sourceA2211 sourceB2211 sourceC2211 difference raw30279; decide +kernel
    rw [ha]
    exact (canonical30279 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2211 + difference 2 1) (sourceB2211 + difference 1 2) sourceC2211) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3417) := by
    have ha : (tripleCharges (sourceA2211 + difference 2 1) (sourceB2211 + difference 1 2) sourceC2211) = raw30280 := by
      apply Matrix.ext; unfold tripleCharges sourceA2211 sourceB2211 sourceC2211 difference raw30280; decide +kernel
    rw [ha]
    exact (canonical30280 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2211 + difference 2 3) (sourceB2211 + difference 3 2) sourceC2211) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3453) := by
    have ha : (tripleCharges (sourceA2211 + difference 2 3) (sourceB2211 + difference 3 2) sourceC2211) = raw30281 := by
      apply Matrix.ext; unfold tripleCharges sourceA2211 sourceB2211 sourceC2211 difference raw30281; decide +kernel
    rw [ha]
    exact (canonical30281 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2211 + difference 2 4) (sourceB2211 + difference 4 2) sourceC2211) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3479) := by
    have ha : (tripleCharges (sourceA2211 + difference 2 4) (sourceB2211 + difference 4 2) sourceC2211) = raw30282 := by
      apply Matrix.ext; unfold tripleCharges sourceA2211 sourceB2211 sourceC2211 difference raw30282; decide +kernel
    rw [ha]
    exact (canonical30282 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2211 + difference 2 5) (sourceB2211 + difference 5 2) sourceC2211) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3470) := by
    have ha : (tripleCharges (sourceA2211 + difference 2 5) (sourceB2211 + difference 5 2) sourceC2211) = raw30283 := by
      apply Matrix.ext; unfold tripleCharges sourceA2211 sourceB2211 sourceC2211 difference raw30283; decide +kernel
    rw [ha]
    exact (canonical30283 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2211 + difference 3 0) (sourceB2211 + difference 0 3) sourceC2211) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3258) := by
    have ha : (tripleCharges (sourceA2211 + difference 3 0) (sourceB2211 + difference 0 3) sourceC2211) = raw30284 := by
      apply Matrix.ext; unfold tripleCharges sourceA2211 sourceB2211 sourceC2211 difference raw30284; decide +kernel
    rw [ha]
    exact (canonical30284 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2211 + difference 3 1) (sourceB2211 + difference 1 3) sourceC2211) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3406) := by
    have ha : (tripleCharges (sourceA2211 + difference 3 1) (sourceB2211 + difference 1 3) sourceC2211) = raw30285 := by
      apply Matrix.ext; unfold tripleCharges sourceA2211 sourceB2211 sourceC2211 difference raw30285; decide +kernel
    rw [ha]
    exact (canonical30285 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2211 + difference 3 2) (sourceB2211 + difference 2 3) sourceC2211) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3462) := by
    have ha : (tripleCharges (sourceA2211 + difference 3 2) (sourceB2211 + difference 2 3) sourceC2211) = raw30286 := by
      apply Matrix.ext; unfold tripleCharges sourceA2211 sourceB2211 sourceC2211 difference raw30286; decide +kernel
    rw [ha]
    exact (canonical30286 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2211 + difference 3 4) (sourceB2211 + difference 4 3) sourceC2211) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3463) := by
    have ha : (tripleCharges (sourceA2211 + difference 3 4) (sourceB2211 + difference 4 3) sourceC2211) = raw30287 := by
      apply Matrix.ext; unfold tripleCharges sourceA2211 sourceB2211 sourceC2211 difference raw30287; decide +kernel
    rw [ha]
    exact (canonical30287 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2211 + difference 3 5) (sourceB2211 + difference 5 3) sourceC2211) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3459) := by
    have ha : (tripleCharges (sourceA2211 + difference 3 5) (sourceB2211 + difference 5 3) sourceC2211) = raw30288 := by
      apply Matrix.ext; unfold tripleCharges sourceA2211 sourceB2211 sourceC2211 difference raw30288; decide +kernel
    rw [ha]
    exact (canonical30288 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2211 + difference 4 0) (sourceB2211 + difference 0 4) sourceC2211) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3268) := by
    have ha : (tripleCharges (sourceA2211 + difference 4 0) (sourceB2211 + difference 0 4) sourceC2211) = raw30289 := by
      apply Matrix.ext; unfold tripleCharges sourceA2211 sourceB2211 sourceC2211 difference raw30289; decide +kernel
    rw [ha]
    exact (canonical30289 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2211 + difference 4 1) (sourceB2211 + difference 1 4) sourceC2211) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3415) := by
    have ha : (tripleCharges (sourceA2211 + difference 4 1) (sourceB2211 + difference 1 4) sourceC2211) = raw30290 := by
      apply Matrix.ext; unfold tripleCharges sourceA2211 sourceB2211 sourceC2211 difference raw30290; decide +kernel
    rw [ha]
    exact (canonical30290 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2211 + difference 4 2) (sourceB2211 + difference 2 4) sourceC2211) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3475) := by
    have ha : (tripleCharges (sourceA2211 + difference 4 2) (sourceB2211 + difference 2 4) sourceC2211) = raw30291 := by
      apply Matrix.ext; unfold tripleCharges sourceA2211 sourceB2211 sourceC2211 difference raw30291; decide +kernel
    rw [ha]
    exact (canonical30291 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2211 + difference 4 3) (sourceB2211 + difference 3 4) sourceC2211) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3452) := by
    have ha : (tripleCharges (sourceA2211 + difference 4 3) (sourceB2211 + difference 3 4) sourceC2211) = raw30292 := by
      apply Matrix.ext; unfold tripleCharges sourceA2211 sourceB2211 sourceC2211 difference raw30292; decide +kernel
    rw [ha]
    exact (canonical30292 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2211 + difference 4 5) (sourceB2211 + difference 5 4) sourceC2211) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3468) := by
    have ha : (tripleCharges (sourceA2211 + difference 4 5) (sourceB2211 + difference 5 4) sourceC2211) = raw30293 := by
      apply Matrix.ext; unfold tripleCharges sourceA2211 sourceB2211 sourceC2211 difference raw30293; decide +kernel
    rw [ha]
    exact (canonical30293 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2211 + difference 5 0) (sourceB2211 + difference 0 5) sourceC2211) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2149) := by
    have ha : (tripleCharges (sourceA2211 + difference 5 0) (sourceB2211 + difference 0 5) sourceC2211) = raw30294 := by
      apply Matrix.ext; unfold tripleCharges sourceA2211 sourceB2211 sourceC2211 difference raw30294; decide +kernel
    rw [ha]
    exact (canonical30294 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2211 + difference 5 1) (sourceB2211 + difference 1 5) sourceC2211) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2164) := by
    have ha : (tripleCharges (sourceA2211 + difference 5 1) (sourceB2211 + difference 1 5) sourceC2211) = raw30295 := by
      apply Matrix.ext; unfold tripleCharges sourceA2211 sourceB2211 sourceC2211 difference raw30295; decide +kernel
    rw [ha]
    exact (canonical30295 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2211 + difference 5 2) (sourceB2211 + difference 2 5) sourceC2211) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2153) := by
    have ha : (tripleCharges (sourceA2211 + difference 5 2) (sourceB2211 + difference 2 5) sourceC2211) = raw30296 := by
      apply Matrix.ext; unfold tripleCharges sourceA2211 sourceB2211 sourceC2211 difference raw30296; decide +kernel
    rw [ha]
    exact (canonical30296 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2211 + difference 5 3) (sourceB2211 + difference 3 5) sourceC2211) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2147) := by
    have ha : (tripleCharges (sourceA2211 + difference 5 3) (sourceB2211 + difference 3 5) sourceC2211) = raw30297 := by
      apply Matrix.ext; unfold tripleCharges sourceA2211 sourceB2211 sourceC2211 difference raw30297; decide +kernel
    rw [ha]
    exact (canonical30297 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2211 + difference 5 4) (sourceB2211 + difference 4 5) sourceC2211) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2259) := by
    have ha : (tripleCharges (sourceA2211 + difference 5 4) (sourceB2211 + difference 4 5) sourceC2211) = raw30298 := by
      apply Matrix.ext; unfold tripleCharges sourceA2211 sourceB2211 sourceC2211 difference raw30298; decide +kernel
    rw [ha]
    exact (canonical30298 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2211 sourceB2211 sourceC2211
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2211, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2212 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2212 : Charge := ![1, 0, 1, 0, 0, -2]
def sourceC2212 : Charge := ![2, 1, -1, 0, -2, 0]
def sourceForm2212 : Integer.Sparse Master := [(Sum.inr 2321, 1), (Sum.inr 2325, 1), (Sum.inr 2327, 1), (Sum.inr 2341, 1), (Sum.inr 2488, 1), (Sum.inr 3693, 1), (Sum.inr 4092, -1)]

theorem sourceEq2212 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2212 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2212 + difference 0 1) (sourceB2212 + difference 1 0) sourceC2212) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3693) := by
    have ha : (tripleCharges (sourceA2212 + difference 0 1) (sourceB2212 + difference 1 0) sourceC2212) = raw30299 := by
      apply Matrix.ext; unfold tripleCharges sourceA2212 sourceB2212 sourceC2212 difference raw30299; decide +kernel
    rw [ha]
    exact (canonical30299 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2212 + difference 1 1) (sourceB2212 + difference 1 1) sourceC2212) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2488) := by
    have ha : (tripleCharges (sourceA2212 + difference 1 1) (sourceB2212 + difference 1 1) sourceC2212) = raw30300 := by
      apply Matrix.ext; unfold tripleCharges sourceA2212 sourceB2212 sourceC2212 difference raw30300; decide +kernel
    rw [ha]
    exact (canonical30300 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2212 + difference 2 1) (sourceB2212 + difference 1 2) sourceC2212) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2341) := by
    have ha : (tripleCharges (sourceA2212 + difference 2 1) (sourceB2212 + difference 1 2) sourceC2212) = raw30301 := by
      apply Matrix.ext; unfold tripleCharges sourceA2212 sourceB2212 sourceC2212 difference raw30301; decide +kernel
    rw [ha]
    exact (canonical30301 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2212 + difference 3 1) (sourceB2212 + difference 1 3) sourceC2212) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2321) := by
    have ha : (tripleCharges (sourceA2212 + difference 3 1) (sourceB2212 + difference 1 3) sourceC2212) = raw30302 := by
      apply Matrix.ext; unfold tripleCharges sourceA2212 sourceB2212 sourceC2212 difference raw30302; decide +kernel
    rw [ha]
    exact (canonical30302 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2212 + difference 4 1) (sourceB2212 + difference 1 4) sourceC2212) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2325) := by
    have ha : (tripleCharges (sourceA2212 + difference 4 1) (sourceB2212 + difference 1 4) sourceC2212) = raw30303 := by
      apply Matrix.ext; unfold tripleCharges sourceA2212 sourceB2212 sourceC2212 difference raw30303; decide +kernel
    rw [ha]
    exact (canonical30303 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2212 + difference 5 1) (sourceB2212 + difference 1 5) sourceC2212) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2327) := by
    have ha : (tripleCharges (sourceA2212 + difference 5 1) (sourceB2212 + difference 1 5) sourceC2212) = raw30304 := by
      apply Matrix.ext; unfold tripleCharges sourceA2212 sourceB2212 sourceC2212 difference raw30304; decide +kernel
    rw [ha]
    exact (canonical30304 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2212 + sourceB2212) sourceC2212) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2212 + sourceB2212) sourceC2212) = raw30305 := by
      apply Matrix.ext; unfold doubleCharges sourceA2212 sourceB2212 sourceC2212 raw30305; decide +kernel
    rw [ha]
    exact (canonical30305 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2212 sourceB2212 sourceC2212
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2212, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2213 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2213 : Charge := ![2, 1, -1, 0, -2, 0]
def sourceC2213 : Charge := ![1, 0, 1, 0, 0, -2]
def sourceForm2213 : Integer.Sparse Master := [(Sum.inr 4291, 1), (Sum.inr 4294, 1), (Sum.inr 4296, 1), (Sum.inr 4313, 1), (Sum.inr 4466, 1), (Sum.inr 4660, 1), (Sum.inr 4662, 1), (Sum.inr 4681, 1), (Sum.inr 4827, 1), (Sum.inr 4905, 1), (Sum.inr 4908, 1), (Sum.inr 4922, 1), (Sum.inr 4960, 1), (Sum.inr 4972, 1), (Sum.inr 5030, 1), (Sum.inr 5038, 1), (Sum.inr 5070, 1), (Sum.inr 5076, 1), (Sum.inr 5078, 1), (Sum.inr 5080, 1), (Sum.inr 5095, 1), (Sum.inr 5105, 1), (Sum.inr 5176, 1), (Sum.inr 5291, 1), (Sum.inr 5294, 1), (Sum.inr 5355, 1), (Sum.inr 5380, 1), (Sum.inr 5388, 1), (Sum.inr 5434, 1), (Sum.inr 5438, 1)]

theorem sourceEq2213 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2213 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2213 + difference 0 1) (sourceB2213 + difference 1 0) sourceC2213) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5355) := by
    have ha : (tripleCharges (sourceA2213 + difference 0 1) (sourceB2213 + difference 1 0) sourceC2213) = raw30306 := by
      apply Matrix.ext; unfold tripleCharges sourceA2213 sourceB2213 sourceC2213 difference raw30306; decide +kernel
    rw [ha]
    exact (canonical30306 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2213 + difference 0 2) (sourceB2213 + difference 2 0) sourceC2213) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5388) := by
    have ha : (tripleCharges (sourceA2213 + difference 0 2) (sourceB2213 + difference 2 0) sourceC2213) = raw30307 := by
      apply Matrix.ext; unfold tripleCharges sourceA2213 sourceB2213 sourceC2213 difference raw30307; decide +kernel
    rw [ha]
    exact (canonical30307 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2213 + difference 0 3) (sourceB2213 + difference 3 0) sourceC2213) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5380) := by
    have ha : (tripleCharges (sourceA2213 + difference 0 3) (sourceB2213 + difference 3 0) sourceC2213) = raw30308 := by
      apply Matrix.ext; unfold tripleCharges sourceA2213 sourceB2213 sourceC2213 difference raw30308; decide +kernel
    rw [ha]
    exact (canonical30308 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2213 + difference 0 4) (sourceB2213 + difference 4 0) sourceC2213) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA2213 + difference 0 4) (sourceB2213 + difference 4 0) sourceC2213) = raw18831 := by
      apply Matrix.ext; unfold tripleCharges sourceA2213 sourceB2213 sourceC2213 difference raw18831; decide +kernel
    rw [ha]
    exact (canonical18831 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2213 + difference 0 5) (sourceB2213 + difference 5 0) sourceC2213) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA2213 + difference 0 5) (sourceB2213 + difference 5 0) sourceC2213) = raw18826 := by
      apply Matrix.ext; unfold tripleCharges sourceA2213 sourceB2213 sourceC2213 difference raw18826; decide +kernel
    rw [ha]
    exact (canonical18826 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2213 + difference 1 0) (sourceB2213 + difference 0 1) sourceC2213) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4466) := by
    have ha : (tripleCharges (sourceA2213 + difference 1 0) (sourceB2213 + difference 0 1) sourceC2213) = raw30309 := by
      apply Matrix.ext; unfold tripleCharges sourceA2213 sourceB2213 sourceC2213 difference raw30309; decide +kernel
    rw [ha]
    exact (canonical30309 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2213 + difference 1 2) (sourceB2213 + difference 2 1) sourceC2213) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5176) := by
    have ha : (tripleCharges (sourceA2213 + difference 1 2) (sourceB2213 + difference 2 1) sourceC2213) = raw30310 := by
      apply Matrix.ext; unfold tripleCharges sourceA2213 sourceB2213 sourceC2213 difference raw30310; decide +kernel
    rw [ha]
    exact (canonical30310 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2213 + difference 1 3) (sourceB2213 + difference 3 1) sourceC2213) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5080) := by
    have ha : (tripleCharges (sourceA2213 + difference 1 3) (sourceB2213 + difference 3 1) sourceC2213) = raw30311 := by
      apply Matrix.ext; unfold tripleCharges sourceA2213 sourceB2213 sourceC2213 difference raw30311; decide +kernel
    rw [ha]
    exact (canonical30311 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2213 + difference 1 4) (sourceB2213 + difference 4 1) sourceC2213) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA2213 + difference 1 4) (sourceB2213 + difference 4 1) sourceC2213) = raw30312 := by
      apply Matrix.ext; unfold tripleCharges sourceA2213 sourceB2213 sourceC2213 difference raw30312; decide +kernel
    rw [ha]
    exact (canonical30312 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2213 + difference 1 5) (sourceB2213 + difference 5 1) sourceC2213) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5291) := by
    have ha : (tripleCharges (sourceA2213 + difference 1 5) (sourceB2213 + difference 5 1) sourceC2213) = raw30313 := by
      apply Matrix.ext; unfold tripleCharges sourceA2213 sourceB2213 sourceC2213 difference raw30313; decide +kernel
    rw [ha]
    exact (canonical30313 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2213 + difference 2 0) (sourceB2213 + difference 0 2) sourceC2213) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4313) := by
    have ha : (tripleCharges (sourceA2213 + difference 2 0) (sourceB2213 + difference 0 2) sourceC2213) = raw30314 := by
      apply Matrix.ext; unfold tripleCharges sourceA2213 sourceB2213 sourceC2213 difference raw30314; decide +kernel
    rw [ha]
    exact (canonical30314 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2213 + difference 2 1) (sourceB2213 + difference 1 2) sourceC2213) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4922) := by
    have ha : (tripleCharges (sourceA2213 + difference 2 1) (sourceB2213 + difference 1 2) sourceC2213) = raw30315 := by
      apply Matrix.ext; unfold tripleCharges sourceA2213 sourceB2213 sourceC2213 difference raw30315; decide +kernel
    rw [ha]
    exact (canonical30315 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2213 + difference 2 3) (sourceB2213 + difference 3 2) sourceC2213) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5030) := by
    have ha : (tripleCharges (sourceA2213 + difference 2 3) (sourceB2213 + difference 3 2) sourceC2213) = raw30316 := by
      apply Matrix.ext; unfold tripleCharges sourceA2213 sourceB2213 sourceC2213 difference raw30316; decide +kernel
    rw [ha]
    exact (canonical30316 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2213 + difference 2 4) (sourceB2213 + difference 4 2) sourceC2213) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5105) := by
    have ha : (tripleCharges (sourceA2213 + difference 2 4) (sourceB2213 + difference 4 2) sourceC2213) = raw30317 := by
      apply Matrix.ext; unfold tripleCharges sourceA2213 sourceB2213 sourceC2213 difference raw30317; decide +kernel
    rw [ha]
    exact (canonical30317 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2213 + difference 2 5) (sourceB2213 + difference 5 2) sourceC2213) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5095) := by
    have ha : (tripleCharges (sourceA2213 + difference 2 5) (sourceB2213 + difference 5 2) sourceC2213) = raw30318 := by
      apply Matrix.ext; unfold tripleCharges sourceA2213 sourceB2213 sourceC2213 difference raw30318; decide +kernel
    rw [ha]
    exact (canonical30318 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2213 + difference 3 0) (sourceB2213 + difference 0 3) sourceC2213) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4291) := by
    have ha : (tripleCharges (sourceA2213 + difference 3 0) (sourceB2213 + difference 0 3) sourceC2213) = raw30319 := by
      apply Matrix.ext; unfold tripleCharges sourceA2213 sourceB2213 sourceC2213 difference raw30319; decide +kernel
    rw [ha]
    exact (canonical30319 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2213 + difference 3 1) (sourceB2213 + difference 1 3) sourceC2213) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4905) := by
    have ha : (tripleCharges (sourceA2213 + difference 3 1) (sourceB2213 + difference 1 3) sourceC2213) = raw30320 := by
      apply Matrix.ext; unfold tripleCharges sourceA2213 sourceB2213 sourceC2213 difference raw30320; decide +kernel
    rw [ha]
    exact (canonical30320 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2213 + difference 3 2) (sourceB2213 + difference 2 3) sourceC2213) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5038) := by
    have ha : (tripleCharges (sourceA2213 + difference 3 2) (sourceB2213 + difference 2 3) sourceC2213) = raw30321 := by
      apply Matrix.ext; unfold tripleCharges sourceA2213 sourceB2213 sourceC2213 difference raw30321; decide +kernel
    rw [ha]
    exact (canonical30321 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2213 + difference 3 4) (sourceB2213 + difference 4 3) sourceC2213) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5076) := by
    have ha : (tripleCharges (sourceA2213 + difference 3 4) (sourceB2213 + difference 4 3) sourceC2213) = raw18828 := by
      apply Matrix.ext; unfold tripleCharges sourceA2213 sourceB2213 sourceC2213 difference raw18828; decide +kernel
    rw [ha]
    exact (canonical18828 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2213 + difference 3 5) (sourceB2213 + difference 5 3) sourceC2213) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5070) := by
    have ha : (tripleCharges (sourceA2213 + difference 3 5) (sourceB2213 + difference 5 3) sourceC2213) = raw18823 := by
      apply Matrix.ext; unfold tripleCharges sourceA2213 sourceB2213 sourceC2213 difference raw18823; decide +kernel
    rw [ha]
    exact (canonical18823 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2213 + difference 4 0) (sourceB2213 + difference 0 4) sourceC2213) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4294) := by
    have ha : (tripleCharges (sourceA2213 + difference 4 0) (sourceB2213 + difference 0 4) sourceC2213) = raw30322 := by
      apply Matrix.ext; unfold tripleCharges sourceA2213 sourceB2213 sourceC2213 difference raw30322; decide +kernel
    rw [ha]
    exact (canonical30322 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2213 + difference 4 1) (sourceB2213 + difference 1 4) sourceC2213) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4662) := by
    have ha : (tripleCharges (sourceA2213 + difference 4 1) (sourceB2213 + difference 1 4) sourceC2213) = raw30323 := by
      apply Matrix.ext; unfold tripleCharges sourceA2213 sourceB2213 sourceC2213 difference raw30323; decide +kernel
    rw [ha]
    exact (canonical30323 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2213 + difference 4 2) (sourceB2213 + difference 2 4) sourceC2213) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4681) := by
    have ha : (tripleCharges (sourceA2213 + difference 4 2) (sourceB2213 + difference 2 4) sourceC2213) = raw30324 := by
      apply Matrix.ext; unfold tripleCharges sourceA2213 sourceB2213 sourceC2213 difference raw30324; decide +kernel
    rw [ha]
    exact (canonical30324 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2213 + difference 4 3) (sourceB2213 + difference 3 4) sourceC2213) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4660) := by
    have ha : (tripleCharges (sourceA2213 + difference 4 3) (sourceB2213 + difference 3 4) sourceC2213) = raw30325 := by
      apply Matrix.ext; unfold tripleCharges sourceA2213 sourceB2213 sourceC2213 difference raw30325; decide +kernel
    rw [ha]
    exact (canonical30325 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2213 + difference 4 5) (sourceB2213 + difference 5 4) sourceC2213) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4827) := by
    have ha : (tripleCharges (sourceA2213 + difference 4 5) (sourceB2213 + difference 5 4) sourceC2213) = raw30326 := by
      apply Matrix.ext; unfold tripleCharges sourceA2213 sourceB2213 sourceC2213 difference raw30326; decide +kernel
    rw [ha]
    exact (canonical30326 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2213 + difference 5 0) (sourceB2213 + difference 0 5) sourceC2213) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4296) := by
    have ha : (tripleCharges (sourceA2213 + difference 5 0) (sourceB2213 + difference 0 5) sourceC2213) = raw30327 := by
      apply Matrix.ext; unfold tripleCharges sourceA2213 sourceB2213 sourceC2213 difference raw30327; decide +kernel
    rw [ha]
    exact (canonical30327 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2213 + difference 5 1) (sourceB2213 + difference 1 5) sourceC2213) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4908) := by
    have ha : (tripleCharges (sourceA2213 + difference 5 1) (sourceB2213 + difference 1 5) sourceC2213) = raw30328 := by
      apply Matrix.ext; unfold tripleCharges sourceA2213 sourceB2213 sourceC2213 difference raw30328; decide +kernel
    rw [ha]
    exact (canonical30328 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2213 + difference 5 2) (sourceB2213 + difference 2 5) sourceC2213) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4972) := by
    have ha : (tripleCharges (sourceA2213 + difference 5 2) (sourceB2213 + difference 2 5) sourceC2213) = raw30329 := by
      apply Matrix.ext; unfold tripleCharges sourceA2213 sourceB2213 sourceC2213 difference raw30329; decide +kernel
    rw [ha]
    exact (canonical30329 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2213 + difference 5 3) (sourceB2213 + difference 3 5) sourceC2213) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4960) := by
    have ha : (tripleCharges (sourceA2213 + difference 5 3) (sourceB2213 + difference 3 5) sourceC2213) = raw30330 := by
      apply Matrix.ext; unfold tripleCharges sourceA2213 sourceB2213 sourceC2213 difference raw30330; decide +kernel
    rw [ha]
    exact (canonical30330 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2213 + difference 5 4) (sourceB2213 + difference 4 5) sourceC2213) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5078) := by
    have ha : (tripleCharges (sourceA2213 + difference 5 4) (sourceB2213 + difference 4 5) sourceC2213) = raw30331 := by
      apply Matrix.ext; unfold tripleCharges sourceA2213 sourceB2213 sourceC2213 difference raw30331; decide +kernel
    rw [ha]
    exact (canonical30331 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2213 sourceB2213 sourceC2213
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2213, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2214 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2214 : Charge := ![2, 1, -1, 0, -2, 0]
def sourceC2214 : Charge := ![1, 0, 1, 0, 0, -2]
def sourceForm2214 : Integer.Sparse Master := [(Sum.inr 869, 1), (Sum.inr 872, 1), (Sum.inr 874, 1), (Sum.inr 891, 1), (Sum.inr 1049, 1), (Sum.inr 1786, 1), (Sum.inr 1788, 1), (Sum.inr 1807, 1), (Sum.inr 2079, 1), (Sum.inr 2298, 1), (Sum.inr 2301, 1), (Sum.inr 2313, 1), (Sum.inr 2412, 1), (Sum.inr 2419, 1), (Sum.inr 2431, 1), (Sum.inr 2434, 1), (Sum.inr 2477, 1), (Sum.inr 2483, 1), (Sum.inr 2485, 1), (Sum.inr 2488, 1), (Sum.inr 2505, 1), (Sum.inr 2515, 1), (Sum.inr 2604, 1), (Sum.inr 2765, 1), (Sum.inr 2768, 1), (Sum.inr 3693, 1), (Sum.inr 3721, 1), (Sum.inr 3737, 1), (Sum.inr 3876, 1), (Sum.inr 3982, 1)]

theorem sourceEq2214 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2214 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2214 + difference 0 1) (sourceB2214 + difference 1 0) sourceC2214) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3693) := by
    have ha : (tripleCharges (sourceA2214 + difference 0 1) (sourceB2214 + difference 1 0) sourceC2214) = raw30332 := by
      apply Matrix.ext; unfold tripleCharges sourceA2214 sourceB2214 sourceC2214 difference raw30332; decide +kernel
    rw [ha]
    exact (canonical30332 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2214 + difference 0 2) (sourceB2214 + difference 2 0) sourceC2214) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3737) := by
    have ha : (tripleCharges (sourceA2214 + difference 0 2) (sourceB2214 + difference 2 0) sourceC2214) = raw30333 := by
      apply Matrix.ext; unfold tripleCharges sourceA2214 sourceB2214 sourceC2214 difference raw30333; decide +kernel
    rw [ha]
    exact (canonical30333 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2214 + difference 0 3) (sourceB2214 + difference 3 0) sourceC2214) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3721) := by
    have ha : (tripleCharges (sourceA2214 + difference 0 3) (sourceB2214 + difference 3 0) sourceC2214) = raw30334 := by
      apply Matrix.ext; unfold tripleCharges sourceA2214 sourceB2214 sourceC2214 difference raw30334; decide +kernel
    rw [ha]
    exact (canonical30334 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2214 + difference 0 4) (sourceB2214 + difference 4 0) sourceC2214) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3982) := by
    have ha : (tripleCharges (sourceA2214 + difference 0 4) (sourceB2214 + difference 4 0) sourceC2214) = raw18861 := by
      apply Matrix.ext; unfold tripleCharges sourceA2214 sourceB2214 sourceC2214 difference raw18861; decide +kernel
    rw [ha]
    exact (canonical18861 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2214 + difference 0 5) (sourceB2214 + difference 5 0) sourceC2214) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3876) := by
    have ha : (tripleCharges (sourceA2214 + difference 0 5) (sourceB2214 + difference 5 0) sourceC2214) = raw18856 := by
      apply Matrix.ext; unfold tripleCharges sourceA2214 sourceB2214 sourceC2214 difference raw18856; decide +kernel
    rw [ha]
    exact (canonical18856 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2214 + difference 1 0) (sourceB2214 + difference 0 1) sourceC2214) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1049) := by
    have ha : (tripleCharges (sourceA2214 + difference 1 0) (sourceB2214 + difference 0 1) sourceC2214) = raw30335 := by
      apply Matrix.ext; unfold tripleCharges sourceA2214 sourceB2214 sourceC2214 difference raw30335; decide +kernel
    rw [ha]
    exact (canonical30335 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2214 + difference 1 2) (sourceB2214 + difference 2 1) sourceC2214) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2604) := by
    have ha : (tripleCharges (sourceA2214 + difference 1 2) (sourceB2214 + difference 2 1) sourceC2214) = raw30336 := by
      apply Matrix.ext; unfold tripleCharges sourceA2214 sourceB2214 sourceC2214 difference raw30336; decide +kernel
    rw [ha]
    exact (canonical30336 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2214 + difference 1 3) (sourceB2214 + difference 3 1) sourceC2214) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2488) := by
    have ha : (tripleCharges (sourceA2214 + difference 1 3) (sourceB2214 + difference 3 1) sourceC2214) = raw30337 := by
      apply Matrix.ext; unfold tripleCharges sourceA2214 sourceB2214 sourceC2214 difference raw30337; decide +kernel
    rw [ha]
    exact (canonical30337 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2214 + difference 1 4) (sourceB2214 + difference 4 1) sourceC2214) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2768) := by
    have ha : (tripleCharges (sourceA2214 + difference 1 4) (sourceB2214 + difference 4 1) sourceC2214) = raw30338 := by
      apply Matrix.ext; unfold tripleCharges sourceA2214 sourceB2214 sourceC2214 difference raw30338; decide +kernel
    rw [ha]
    exact (canonical30338 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2214 + difference 1 5) (sourceB2214 + difference 5 1) sourceC2214) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2765) := by
    have ha : (tripleCharges (sourceA2214 + difference 1 5) (sourceB2214 + difference 5 1) sourceC2214) = raw30339 := by
      apply Matrix.ext; unfold tripleCharges sourceA2214 sourceB2214 sourceC2214 difference raw30339; decide +kernel
    rw [ha]
    exact (canonical30339 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2214 + difference 2 0) (sourceB2214 + difference 0 2) sourceC2214) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 891) := by
    have ha : (tripleCharges (sourceA2214 + difference 2 0) (sourceB2214 + difference 0 2) sourceC2214) = raw30340 := by
      apply Matrix.ext; unfold tripleCharges sourceA2214 sourceB2214 sourceC2214 difference raw30340; decide +kernel
    rw [ha]
    exact (canonical30340 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2214 + difference 2 1) (sourceB2214 + difference 1 2) sourceC2214) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2313) := by
    have ha : (tripleCharges (sourceA2214 + difference 2 1) (sourceB2214 + difference 1 2) sourceC2214) = raw30341 := by
      apply Matrix.ext; unfold tripleCharges sourceA2214 sourceB2214 sourceC2214 difference raw30341; decide +kernel
    rw [ha]
    exact (canonical30341 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2214 + difference 2 3) (sourceB2214 + difference 3 2) sourceC2214) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2419) := by
    have ha : (tripleCharges (sourceA2214 + difference 2 3) (sourceB2214 + difference 3 2) sourceC2214) = raw30342 := by
      apply Matrix.ext; unfold tripleCharges sourceA2214 sourceB2214 sourceC2214 difference raw30342; decide +kernel
    rw [ha]
    exact (canonical30342 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2214 + difference 2 4) (sourceB2214 + difference 4 2) sourceC2214) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2515) := by
    have ha : (tripleCharges (sourceA2214 + difference 2 4) (sourceB2214 + difference 4 2) sourceC2214) = raw30343 := by
      apply Matrix.ext; unfold tripleCharges sourceA2214 sourceB2214 sourceC2214 difference raw30343; decide +kernel
    rw [ha]
    exact (canonical30343 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2214 + difference 2 5) (sourceB2214 + difference 5 2) sourceC2214) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2505) := by
    have ha : (tripleCharges (sourceA2214 + difference 2 5) (sourceB2214 + difference 5 2) sourceC2214) = raw30344 := by
      apply Matrix.ext; unfold tripleCharges sourceA2214 sourceB2214 sourceC2214 difference raw30344; decide +kernel
    rw [ha]
    exact (canonical30344 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2214 + difference 3 0) (sourceB2214 + difference 0 3) sourceC2214) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 869) := by
    have ha : (tripleCharges (sourceA2214 + difference 3 0) (sourceB2214 + difference 0 3) sourceC2214) = raw30345 := by
      apply Matrix.ext; unfold tripleCharges sourceA2214 sourceB2214 sourceC2214 difference raw30345; decide +kernel
    rw [ha]
    exact (canonical30345 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2214 + difference 3 1) (sourceB2214 + difference 1 3) sourceC2214) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2298) := by
    have ha : (tripleCharges (sourceA2214 + difference 3 1) (sourceB2214 + difference 1 3) sourceC2214) = raw30346 := by
      apply Matrix.ext; unfold tripleCharges sourceA2214 sourceB2214 sourceC2214 difference raw30346; decide +kernel
    rw [ha]
    exact (canonical30346 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2214 + difference 3 2) (sourceB2214 + difference 2 3) sourceC2214) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2431) := by
    have ha : (tripleCharges (sourceA2214 + difference 3 2) (sourceB2214 + difference 2 3) sourceC2214) = raw30347 := by
      apply Matrix.ext; unfold tripleCharges sourceA2214 sourceB2214 sourceC2214 difference raw30347; decide +kernel
    rw [ha]
    exact (canonical30347 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2214 + difference 3 4) (sourceB2214 + difference 4 3) sourceC2214) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2483) := by
    have ha : (tripleCharges (sourceA2214 + difference 3 4) (sourceB2214 + difference 4 3) sourceC2214) = raw18858 := by
      apply Matrix.ext; unfold tripleCharges sourceA2214 sourceB2214 sourceC2214 difference raw18858; decide +kernel
    rw [ha]
    exact (canonical18858 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2214 + difference 3 5) (sourceB2214 + difference 5 3) sourceC2214) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2477) := by
    have ha : (tripleCharges (sourceA2214 + difference 3 5) (sourceB2214 + difference 5 3) sourceC2214) = raw18853 := by
      apply Matrix.ext; unfold tripleCharges sourceA2214 sourceB2214 sourceC2214 difference raw18853; decide +kernel
    rw [ha]
    exact (canonical18853 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2214 + difference 4 0) (sourceB2214 + difference 0 4) sourceC2214) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 872) := by
    have ha : (tripleCharges (sourceA2214 + difference 4 0) (sourceB2214 + difference 0 4) sourceC2214) = raw30348 := by
      apply Matrix.ext; unfold tripleCharges sourceA2214 sourceB2214 sourceC2214 difference raw30348; decide +kernel
    rw [ha]
    exact (canonical30348 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2214 + difference 4 1) (sourceB2214 + difference 1 4) sourceC2214) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1788) := by
    have ha : (tripleCharges (sourceA2214 + difference 4 1) (sourceB2214 + difference 1 4) sourceC2214) = raw30349 := by
      apply Matrix.ext; unfold tripleCharges sourceA2214 sourceB2214 sourceC2214 difference raw30349; decide +kernel
    rw [ha]
    exact (canonical30349 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2214 + difference 4 2) (sourceB2214 + difference 2 4) sourceC2214) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1807) := by
    have ha : (tripleCharges (sourceA2214 + difference 4 2) (sourceB2214 + difference 2 4) sourceC2214) = raw30350 := by
      apply Matrix.ext; unfold tripleCharges sourceA2214 sourceB2214 sourceC2214 difference raw30350; decide +kernel
    rw [ha]
    exact (canonical30350 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2214 + difference 4 3) (sourceB2214 + difference 3 4) sourceC2214) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1786) := by
    have ha : (tripleCharges (sourceA2214 + difference 4 3) (sourceB2214 + difference 3 4) sourceC2214) = raw30351 := by
      apply Matrix.ext; unfold tripleCharges sourceA2214 sourceB2214 sourceC2214 difference raw30351; decide +kernel
    rw [ha]
    exact (canonical30351 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2214 + difference 4 5) (sourceB2214 + difference 5 4) sourceC2214) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2079) := by
    have ha : (tripleCharges (sourceA2214 + difference 4 5) (sourceB2214 + difference 5 4) sourceC2214) = raw30352 := by
      apply Matrix.ext; unfold tripleCharges sourceA2214 sourceB2214 sourceC2214 difference raw30352; decide +kernel
    rw [ha]
    exact (canonical30352 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2214 + difference 5 0) (sourceB2214 + difference 0 5) sourceC2214) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 874) := by
    have ha : (tripleCharges (sourceA2214 + difference 5 0) (sourceB2214 + difference 0 5) sourceC2214) = raw30353 := by
      apply Matrix.ext; unfold tripleCharges sourceA2214 sourceB2214 sourceC2214 difference raw30353; decide +kernel
    rw [ha]
    exact (canonical30353 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2214 + difference 5 1) (sourceB2214 + difference 1 5) sourceC2214) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2301) := by
    have ha : (tripleCharges (sourceA2214 + difference 5 1) (sourceB2214 + difference 1 5) sourceC2214) = raw30354 := by
      apply Matrix.ext; unfold tripleCharges sourceA2214 sourceB2214 sourceC2214 difference raw30354; decide +kernel
    rw [ha]
    exact (canonical30354 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2214 + difference 5 2) (sourceB2214 + difference 2 5) sourceC2214) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2434) := by
    have ha : (tripleCharges (sourceA2214 + difference 5 2) (sourceB2214 + difference 2 5) sourceC2214) = raw30355 := by
      apply Matrix.ext; unfold tripleCharges sourceA2214 sourceB2214 sourceC2214 difference raw30355; decide +kernel
    rw [ha]
    exact (canonical30355 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2214 + difference 5 3) (sourceB2214 + difference 3 5) sourceC2214) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2412) := by
    have ha : (tripleCharges (sourceA2214 + difference 5 3) (sourceB2214 + difference 3 5) sourceC2214) = raw30356 := by
      apply Matrix.ext; unfold tripleCharges sourceA2214 sourceB2214 sourceC2214 difference raw30356; decide +kernel
    rw [ha]
    exact (canonical30356 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2214 + difference 5 4) (sourceB2214 + difference 4 5) sourceC2214) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2485) := by
    have ha : (tripleCharges (sourceA2214 + difference 5 4) (sourceB2214 + difference 4 5) sourceC2214) = raw30357 := by
      apply Matrix.ext; unfold tripleCharges sourceA2214 sourceB2214 sourceC2214 difference raw30357; decide +kernel
    rw [ha]
    exact (canonical30357 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2214 sourceB2214 sourceC2214
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2214, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2215 : Charge := ![1, 0, 1, 0, 0, -2]
def sourceB2215 : Charge := ![2, 1, -1, 0, -2, 0]
def sourceC2215 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceForm2215 : Integer.Sparse Master := [(Sum.inr 4731, 1), (Sum.inr 4744, 1), (Sum.inr 4745, 1), (Sum.inr 4749, 1), (Sum.inr 4810, 1), (Sum.inr 4993, 1), (Sum.inr 5002, 1), (Sum.inr 5003, 1), (Sum.inr 5009, 1), (Sum.inr 5049, 1), (Sum.inr 5050, 1), (Sum.inr 5053, 1), (Sum.inr 5066, 1), (Sum.inr 5067, 1), (Sum.inr 5079, 1), (Sum.inr 5080, 1), (Sum.inr 5081, 1), (Sum.inr 5089, 1), (Sum.inr 5090, 1), (Sum.inr 5110, 1), (Sum.inr 5111, 1), (Sum.inr 5129, 2), (Sum.inr 5140, 1), (Sum.inr 5141, 1), (Sum.inr 5151, 1), (Sum.inr 5152, 1), (Sum.inr 5176, 2), (Sum.inr 5188, 1)]

theorem sourceEq2215 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2215 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2215 + difference 0 1) (sourceB2215 + difference 1 0) sourceC2215) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5188) := by
    have ha : (tripleCharges (sourceA2215 + difference 0 1) (sourceB2215 + difference 1 0) sourceC2215) = raw30358 := by
      apply Matrix.ext; unfold tripleCharges sourceA2215 sourceB2215 sourceC2215 difference raw30358; decide +kernel
    rw [ha]
    exact (canonical30358 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2215 + difference 0 2) (sourceB2215 + difference 2 0) sourceC2215) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5176) := by
    have ha : (tripleCharges (sourceA2215 + difference 0 2) (sourceB2215 + difference 2 0) sourceC2215) = raw30359 := by
      apply Matrix.ext; unfold tripleCharges sourceA2215 sourceB2215 sourceC2215 difference raw30359; decide +kernel
    rw [ha]
    exact (canonical30359 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2215 + difference 0 3) (sourceB2215 + difference 3 0) sourceC2215) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5129) := by
    have ha : (tripleCharges (sourceA2215 + difference 0 3) (sourceB2215 + difference 3 0) sourceC2215) = raw30360 := by
      apply Matrix.ext; unfold tripleCharges sourceA2215 sourceB2215 sourceC2215 difference raw30360; decide +kernel
    rw [ha]
    exact (canonical30360 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2215 + difference 0 4) (sourceB2215 + difference 4 0) sourceC2215) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA2215 + difference 0 4) (sourceB2215 + difference 4 0) sourceC2215) = raw30361 := by
      apply Matrix.ext; unfold tripleCharges sourceA2215 sourceB2215 sourceC2215 difference raw30361; decide +kernel
    rw [ha]
    exact (canonical30361 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2215 + difference 0 5) (sourceB2215 + difference 5 0) sourceC2215) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5140) := by
    have ha : (tripleCharges (sourceA2215 + difference 0 5) (sourceB2215 + difference 5 0) sourceC2215) = raw30362 := by
      apply Matrix.ext; unfold tripleCharges sourceA2215 sourceB2215 sourceC2215 difference raw30362; decide +kernel
    rw [ha]
    exact (canonical30362 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2215 + difference 1 0) (sourceB2215 + difference 0 1) sourceC2215) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4810) := by
    have ha : (tripleCharges (sourceA2215 + difference 1 0) (sourceB2215 + difference 0 1) sourceC2215) = raw30363 := by
      apply Matrix.ext; unfold tripleCharges sourceA2215 sourceB2215 sourceC2215 difference raw30363; decide +kernel
    rw [ha]
    exact (canonical30363 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2215 + difference 1 2) (sourceB2215 + difference 2 1) sourceC2215) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5176) := by
    have ha : (tripleCharges (sourceA2215 + difference 1 2) (sourceB2215 + difference 2 1) sourceC2215) = raw29694 := by
      apply Matrix.ext; unfold tripleCharges sourceA2215 sourceB2215 sourceC2215 difference raw29694; decide +kernel
    rw [ha]
    exact (canonical29694 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2215 + difference 1 3) (sourceB2215 + difference 3 1) sourceC2215) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5129) := by
    have ha : (tripleCharges (sourceA2215 + difference 1 3) (sourceB2215 + difference 3 1) sourceC2215) = raw30176 := by
      apply Matrix.ext; unfold tripleCharges sourceA2215 sourceB2215 sourceC2215 difference raw30176; decide +kernel
    rw [ha]
    exact (canonical30176 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2215 + difference 1 4) (sourceB2215 + difference 4 1) sourceC2215) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5152) := by
    have ha : (tripleCharges (sourceA2215 + difference 1 4) (sourceB2215 + difference 4 1) sourceC2215) = raw29685 := by
      apply Matrix.ext; unfold tripleCharges sourceA2215 sourceB2215 sourceC2215 difference raw29685; decide +kernel
    rw [ha]
    exact (canonical29685 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2215 + difference 1 5) (sourceB2215 + difference 5 1) sourceC2215) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5151) := by
    have ha : (tripleCharges (sourceA2215 + difference 1 5) (sourceB2215 + difference 5 1) sourceC2215) = raw30364 := by
      apply Matrix.ext; unfold tripleCharges sourceA2215 sourceB2215 sourceC2215 difference raw30364; decide +kernel
    rw [ha]
    exact (canonical30364 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2215 + difference 2 0) (sourceB2215 + difference 0 2) sourceC2215) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4749) := by
    have ha : (tripleCharges (sourceA2215 + difference 2 0) (sourceB2215 + difference 0 2) sourceC2215) = raw30365 := by
      apply Matrix.ext; unfold tripleCharges sourceA2215 sourceB2215 sourceC2215 difference raw30365; decide +kernel
    rw [ha]
    exact (canonical30365 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2215 + difference 2 1) (sourceB2215 + difference 1 2) sourceC2215) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5009) := by
    have ha : (tripleCharges (sourceA2215 + difference 2 1) (sourceB2215 + difference 1 2) sourceC2215) = raw30366 := by
      apply Matrix.ext; unfold tripleCharges sourceA2215 sourceB2215 sourceC2215 difference raw30366; decide +kernel
    rw [ha]
    exact (canonical30366 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2215 + difference 2 3) (sourceB2215 + difference 3 2) sourceC2215) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5053) := by
    have ha : (tripleCharges (sourceA2215 + difference 2 3) (sourceB2215 + difference 3 2) sourceC2215) = raw30367 := by
      apply Matrix.ext; unfold tripleCharges sourceA2215 sourceB2215 sourceC2215 difference raw30367; decide +kernel
    rw [ha]
    exact (canonical30367 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2215 + difference 2 4) (sourceB2215 + difference 4 2) sourceC2215) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5090) := by
    have ha : (tripleCharges (sourceA2215 + difference 2 4) (sourceB2215 + difference 4 2) sourceC2215) = raw30368 := by
      apply Matrix.ext; unfold tripleCharges sourceA2215 sourceB2215 sourceC2215 difference raw30368; decide +kernel
    rw [ha]
    exact (canonical30368 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2215 + difference 2 5) (sourceB2215 + difference 5 2) sourceC2215) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5089) := by
    have ha : (tripleCharges (sourceA2215 + difference 2 5) (sourceB2215 + difference 5 2) sourceC2215) = raw30369 := by
      apply Matrix.ext; unfold tripleCharges sourceA2215 sourceB2215 sourceC2215 difference raw30369; decide +kernel
    rw [ha]
    exact (canonical30369 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2215 + difference 3 0) (sourceB2215 + difference 0 3) sourceC2215) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4731) := by
    have ha : (tripleCharges (sourceA2215 + difference 3 0) (sourceB2215 + difference 0 3) sourceC2215) = raw30370 := by
      apply Matrix.ext; unfold tripleCharges sourceA2215 sourceB2215 sourceC2215 difference raw30370; decide +kernel
    rw [ha]
    exact (canonical30370 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2215 + difference 3 1) (sourceB2215 + difference 1 3) sourceC2215) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4993) := by
    have ha : (tripleCharges (sourceA2215 + difference 3 1) (sourceB2215 + difference 1 3) sourceC2215) = raw30371 := by
      apply Matrix.ext; unfold tripleCharges sourceA2215 sourceB2215 sourceC2215 difference raw30371; decide +kernel
    rw [ha]
    exact (canonical30371 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2215 + difference 3 2) (sourceB2215 + difference 2 3) sourceC2215) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5080) := by
    have ha : (tripleCharges (sourceA2215 + difference 3 2) (sourceB2215 + difference 2 3) sourceC2215) = raw30372 := by
      apply Matrix.ext; unfold tripleCharges sourceA2215 sourceB2215 sourceC2215 difference raw30372; decide +kernel
    rw [ha]
    exact (canonical30372 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2215 + difference 3 4) (sourceB2215 + difference 4 3) sourceC2215) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5067) := by
    have ha : (tripleCharges (sourceA2215 + difference 3 4) (sourceB2215 + difference 4 3) sourceC2215) = raw30373 := by
      apply Matrix.ext; unfold tripleCharges sourceA2215 sourceB2215 sourceC2215 difference raw30373; decide +kernel
    rw [ha]
    exact (canonical30373 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2215 + difference 3 5) (sourceB2215 + difference 5 3) sourceC2215) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5066) := by
    have ha : (tripleCharges (sourceA2215 + difference 3 5) (sourceB2215 + difference 5 3) sourceC2215) = raw30374 := by
      apply Matrix.ext; unfold tripleCharges sourceA2215 sourceB2215 sourceC2215 difference raw30374; decide +kernel
    rw [ha]
    exact (canonical30374 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2215 + difference 4 0) (sourceB2215 + difference 0 4) sourceC2215) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4744) := by
    have ha : (tripleCharges (sourceA2215 + difference 4 0) (sourceB2215 + difference 0 4) sourceC2215) = raw30375 := by
      apply Matrix.ext; unfold tripleCharges sourceA2215 sourceB2215 sourceC2215 difference raw30375; decide +kernel
    rw [ha]
    exact (canonical30375 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2215 + difference 4 1) (sourceB2215 + difference 1 4) sourceC2215) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5002) := by
    have ha : (tripleCharges (sourceA2215 + difference 4 1) (sourceB2215 + difference 1 4) sourceC2215) = raw30376 := by
      apply Matrix.ext; unfold tripleCharges sourceA2215 sourceB2215 sourceC2215 difference raw30376; decide +kernel
    rw [ha]
    exact (canonical30376 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2215 + difference 4 2) (sourceB2215 + difference 2 4) sourceC2215) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5110) := by
    have ha : (tripleCharges (sourceA2215 + difference 4 2) (sourceB2215 + difference 2 4) sourceC2215) = raw30377 := by
      apply Matrix.ext; unfold tripleCharges sourceA2215 sourceB2215 sourceC2215 difference raw30377; decide +kernel
    rw [ha]
    exact (canonical30377 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2215 + difference 4 3) (sourceB2215 + difference 3 4) sourceC2215) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5049) := by
    have ha : (tripleCharges (sourceA2215 + difference 4 3) (sourceB2215 + difference 3 4) sourceC2215) = raw30378 := by
      apply Matrix.ext; unfold tripleCharges sourceA2215 sourceB2215 sourceC2215 difference raw30378; decide +kernel
    rw [ha]
    exact (canonical30378 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2215 + difference 4 5) (sourceB2215 + difference 5 4) sourceC2215) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5079) := by
    have ha : (tripleCharges (sourceA2215 + difference 4 5) (sourceB2215 + difference 5 4) sourceC2215) = raw30379 := by
      apply Matrix.ext; unfold tripleCharges sourceA2215 sourceB2215 sourceC2215 difference raw30379; decide +kernel
    rw [ha]
    exact (canonical30379 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2215 + difference 5 0) (sourceB2215 + difference 0 5) sourceC2215) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4745) := by
    have ha : (tripleCharges (sourceA2215 + difference 5 0) (sourceB2215 + difference 0 5) sourceC2215) = raw30380 := by
      apply Matrix.ext; unfold tripleCharges sourceA2215 sourceB2215 sourceC2215 difference raw30380; decide +kernel
    rw [ha]
    exact (canonical30380 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2215 + difference 5 1) (sourceB2215 + difference 1 5) sourceC2215) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5003) := by
    have ha : (tripleCharges (sourceA2215 + difference 5 1) (sourceB2215 + difference 1 5) sourceC2215) = raw30381 := by
      apply Matrix.ext; unfold tripleCharges sourceA2215 sourceB2215 sourceC2215 difference raw30381; decide +kernel
    rw [ha]
    exact (canonical30381 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2215 + difference 5 2) (sourceB2215 + difference 2 5) sourceC2215) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5111) := by
    have ha : (tripleCharges (sourceA2215 + difference 5 2) (sourceB2215 + difference 2 5) sourceC2215) = raw29691 := by
      apply Matrix.ext; unfold tripleCharges sourceA2215 sourceB2215 sourceC2215 difference raw29691; decide +kernel
    rw [ha]
    exact (canonical29691 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2215 + difference 5 3) (sourceB2215 + difference 3 5) sourceC2215) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5050) := by
    have ha : (tripleCharges (sourceA2215 + difference 5 3) (sourceB2215 + difference 3 5) sourceC2215) = raw30174 := by
      apply Matrix.ext; unfold tripleCharges sourceA2215 sourceB2215 sourceC2215 difference raw30174; decide +kernel
    rw [ha]
    exact (canonical30174 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2215 + difference 5 4) (sourceB2215 + difference 4 5) sourceC2215) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5081) := by
    have ha : (tripleCharges (sourceA2215 + difference 5 4) (sourceB2215 + difference 4 5) sourceC2215) = raw29683 := by
      apply Matrix.ext; unfold tripleCharges sourceA2215 sourceB2215 sourceC2215 difference raw29683; decide +kernel
    rw [ha]
    exact (canonical29683 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2215 sourceB2215 sourceC2215
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2215, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2216 : Charge := ![1, 0, 1, 0, 0, -2]
def sourceB2216 : Charge := ![2, 1, -1, 0, -2, 0]
def sourceC2216 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceForm2216 : Integer.Sparse Master := [(Sum.inr 1900, 1), (Sum.inr 1917, 1), (Sum.inr 1918, 1), (Sum.inr 1928, 1), (Sum.inr 2028, 1), (Sum.inr 2379, 1), (Sum.inr 2387, 1), (Sum.inr 2388, 1), (Sum.inr 2394, 1), (Sum.inr 2451, 1), (Sum.inr 2452, 1), (Sum.inr 2455, 1), (Sum.inr 2472, 1), (Sum.inr 2473, 1), (Sum.inr 2487, 1), (Sum.inr 2488, 1), (Sum.inr 2489, 1), (Sum.inr 2498, 1), (Sum.inr 2499, 1), (Sum.inr 2522, 1), (Sum.inr 2523, 1), (Sum.inr 2545, 1), (Sum.inr 2575, 1), (Sum.inr 2576, 1), (Sum.inr 2604, 1), (Sum.inr 2867, 1), (Sum.inr 2916, 1), (Sum.inr 2942, 1), (Sum.inr 2943, 1), (Sum.inr 2968, 1)]

theorem sourceEq2216 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2216 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2216 + difference 0 1) (sourceB2216 + difference 1 0) sourceC2216) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2867) := by
    have ha : (tripleCharges (sourceA2216 + difference 0 1) (sourceB2216 + difference 1 0) sourceC2216) = raw30382 := by
      apply Matrix.ext; unfold tripleCharges sourceA2216 sourceB2216 sourceC2216 difference raw30382; decide +kernel
    rw [ha]
    exact (canonical30382 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2216 + difference 0 2) (sourceB2216 + difference 2 0) sourceC2216) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2968) := by
    have ha : (tripleCharges (sourceA2216 + difference 0 2) (sourceB2216 + difference 2 0) sourceC2216) = raw30383 := by
      apply Matrix.ext; unfold tripleCharges sourceA2216 sourceB2216 sourceC2216 difference raw30383; decide +kernel
    rw [ha]
    exact (canonical30383 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2216 + difference 0 3) (sourceB2216 + difference 3 0) sourceC2216) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2916) := by
    have ha : (tripleCharges (sourceA2216 + difference 0 3) (sourceB2216 + difference 3 0) sourceC2216) = raw30384 := by
      apply Matrix.ext; unfold tripleCharges sourceA2216 sourceB2216 sourceC2216 difference raw30384; decide +kernel
    rw [ha]
    exact (canonical30384 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2216 + difference 0 4) (sourceB2216 + difference 4 0) sourceC2216) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2943) := by
    have ha : (tripleCharges (sourceA2216 + difference 0 4) (sourceB2216 + difference 4 0) sourceC2216) = raw30385 := by
      apply Matrix.ext; unfold tripleCharges sourceA2216 sourceB2216 sourceC2216 difference raw30385; decide +kernel
    rw [ha]
    exact (canonical30385 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2216 + difference 0 5) (sourceB2216 + difference 5 0) sourceC2216) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2942) := by
    have ha : (tripleCharges (sourceA2216 + difference 0 5) (sourceB2216 + difference 5 0) sourceC2216) = raw30386 := by
      apply Matrix.ext; unfold tripleCharges sourceA2216 sourceB2216 sourceC2216 difference raw30386; decide +kernel
    rw [ha]
    exact (canonical30386 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2216 + difference 1 0) (sourceB2216 + difference 0 1) sourceC2216) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2028) := by
    have ha : (tripleCharges (sourceA2216 + difference 1 0) (sourceB2216 + difference 0 1) sourceC2216) = raw30387 := by
      apply Matrix.ext; unfold tripleCharges sourceA2216 sourceB2216 sourceC2216 difference raw30387; decide +kernel
    rw [ha]
    exact (canonical30387 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2216 + difference 1 2) (sourceB2216 + difference 2 1) sourceC2216) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2604) := by
    have ha : (tripleCharges (sourceA2216 + difference 1 2) (sourceB2216 + difference 2 1) sourceC2216) = raw30388 := by
      apply Matrix.ext; unfold tripleCharges sourceA2216 sourceB2216 sourceC2216 difference raw30388; decide +kernel
    rw [ha]
    exact (canonical30388 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2216 + difference 1 3) (sourceB2216 + difference 3 1) sourceC2216) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2545) := by
    have ha : (tripleCharges (sourceA2216 + difference 1 3) (sourceB2216 + difference 3 1) sourceC2216) = raw30389 := by
      apply Matrix.ext; unfold tripleCharges sourceA2216 sourceB2216 sourceC2216 difference raw30389; decide +kernel
    rw [ha]
    exact (canonical30389 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2216 + difference 1 4) (sourceB2216 + difference 4 1) sourceC2216) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2576) := by
    have ha : (tripleCharges (sourceA2216 + difference 1 4) (sourceB2216 + difference 4 1) sourceC2216) = raw30390 := by
      apply Matrix.ext; unfold tripleCharges sourceA2216 sourceB2216 sourceC2216 difference raw30390; decide +kernel
    rw [ha]
    exact (canonical30390 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2216 + difference 1 5) (sourceB2216 + difference 5 1) sourceC2216) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2575) := by
    have ha : (tripleCharges (sourceA2216 + difference 1 5) (sourceB2216 + difference 5 1) sourceC2216) = raw30391 := by
      apply Matrix.ext; unfold tripleCharges sourceA2216 sourceB2216 sourceC2216 difference raw30391; decide +kernel
    rw [ha]
    exact (canonical30391 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2216 + difference 2 0) (sourceB2216 + difference 0 2) sourceC2216) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1928) := by
    have ha : (tripleCharges (sourceA2216 + difference 2 0) (sourceB2216 + difference 0 2) sourceC2216) = raw30392 := by
      apply Matrix.ext; unfold tripleCharges sourceA2216 sourceB2216 sourceC2216 difference raw30392; decide +kernel
    rw [ha]
    exact (canonical30392 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2216 + difference 2 1) (sourceB2216 + difference 1 2) sourceC2216) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2394) := by
    have ha : (tripleCharges (sourceA2216 + difference 2 1) (sourceB2216 + difference 1 2) sourceC2216) = raw30393 := by
      apply Matrix.ext; unfold tripleCharges sourceA2216 sourceB2216 sourceC2216 difference raw30393; decide +kernel
    rw [ha]
    exact (canonical30393 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2216 + difference 2 3) (sourceB2216 + difference 3 2) sourceC2216) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2455) := by
    have ha : (tripleCharges (sourceA2216 + difference 2 3) (sourceB2216 + difference 3 2) sourceC2216) = raw30394 := by
      apply Matrix.ext; unfold tripleCharges sourceA2216 sourceB2216 sourceC2216 difference raw30394; decide +kernel
    rw [ha]
    exact (canonical30394 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2216 + difference 2 4) (sourceB2216 + difference 4 2) sourceC2216) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2499) := by
    have ha : (tripleCharges (sourceA2216 + difference 2 4) (sourceB2216 + difference 4 2) sourceC2216) = raw30395 := by
      apply Matrix.ext; unfold tripleCharges sourceA2216 sourceB2216 sourceC2216 difference raw30395; decide +kernel
    rw [ha]
    exact (canonical30395 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2216 + difference 2 5) (sourceB2216 + difference 5 2) sourceC2216) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2498) := by
    have ha : (tripleCharges (sourceA2216 + difference 2 5) (sourceB2216 + difference 5 2) sourceC2216) = raw30396 := by
      apply Matrix.ext; unfold tripleCharges sourceA2216 sourceB2216 sourceC2216 difference raw30396; decide +kernel
    rw [ha]
    exact (canonical30396 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2216 + difference 3 0) (sourceB2216 + difference 0 3) sourceC2216) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1900) := by
    have ha : (tripleCharges (sourceA2216 + difference 3 0) (sourceB2216 + difference 0 3) sourceC2216) = raw30397 := by
      apply Matrix.ext; unfold tripleCharges sourceA2216 sourceB2216 sourceC2216 difference raw30397; decide +kernel
    rw [ha]
    exact (canonical30397 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2216 + difference 3 1) (sourceB2216 + difference 1 3) sourceC2216) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2379) := by
    have ha : (tripleCharges (sourceA2216 + difference 3 1) (sourceB2216 + difference 1 3) sourceC2216) = raw30398 := by
      apply Matrix.ext; unfold tripleCharges sourceA2216 sourceB2216 sourceC2216 difference raw30398; decide +kernel
    rw [ha]
    exact (canonical30398 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2216 + difference 3 2) (sourceB2216 + difference 2 3) sourceC2216) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2488) := by
    have ha : (tripleCharges (sourceA2216 + difference 3 2) (sourceB2216 + difference 2 3) sourceC2216) = raw30399 := by
      apply Matrix.ext; unfold tripleCharges sourceA2216 sourceB2216 sourceC2216 difference raw30399; decide +kernel
    rw [ha]
    exact (canonical30399 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2216 + difference 3 4) (sourceB2216 + difference 4 3) sourceC2216) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2473) := by
    have ha : (tripleCharges (sourceA2216 + difference 3 4) (sourceB2216 + difference 4 3) sourceC2216) = raw30400 := by
      apply Matrix.ext; unfold tripleCharges sourceA2216 sourceB2216 sourceC2216 difference raw30400; decide +kernel
    rw [ha]
    exact (canonical30400 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2216 + difference 3 5) (sourceB2216 + difference 5 3) sourceC2216) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2472) := by
    have ha : (tripleCharges (sourceA2216 + difference 3 5) (sourceB2216 + difference 5 3) sourceC2216) = raw30401 := by
      apply Matrix.ext; unfold tripleCharges sourceA2216 sourceB2216 sourceC2216 difference raw30401; decide +kernel
    rw [ha]
    exact (canonical30401 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2216 + difference 4 0) (sourceB2216 + difference 0 4) sourceC2216) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1917) := by
    have ha : (tripleCharges (sourceA2216 + difference 4 0) (sourceB2216 + difference 0 4) sourceC2216) = raw30402 := by
      apply Matrix.ext; unfold tripleCharges sourceA2216 sourceB2216 sourceC2216 difference raw30402; decide +kernel
    rw [ha]
    exact (canonical30402 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2216 + difference 4 1) (sourceB2216 + difference 1 4) sourceC2216) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2387) := by
    have ha : (tripleCharges (sourceA2216 + difference 4 1) (sourceB2216 + difference 1 4) sourceC2216) = raw30403 := by
      apply Matrix.ext; unfold tripleCharges sourceA2216 sourceB2216 sourceC2216 difference raw30403; decide +kernel
    rw [ha]
    exact (canonical30403 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2216 + difference 4 2) (sourceB2216 + difference 2 4) sourceC2216) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2522) := by
    have ha : (tripleCharges (sourceA2216 + difference 4 2) (sourceB2216 + difference 2 4) sourceC2216) = raw30404 := by
      apply Matrix.ext; unfold tripleCharges sourceA2216 sourceB2216 sourceC2216 difference raw30404; decide +kernel
    rw [ha]
    exact (canonical30404 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2216 + difference 4 3) (sourceB2216 + difference 3 4) sourceC2216) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2451) := by
    have ha : (tripleCharges (sourceA2216 + difference 4 3) (sourceB2216 + difference 3 4) sourceC2216) = raw30405 := by
      apply Matrix.ext; unfold tripleCharges sourceA2216 sourceB2216 sourceC2216 difference raw30405; decide +kernel
    rw [ha]
    exact (canonical30405 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2216 + difference 4 5) (sourceB2216 + difference 5 4) sourceC2216) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2487) := by
    have ha : (tripleCharges (sourceA2216 + difference 4 5) (sourceB2216 + difference 5 4) sourceC2216) = raw30406 := by
      apply Matrix.ext; unfold tripleCharges sourceA2216 sourceB2216 sourceC2216 difference raw30406; decide +kernel
    rw [ha]
    exact (canonical30406 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2216 + difference 5 0) (sourceB2216 + difference 0 5) sourceC2216) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1918) := by
    have ha : (tripleCharges (sourceA2216 + difference 5 0) (sourceB2216 + difference 0 5) sourceC2216) = raw30407 := by
      apply Matrix.ext; unfold tripleCharges sourceA2216 sourceB2216 sourceC2216 difference raw30407; decide +kernel
    rw [ha]
    exact (canonical30407 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2216 + difference 5 1) (sourceB2216 + difference 1 5) sourceC2216) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2388) := by
    have ha : (tripleCharges (sourceA2216 + difference 5 1) (sourceB2216 + difference 1 5) sourceC2216) = raw30408 := by
      apply Matrix.ext; unfold tripleCharges sourceA2216 sourceB2216 sourceC2216 difference raw30408; decide +kernel
    rw [ha]
    exact (canonical30408 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2216 + difference 5 2) (sourceB2216 + difference 2 5) sourceC2216) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2523) := by
    have ha : (tripleCharges (sourceA2216 + difference 5 2) (sourceB2216 + difference 2 5) sourceC2216) = raw30409 := by
      apply Matrix.ext; unfold tripleCharges sourceA2216 sourceB2216 sourceC2216 difference raw30409; decide +kernel
    rw [ha]
    exact (canonical30409 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2216 + difference 5 3) (sourceB2216 + difference 3 5) sourceC2216) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2452) := by
    have ha : (tripleCharges (sourceA2216 + difference 5 3) (sourceB2216 + difference 3 5) sourceC2216) = raw30410 := by
      apply Matrix.ext; unfold tripleCharges sourceA2216 sourceB2216 sourceC2216 difference raw30410; decide +kernel
    rw [ha]
    exact (canonical30410 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2216 + difference 5 4) (sourceB2216 + difference 4 5) sourceC2216) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2489) := by
    have ha : (tripleCharges (sourceA2216 + difference 5 4) (sourceB2216 + difference 4 5) sourceC2216) = raw30411 := by
      apply Matrix.ext; unfold tripleCharges sourceA2216 sourceB2216 sourceC2216 difference raw30411; decide +kernel
    rw [ha]
    exact (canonical30411 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2216 sourceB2216 sourceC2216
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2216, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2217 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2217 : Charge := ![1, 0, 1, 0, -1, -1]
def sourceC2217 : Charge := ![2, 1, -1, 0, -1, -1]
def sourceForm2217 : Integer.Sparse Master := [(Sum.inr 4530, 1), (Sum.inr 4535, 2), (Sum.inr 4554, 1), (Sum.inr 4593, 1), (Sum.inr 4930, 2), (Sum.inr 4932, 1), (Sum.inr 4935, 2), (Sum.inr 4944, 2), (Sum.inr 4950, 1), (Sum.inr 5039, 1), (Sum.inr 5043, 1), (Sum.inr 5073, 2), (Sum.inr 5078, 2), (Sum.inr 5104, 2), (Sum.inr 5130, 1), (Sum.inr 5189, 1), (Sum.inr 5259, 2), (Sum.inr 5356, 1), (Sum.inr 5393, 1), (Sum.inr 5404, 1), (Sum.inr 5410, 2)]

theorem sourceEq2217 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2217 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2217 + difference 0 1) (sourceB2217 + difference 1 0) sourceC2217) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5356) := by
    have ha : (tripleCharges (sourceA2217 + difference 0 1) (sourceB2217 + difference 1 0) sourceC2217) = raw30412 := by
      apply Matrix.ext; unfold tripleCharges sourceA2217 sourceB2217 sourceC2217 difference raw30412; decide +kernel
    rw [ha]
    exact (canonical30412 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2217 + difference 0 2) (sourceB2217 + difference 2 0) sourceC2217) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5404) := by
    have ha : (tripleCharges (sourceA2217 + difference 0 2) (sourceB2217 + difference 2 0) sourceC2217) = raw30413 := by
      apply Matrix.ext; unfold tripleCharges sourceA2217 sourceB2217 sourceC2217 difference raw30413; decide +kernel
    rw [ha]
    exact (canonical30413 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2217 + difference 0 3) (sourceB2217 + difference 3 0) sourceC2217) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5393) := by
    have ha : (tripleCharges (sourceA2217 + difference 0 3) (sourceB2217 + difference 3 0) sourceC2217) = raw30414 := by
      apply Matrix.ext; unfold tripleCharges sourceA2217 sourceB2217 sourceC2217 difference raw30414; decide +kernel
    rw [ha]
    exact (canonical30414 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2217 + difference 0 4) (sourceB2217 + difference 4 0) sourceC2217) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5410) := by
    have ha : (tripleCharges (sourceA2217 + difference 0 4) (sourceB2217 + difference 4 0) sourceC2217) = raw30415 := by
      apply Matrix.ext; unfold tripleCharges sourceA2217 sourceB2217 sourceC2217 difference raw30415; decide +kernel
    rw [ha]
    exact (canonical30415 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2217 + difference 0 5) (sourceB2217 + difference 5 0) sourceC2217) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5410) := by
    have ha : (tripleCharges (sourceA2217 + difference 0 5) (sourceB2217 + difference 5 0) sourceC2217) = raw30416 := by
      apply Matrix.ext; unfold tripleCharges sourceA2217 sourceB2217 sourceC2217 difference raw30416; decide +kernel
    rw [ha]
    exact (canonical30416 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2217 + difference 1 0) (sourceB2217 + difference 0 1) sourceC2217) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4593) := by
    have ha : (tripleCharges (sourceA2217 + difference 1 0) (sourceB2217 + difference 0 1) sourceC2217) = raw30417 := by
      apply Matrix.ext; unfold tripleCharges sourceA2217 sourceB2217 sourceC2217 difference raw30417; decide +kernel
    rw [ha]
    exact (canonical30417 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2217 + difference 1 2) (sourceB2217 + difference 2 1) sourceC2217) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5189) := by
    have ha : (tripleCharges (sourceA2217 + difference 1 2) (sourceB2217 + difference 2 1) sourceC2217) = raw30418 := by
      apply Matrix.ext; unfold tripleCharges sourceA2217 sourceB2217 sourceC2217 difference raw30418; decide +kernel
    rw [ha]
    exact (canonical30418 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2217 + difference 1 3) (sourceB2217 + difference 3 1) sourceC2217) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5130) := by
    have ha : (tripleCharges (sourceA2217 + difference 1 3) (sourceB2217 + difference 3 1) sourceC2217) = raw30419 := by
      apply Matrix.ext; unfold tripleCharges sourceA2217 sourceB2217 sourceC2217 difference raw30419; decide +kernel
    rw [ha]
    exact (canonical30419 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2217 + difference 1 4) (sourceB2217 + difference 4 1) sourceC2217) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA2217 + difference 1 4) (sourceB2217 + difference 4 1) sourceC2217) = raw30420 := by
      apply Matrix.ext; unfold tripleCharges sourceA2217 sourceB2217 sourceC2217 difference raw30420; decide +kernel
    rw [ha]
    exact (canonical30420 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2217 + difference 1 5) (sourceB2217 + difference 5 1) sourceC2217) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA2217 + difference 1 5) (sourceB2217 + difference 5 1) sourceC2217) = raw30421 := by
      apply Matrix.ext; unfold tripleCharges sourceA2217 sourceB2217 sourceC2217 difference raw30421; decide +kernel
    rw [ha]
    exact (canonical30421 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2217 + difference 2 0) (sourceB2217 + difference 0 2) sourceC2217) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4554) := by
    have ha : (tripleCharges (sourceA2217 + difference 2 0) (sourceB2217 + difference 0 2) sourceC2217) = raw30422 := by
      apply Matrix.ext; unfold tripleCharges sourceA2217 sourceB2217 sourceC2217 difference raw30422; decide +kernel
    rw [ha]
    exact (canonical30422 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2217 + difference 2 1) (sourceB2217 + difference 1 2) sourceC2217) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4950) := by
    have ha : (tripleCharges (sourceA2217 + difference 2 1) (sourceB2217 + difference 1 2) sourceC2217) = raw30423 := by
      apply Matrix.ext; unfold tripleCharges sourceA2217 sourceB2217 sourceC2217 difference raw30423; decide +kernel
    rw [ha]
    exact (canonical30423 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2217 + difference 2 3) (sourceB2217 + difference 3 2) sourceC2217) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5039) := by
    have ha : (tripleCharges (sourceA2217 + difference 2 3) (sourceB2217 + difference 3 2) sourceC2217) = raw30424 := by
      apply Matrix.ext; unfold tripleCharges sourceA2217 sourceB2217 sourceC2217 difference raw30424; decide +kernel
    rw [ha]
    exact (canonical30424 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2217 + difference 2 4) (sourceB2217 + difference 4 2) sourceC2217) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5104) := by
    have ha : (tripleCharges (sourceA2217 + difference 2 4) (sourceB2217 + difference 4 2) sourceC2217) = raw30425 := by
      apply Matrix.ext; unfold tripleCharges sourceA2217 sourceB2217 sourceC2217 difference raw30425; decide +kernel
    rw [ha]
    exact (canonical30425 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2217 + difference 2 5) (sourceB2217 + difference 5 2) sourceC2217) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5104) := by
    have ha : (tripleCharges (sourceA2217 + difference 2 5) (sourceB2217 + difference 5 2) sourceC2217) = raw30426 := by
      apply Matrix.ext; unfold tripleCharges sourceA2217 sourceB2217 sourceC2217 difference raw30426; decide +kernel
    rw [ha]
    exact (canonical30426 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2217 + difference 3 0) (sourceB2217 + difference 0 3) sourceC2217) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4530) := by
    have ha : (tripleCharges (sourceA2217 + difference 3 0) (sourceB2217 + difference 0 3) sourceC2217) = raw30427 := by
      apply Matrix.ext; unfold tripleCharges sourceA2217 sourceB2217 sourceC2217 difference raw30427; decide +kernel
    rw [ha]
    exact (canonical30427 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2217 + difference 3 1) (sourceB2217 + difference 1 3) sourceC2217) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4932) := by
    have ha : (tripleCharges (sourceA2217 + difference 3 1) (sourceB2217 + difference 1 3) sourceC2217) = raw30428 := by
      apply Matrix.ext; unfold tripleCharges sourceA2217 sourceB2217 sourceC2217 difference raw30428; decide +kernel
    rw [ha]
    exact (canonical30428 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2217 + difference 3 2) (sourceB2217 + difference 2 3) sourceC2217) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5043) := by
    have ha : (tripleCharges (sourceA2217 + difference 3 2) (sourceB2217 + difference 2 3) sourceC2217) = raw30429 := by
      apply Matrix.ext; unfold tripleCharges sourceA2217 sourceB2217 sourceC2217 difference raw30429; decide +kernel
    rw [ha]
    exact (canonical30429 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2217 + difference 3 4) (sourceB2217 + difference 4 3) sourceC2217) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5073) := by
    have ha : (tripleCharges (sourceA2217 + difference 3 4) (sourceB2217 + difference 4 3) sourceC2217) = raw30430 := by
      apply Matrix.ext; unfold tripleCharges sourceA2217 sourceB2217 sourceC2217 difference raw30430; decide +kernel
    rw [ha]
    exact (canonical30430 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2217 + difference 3 5) (sourceB2217 + difference 5 3) sourceC2217) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5073) := by
    have ha : (tripleCharges (sourceA2217 + difference 3 5) (sourceB2217 + difference 5 3) sourceC2217) = raw30431 := by
      apply Matrix.ext; unfold tripleCharges sourceA2217 sourceB2217 sourceC2217 difference raw30431; decide +kernel
    rw [ha]
    exact (canonical30431 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2217 + difference 4 0) (sourceB2217 + difference 0 4) sourceC2217) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4535) := by
    have ha : (tripleCharges (sourceA2217 + difference 4 0) (sourceB2217 + difference 0 4) sourceC2217) = raw30432 := by
      apply Matrix.ext; unfold tripleCharges sourceA2217 sourceB2217 sourceC2217 difference raw30432; decide +kernel
    rw [ha]
    exact (canonical30432 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2217 + difference 4 1) (sourceB2217 + difference 1 4) sourceC2217) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4935) := by
    have ha : (tripleCharges (sourceA2217 + difference 4 1) (sourceB2217 + difference 1 4) sourceC2217) = raw30433 := by
      apply Matrix.ext; unfold tripleCharges sourceA2217 sourceB2217 sourceC2217 difference raw30433; decide +kernel
    rw [ha]
    exact (canonical30433 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2217 + difference 4 2) (sourceB2217 + difference 2 4) sourceC2217) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4944) := by
    have ha : (tripleCharges (sourceA2217 + difference 4 2) (sourceB2217 + difference 2 4) sourceC2217) = raw30434 := by
      apply Matrix.ext; unfold tripleCharges sourceA2217 sourceB2217 sourceC2217 difference raw30434; decide +kernel
    rw [ha]
    exact (canonical30434 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2217 + difference 4 3) (sourceB2217 + difference 3 4) sourceC2217) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4930) := by
    have ha : (tripleCharges (sourceA2217 + difference 4 3) (sourceB2217 + difference 3 4) sourceC2217) = raw30435 := by
      apply Matrix.ext; unfold tripleCharges sourceA2217 sourceB2217 sourceC2217 difference raw30435; decide +kernel
    rw [ha]
    exact (canonical30435 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2217 + difference 4 5) (sourceB2217 + difference 5 4) sourceC2217) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5078) := by
    have ha : (tripleCharges (sourceA2217 + difference 4 5) (sourceB2217 + difference 5 4) sourceC2217) = raw30436 := by
      apply Matrix.ext; unfold tripleCharges sourceA2217 sourceB2217 sourceC2217 difference raw30436; decide +kernel
    rw [ha]
    exact (canonical30436 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2217 + difference 5 0) (sourceB2217 + difference 0 5) sourceC2217) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4535) := by
    have ha : (tripleCharges (sourceA2217 + difference 5 0) (sourceB2217 + difference 0 5) sourceC2217) = raw30437 := by
      apply Matrix.ext; unfold tripleCharges sourceA2217 sourceB2217 sourceC2217 difference raw30437; decide +kernel
    rw [ha]
    exact (canonical30437 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2217 + difference 5 1) (sourceB2217 + difference 1 5) sourceC2217) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4935) := by
    have ha : (tripleCharges (sourceA2217 + difference 5 1) (sourceB2217 + difference 1 5) sourceC2217) = raw30438 := by
      apply Matrix.ext; unfold tripleCharges sourceA2217 sourceB2217 sourceC2217 difference raw30438; decide +kernel
    rw [ha]
    exact (canonical30438 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2217 + difference 5 2) (sourceB2217 + difference 2 5) sourceC2217) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4944) := by
    have ha : (tripleCharges (sourceA2217 + difference 5 2) (sourceB2217 + difference 2 5) sourceC2217) = raw30439 := by
      apply Matrix.ext; unfold tripleCharges sourceA2217 sourceB2217 sourceC2217 difference raw30439; decide +kernel
    rw [ha]
    exact (canonical30439 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2217 + difference 5 3) (sourceB2217 + difference 3 5) sourceC2217) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4930) := by
    have ha : (tripleCharges (sourceA2217 + difference 5 3) (sourceB2217 + difference 3 5) sourceC2217) = raw30440 := by
      apply Matrix.ext; unfold tripleCharges sourceA2217 sourceB2217 sourceC2217 difference raw30440; decide +kernel
    rw [ha]
    exact (canonical30440 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2217 + difference 5 4) (sourceB2217 + difference 4 5) sourceC2217) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5078) := by
    have ha : (tripleCharges (sourceA2217 + difference 5 4) (sourceB2217 + difference 4 5) sourceC2217) = raw30441 := by
      apply Matrix.ext; unfold tripleCharges sourceA2217 sourceB2217 sourceC2217 difference raw30441; decide +kernel
    rw [ha]
    exact (canonical30441 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2217 sourceB2217 sourceC2217
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2217, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2218 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2218 : Charge := ![1, 0, 1, 0, -1, -1]
def sourceC2218 : Charge := ![2, 1, -1, 0, -1, -1]
def sourceForm2218 : Integer.Sparse Master := [(Sum.inr 3261, 1), (Sum.inr 3272, 2), (Sum.inr 3274, 1), (Sum.inr 3297, 1), (Sum.inr 3408, 2), (Sum.inr 3409, 1), (Sum.inr 3413, 2), (Sum.inr 3419, 2), (Sum.inr 3421, 1), (Sum.inr 3456, 1), (Sum.inr 3465, 1), (Sum.inr 3467, 2), (Sum.inr 3481, 2), (Sum.inr 3483, 2), (Sum.inr 3520, 1), (Sum.inr 3542, 1), (Sum.inr 3544, 2), (Sum.inr 3773, 1), (Sum.inr 3797, 1), (Sum.inr 3815, 1), (Sum.inr 3816, 2)]

theorem sourceEq2218 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2218 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2218 + difference 0 1) (sourceB2218 + difference 1 0) sourceC2218) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3773) := by
    have ha : (tripleCharges (sourceA2218 + difference 0 1) (sourceB2218 + difference 1 0) sourceC2218) = raw30442 := by
      apply Matrix.ext; unfold tripleCharges sourceA2218 sourceB2218 sourceC2218 difference raw30442; decide +kernel
    rw [ha]
    exact (canonical30442 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2218 + difference 0 2) (sourceB2218 + difference 2 0) sourceC2218) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3815) := by
    have ha : (tripleCharges (sourceA2218 + difference 0 2) (sourceB2218 + difference 2 0) sourceC2218) = raw30443 := by
      apply Matrix.ext; unfold tripleCharges sourceA2218 sourceB2218 sourceC2218 difference raw30443; decide +kernel
    rw [ha]
    exact (canonical30443 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2218 + difference 0 3) (sourceB2218 + difference 3 0) sourceC2218) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3797) := by
    have ha : (tripleCharges (sourceA2218 + difference 0 3) (sourceB2218 + difference 3 0) sourceC2218) = raw30444 := by
      apply Matrix.ext; unfold tripleCharges sourceA2218 sourceB2218 sourceC2218 difference raw30444; decide +kernel
    rw [ha]
    exact (canonical30444 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2218 + difference 0 4) (sourceB2218 + difference 4 0) sourceC2218) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3816) := by
    have ha : (tripleCharges (sourceA2218 + difference 0 4) (sourceB2218 + difference 4 0) sourceC2218) = raw30445 := by
      apply Matrix.ext; unfold tripleCharges sourceA2218 sourceB2218 sourceC2218 difference raw30445; decide +kernel
    rw [ha]
    exact (canonical30445 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2218 + difference 0 5) (sourceB2218 + difference 5 0) sourceC2218) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3816) := by
    have ha : (tripleCharges (sourceA2218 + difference 0 5) (sourceB2218 + difference 5 0) sourceC2218) = raw30446 := by
      apply Matrix.ext; unfold tripleCharges sourceA2218 sourceB2218 sourceC2218 difference raw30446; decide +kernel
    rw [ha]
    exact (canonical30446 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2218 + difference 1 0) (sourceB2218 + difference 0 1) sourceC2218) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3297) := by
    have ha : (tripleCharges (sourceA2218 + difference 1 0) (sourceB2218 + difference 0 1) sourceC2218) = raw30447 := by
      apply Matrix.ext; unfold tripleCharges sourceA2218 sourceB2218 sourceC2218 difference raw30447; decide +kernel
    rw [ha]
    exact (canonical30447 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2218 + difference 1 2) (sourceB2218 + difference 2 1) sourceC2218) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3542) := by
    have ha : (tripleCharges (sourceA2218 + difference 1 2) (sourceB2218 + difference 2 1) sourceC2218) = raw30448 := by
      apply Matrix.ext; unfold tripleCharges sourceA2218 sourceB2218 sourceC2218 difference raw30448; decide +kernel
    rw [ha]
    exact (canonical30448 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2218 + difference 1 3) (sourceB2218 + difference 3 1) sourceC2218) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3520) := by
    have ha : (tripleCharges (sourceA2218 + difference 1 3) (sourceB2218 + difference 3 1) sourceC2218) = raw30449 := by
      apply Matrix.ext; unfold tripleCharges sourceA2218 sourceB2218 sourceC2218 difference raw30449; decide +kernel
    rw [ha]
    exact (canonical30449 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2218 + difference 1 4) (sourceB2218 + difference 4 1) sourceC2218) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3544) := by
    have ha : (tripleCharges (sourceA2218 + difference 1 4) (sourceB2218 + difference 4 1) sourceC2218) = raw30450 := by
      apply Matrix.ext; unfold tripleCharges sourceA2218 sourceB2218 sourceC2218 difference raw30450; decide +kernel
    rw [ha]
    exact (canonical30450 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2218 + difference 1 5) (sourceB2218 + difference 5 1) sourceC2218) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3544) := by
    have ha : (tripleCharges (sourceA2218 + difference 1 5) (sourceB2218 + difference 5 1) sourceC2218) = raw30451 := by
      apply Matrix.ext; unfold tripleCharges sourceA2218 sourceB2218 sourceC2218 difference raw30451; decide +kernel
    rw [ha]
    exact (canonical30451 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2218 + difference 2 0) (sourceB2218 + difference 0 2) sourceC2218) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3274) := by
    have ha : (tripleCharges (sourceA2218 + difference 2 0) (sourceB2218 + difference 0 2) sourceC2218) = raw30452 := by
      apply Matrix.ext; unfold tripleCharges sourceA2218 sourceB2218 sourceC2218 difference raw30452; decide +kernel
    rw [ha]
    exact (canonical30452 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2218 + difference 2 1) (sourceB2218 + difference 1 2) sourceC2218) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3421) := by
    have ha : (tripleCharges (sourceA2218 + difference 2 1) (sourceB2218 + difference 1 2) sourceC2218) = raw30453 := by
      apply Matrix.ext; unfold tripleCharges sourceA2218 sourceB2218 sourceC2218 difference raw30453; decide +kernel
    rw [ha]
    exact (canonical30453 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2218 + difference 2 3) (sourceB2218 + difference 3 2) sourceC2218) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3456) := by
    have ha : (tripleCharges (sourceA2218 + difference 2 3) (sourceB2218 + difference 3 2) sourceC2218) = raw30454 := by
      apply Matrix.ext; unfold tripleCharges sourceA2218 sourceB2218 sourceC2218 difference raw30454; decide +kernel
    rw [ha]
    exact (canonical30454 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2218 + difference 2 4) (sourceB2218 + difference 4 2) sourceC2218) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3483) := by
    have ha : (tripleCharges (sourceA2218 + difference 2 4) (sourceB2218 + difference 4 2) sourceC2218) = raw30455 := by
      apply Matrix.ext; unfold tripleCharges sourceA2218 sourceB2218 sourceC2218 difference raw30455; decide +kernel
    rw [ha]
    exact (canonical30455 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2218 + difference 2 5) (sourceB2218 + difference 5 2) sourceC2218) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3483) := by
    have ha : (tripleCharges (sourceA2218 + difference 2 5) (sourceB2218 + difference 5 2) sourceC2218) = raw30456 := by
      apply Matrix.ext; unfold tripleCharges sourceA2218 sourceB2218 sourceC2218 difference raw30456; decide +kernel
    rw [ha]
    exact (canonical30456 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2218 + difference 3 0) (sourceB2218 + difference 0 3) sourceC2218) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3261) := by
    have ha : (tripleCharges (sourceA2218 + difference 3 0) (sourceB2218 + difference 0 3) sourceC2218) = raw30457 := by
      apply Matrix.ext; unfold tripleCharges sourceA2218 sourceB2218 sourceC2218 difference raw30457; decide +kernel
    rw [ha]
    exact (canonical30457 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2218 + difference 3 1) (sourceB2218 + difference 1 3) sourceC2218) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3409) := by
    have ha : (tripleCharges (sourceA2218 + difference 3 1) (sourceB2218 + difference 1 3) sourceC2218) = raw30458 := by
      apply Matrix.ext; unfold tripleCharges sourceA2218 sourceB2218 sourceC2218 difference raw30458; decide +kernel
    rw [ha]
    exact (canonical30458 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2218 + difference 3 2) (sourceB2218 + difference 2 3) sourceC2218) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3465) := by
    have ha : (tripleCharges (sourceA2218 + difference 3 2) (sourceB2218 + difference 2 3) sourceC2218) = raw30459 := by
      apply Matrix.ext; unfold tripleCharges sourceA2218 sourceB2218 sourceC2218 difference raw30459; decide +kernel
    rw [ha]
    exact (canonical30459 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2218 + difference 3 4) (sourceB2218 + difference 4 3) sourceC2218) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3467) := by
    have ha : (tripleCharges (sourceA2218 + difference 3 4) (sourceB2218 + difference 4 3) sourceC2218) = raw30460 := by
      apply Matrix.ext; unfold tripleCharges sourceA2218 sourceB2218 sourceC2218 difference raw30460; decide +kernel
    rw [ha]
    exact (canonical30460 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2218 + difference 3 5) (sourceB2218 + difference 5 3) sourceC2218) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3467) := by
    have ha : (tripleCharges (sourceA2218 + difference 3 5) (sourceB2218 + difference 5 3) sourceC2218) = raw30461 := by
      apply Matrix.ext; unfold tripleCharges sourceA2218 sourceB2218 sourceC2218 difference raw30461; decide +kernel
    rw [ha]
    exact (canonical30461 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2218 + difference 4 0) (sourceB2218 + difference 0 4) sourceC2218) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3272) := by
    have ha : (tripleCharges (sourceA2218 + difference 4 0) (sourceB2218 + difference 0 4) sourceC2218) = raw30462 := by
      apply Matrix.ext; unfold tripleCharges sourceA2218 sourceB2218 sourceC2218 difference raw30462; decide +kernel
    rw [ha]
    exact (canonical30462 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2218 + difference 4 1) (sourceB2218 + difference 1 4) sourceC2218) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3419) := by
    have ha : (tripleCharges (sourceA2218 + difference 4 1) (sourceB2218 + difference 1 4) sourceC2218) = raw30463 := by
      apply Matrix.ext; unfold tripleCharges sourceA2218 sourceB2218 sourceC2218 difference raw30463; decide +kernel
    rw [ha]
    exact (canonical30463 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2218 + difference 4 2) (sourceB2218 + difference 2 4) sourceC2218) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3413) := by
    have ha : (tripleCharges (sourceA2218 + difference 4 2) (sourceB2218 + difference 2 4) sourceC2218) = raw30464 := by
      apply Matrix.ext; unfold tripleCharges sourceA2218 sourceB2218 sourceC2218 difference raw30464; decide +kernel
    rw [ha]
    exact (canonical30464 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2218 + difference 4 3) (sourceB2218 + difference 3 4) sourceC2218) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3408) := by
    have ha : (tripleCharges (sourceA2218 + difference 4 3) (sourceB2218 + difference 3 4) sourceC2218) = raw30465 := by
      apply Matrix.ext; unfold tripleCharges sourceA2218 sourceB2218 sourceC2218 difference raw30465; decide +kernel
    rw [ha]
    exact (canonical30465 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2218 + difference 4 5) (sourceB2218 + difference 5 4) sourceC2218) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3481) := by
    have ha : (tripleCharges (sourceA2218 + difference 4 5) (sourceB2218 + difference 5 4) sourceC2218) = raw30466 := by
      apply Matrix.ext; unfold tripleCharges sourceA2218 sourceB2218 sourceC2218 difference raw30466; decide +kernel
    rw [ha]
    exact (canonical30466 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2218 + difference 5 0) (sourceB2218 + difference 0 5) sourceC2218) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3272) := by
    have ha : (tripleCharges (sourceA2218 + difference 5 0) (sourceB2218 + difference 0 5) sourceC2218) = raw30467 := by
      apply Matrix.ext; unfold tripleCharges sourceA2218 sourceB2218 sourceC2218 difference raw30467; decide +kernel
    rw [ha]
    exact (canonical30467 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2218 + difference 5 1) (sourceB2218 + difference 1 5) sourceC2218) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3419) := by
    have ha : (tripleCharges (sourceA2218 + difference 5 1) (sourceB2218 + difference 1 5) sourceC2218) = raw30468 := by
      apply Matrix.ext; unfold tripleCharges sourceA2218 sourceB2218 sourceC2218 difference raw30468; decide +kernel
    rw [ha]
    exact (canonical30468 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2218 + difference 5 2) (sourceB2218 + difference 2 5) sourceC2218) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3413) := by
    have ha : (tripleCharges (sourceA2218 + difference 5 2) (sourceB2218 + difference 2 5) sourceC2218) = raw30469 := by
      apply Matrix.ext; unfold tripleCharges sourceA2218 sourceB2218 sourceC2218 difference raw30469; decide +kernel
    rw [ha]
    exact (canonical30469 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2218 + difference 5 3) (sourceB2218 + difference 3 5) sourceC2218) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3408) := by
    have ha : (tripleCharges (sourceA2218 + difference 5 3) (sourceB2218 + difference 3 5) sourceC2218) = raw30470 := by
      apply Matrix.ext; unfold tripleCharges sourceA2218 sourceB2218 sourceC2218 difference raw30470; decide +kernel
    rw [ha]
    exact (canonical30470 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2218 + difference 5 4) (sourceB2218 + difference 4 5) sourceC2218) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3481) := by
    have ha : (tripleCharges (sourceA2218 + difference 5 4) (sourceB2218 + difference 4 5) sourceC2218) = raw30471 := by
      apply Matrix.ext; unfold tripleCharges sourceA2218 sourceB2218 sourceC2218 difference raw30471; decide +kernel
    rw [ha]
    exact (canonical30471 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2218 sourceB2218 sourceC2218
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2218, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2219 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2219 : Charge := ![1, 0, 1, 0, -1, -1]
def sourceC2219 : Charge := ![2, 1, -1, 0, -1, -1]
def sourceForm2219 : Integer.Sparse Master := [(Sum.inr 2322, 1), (Sum.inr 2326, 2), (Sum.inr 2342, 1), (Sum.inr 2489, 1), (Sum.inr 3694, 1), (Sum.inr 4091, -1)]

theorem sourceEq2219 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2219 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2219 + difference 0 1) (sourceB2219 + difference 1 0) sourceC2219) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3694) := by
    have ha : (tripleCharges (sourceA2219 + difference 0 1) (sourceB2219 + difference 1 0) sourceC2219) = raw30472 := by
      apply Matrix.ext; unfold tripleCharges sourceA2219 sourceB2219 sourceC2219 difference raw30472; decide +kernel
    rw [ha]
    exact (canonical30472 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2219 + difference 1 1) (sourceB2219 + difference 1 1) sourceC2219) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2489) := by
    have ha : (tripleCharges (sourceA2219 + difference 1 1) (sourceB2219 + difference 1 1) sourceC2219) = raw30473 := by
      apply Matrix.ext; unfold tripleCharges sourceA2219 sourceB2219 sourceC2219 difference raw30473; decide +kernel
    rw [ha]
    exact (canonical30473 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2219 + difference 2 1) (sourceB2219 + difference 1 2) sourceC2219) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2342) := by
    have ha : (tripleCharges (sourceA2219 + difference 2 1) (sourceB2219 + difference 1 2) sourceC2219) = raw30474 := by
      apply Matrix.ext; unfold tripleCharges sourceA2219 sourceB2219 sourceC2219 difference raw30474; decide +kernel
    rw [ha]
    exact (canonical30474 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2219 + difference 3 1) (sourceB2219 + difference 1 3) sourceC2219) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2322) := by
    have ha : (tripleCharges (sourceA2219 + difference 3 1) (sourceB2219 + difference 1 3) sourceC2219) = raw30475 := by
      apply Matrix.ext; unfold tripleCharges sourceA2219 sourceB2219 sourceC2219 difference raw30475; decide +kernel
    rw [ha]
    exact (canonical30475 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2219 + difference 4 1) (sourceB2219 + difference 1 4) sourceC2219) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2326) := by
    have ha : (tripleCharges (sourceA2219 + difference 4 1) (sourceB2219 + difference 1 4) sourceC2219) = raw30476 := by
      apply Matrix.ext; unfold tripleCharges sourceA2219 sourceB2219 sourceC2219 difference raw30476; decide +kernel
    rw [ha]
    exact (canonical30476 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2219 + difference 5 1) (sourceB2219 + difference 1 5) sourceC2219) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2326) := by
    have ha : (tripleCharges (sourceA2219 + difference 5 1) (sourceB2219 + difference 1 5) sourceC2219) = raw30477 := by
      apply Matrix.ext; unfold tripleCharges sourceA2219 sourceB2219 sourceC2219 difference raw30477; decide +kernel
    rw [ha]
    exact (canonical30477 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2219 + sourceB2219) sourceC2219) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA2219 + sourceB2219) sourceC2219) = raw24045 := by
      apply Matrix.ext; unfold doubleCharges sourceA2219 sourceB2219 sourceC2219 raw24045; decide +kernel
    rw [ha]
    exact (canonical24045 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2219 sourceB2219 sourceC2219
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2219, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2220 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2220 : Charge := ![2, 1, -1, 0, -1, -1]
def sourceC2220 : Charge := ![1, 0, 1, 0, -1, -1]
def sourceForm2220 : Integer.Sparse Master := [(Sum.inr 4292, 1), (Sum.inr 4295, 2), (Sum.inr 4314, 1), (Sum.inr 4467, 1), (Sum.inr 4906, 1), (Sum.inr 4907, 2), (Sum.inr 4923, 1), (Sum.inr 4927, 2), (Sum.inr 4943, 2), (Sum.inr 5031, 1), (Sum.inr 5039, 1), (Sum.inr 5073, 2), (Sum.inr 5075, 2), (Sum.inr 5081, 1), (Sum.inr 5102, 2), (Sum.inr 5177, 1), (Sum.inr 5293, 2), (Sum.inr 5356, 1), (Sum.inr 5460, 1), (Sum.inr 5465, 1), (Sum.inr 5483, 2)]

theorem sourceEq2220 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2220 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2220 + difference 0 1) (sourceB2220 + difference 1 0) sourceC2220) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5356) := by
    have ha : (tripleCharges (sourceA2220 + difference 0 1) (sourceB2220 + difference 1 0) sourceC2220) = raw30478 := by
      apply Matrix.ext; unfold tripleCharges sourceA2220 sourceB2220 sourceC2220 difference raw30478; decide +kernel
    rw [ha]
    exact (canonical30478 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2220 + difference 0 2) (sourceB2220 + difference 2 0) sourceC2220) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5465) := by
    have ha : (tripleCharges (sourceA2220 + difference 0 2) (sourceB2220 + difference 2 0) sourceC2220) = raw30479 := by
      apply Matrix.ext; unfold tripleCharges sourceA2220 sourceB2220 sourceC2220 difference raw30479; decide +kernel
    rw [ha]
    exact (canonical30479 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2220 + difference 0 3) (sourceB2220 + difference 3 0) sourceC2220) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5460) := by
    have ha : (tripleCharges (sourceA2220 + difference 0 3) (sourceB2220 + difference 3 0) sourceC2220) = raw30480 := by
      apply Matrix.ext; unfold tripleCharges sourceA2220 sourceB2220 sourceC2220 difference raw30480; decide +kernel
    rw [ha]
    exact (canonical30480 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2220 + difference 0 4) (sourceB2220 + difference 4 0) sourceC2220) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA2220 + difference 0 4) (sourceB2220 + difference 4 0) sourceC2220) = raw30481 := by
      apply Matrix.ext; unfold tripleCharges sourceA2220 sourceB2220 sourceC2220 difference raw30481; decide +kernel
    rw [ha]
    exact (canonical30481 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2220 + difference 0 5) (sourceB2220 + difference 5 0) sourceC2220) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5483) := by
    have ha : (tripleCharges (sourceA2220 + difference 0 5) (sourceB2220 + difference 5 0) sourceC2220) = raw30482 := by
      apply Matrix.ext; unfold tripleCharges sourceA2220 sourceB2220 sourceC2220 difference raw30482; decide +kernel
    rw [ha]
    exact (canonical30482 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2220 + difference 1 0) (sourceB2220 + difference 0 1) sourceC2220) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4467) := by
    have ha : (tripleCharges (sourceA2220 + difference 1 0) (sourceB2220 + difference 0 1) sourceC2220) = raw30483 := by
      apply Matrix.ext; unfold tripleCharges sourceA2220 sourceB2220 sourceC2220 difference raw30483; decide +kernel
    rw [ha]
    exact (canonical30483 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2220 + difference 1 2) (sourceB2220 + difference 2 1) sourceC2220) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5177) := by
    have ha : (tripleCharges (sourceA2220 + difference 1 2) (sourceB2220 + difference 2 1) sourceC2220) = raw30484 := by
      apply Matrix.ext; unfold tripleCharges sourceA2220 sourceB2220 sourceC2220 difference raw30484; decide +kernel
    rw [ha]
    exact (canonical30484 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2220 + difference 1 3) (sourceB2220 + difference 3 1) sourceC2220) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5081) := by
    have ha : (tripleCharges (sourceA2220 + difference 1 3) (sourceB2220 + difference 3 1) sourceC2220) = raw30485 := by
      apply Matrix.ext; unfold tripleCharges sourceA2220 sourceB2220 sourceC2220 difference raw30485; decide +kernel
    rw [ha]
    exact (canonical30485 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2220 + difference 1 4) (sourceB2220 + difference 4 1) sourceC2220) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA2220 + difference 1 4) (sourceB2220 + difference 4 1) sourceC2220) = raw30486 := by
      apply Matrix.ext; unfold tripleCharges sourceA2220 sourceB2220 sourceC2220 difference raw30486; decide +kernel
    rw [ha]
    exact (canonical30486 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2220 + difference 1 5) (sourceB2220 + difference 5 1) sourceC2220) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA2220 + difference 1 5) (sourceB2220 + difference 5 1) sourceC2220) = raw30487 := by
      apply Matrix.ext; unfold tripleCharges sourceA2220 sourceB2220 sourceC2220 difference raw30487; decide +kernel
    rw [ha]
    exact (canonical30487 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2220 + difference 2 0) (sourceB2220 + difference 0 2) sourceC2220) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4314) := by
    have ha : (tripleCharges (sourceA2220 + difference 2 0) (sourceB2220 + difference 0 2) sourceC2220) = raw30488 := by
      apply Matrix.ext; unfold tripleCharges sourceA2220 sourceB2220 sourceC2220 difference raw30488; decide +kernel
    rw [ha]
    exact (canonical30488 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2220 + difference 2 1) (sourceB2220 + difference 1 2) sourceC2220) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4923) := by
    have ha : (tripleCharges (sourceA2220 + difference 2 1) (sourceB2220 + difference 1 2) sourceC2220) = raw30489 := by
      apply Matrix.ext; unfold tripleCharges sourceA2220 sourceB2220 sourceC2220 difference raw30489; decide +kernel
    rw [ha]
    exact (canonical30489 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2220 + difference 2 3) (sourceB2220 + difference 3 2) sourceC2220) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5031) := by
    have ha : (tripleCharges (sourceA2220 + difference 2 3) (sourceB2220 + difference 3 2) sourceC2220) = raw30490 := by
      apply Matrix.ext; unfold tripleCharges sourceA2220 sourceB2220 sourceC2220 difference raw30490; decide +kernel
    rw [ha]
    exact (canonical30490 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2220 + difference 2 4) (sourceB2220 + difference 4 2) sourceC2220) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5102) := by
    have ha : (tripleCharges (sourceA2220 + difference 2 4) (sourceB2220 + difference 4 2) sourceC2220) = raw30491 := by
      apply Matrix.ext; unfold tripleCharges sourceA2220 sourceB2220 sourceC2220 difference raw30491; decide +kernel
    rw [ha]
    exact (canonical30491 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2220 + difference 2 5) (sourceB2220 + difference 5 2) sourceC2220) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5102) := by
    have ha : (tripleCharges (sourceA2220 + difference 2 5) (sourceB2220 + difference 5 2) sourceC2220) = raw30492 := by
      apply Matrix.ext; unfold tripleCharges sourceA2220 sourceB2220 sourceC2220 difference raw30492; decide +kernel
    rw [ha]
    exact (canonical30492 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2220 + difference 3 0) (sourceB2220 + difference 0 3) sourceC2220) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4292) := by
    have ha : (tripleCharges (sourceA2220 + difference 3 0) (sourceB2220 + difference 0 3) sourceC2220) = raw30493 := by
      apply Matrix.ext; unfold tripleCharges sourceA2220 sourceB2220 sourceC2220 difference raw30493; decide +kernel
    rw [ha]
    exact (canonical30493 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2220 + difference 3 1) (sourceB2220 + difference 1 3) sourceC2220) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4906) := by
    have ha : (tripleCharges (sourceA2220 + difference 3 1) (sourceB2220 + difference 1 3) sourceC2220) = raw30494 := by
      apply Matrix.ext; unfold tripleCharges sourceA2220 sourceB2220 sourceC2220 difference raw30494; decide +kernel
    rw [ha]
    exact (canonical30494 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2220 + difference 3 2) (sourceB2220 + difference 2 3) sourceC2220) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5039) := by
    have ha : (tripleCharges (sourceA2220 + difference 3 2) (sourceB2220 + difference 2 3) sourceC2220) = raw30495 := by
      apply Matrix.ext; unfold tripleCharges sourceA2220 sourceB2220 sourceC2220 difference raw30495; decide +kernel
    rw [ha]
    exact (canonical30495 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2220 + difference 3 4) (sourceB2220 + difference 4 3) sourceC2220) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5073) := by
    have ha : (tripleCharges (sourceA2220 + difference 3 4) (sourceB2220 + difference 4 3) sourceC2220) = raw30496 := by
      apply Matrix.ext; unfold tripleCharges sourceA2220 sourceB2220 sourceC2220 difference raw30496; decide +kernel
    rw [ha]
    exact (canonical30496 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2220 + difference 3 5) (sourceB2220 + difference 5 3) sourceC2220) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5073) := by
    have ha : (tripleCharges (sourceA2220 + difference 3 5) (sourceB2220 + difference 5 3) sourceC2220) = raw30497 := by
      apply Matrix.ext; unfold tripleCharges sourceA2220 sourceB2220 sourceC2220 difference raw30497; decide +kernel
    rw [ha]
    exact (canonical30497 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2220 + difference 4 0) (sourceB2220 + difference 0 4) sourceC2220) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4295) := by
    have ha : (tripleCharges (sourceA2220 + difference 4 0) (sourceB2220 + difference 0 4) sourceC2220) = raw30498 := by
      apply Matrix.ext; unfold tripleCharges sourceA2220 sourceB2220 sourceC2220 difference raw30498; decide +kernel
    rw [ha]
    exact (canonical30498 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2220 + difference 4 1) (sourceB2220 + difference 1 4) sourceC2220) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4907) := by
    have ha : (tripleCharges (sourceA2220 + difference 4 1) (sourceB2220 + difference 1 4) sourceC2220) = raw30499 := by
      apply Matrix.ext; unfold tripleCharges sourceA2220 sourceB2220 sourceC2220 difference raw30499; decide +kernel
    rw [ha]
    exact (canonical30499 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2220 + difference 4 2) (sourceB2220 + difference 2 4) sourceC2220) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4943) := by
    have ha : (tripleCharges (sourceA2220 + difference 4 2) (sourceB2220 + difference 2 4) sourceC2220) = raw30500 := by
      apply Matrix.ext; unfold tripleCharges sourceA2220 sourceB2220 sourceC2220 difference raw30500; decide +kernel
    rw [ha]
    exact (canonical30500 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2220 + difference 4 3) (sourceB2220 + difference 3 4) sourceC2220) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4927) := by
    have ha : (tripleCharges (sourceA2220 + difference 4 3) (sourceB2220 + difference 3 4) sourceC2220) = raw30501 := by
      apply Matrix.ext; unfold tripleCharges sourceA2220 sourceB2220 sourceC2220 difference raw30501; decide +kernel
    rw [ha]
    exact (canonical30501 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2220 + difference 4 5) (sourceB2220 + difference 5 4) sourceC2220) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA2220 + difference 4 5) (sourceB2220 + difference 5 4) sourceC2220) = raw30502 := by
      apply Matrix.ext; unfold tripleCharges sourceA2220 sourceB2220 sourceC2220 difference raw30502; decide +kernel
    rw [ha]
    exact (canonical30502 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2220 + difference 5 0) (sourceB2220 + difference 0 5) sourceC2220) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4295) := by
    have ha : (tripleCharges (sourceA2220 + difference 5 0) (sourceB2220 + difference 0 5) sourceC2220) = raw30503 := by
      apply Matrix.ext; unfold tripleCharges sourceA2220 sourceB2220 sourceC2220 difference raw30503; decide +kernel
    rw [ha]
    exact (canonical30503 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2220 + difference 5 1) (sourceB2220 + difference 1 5) sourceC2220) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4907) := by
    have ha : (tripleCharges (sourceA2220 + difference 5 1) (sourceB2220 + difference 1 5) sourceC2220) = raw30504 := by
      apply Matrix.ext; unfold tripleCharges sourceA2220 sourceB2220 sourceC2220 difference raw30504; decide +kernel
    rw [ha]
    exact (canonical30504 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2220 + difference 5 2) (sourceB2220 + difference 2 5) sourceC2220) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4943) := by
    have ha : (tripleCharges (sourceA2220 + difference 5 2) (sourceB2220 + difference 2 5) sourceC2220) = raw30505 := by
      apply Matrix.ext; unfold tripleCharges sourceA2220 sourceB2220 sourceC2220 difference raw30505; decide +kernel
    rw [ha]
    exact (canonical30505 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2220 + difference 5 3) (sourceB2220 + difference 3 5) sourceC2220) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4927) := by
    have ha : (tripleCharges (sourceA2220 + difference 5 3) (sourceB2220 + difference 3 5) sourceC2220) = raw30506 := by
      apply Matrix.ext; unfold tripleCharges sourceA2220 sourceB2220 sourceC2220 difference raw30506; decide +kernel
    rw [ha]
    exact (canonical30506 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2220 + difference 5 4) (sourceB2220 + difference 4 5) sourceC2220) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA2220 + difference 5 4) (sourceB2220 + difference 4 5) sourceC2220) = raw30507 := by
      apply Matrix.ext; unfold tripleCharges sourceA2220 sourceB2220 sourceC2220 difference raw30507; decide +kernel
    rw [ha]
    exact (canonical30507 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2220 sourceB2220 sourceC2220
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2220, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2221 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2221 : Charge := ![2, 1, -1, 0, -1, -1]
def sourceC2221 : Charge := ![1, 0, 1, 0, -1, -1]
def sourceForm2221 : Integer.Sparse Master := [(Sum.inr 870, 1), (Sum.inr 873, 2), (Sum.inr 892, 1), (Sum.inr 1050, 1), (Sum.inr 2299, 1), (Sum.inr 2300, 2), (Sum.inr 2314, 1), (Sum.inr 2317, 2), (Sum.inr 2334, 2), (Sum.inr 2420, 1), (Sum.inr 2432, 1), (Sum.inr 2480, 2), (Sum.inr 2482, 2), (Sum.inr 2489, 1), (Sum.inr 2512, 2), (Sum.inr 2605, 1), (Sum.inr 2767, 2), (Sum.inr 3694, 1), (Sum.inr 3921, 1), (Sum.inr 3931, 1), (Sum.inr 3981, 2)]

theorem sourceEq2221 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2221 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2221 + difference 0 1) (sourceB2221 + difference 1 0) sourceC2221) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3694) := by
    have ha : (tripleCharges (sourceA2221 + difference 0 1) (sourceB2221 + difference 1 0) sourceC2221) = raw30508 := by
      apply Matrix.ext; unfold tripleCharges sourceA2221 sourceB2221 sourceC2221 difference raw30508; decide +kernel
    rw [ha]
    exact (canonical30508 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2221 + difference 0 2) (sourceB2221 + difference 2 0) sourceC2221) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3931) := by
    have ha : (tripleCharges (sourceA2221 + difference 0 2) (sourceB2221 + difference 2 0) sourceC2221) = raw30509 := by
      apply Matrix.ext; unfold tripleCharges sourceA2221 sourceB2221 sourceC2221 difference raw30509; decide +kernel
    rw [ha]
    exact (canonical30509 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2221 + difference 0 3) (sourceB2221 + difference 3 0) sourceC2221) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3921) := by
    have ha : (tripleCharges (sourceA2221 + difference 0 3) (sourceB2221 + difference 3 0) sourceC2221) = raw30510 := by
      apply Matrix.ext; unfold tripleCharges sourceA2221 sourceB2221 sourceC2221 difference raw30510; decide +kernel
    rw [ha]
    exact (canonical30510 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2221 + difference 0 4) (sourceB2221 + difference 4 0) sourceC2221) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3981) := by
    have ha : (tripleCharges (sourceA2221 + difference 0 4) (sourceB2221 + difference 4 0) sourceC2221) = raw30511 := by
      apply Matrix.ext; unfold tripleCharges sourceA2221 sourceB2221 sourceC2221 difference raw30511; decide +kernel
    rw [ha]
    exact (canonical30511 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2221 + difference 0 5) (sourceB2221 + difference 5 0) sourceC2221) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3981) := by
    have ha : (tripleCharges (sourceA2221 + difference 0 5) (sourceB2221 + difference 5 0) sourceC2221) = raw30512 := by
      apply Matrix.ext; unfold tripleCharges sourceA2221 sourceB2221 sourceC2221 difference raw30512; decide +kernel
    rw [ha]
    exact (canonical30512 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2221 + difference 1 0) (sourceB2221 + difference 0 1) sourceC2221) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1050) := by
    have ha : (tripleCharges (sourceA2221 + difference 1 0) (sourceB2221 + difference 0 1) sourceC2221) = raw30513 := by
      apply Matrix.ext; unfold tripleCharges sourceA2221 sourceB2221 sourceC2221 difference raw30513; decide +kernel
    rw [ha]
    exact (canonical30513 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2221 + difference 1 2) (sourceB2221 + difference 2 1) sourceC2221) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2605) := by
    have ha : (tripleCharges (sourceA2221 + difference 1 2) (sourceB2221 + difference 2 1) sourceC2221) = raw30514 := by
      apply Matrix.ext; unfold tripleCharges sourceA2221 sourceB2221 sourceC2221 difference raw30514; decide +kernel
    rw [ha]
    exact (canonical30514 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2221 + difference 1 3) (sourceB2221 + difference 3 1) sourceC2221) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2489) := by
    have ha : (tripleCharges (sourceA2221 + difference 1 3) (sourceB2221 + difference 3 1) sourceC2221) = raw30515 := by
      apply Matrix.ext; unfold tripleCharges sourceA2221 sourceB2221 sourceC2221 difference raw30515; decide +kernel
    rw [ha]
    exact (canonical30515 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2221 + difference 1 4) (sourceB2221 + difference 4 1) sourceC2221) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2767) := by
    have ha : (tripleCharges (sourceA2221 + difference 1 4) (sourceB2221 + difference 4 1) sourceC2221) = raw30516 := by
      apply Matrix.ext; unfold tripleCharges sourceA2221 sourceB2221 sourceC2221 difference raw30516; decide +kernel
    rw [ha]
    exact (canonical30516 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2221 + difference 1 5) (sourceB2221 + difference 5 1) sourceC2221) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2767) := by
    have ha : (tripleCharges (sourceA2221 + difference 1 5) (sourceB2221 + difference 5 1) sourceC2221) = raw30517 := by
      apply Matrix.ext; unfold tripleCharges sourceA2221 sourceB2221 sourceC2221 difference raw30517; decide +kernel
    rw [ha]
    exact (canonical30517 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2221 + difference 2 0) (sourceB2221 + difference 0 2) sourceC2221) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 892) := by
    have ha : (tripleCharges (sourceA2221 + difference 2 0) (sourceB2221 + difference 0 2) sourceC2221) = raw30518 := by
      apply Matrix.ext; unfold tripleCharges sourceA2221 sourceB2221 sourceC2221 difference raw30518; decide +kernel
    rw [ha]
    exact (canonical30518 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2221 + difference 2 1) (sourceB2221 + difference 1 2) sourceC2221) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2314) := by
    have ha : (tripleCharges (sourceA2221 + difference 2 1) (sourceB2221 + difference 1 2) sourceC2221) = raw30519 := by
      apply Matrix.ext; unfold tripleCharges sourceA2221 sourceB2221 sourceC2221 difference raw30519; decide +kernel
    rw [ha]
    exact (canonical30519 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2221 + difference 2 3) (sourceB2221 + difference 3 2) sourceC2221) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2420) := by
    have ha : (tripleCharges (sourceA2221 + difference 2 3) (sourceB2221 + difference 3 2) sourceC2221) = raw30520 := by
      apply Matrix.ext; unfold tripleCharges sourceA2221 sourceB2221 sourceC2221 difference raw30520; decide +kernel
    rw [ha]
    exact (canonical30520 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2221 + difference 2 4) (sourceB2221 + difference 4 2) sourceC2221) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2512) := by
    have ha : (tripleCharges (sourceA2221 + difference 2 4) (sourceB2221 + difference 4 2) sourceC2221) = raw30521 := by
      apply Matrix.ext; unfold tripleCharges sourceA2221 sourceB2221 sourceC2221 difference raw30521; decide +kernel
    rw [ha]
    exact (canonical30521 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2221 + difference 2 5) (sourceB2221 + difference 5 2) sourceC2221) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2512) := by
    have ha : (tripleCharges (sourceA2221 + difference 2 5) (sourceB2221 + difference 5 2) sourceC2221) = raw30522 := by
      apply Matrix.ext; unfold tripleCharges sourceA2221 sourceB2221 sourceC2221 difference raw30522; decide +kernel
    rw [ha]
    exact (canonical30522 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2221 + difference 3 0) (sourceB2221 + difference 0 3) sourceC2221) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 870) := by
    have ha : (tripleCharges (sourceA2221 + difference 3 0) (sourceB2221 + difference 0 3) sourceC2221) = raw30523 := by
      apply Matrix.ext; unfold tripleCharges sourceA2221 sourceB2221 sourceC2221 difference raw30523; decide +kernel
    rw [ha]
    exact (canonical30523 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2221 + difference 3 1) (sourceB2221 + difference 1 3) sourceC2221) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2299) := by
    have ha : (tripleCharges (sourceA2221 + difference 3 1) (sourceB2221 + difference 1 3) sourceC2221) = raw30524 := by
      apply Matrix.ext; unfold tripleCharges sourceA2221 sourceB2221 sourceC2221 difference raw30524; decide +kernel
    rw [ha]
    exact (canonical30524 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2221 + difference 3 2) (sourceB2221 + difference 2 3) sourceC2221) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2432) := by
    have ha : (tripleCharges (sourceA2221 + difference 3 2) (sourceB2221 + difference 2 3) sourceC2221) = raw30525 := by
      apply Matrix.ext; unfold tripleCharges sourceA2221 sourceB2221 sourceC2221 difference raw30525; decide +kernel
    rw [ha]
    exact (canonical30525 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2221 + difference 3 4) (sourceB2221 + difference 4 3) sourceC2221) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2480) := by
    have ha : (tripleCharges (sourceA2221 + difference 3 4) (sourceB2221 + difference 4 3) sourceC2221) = raw30526 := by
      apply Matrix.ext; unfold tripleCharges sourceA2221 sourceB2221 sourceC2221 difference raw30526; decide +kernel
    rw [ha]
    exact (canonical30526 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2221 + difference 3 5) (sourceB2221 + difference 5 3) sourceC2221) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2480) := by
    have ha : (tripleCharges (sourceA2221 + difference 3 5) (sourceB2221 + difference 5 3) sourceC2221) = raw30527 := by
      apply Matrix.ext; unfold tripleCharges sourceA2221 sourceB2221 sourceC2221 difference raw30527; decide +kernel
    rw [ha]
    exact (canonical30527 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2221 + difference 4 0) (sourceB2221 + difference 0 4) sourceC2221) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 873) := by
    have ha : (tripleCharges (sourceA2221 + difference 4 0) (sourceB2221 + difference 0 4) sourceC2221) = raw30528 := by
      apply Matrix.ext; unfold tripleCharges sourceA2221 sourceB2221 sourceC2221 difference raw30528; decide +kernel
    rw [ha]
    exact (canonical30528 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2221 + difference 4 1) (sourceB2221 + difference 1 4) sourceC2221) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2300) := by
    have ha : (tripleCharges (sourceA2221 + difference 4 1) (sourceB2221 + difference 1 4) sourceC2221) = raw30529 := by
      apply Matrix.ext; unfold tripleCharges sourceA2221 sourceB2221 sourceC2221 difference raw30529; decide +kernel
    rw [ha]
    exact (canonical30529 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2221 + difference 4 2) (sourceB2221 + difference 2 4) sourceC2221) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2334) := by
    have ha : (tripleCharges (sourceA2221 + difference 4 2) (sourceB2221 + difference 2 4) sourceC2221) = raw30530 := by
      apply Matrix.ext; unfold tripleCharges sourceA2221 sourceB2221 sourceC2221 difference raw30530; decide +kernel
    rw [ha]
    exact (canonical30530 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2221 + difference 4 3) (sourceB2221 + difference 3 4) sourceC2221) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2317) := by
    have ha : (tripleCharges (sourceA2221 + difference 4 3) (sourceB2221 + difference 3 4) sourceC2221) = raw30531 := by
      apply Matrix.ext; unfold tripleCharges sourceA2221 sourceB2221 sourceC2221 difference raw30531; decide +kernel
    rw [ha]
    exact (canonical30531 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2221 + difference 4 5) (sourceB2221 + difference 5 4) sourceC2221) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2482) := by
    have ha : (tripleCharges (sourceA2221 + difference 4 5) (sourceB2221 + difference 5 4) sourceC2221) = raw30532 := by
      apply Matrix.ext; unfold tripleCharges sourceA2221 sourceB2221 sourceC2221 difference raw30532; decide +kernel
    rw [ha]
    exact (canonical30532 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2221 + difference 5 0) (sourceB2221 + difference 0 5) sourceC2221) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 873) := by
    have ha : (tripleCharges (sourceA2221 + difference 5 0) (sourceB2221 + difference 0 5) sourceC2221) = raw30533 := by
      apply Matrix.ext; unfold tripleCharges sourceA2221 sourceB2221 sourceC2221 difference raw30533; decide +kernel
    rw [ha]
    exact (canonical30533 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2221 + difference 5 1) (sourceB2221 + difference 1 5) sourceC2221) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2300) := by
    have ha : (tripleCharges (sourceA2221 + difference 5 1) (sourceB2221 + difference 1 5) sourceC2221) = raw30534 := by
      apply Matrix.ext; unfold tripleCharges sourceA2221 sourceB2221 sourceC2221 difference raw30534; decide +kernel
    rw [ha]
    exact (canonical30534 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2221 + difference 5 2) (sourceB2221 + difference 2 5) sourceC2221) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2334) := by
    have ha : (tripleCharges (sourceA2221 + difference 5 2) (sourceB2221 + difference 2 5) sourceC2221) = raw30535 := by
      apply Matrix.ext; unfold tripleCharges sourceA2221 sourceB2221 sourceC2221 difference raw30535; decide +kernel
    rw [ha]
    exact (canonical30535 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2221 + difference 5 3) (sourceB2221 + difference 3 5) sourceC2221) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2317) := by
    have ha : (tripleCharges (sourceA2221 + difference 5 3) (sourceB2221 + difference 3 5) sourceC2221) = raw30536 := by
      apply Matrix.ext; unfold tripleCharges sourceA2221 sourceB2221 sourceC2221 difference raw30536; decide +kernel
    rw [ha]
    exact (canonical30536 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2221 + difference 5 4) (sourceB2221 + difference 4 5) sourceC2221) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2482) := by
    have ha : (tripleCharges (sourceA2221 + difference 5 4) (sourceB2221 + difference 4 5) sourceC2221) = raw30537 := by
      apply Matrix.ext; unfold tripleCharges sourceA2221 sourceB2221 sourceC2221 difference raw30537; decide +kernel
    rw [ha]
    exact (canonical30537 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2221 sourceB2221 sourceC2221
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2221, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2222 : Charge := ![1, 0, 1, 0, -1, -1]
def sourceB2222 : Charge := ![2, 1, -1, 0, -1, -1]
def sourceC2222 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceForm2222 : Integer.Sparse Master := [(Sum.inr 4732, 1), (Sum.inr 4745, 2), (Sum.inr 4750, 1), (Sum.inr 4811, 1), (Sum.inr 4994, 1), (Sum.inr 5003, 2), (Sum.inr 5010, 1), (Sum.inr 5050, 2), (Sum.inr 5054, 1), (Sum.inr 5067, 2), (Sum.inr 5080, 2), (Sum.inr 5081, 1), (Sum.inr 5090, 2), (Sum.inr 5111, 2), (Sum.inr 5130, 2), (Sum.inr 5141, 2), (Sum.inr 5152, 2), (Sum.inr 5177, 2), (Sum.inr 5189, 1)]

theorem sourceEq2222 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2222 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2222 + difference 0 1) (sourceB2222 + difference 1 0) sourceC2222) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5189) := by
    have ha : (tripleCharges (sourceA2222 + difference 0 1) (sourceB2222 + difference 1 0) sourceC2222) = raw30538 := by
      apply Matrix.ext; unfold tripleCharges sourceA2222 sourceB2222 sourceC2222 difference raw30538; decide +kernel
    rw [ha]
    exact (canonical30538 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2222 + difference 0 2) (sourceB2222 + difference 2 0) sourceC2222) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5177) := by
    have ha : (tripleCharges (sourceA2222 + difference 0 2) (sourceB2222 + difference 2 0) sourceC2222) = raw29674 := by
      apply Matrix.ext; unfold tripleCharges sourceA2222 sourceB2222 sourceC2222 difference raw29674; decide +kernel
    rw [ha]
    exact (canonical29674 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2222 + difference 0 3) (sourceB2222 + difference 3 0) sourceC2222) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5130) := by
    have ha : (tripleCharges (sourceA2222 + difference 0 3) (sourceB2222 + difference 3 0) sourceC2222) = raw30539 := by
      apply Matrix.ext; unfold tripleCharges sourceA2222 sourceB2222 sourceC2222 difference raw30539; decide +kernel
    rw [ha]
    exact (canonical30539 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2222 + difference 0 4) (sourceB2222 + difference 4 0) sourceC2222) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA2222 + difference 0 4) (sourceB2222 + difference 4 0) sourceC2222) = raw30540 := by
      apply Matrix.ext; unfold tripleCharges sourceA2222 sourceB2222 sourceC2222 difference raw30540; decide +kernel
    rw [ha]
    exact (canonical30540 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2222 + difference 0 5) (sourceB2222 + difference 5 0) sourceC2222) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA2222 + difference 0 5) (sourceB2222 + difference 5 0) sourceC2222) = raw30361 := by
      apply Matrix.ext; unfold tripleCharges sourceA2222 sourceB2222 sourceC2222 difference raw30361; decide +kernel
    rw [ha]
    exact (canonical30361 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2222 + difference 1 0) (sourceB2222 + difference 0 1) sourceC2222) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4811) := by
    have ha : (tripleCharges (sourceA2222 + difference 1 0) (sourceB2222 + difference 0 1) sourceC2222) = raw29682 := by
      apply Matrix.ext; unfold tripleCharges sourceA2222 sourceB2222 sourceC2222 difference raw29682; decide +kernel
    rw [ha]
    exact (canonical29682 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2222 + difference 1 2) (sourceB2222 + difference 2 1) sourceC2222) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5177) := by
    have ha : (tripleCharges (sourceA2222 + difference 1 2) (sourceB2222 + difference 2 1) sourceC2222) = raw29586 := by
      apply Matrix.ext; unfold tripleCharges sourceA2222 sourceB2222 sourceC2222 difference raw29586; decide +kernel
    rw [ha]
    exact (canonical29586 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2222 + difference 1 3) (sourceB2222 + difference 3 1) sourceC2222) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5130) := by
    have ha : (tripleCharges (sourceA2222 + difference 1 3) (sourceB2222 + difference 3 1) sourceC2222) = raw29684 := by
      apply Matrix.ext; unfold tripleCharges sourceA2222 sourceB2222 sourceC2222 difference raw29684; decide +kernel
    rw [ha]
    exact (canonical29684 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2222 + difference 1 4) (sourceB2222 + difference 4 1) sourceC2222) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5152) := by
    have ha : (tripleCharges (sourceA2222 + difference 1 4) (sourceB2222 + difference 4 1) sourceC2222) = raw29576 := by
      apply Matrix.ext; unfold tripleCharges sourceA2222 sourceB2222 sourceC2222 difference raw29576; decide +kernel
    rw [ha]
    exact (canonical29576 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2222 + difference 1 5) (sourceB2222 + difference 5 1) sourceC2222) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5152) := by
    have ha : (tripleCharges (sourceA2222 + difference 1 5) (sourceB2222 + difference 5 1) sourceC2222) = raw29685 := by
      apply Matrix.ext; unfold tripleCharges sourceA2222 sourceB2222 sourceC2222 difference raw29685; decide +kernel
    rw [ha]
    exact (canonical29685 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2222 + difference 2 0) (sourceB2222 + difference 0 2) sourceC2222) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4750) := by
    have ha : (tripleCharges (sourceA2222 + difference 2 0) (sourceB2222 + difference 0 2) sourceC2222) = raw30541 := by
      apply Matrix.ext; unfold tripleCharges sourceA2222 sourceB2222 sourceC2222 difference raw30541; decide +kernel
    rw [ha]
    exact (canonical30541 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2222 + difference 2 1) (sourceB2222 + difference 1 2) sourceC2222) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5010) := by
    have ha : (tripleCharges (sourceA2222 + difference 2 1) (sourceB2222 + difference 1 2) sourceC2222) = raw30542 := by
      apply Matrix.ext; unfold tripleCharges sourceA2222 sourceB2222 sourceC2222 difference raw30542; decide +kernel
    rw [ha]
    exact (canonical30542 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2222 + difference 2 3) (sourceB2222 + difference 3 2) sourceC2222) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5054) := by
    have ha : (tripleCharges (sourceA2222 + difference 2 3) (sourceB2222 + difference 3 2) sourceC2222) = raw30543 := by
      apply Matrix.ext; unfold tripleCharges sourceA2222 sourceB2222 sourceC2222 difference raw30543; decide +kernel
    rw [ha]
    exact (canonical30543 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2222 + difference 2 4) (sourceB2222 + difference 4 2) sourceC2222) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5090) := by
    have ha : (tripleCharges (sourceA2222 + difference 2 4) (sourceB2222 + difference 4 2) sourceC2222) = raw30544 := by
      apply Matrix.ext; unfold tripleCharges sourceA2222 sourceB2222 sourceC2222 difference raw30544; decide +kernel
    rw [ha]
    exact (canonical30544 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2222 + difference 2 5) (sourceB2222 + difference 5 2) sourceC2222) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5090) := by
    have ha : (tripleCharges (sourceA2222 + difference 2 5) (sourceB2222 + difference 5 2) sourceC2222) = raw30368 := by
      apply Matrix.ext; unfold tripleCharges sourceA2222 sourceB2222 sourceC2222 difference raw30368; decide +kernel
    rw [ha]
    exact (canonical30368 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2222 + difference 3 0) (sourceB2222 + difference 0 3) sourceC2222) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4732) := by
    have ha : (tripleCharges (sourceA2222 + difference 3 0) (sourceB2222 + difference 0 3) sourceC2222) = raw30545 := by
      apply Matrix.ext; unfold tripleCharges sourceA2222 sourceB2222 sourceC2222 difference raw30545; decide +kernel
    rw [ha]
    exact (canonical30545 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2222 + difference 3 1) (sourceB2222 + difference 1 3) sourceC2222) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4994) := by
    have ha : (tripleCharges (sourceA2222 + difference 3 1) (sourceB2222 + difference 1 3) sourceC2222) = raw30546 := by
      apply Matrix.ext; unfold tripleCharges sourceA2222 sourceB2222 sourceC2222 difference raw30546; decide +kernel
    rw [ha]
    exact (canonical30546 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2222 + difference 3 2) (sourceB2222 + difference 2 3) sourceC2222) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5081) := by
    have ha : (tripleCharges (sourceA2222 + difference 3 2) (sourceB2222 + difference 2 3) sourceC2222) = raw29687 := by
      apply Matrix.ext; unfold tripleCharges sourceA2222 sourceB2222 sourceC2222 difference raw29687; decide +kernel
    rw [ha]
    exact (canonical29687 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2222 + difference 3 4) (sourceB2222 + difference 4 3) sourceC2222) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5067) := by
    have ha : (tripleCharges (sourceA2222 + difference 3 4) (sourceB2222 + difference 4 3) sourceC2222) = raw29830 := by
      apply Matrix.ext; unfold tripleCharges sourceA2222 sourceB2222 sourceC2222 difference raw29830; decide +kernel
    rw [ha]
    exact (canonical29830 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2222 + difference 3 5) (sourceB2222 + difference 5 3) sourceC2222) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5067) := by
    have ha : (tripleCharges (sourceA2222 + difference 3 5) (sourceB2222 + difference 5 3) sourceC2222) = raw30373 := by
      apply Matrix.ext; unfold tripleCharges sourceA2222 sourceB2222 sourceC2222 difference raw30373; decide +kernel
    rw [ha]
    exact (canonical30373 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2222 + difference 4 0) (sourceB2222 + difference 0 4) sourceC2222) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4745) := by
    have ha : (tripleCharges (sourceA2222 + difference 4 0) (sourceB2222 + difference 0 4) sourceC2222) = raw30380 := by
      apply Matrix.ext; unfold tripleCharges sourceA2222 sourceB2222 sourceC2222 difference raw30380; decide +kernel
    rw [ha]
    exact (canonical30380 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2222 + difference 4 1) (sourceB2222 + difference 1 4) sourceC2222) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5003) := by
    have ha : (tripleCharges (sourceA2222 + difference 4 1) (sourceB2222 + difference 1 4) sourceC2222) = raw30381 := by
      apply Matrix.ext; unfold tripleCharges sourceA2222 sourceB2222 sourceC2222 difference raw30381; decide +kernel
    rw [ha]
    exact (canonical30381 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2222 + difference 4 2) (sourceB2222 + difference 2 4) sourceC2222) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5111) := by
    have ha : (tripleCharges (sourceA2222 + difference 4 2) (sourceB2222 + difference 2 4) sourceC2222) = raw29691 := by
      apply Matrix.ext; unfold tripleCharges sourceA2222 sourceB2222 sourceC2222 difference raw29691; decide +kernel
    rw [ha]
    exact (canonical29691 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2222 + difference 4 3) (sourceB2222 + difference 3 4) sourceC2222) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5050) := by
    have ha : (tripleCharges (sourceA2222 + difference 4 3) (sourceB2222 + difference 3 4) sourceC2222) = raw30174 := by
      apply Matrix.ext; unfold tripleCharges sourceA2222 sourceB2222 sourceC2222 difference raw30174; decide +kernel
    rw [ha]
    exact (canonical30174 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2222 + difference 4 5) (sourceB2222 + difference 5 4) sourceC2222) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5080) := by
    have ha : (tripleCharges (sourceA2222 + difference 4 5) (sourceB2222 + difference 5 4) sourceC2222) = raw30547 := by
      apply Matrix.ext; unfold tripleCharges sourceA2222 sourceB2222 sourceC2222 difference raw30547; decide +kernel
    rw [ha]
    exact (canonical30547 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2222 + difference 5 0) (sourceB2222 + difference 0 5) sourceC2222) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4745) := by
    have ha : (tripleCharges (sourceA2222 + difference 5 0) (sourceB2222 + difference 0 5) sourceC2222) = raw30548 := by
      apply Matrix.ext; unfold tripleCharges sourceA2222 sourceB2222 sourceC2222 difference raw30548; decide +kernel
    rw [ha]
    exact (canonical30548 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2222 + difference 5 1) (sourceB2222 + difference 1 5) sourceC2222) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5003) := by
    have ha : (tripleCharges (sourceA2222 + difference 5 1) (sourceB2222 + difference 1 5) sourceC2222) = raw30549 := by
      apply Matrix.ext; unfold tripleCharges sourceA2222 sourceB2222 sourceC2222 difference raw30549; decide +kernel
    rw [ha]
    exact (canonical30549 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2222 + difference 5 2) (sourceB2222 + difference 2 5) sourceC2222) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5111) := by
    have ha : (tripleCharges (sourceA2222 + difference 5 2) (sourceB2222 + difference 2 5) sourceC2222) = raw29583 := by
      apply Matrix.ext; unfold tripleCharges sourceA2222 sourceB2222 sourceC2222 difference raw29583; decide +kernel
    rw [ha]
    exact (canonical29583 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2222 + difference 5 3) (sourceB2222 + difference 3 5) sourceC2222) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5050) := by
    have ha : (tripleCharges (sourceA2222 + difference 5 3) (sourceB2222 + difference 3 5) sourceC2222) = raw30550 := by
      apply Matrix.ext; unfold tripleCharges sourceA2222 sourceB2222 sourceC2222 difference raw30550; decide +kernel
    rw [ha]
    exact (canonical30550 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2222 + difference 5 4) (sourceB2222 + difference 4 5) sourceC2222) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5080) := by
    have ha : (tripleCharges (sourceA2222 + difference 5 4) (sourceB2222 + difference 4 5) sourceC2222) = raw29573 := by
      apply Matrix.ext; unfold tripleCharges sourceA2222 sourceB2222 sourceC2222 difference raw29573; decide +kernel
    rw [ha]
    exact (canonical29573 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2222 sourceB2222 sourceC2222
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2222, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2223 : Charge := ![1, 0, 1, 0, -1, -1]
def sourceB2223 : Charge := ![2, 1, -1, 0, -1, -1]
def sourceC2223 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceForm2223 : Integer.Sparse Master := [(Sum.inr 1901, 1), (Sum.inr 1918, 2), (Sum.inr 1929, 1), (Sum.inr 2029, 1), (Sum.inr 2380, 1), (Sum.inr 2388, 2), (Sum.inr 2395, 1), (Sum.inr 2452, 2), (Sum.inr 2456, 1), (Sum.inr 2473, 2), (Sum.inr 2488, 2), (Sum.inr 2489, 1), (Sum.inr 2499, 2), (Sum.inr 2523, 2), (Sum.inr 2546, 1), (Sum.inr 2576, 2), (Sum.inr 2605, 1), (Sum.inr 2868, 1), (Sum.inr 2917, 1), (Sum.inr 2943, 2), (Sum.inr 2969, 1)]

theorem sourceEq2223 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2223 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2223 + difference 0 1) (sourceB2223 + difference 1 0) sourceC2223) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2868) := by
    have ha : (tripleCharges (sourceA2223 + difference 0 1) (sourceB2223 + difference 1 0) sourceC2223) = raw30551 := by
      apply Matrix.ext; unfold tripleCharges sourceA2223 sourceB2223 sourceC2223 difference raw30551; decide +kernel
    rw [ha]
    exact (canonical30551 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2223 + difference 0 2) (sourceB2223 + difference 2 0) sourceC2223) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2969) := by
    have ha : (tripleCharges (sourceA2223 + difference 0 2) (sourceB2223 + difference 2 0) sourceC2223) = raw30552 := by
      apply Matrix.ext; unfold tripleCharges sourceA2223 sourceB2223 sourceC2223 difference raw30552; decide +kernel
    rw [ha]
    exact (canonical30552 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2223 + difference 0 3) (sourceB2223 + difference 3 0) sourceC2223) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2917) := by
    have ha : (tripleCharges (sourceA2223 + difference 0 3) (sourceB2223 + difference 3 0) sourceC2223) = raw30553 := by
      apply Matrix.ext; unfold tripleCharges sourceA2223 sourceB2223 sourceC2223 difference raw30553; decide +kernel
    rw [ha]
    exact (canonical30553 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2223 + difference 0 4) (sourceB2223 + difference 4 0) sourceC2223) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2943) := by
    have ha : (tripleCharges (sourceA2223 + difference 0 4) (sourceB2223 + difference 4 0) sourceC2223) = raw30554 := by
      apply Matrix.ext; unfold tripleCharges sourceA2223 sourceB2223 sourceC2223 difference raw30554; decide +kernel
    rw [ha]
    exact (canonical30554 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2223 + difference 0 5) (sourceB2223 + difference 5 0) sourceC2223) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2943) := by
    have ha : (tripleCharges (sourceA2223 + difference 0 5) (sourceB2223 + difference 5 0) sourceC2223) = raw30385 := by
      apply Matrix.ext; unfold tripleCharges sourceA2223 sourceB2223 sourceC2223 difference raw30385; decide +kernel
    rw [ha]
    exact (canonical30385 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2223 + difference 1 0) (sourceB2223 + difference 0 1) sourceC2223) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2029) := by
    have ha : (tripleCharges (sourceA2223 + difference 1 0) (sourceB2223 + difference 0 1) sourceC2223) = raw30555 := by
      apply Matrix.ext; unfold tripleCharges sourceA2223 sourceB2223 sourceC2223 difference raw30555; decide +kernel
    rw [ha]
    exact (canonical30555 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2223 + difference 1 2) (sourceB2223 + difference 2 1) sourceC2223) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2605) := by
    have ha : (tripleCharges (sourceA2223 + difference 1 2) (sourceB2223 + difference 2 1) sourceC2223) = raw30556 := by
      apply Matrix.ext; unfold tripleCharges sourceA2223 sourceB2223 sourceC2223 difference raw30556; decide +kernel
    rw [ha]
    exact (canonical30556 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2223 + difference 1 3) (sourceB2223 + difference 3 1) sourceC2223) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2546) := by
    have ha : (tripleCharges (sourceA2223 + difference 1 3) (sourceB2223 + difference 3 1) sourceC2223) = raw30557 := by
      apply Matrix.ext; unfold tripleCharges sourceA2223 sourceB2223 sourceC2223 difference raw30557; decide +kernel
    rw [ha]
    exact (canonical30557 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2223 + difference 1 4) (sourceB2223 + difference 4 1) sourceC2223) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2576) := by
    have ha : (tripleCharges (sourceA2223 + difference 1 4) (sourceB2223 + difference 4 1) sourceC2223) = raw30558 := by
      apply Matrix.ext; unfold tripleCharges sourceA2223 sourceB2223 sourceC2223 difference raw30558; decide +kernel
    rw [ha]
    exact (canonical30558 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2223 + difference 1 5) (sourceB2223 + difference 5 1) sourceC2223) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2576) := by
    have ha : (tripleCharges (sourceA2223 + difference 1 5) (sourceB2223 + difference 5 1) sourceC2223) = raw30390 := by
      apply Matrix.ext; unfold tripleCharges sourceA2223 sourceB2223 sourceC2223 difference raw30390; decide +kernel
    rw [ha]
    exact (canonical30390 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2223 + difference 2 0) (sourceB2223 + difference 0 2) sourceC2223) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1929) := by
    have ha : (tripleCharges (sourceA2223 + difference 2 0) (sourceB2223 + difference 0 2) sourceC2223) = raw30559 := by
      apply Matrix.ext; unfold tripleCharges sourceA2223 sourceB2223 sourceC2223 difference raw30559; decide +kernel
    rw [ha]
    exact (canonical30559 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2223 + difference 2 1) (sourceB2223 + difference 1 2) sourceC2223) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2395) := by
    have ha : (tripleCharges (sourceA2223 + difference 2 1) (sourceB2223 + difference 1 2) sourceC2223) = raw30560 := by
      apply Matrix.ext; unfold tripleCharges sourceA2223 sourceB2223 sourceC2223 difference raw30560; decide +kernel
    rw [ha]
    exact (canonical30560 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2223 + difference 2 3) (sourceB2223 + difference 3 2) sourceC2223) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2456) := by
    have ha : (tripleCharges (sourceA2223 + difference 2 3) (sourceB2223 + difference 3 2) sourceC2223) = raw30561 := by
      apply Matrix.ext; unfold tripleCharges sourceA2223 sourceB2223 sourceC2223 difference raw30561; decide +kernel
    rw [ha]
    exact (canonical30561 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2223 + difference 2 4) (sourceB2223 + difference 4 2) sourceC2223) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2499) := by
    have ha : (tripleCharges (sourceA2223 + difference 2 4) (sourceB2223 + difference 4 2) sourceC2223) = raw30562 := by
      apply Matrix.ext; unfold tripleCharges sourceA2223 sourceB2223 sourceC2223 difference raw30562; decide +kernel
    rw [ha]
    exact (canonical30562 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2223 + difference 2 5) (sourceB2223 + difference 5 2) sourceC2223) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2499) := by
    have ha : (tripleCharges (sourceA2223 + difference 2 5) (sourceB2223 + difference 5 2) sourceC2223) = raw30395 := by
      apply Matrix.ext; unfold tripleCharges sourceA2223 sourceB2223 sourceC2223 difference raw30395; decide +kernel
    rw [ha]
    exact (canonical30395 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2223 + difference 3 0) (sourceB2223 + difference 0 3) sourceC2223) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1901) := by
    have ha : (tripleCharges (sourceA2223 + difference 3 0) (sourceB2223 + difference 0 3) sourceC2223) = raw30563 := by
      apply Matrix.ext; unfold tripleCharges sourceA2223 sourceB2223 sourceC2223 difference raw30563; decide +kernel
    rw [ha]
    exact (canonical30563 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2223 + difference 3 1) (sourceB2223 + difference 1 3) sourceC2223) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2380) := by
    have ha : (tripleCharges (sourceA2223 + difference 3 1) (sourceB2223 + difference 1 3) sourceC2223) = raw30564 := by
      apply Matrix.ext; unfold tripleCharges sourceA2223 sourceB2223 sourceC2223 difference raw30564; decide +kernel
    rw [ha]
    exact (canonical30564 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2223 + difference 3 2) (sourceB2223 + difference 2 3) sourceC2223) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2489) := by
    have ha : (tripleCharges (sourceA2223 + difference 3 2) (sourceB2223 + difference 2 3) sourceC2223) = raw30565 := by
      apply Matrix.ext; unfold tripleCharges sourceA2223 sourceB2223 sourceC2223 difference raw30565; decide +kernel
    rw [ha]
    exact (canonical30565 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2223 + difference 3 4) (sourceB2223 + difference 4 3) sourceC2223) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2473) := by
    have ha : (tripleCharges (sourceA2223 + difference 3 4) (sourceB2223 + difference 4 3) sourceC2223) = raw30566 := by
      apply Matrix.ext; unfold tripleCharges sourceA2223 sourceB2223 sourceC2223 difference raw30566; decide +kernel
    rw [ha]
    exact (canonical30566 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2223 + difference 3 5) (sourceB2223 + difference 5 3) sourceC2223) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2473) := by
    have ha : (tripleCharges (sourceA2223 + difference 3 5) (sourceB2223 + difference 5 3) sourceC2223) = raw30400 := by
      apply Matrix.ext; unfold tripleCharges sourceA2223 sourceB2223 sourceC2223 difference raw30400; decide +kernel
    rw [ha]
    exact (canonical30400 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2223 + difference 4 0) (sourceB2223 + difference 0 4) sourceC2223) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1918) := by
    have ha : (tripleCharges (sourceA2223 + difference 4 0) (sourceB2223 + difference 0 4) sourceC2223) = raw30407 := by
      apply Matrix.ext; unfold tripleCharges sourceA2223 sourceB2223 sourceC2223 difference raw30407; decide +kernel
    rw [ha]
    exact (canonical30407 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2223 + difference 4 1) (sourceB2223 + difference 1 4) sourceC2223) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2388) := by
    have ha : (tripleCharges (sourceA2223 + difference 4 1) (sourceB2223 + difference 1 4) sourceC2223) = raw30408 := by
      apply Matrix.ext; unfold tripleCharges sourceA2223 sourceB2223 sourceC2223 difference raw30408; decide +kernel
    rw [ha]
    exact (canonical30408 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2223 + difference 4 2) (sourceB2223 + difference 2 4) sourceC2223) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2523) := by
    have ha : (tripleCharges (sourceA2223 + difference 4 2) (sourceB2223 + difference 2 4) sourceC2223) = raw30409 := by
      apply Matrix.ext; unfold tripleCharges sourceA2223 sourceB2223 sourceC2223 difference raw30409; decide +kernel
    rw [ha]
    exact (canonical30409 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2223 + difference 4 3) (sourceB2223 + difference 3 4) sourceC2223) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2452) := by
    have ha : (tripleCharges (sourceA2223 + difference 4 3) (sourceB2223 + difference 3 4) sourceC2223) = raw30410 := by
      apply Matrix.ext; unfold tripleCharges sourceA2223 sourceB2223 sourceC2223 difference raw30410; decide +kernel
    rw [ha]
    exact (canonical30410 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2223 + difference 4 5) (sourceB2223 + difference 5 4) sourceC2223) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2488) := by
    have ha : (tripleCharges (sourceA2223 + difference 4 5) (sourceB2223 + difference 5 4) sourceC2223) = raw30567 := by
      apply Matrix.ext; unfold tripleCharges sourceA2223 sourceB2223 sourceC2223 difference raw30567; decide +kernel
    rw [ha]
    exact (canonical30567 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2223 + difference 5 0) (sourceB2223 + difference 0 5) sourceC2223) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1918) := by
    have ha : (tripleCharges (sourceA2223 + difference 5 0) (sourceB2223 + difference 0 5) sourceC2223) = raw30568 := by
      apply Matrix.ext; unfold tripleCharges sourceA2223 sourceB2223 sourceC2223 difference raw30568; decide +kernel
    rw [ha]
    exact (canonical30568 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2223 + difference 5 1) (sourceB2223 + difference 1 5) sourceC2223) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2388) := by
    have ha : (tripleCharges (sourceA2223 + difference 5 1) (sourceB2223 + difference 1 5) sourceC2223) = raw30569 := by
      apply Matrix.ext; unfold tripleCharges sourceA2223 sourceB2223 sourceC2223 difference raw30569; decide +kernel
    rw [ha]
    exact (canonical30569 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2223 + difference 5 2) (sourceB2223 + difference 2 5) sourceC2223) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2523) := by
    have ha : (tripleCharges (sourceA2223 + difference 5 2) (sourceB2223 + difference 2 5) sourceC2223) = raw30570 := by
      apply Matrix.ext; unfold tripleCharges sourceA2223 sourceB2223 sourceC2223 difference raw30570; decide +kernel
    rw [ha]
    exact (canonical30570 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2223 + difference 5 3) (sourceB2223 + difference 3 5) sourceC2223) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2452) := by
    have ha : (tripleCharges (sourceA2223 + difference 5 3) (sourceB2223 + difference 3 5) sourceC2223) = raw30571 := by
      apply Matrix.ext; unfold tripleCharges sourceA2223 sourceB2223 sourceC2223 difference raw30571; decide +kernel
    rw [ha]
    exact (canonical30571 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2223 + difference 5 4) (sourceB2223 + difference 4 5) sourceC2223) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2488) := by
    have ha : (tripleCharges (sourceA2223 + difference 5 4) (sourceB2223 + difference 4 5) sourceC2223) = raw30572 := by
      apply Matrix.ext; unfold tripleCharges sourceA2223 sourceB2223 sourceC2223 difference raw30572; decide +kernel
    rw [ha]
    exact (canonical30572 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2223 sourceB2223 sourceC2223
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2223, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2224 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2224 : Charge := ![1, 0, 1, -1, 1, -2]
def sourceC2224 : Charge := ![2, 1, -1, 1, -3, 0]
def sourceForm2224 : Integer.Sparse Master := [(Sum.inr 2451, 1), (Sum.inr 3367, 1), (Sum.inr 3370, 1), (Sum.inr 3374, 1), (Sum.inr 3464, 1), (Sum.inr 3514, 1), (Sum.inr 4080, -1)]

theorem sourceEq2224 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2224 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2224 + difference 0 0) (sourceB2224 + difference 0 0) sourceC2224) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2451) := by
    have ha : (tripleCharges (sourceA2224 + difference 0 0) (sourceB2224 + difference 0 0) sourceC2224) = raw30573 := by
      apply Matrix.ext; unfold tripleCharges sourceA2224 sourceB2224 sourceC2224 difference raw30573; decide +kernel
    rw [ha]
    exact (canonical30573 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2224 + difference 0 1) (sourceB2224 + difference 1 0) sourceC2224) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3367) := by
    have ha : (tripleCharges (sourceA2224 + difference 0 1) (sourceB2224 + difference 1 0) sourceC2224) = raw30574 := by
      apply Matrix.ext; unfold tripleCharges sourceA2224 sourceB2224 sourceC2224 difference raw30574; decide +kernel
    rw [ha]
    exact (canonical30574 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2224 + difference 0 2) (sourceB2224 + difference 2 0) sourceC2224) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3374) := by
    have ha : (tripleCharges (sourceA2224 + difference 0 2) (sourceB2224 + difference 2 0) sourceC2224) = raw30575 := by
      apply Matrix.ext; unfold tripleCharges sourceA2224 sourceB2224 sourceC2224 difference raw30575; decide +kernel
    rw [ha]
    exact (canonical30575 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2224 + difference 0 3) (sourceB2224 + difference 3 0) sourceC2224) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3370) := by
    have ha : (tripleCharges (sourceA2224 + difference 0 3) (sourceB2224 + difference 3 0) sourceC2224) = raw30576 := by
      apply Matrix.ext; unfold tripleCharges sourceA2224 sourceB2224 sourceC2224 difference raw30576; decide +kernel
    rw [ha]
    exact (canonical30576 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2224 + difference 0 4) (sourceB2224 + difference 4 0) sourceC2224) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3464) := by
    have ha : (tripleCharges (sourceA2224 + difference 0 4) (sourceB2224 + difference 4 0) sourceC2224) = raw30577 := by
      apply Matrix.ext; unfold tripleCharges sourceA2224 sourceB2224 sourceC2224 difference raw30577; decide +kernel
    rw [ha]
    exact (canonical30577 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2224 + difference 0 5) (sourceB2224 + difference 5 0) sourceC2224) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3514) := by
    have ha : (tripleCharges (sourceA2224 + difference 0 5) (sourceB2224 + difference 5 0) sourceC2224) = raw30578 := by
      apply Matrix.ext; unfold tripleCharges sourceA2224 sourceB2224 sourceC2224 difference raw30578; decide +kernel
    rw [ha]
    exact (canonical30578 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2224 + sourceB2224) sourceC2224) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA2224 + sourceB2224) sourceC2224) = raw30579 := by
      apply Matrix.ext; unfold doubleCharges sourceA2224 sourceB2224 sourceC2224 raw30579; decide +kernel
    rw [ha]
    exact (canonical30579 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2224 sourceB2224 sourceC2224
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2224, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2225 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2225 : Charge := ![1, 0, 1, -1, 0, -1]
def sourceC2225 : Charge := ![2, 1, -1, 1, -2, -1]
def sourceForm2225 : Integer.Sparse Master := [(Sum.inr 1108, 1), (Sum.inr 2318, 1), (Sum.inr 2418, 1), (Sum.inr 2452, 1), (Sum.inr 2461, 1), (Sum.inr 2462, 1), (Sum.inr 4090, -1)]

theorem sourceEq2225 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2225 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2225 + difference 2 0) (sourceB2225 + difference 0 2) sourceC2225) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1108) := by
    have ha : (tripleCharges (sourceA2225 + difference 2 0) (sourceB2225 + difference 0 2) sourceC2225) = raw30580 := by
      apply Matrix.ext; unfold tripleCharges sourceA2225 sourceB2225 sourceC2225 difference raw30580; decide +kernel
    rw [ha]
    exact (canonical30580 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2225 + difference 2 1) (sourceB2225 + difference 1 2) sourceC2225) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2318) := by
    have ha : (tripleCharges (sourceA2225 + difference 2 1) (sourceB2225 + difference 1 2) sourceC2225) = raw30581 := by
      apply Matrix.ext; unfold tripleCharges sourceA2225 sourceB2225 sourceC2225 difference raw30581; decide +kernel
    rw [ha]
    exact (canonical30581 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2225 + difference 2 2) (sourceB2225 + difference 2 2) sourceC2225) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2452) := by
    have ha : (tripleCharges (sourceA2225 + difference 2 2) (sourceB2225 + difference 2 2) sourceC2225) = raw30582 := by
      apply Matrix.ext; unfold tripleCharges sourceA2225 sourceB2225 sourceC2225 difference raw30582; decide +kernel
    rw [ha]
    exact (canonical30582 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2225 + difference 2 3) (sourceB2225 + difference 3 2) sourceC2225) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2418) := by
    have ha : (tripleCharges (sourceA2225 + difference 2 3) (sourceB2225 + difference 3 2) sourceC2225) = raw30583 := by
      apply Matrix.ext; unfold tripleCharges sourceA2225 sourceB2225 sourceC2225 difference raw30583; decide +kernel
    rw [ha]
    exact (canonical30583 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2225 + difference 2 4) (sourceB2225 + difference 4 2) sourceC2225) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2462) := by
    have ha : (tripleCharges (sourceA2225 + difference 2 4) (sourceB2225 + difference 4 2) sourceC2225) = raw30584 := by
      apply Matrix.ext; unfold tripleCharges sourceA2225 sourceB2225 sourceC2225 difference raw30584; decide +kernel
    rw [ha]
    exact (canonical30584 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2225 + difference 2 5) (sourceB2225 + difference 5 2) sourceC2225) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2461) := by
    have ha : (tripleCharges (sourceA2225 + difference 2 5) (sourceB2225 + difference 5 2) sourceC2225) = raw30585 := by
      apply Matrix.ext; unfold tripleCharges sourceA2225 sourceB2225 sourceC2225 difference raw30585; decide +kernel
    rw [ha]
    exact (canonical30585 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2225 + sourceB2225) sourceC2225) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (doubleCharges (sourceA2225 + sourceB2225) sourceC2225) = raw30586 := by
      apply Matrix.ext; unfold doubleCharges sourceA2225 sourceB2225 sourceC2225 raw30586; decide +kernel
    rw [ha]
    exact (canonical30586 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2225 sourceB2225 sourceC2225
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2225, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2226 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2226 : Charge := ![1, 0, 1, -1, 0, -1]
def sourceC2226 : Charge := ![2, 1, -1, 1, -2, -1]
def sourceForm2226 : Integer.Sparse Master := [(Sum.inr 2317, 1), (Sum.inr 2412, 1), (Sum.inr 2418, 1), (Sum.inr 2452, 2), (Sum.inr 3682, 1), (Sum.inr 4090, -1)]

theorem sourceEq2226 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2226 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2226 + difference 0 3) (sourceB2226 + difference 3 0) sourceC2226) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3682) := by
    have ha : (tripleCharges (sourceA2226 + difference 0 3) (sourceB2226 + difference 3 0) sourceC2226) = raw30587 := by
      apply Matrix.ext; unfold tripleCharges sourceA2226 sourceB2226 sourceC2226 difference raw30587; decide +kernel
    rw [ha]
    exact (canonical30587 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2226 + difference 1 3) (sourceB2226 + difference 3 1) sourceC2226) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2452) := by
    have ha : (tripleCharges (sourceA2226 + difference 1 3) (sourceB2226 + difference 3 1) sourceC2226) = raw30588 := by
      apply Matrix.ext; unfold tripleCharges sourceA2226 sourceB2226 sourceC2226 difference raw30588; decide +kernel
    rw [ha]
    exact (canonical30588 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2226 + difference 2 3) (sourceB2226 + difference 3 2) sourceC2226) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2418) := by
    have ha : (tripleCharges (sourceA2226 + difference 2 3) (sourceB2226 + difference 3 2) sourceC2226) = raw30583 := by
      apply Matrix.ext; unfold tripleCharges sourceA2226 sourceB2226 sourceC2226 difference raw30583; decide +kernel
    rw [ha]
    exact (canonical30583 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2226 + difference 3 3) (sourceB2226 + difference 3 3) sourceC2226) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2452) := by
    have ha : (tripleCharges (sourceA2226 + difference 3 3) (sourceB2226 + difference 3 3) sourceC2226) = raw30582 := by
      apply Matrix.ext; unfold tripleCharges sourceA2226 sourceB2226 sourceC2226 difference raw30582; decide +kernel
    rw [ha]
    exact (canonical30582 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2226 + difference 4 3) (sourceB2226 + difference 3 4) sourceC2226) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2317) := by
    have ha : (tripleCharges (sourceA2226 + difference 4 3) (sourceB2226 + difference 3 4) sourceC2226) = raw30589 := by
      apply Matrix.ext; unfold tripleCharges sourceA2226 sourceB2226 sourceC2226 difference raw30589; decide +kernel
    rw [ha]
    exact (canonical30589 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2226 + difference 5 3) (sourceB2226 + difference 3 5) sourceC2226) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2412) := by
    have ha : (tripleCharges (sourceA2226 + difference 5 3) (sourceB2226 + difference 3 5) sourceC2226) = raw30590 := by
      apply Matrix.ext; unfold tripleCharges sourceA2226 sourceB2226 sourceC2226 difference raw30590; decide +kernel
    rw [ha]
    exact (canonical30590 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2226 + sourceB2226) sourceC2226) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (doubleCharges (sourceA2226 + sourceB2226) sourceC2226) = raw30586 := by
      apply Matrix.ext; unfold doubleCharges sourceA2226 sourceB2226 sourceC2226 raw30586; decide +kernel
    rw [ha]
    exact (canonical30586 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2226 sourceB2226 sourceC2226
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2226, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2227 : Charge := ![1, 0, 1, -1, 0, -1]
def sourceB2227 : Charge := ![2, 1, -1, 1, -2, -1]
def sourceC2227 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceForm2227 : Integer.Sparse Master := [(Sum.inr 1863, 1), (Sum.inr 1865, 1), (Sum.inr 1870, 1), (Sum.inr 1945, 1), (Sum.inr 1997, 1), (Sum.inr 3433, 1), (Sum.inr 4082, -1)]

theorem sourceEq2227 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2227 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2227 + difference 0 0) (sourceB2227 + difference 0 0) sourceC2227) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3433) := by
    have ha : (tripleCharges (sourceA2227 + difference 0 0) (sourceB2227 + difference 0 0) sourceC2227) = raw30591 := by
      apply Matrix.ext; unfold tripleCharges sourceA2227 sourceB2227 sourceC2227 difference raw30591; decide +kernel
    rw [ha]
    exact (canonical30591 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2227 + difference 1 0) (sourceB2227 + difference 0 1) sourceC2227) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1997) := by
    have ha : (tripleCharges (sourceA2227 + difference 1 0) (sourceB2227 + difference 0 1) sourceC2227) = raw30592 := by
      apply Matrix.ext; unfold tripleCharges sourceA2227 sourceB2227 sourceC2227 difference raw30592; decide +kernel
    rw [ha]
    exact (canonical30592 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2227 + difference 2 0) (sourceB2227 + difference 0 2) sourceC2227) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1870) := by
    have ha : (tripleCharges (sourceA2227 + difference 2 0) (sourceB2227 + difference 0 2) sourceC2227) = raw30593 := by
      apply Matrix.ext; unfold tripleCharges sourceA2227 sourceB2227 sourceC2227 difference raw30593; decide +kernel
    rw [ha]
    exact (canonical30593 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2227 + difference 3 0) (sourceB2227 + difference 0 3) sourceC2227) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1945) := by
    have ha : (tripleCharges (sourceA2227 + difference 3 0) (sourceB2227 + difference 0 3) sourceC2227) = raw30594 := by
      apply Matrix.ext; unfold tripleCharges sourceA2227 sourceB2227 sourceC2227 difference raw30594; decide +kernel
    rw [ha]
    exact (canonical30594 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2227 + difference 4 0) (sourceB2227 + difference 0 4) sourceC2227) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1863) := by
    have ha : (tripleCharges (sourceA2227 + difference 4 0) (sourceB2227 + difference 0 4) sourceC2227) = raw30595 := by
      apply Matrix.ext; unfold tripleCharges sourceA2227 sourceB2227 sourceC2227 difference raw30595; decide +kernel
    rw [ha]
    exact (canonical30595 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2227 + difference 5 0) (sourceB2227 + difference 0 5) sourceC2227) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1865) := by
    have ha : (tripleCharges (sourceA2227 + difference 5 0) (sourceB2227 + difference 0 5) sourceC2227) = raw30596 := by
      apply Matrix.ext; unfold tripleCharges sourceA2227 sourceB2227 sourceC2227 difference raw30596; decide +kernel
    rw [ha]
    exact (canonical30596 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2227 + sourceB2227) sourceC2227) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2227 + sourceB2227) sourceC2227) = raw29319 := by
      apply Matrix.ext; unfold doubleCharges sourceA2227 sourceB2227 sourceC2227 raw29319; decide +kernel
    rw [ha]
    exact (canonical29319 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2227 sourceB2227 sourceC2227
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2227, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2228 : Charge := ![1, 0, 1, -1, 0, -1]
def sourceB2228 : Charge := ![2, 1, -1, 1, -2, -1]
def sourceC2228 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceForm2228 : Integer.Sparse Master := [(Sum.inr 1865, 1), (Sum.inr 3332, 1), (Sum.inr 3362, 1), (Sum.inr 3433, 2), (Sum.inr 3439, 1), (Sum.inr 4082, -1)]

theorem sourceEq2228 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2228 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2228 + difference 5 0) (sourceB2228 + difference 0 5) sourceC2228) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1865) := by
    have ha : (tripleCharges (sourceA2228 + difference 5 0) (sourceB2228 + difference 0 5) sourceC2228) = raw30596 := by
      apply Matrix.ext; unfold tripleCharges sourceA2228 sourceB2228 sourceC2228 difference raw30596; decide +kernel
    rw [ha]
    exact (canonical30596 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2228 + difference 5 1) (sourceB2228 + difference 1 5) sourceC2228) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3332) := by
    have ha : (tripleCharges (sourceA2228 + difference 5 1) (sourceB2228 + difference 1 5) sourceC2228) = raw30597 := by
      apply Matrix.ext; unfold tripleCharges sourceA2228 sourceB2228 sourceC2228 difference raw30597; decide +kernel
    rw [ha]
    exact (canonical30597 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2228 + difference 5 2) (sourceB2228 + difference 2 5) sourceC2228) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3439) := by
    have ha : (tripleCharges (sourceA2228 + difference 5 2) (sourceB2228 + difference 2 5) sourceC2228) = raw30598 := by
      apply Matrix.ext; unfold tripleCharges sourceA2228 sourceB2228 sourceC2228 difference raw30598; decide +kernel
    rw [ha]
    exact (canonical30598 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2228 + difference 5 3) (sourceB2228 + difference 3 5) sourceC2228) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3362) := by
    have ha : (tripleCharges (sourceA2228 + difference 5 3) (sourceB2228 + difference 3 5) sourceC2228) = raw30599 := by
      apply Matrix.ext; unfold tripleCharges sourceA2228 sourceB2228 sourceC2228 difference raw30599; decide +kernel
    rw [ha]
    exact (canonical30599 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2228 + difference 5 4) (sourceB2228 + difference 4 5) sourceC2228) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3433) := by
    have ha : (tripleCharges (sourceA2228 + difference 5 4) (sourceB2228 + difference 4 5) sourceC2228) = raw30600 := by
      apply Matrix.ext; unfold tripleCharges sourceA2228 sourceB2228 sourceC2228 difference raw30600; decide +kernel
    rw [ha]
    exact (canonical30600 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2228 + difference 5 5) (sourceB2228 + difference 5 5) sourceC2228) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3433) := by
    have ha : (tripleCharges (sourceA2228 + difference 5 5) (sourceB2228 + difference 5 5) sourceC2228) = raw30591 := by
      apply Matrix.ext; unfold tripleCharges sourceA2228 sourceB2228 sourceC2228 difference raw30591; decide +kernel
    rw [ha]
    exact (canonical30591 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2228 + sourceB2228) sourceC2228) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2228 + sourceB2228) sourceC2228) = raw29319 := by
      apply Matrix.ext; unfold doubleCharges sourceA2228 sourceB2228 sourceC2228 raw29319; decide +kernel
    rw [ha]
    exact (canonical29319 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2228 sourceB2228 sourceC2228
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2228, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2229 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2229 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceC2229 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceForm2229 : Integer.Sparse Master := [(Sum.inr 4548, 2), (Sum.inr 4557, 1), (Sum.inr 4560, 1), (Sum.inr 4611, 1), (Sum.inr 4681, 2), (Sum.inr 4692, 1), (Sum.inr 4699, 2), (Sum.inr 4705, 1), (Sum.inr 4841, 1), (Sum.inr 4881, 1), (Sum.inr 4945, 2), (Sum.inr 5035, 2), (Sum.inr 5099, 2), (Sum.inr 5103, 2), (Sum.inr 5140, 2), (Sum.inr 5228, 2), (Sum.inr 5238, 1), (Sum.inr 5272, 1), (Sum.inr 5274, 1), (Sum.inr 5276, 1), (Sum.inr 5302, 1)]

theorem sourceEq2229 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2229 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2229 + difference 0 1) (sourceB2229 + difference 1 0) sourceC2229) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5238) := by
    have ha : (tripleCharges (sourceA2229 + difference 0 1) (sourceB2229 + difference 1 0) sourceC2229) = raw30601 := by
      apply Matrix.ext; unfold tripleCharges sourceA2229 sourceB2229 sourceC2229 difference raw30601; decide +kernel
    rw [ha]
    exact (canonical30601 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2229 + difference 0 2) (sourceB2229 + difference 2 0) sourceC2229) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5228) := by
    have ha : (tripleCharges (sourceA2229 + difference 0 2) (sourceB2229 + difference 2 0) sourceC2229) = raw30602 := by
      apply Matrix.ext; unfold tripleCharges sourceA2229 sourceB2229 sourceC2229 difference raw30602; decide +kernel
    rw [ha]
    exact (canonical30602 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2229 + difference 0 3) (sourceB2229 + difference 3 0) sourceC2229) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5228) := by
    have ha : (tripleCharges (sourceA2229 + difference 0 3) (sourceB2229 + difference 3 0) sourceC2229) = raw30603 := by
      apply Matrix.ext; unfold tripleCharges sourceA2229 sourceB2229 sourceC2229 difference raw30603; decide +kernel
    rw [ha]
    exact (canonical30603 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2229 + difference 0 4) (sourceB2229 + difference 4 0) sourceC2229) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA2229 + difference 0 4) (sourceB2229 + difference 4 0) sourceC2229) = raw5771 := by
      apply Matrix.ext; unfold tripleCharges sourceA2229 sourceB2229 sourceC2229 difference raw5771; decide +kernel
    rw [ha]
    exact (canonical5771 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2229 + difference 0 5) (sourceB2229 + difference 5 0) sourceC2229) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5274) := by
    have ha : (tripleCharges (sourceA2229 + difference 0 5) (sourceB2229 + difference 5 0) sourceC2229) = raw30604 := by
      apply Matrix.ext; unfold tripleCharges sourceA2229 sourceB2229 sourceC2229 difference raw30604; decide +kernel
    rw [ha]
    exact (canonical30604 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2229 + difference 1 0) (sourceB2229 + difference 0 1) sourceC2229) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4611) := by
    have ha : (tripleCharges (sourceA2229 + difference 1 0) (sourceB2229 + difference 0 1) sourceC2229) = raw5791 := by
      apply Matrix.ext; unfold tripleCharges sourceA2229 sourceB2229 sourceC2229 difference raw5791; decide +kernel
    rw [ha]
    exact (canonical5791 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2229 + difference 1 2) (sourceB2229 + difference 2 1) sourceC2229) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5140) := by
    have ha : (tripleCharges (sourceA2229 + difference 1 2) (sourceB2229 + difference 2 1) sourceC2229) = raw5793 := by
      apply Matrix.ext; unfold tripleCharges sourceA2229 sourceB2229 sourceC2229 difference raw5793; decide +kernel
    rw [ha]
    exact (canonical5793 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2229 + difference 1 3) (sourceB2229 + difference 3 1) sourceC2229) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5140) := by
    have ha : (tripleCharges (sourceA2229 + difference 1 3) (sourceB2229 + difference 3 1) sourceC2229) = raw5794 := by
      apply Matrix.ext; unfold tripleCharges sourceA2229 sourceB2229 sourceC2229 difference raw5794; decide +kernel
    rw [ha]
    exact (canonical5794 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2229 + difference 1 4) (sourceB2229 + difference 4 1) sourceC2229) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5276) := by
    have ha : (tripleCharges (sourceA2229 + difference 1 4) (sourceB2229 + difference 4 1) sourceC2229) = raw30605 := by
      apply Matrix.ext; unfold tripleCharges sourceA2229 sourceB2229 sourceC2229 difference raw30605; decide +kernel
    rw [ha]
    exact (canonical30605 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2229 + difference 1 5) (sourceB2229 + difference 5 1) sourceC2229) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5272) := by
    have ha : (tripleCharges (sourceA2229 + difference 1 5) (sourceB2229 + difference 5 1) sourceC2229) = raw5795 := by
      apply Matrix.ext; unfold tripleCharges sourceA2229 sourceB2229 sourceC2229 difference raw5795; decide +kernel
    rw [ha]
    exact (canonical5795 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2229 + difference 2 0) (sourceB2229 + difference 0 2) sourceC2229) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4548) := by
    have ha : (tripleCharges (sourceA2229 + difference 2 0) (sourceB2229 + difference 0 2) sourceC2229) = raw30606 := by
      apply Matrix.ext; unfold tripleCharges sourceA2229 sourceB2229 sourceC2229 difference raw30606; decide +kernel
    rw [ha]
    exact (canonical30606 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2229 + difference 2 1) (sourceB2229 + difference 1 2) sourceC2229) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4945) := by
    have ha : (tripleCharges (sourceA2229 + difference 2 1) (sourceB2229 + difference 1 2) sourceC2229) = raw30607 := by
      apply Matrix.ext; unfold tripleCharges sourceA2229 sourceB2229 sourceC2229 difference raw30607; decide +kernel
    rw [ha]
    exact (canonical30607 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2229 + difference 2 3) (sourceB2229 + difference 3 2) sourceC2229) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5035) := by
    have ha : (tripleCharges (sourceA2229 + difference 2 3) (sourceB2229 + difference 3 2) sourceC2229) = raw30608 := by
      apply Matrix.ext; unfold tripleCharges sourceA2229 sourceB2229 sourceC2229 difference raw30608; decide +kernel
    rw [ha]
    exact (canonical30608 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2229 + difference 2 4) (sourceB2229 + difference 4 2) sourceC2229) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5103) := by
    have ha : (tripleCharges (sourceA2229 + difference 2 4) (sourceB2229 + difference 4 2) sourceC2229) = raw5782 := by
      apply Matrix.ext; unfold tripleCharges sourceA2229 sourceB2229 sourceC2229 difference raw5782; decide +kernel
    rw [ha]
    exact (canonical5782 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2229 + difference 2 5) (sourceB2229 + difference 5 2) sourceC2229) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5099) := by
    have ha : (tripleCharges (sourceA2229 + difference 2 5) (sourceB2229 + difference 5 2) sourceC2229) = raw30609 := by
      apply Matrix.ext; unfold tripleCharges sourceA2229 sourceB2229 sourceC2229 difference raw30609; decide +kernel
    rw [ha]
    exact (canonical30609 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2229 + difference 3 0) (sourceB2229 + difference 0 3) sourceC2229) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4548) := by
    have ha : (tripleCharges (sourceA2229 + difference 3 0) (sourceB2229 + difference 0 3) sourceC2229) = raw30610 := by
      apply Matrix.ext; unfold tripleCharges sourceA2229 sourceB2229 sourceC2229 difference raw30610; decide +kernel
    rw [ha]
    exact (canonical30610 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2229 + difference 3 1) (sourceB2229 + difference 1 3) sourceC2229) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4945) := by
    have ha : (tripleCharges (sourceA2229 + difference 3 1) (sourceB2229 + difference 1 3) sourceC2229) = raw30611 := by
      apply Matrix.ext; unfold tripleCharges sourceA2229 sourceB2229 sourceC2229 difference raw30611; decide +kernel
    rw [ha]
    exact (canonical30611 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2229 + difference 3 2) (sourceB2229 + difference 2 3) sourceC2229) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5035) := by
    have ha : (tripleCharges (sourceA2229 + difference 3 2) (sourceB2229 + difference 2 3) sourceC2229) = raw30612 := by
      apply Matrix.ext; unfold tripleCharges sourceA2229 sourceB2229 sourceC2229 difference raw30612; decide +kernel
    rw [ha]
    exact (canonical30612 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2229 + difference 3 4) (sourceB2229 + difference 4 3) sourceC2229) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5103) := by
    have ha : (tripleCharges (sourceA2229 + difference 3 4) (sourceB2229 + difference 4 3) sourceC2229) = raw5787 := by
      apply Matrix.ext; unfold tripleCharges sourceA2229 sourceB2229 sourceC2229 difference raw5787; decide +kernel
    rw [ha]
    exact (canonical5787 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2229 + difference 3 5) (sourceB2229 + difference 5 3) sourceC2229) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5099) := by
    have ha : (tripleCharges (sourceA2229 + difference 3 5) (sourceB2229 + difference 5 3) sourceC2229) = raw30613 := by
      apply Matrix.ext; unfold tripleCharges sourceA2229 sourceB2229 sourceC2229 difference raw30613; decide +kernel
    rw [ha]
    exact (canonical30613 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2229 + difference 4 0) (sourceB2229 + difference 0 4) sourceC2229) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4557) := by
    have ha : (tripleCharges (sourceA2229 + difference 4 0) (sourceB2229 + difference 0 4) sourceC2229) = raw30614 := by
      apply Matrix.ext; unfold tripleCharges sourceA2229 sourceB2229 sourceC2229 difference raw30614; decide +kernel
    rw [ha]
    exact (canonical30614 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2229 + difference 4 1) (sourceB2229 + difference 1 4) sourceC2229) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4692) := by
    have ha : (tripleCharges (sourceA2229 + difference 4 1) (sourceB2229 + difference 1 4) sourceC2229) = raw30615 := by
      apply Matrix.ext; unfold tripleCharges sourceA2229 sourceB2229 sourceC2229 difference raw30615; decide +kernel
    rw [ha]
    exact (canonical30615 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2229 + difference 4 2) (sourceB2229 + difference 2 4) sourceC2229) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4681) := by
    have ha : (tripleCharges (sourceA2229 + difference 4 2) (sourceB2229 + difference 2 4) sourceC2229) = raw30616 := by
      apply Matrix.ext; unfold tripleCharges sourceA2229 sourceB2229 sourceC2229 difference raw30616; decide +kernel
    rw [ha]
    exact (canonical30616 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2229 + difference 4 3) (sourceB2229 + difference 3 4) sourceC2229) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4681) := by
    have ha : (tripleCharges (sourceA2229 + difference 4 3) (sourceB2229 + difference 3 4) sourceC2229) = raw30617 := by
      apply Matrix.ext; unfold tripleCharges sourceA2229 sourceB2229 sourceC2229 difference raw30617; decide +kernel
    rw [ha]
    exact (canonical30617 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2229 + difference 4 5) (sourceB2229 + difference 5 4) sourceC2229) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4841) := by
    have ha : (tripleCharges (sourceA2229 + difference 4 5) (sourceB2229 + difference 5 4) sourceC2229) = raw30618 := by
      apply Matrix.ext; unfold tripleCharges sourceA2229 sourceB2229 sourceC2229 difference raw30618; decide +kernel
    rw [ha]
    exact (canonical30618 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2229 + difference 5 0) (sourceB2229 + difference 0 5) sourceC2229) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4560) := by
    have ha : (tripleCharges (sourceA2229 + difference 5 0) (sourceB2229 + difference 0 5) sourceC2229) = raw30619 := by
      apply Matrix.ext; unfold tripleCharges sourceA2229 sourceB2229 sourceC2229 difference raw30619; decide +kernel
    rw [ha]
    exact (canonical30619 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2229 + difference 5 1) (sourceB2229 + difference 1 5) sourceC2229) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4705) := by
    have ha : (tripleCharges (sourceA2229 + difference 5 1) (sourceB2229 + difference 1 5) sourceC2229) = raw30620 := by
      apply Matrix.ext; unfold tripleCharges sourceA2229 sourceB2229 sourceC2229 difference raw30620; decide +kernel
    rw [ha]
    exact (canonical30620 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2229 + difference 5 2) (sourceB2229 + difference 2 5) sourceC2229) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4699) := by
    have ha : (tripleCharges (sourceA2229 + difference 5 2) (sourceB2229 + difference 2 5) sourceC2229) = raw30621 := by
      apply Matrix.ext; unfold tripleCharges sourceA2229 sourceB2229 sourceC2229 difference raw30621; decide +kernel
    rw [ha]
    exact (canonical30621 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2229 + difference 5 3) (sourceB2229 + difference 3 5) sourceC2229) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4699) := by
    have ha : (tripleCharges (sourceA2229 + difference 5 3) (sourceB2229 + difference 3 5) sourceC2229) = raw30622 := by
      apply Matrix.ext; unfold tripleCharges sourceA2229 sourceB2229 sourceC2229 difference raw30622; decide +kernel
    rw [ha]
    exact (canonical30622 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2229 + difference 5 4) (sourceB2229 + difference 4 5) sourceC2229) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4881) := by
    have ha : (tripleCharges (sourceA2229 + difference 5 4) (sourceB2229 + difference 4 5) sourceC2229) = raw5797 := by
      apply Matrix.ext; unfold tripleCharges sourceA2229 sourceB2229 sourceC2229 difference raw5797; decide +kernel
    rw [ha]
    exact (canonical5797 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2229 sourceB2229 sourceC2229
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2229, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2230 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2230 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceC2230 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceForm2230 : Integer.Sparse Master := [(Sum.inr 2151, 2), (Sum.inr 2167, 1), (Sum.inr 2168, 1), (Sum.inr 2228, 1), (Sum.inr 2256, 2), (Sum.inr 2258, 1), (Sum.inr 2267, 1), (Sum.inr 2286, 1), (Sum.inr 2652, 2), (Sum.inr 2657, 2), (Sum.inr 2658, 2), (Sum.inr 2670, 2), (Sum.inr 2672, 2), (Sum.inr 2683, 1), (Sum.inr 2686, 1), (Sum.inr 2704, 2), (Sum.inr 2740, 1), (Sum.inr 2742, 1), (Sum.inr 3024, 2), (Sum.inr 3052, 1), (Sum.inr 3054, 1)]

theorem sourceEq2230 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2230 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2230 + difference 0 1) (sourceB2230 + difference 1 0) sourceC2230) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2686) := by
    have ha : (tripleCharges (sourceA2230 + difference 0 1) (sourceB2230 + difference 1 0) sourceC2230) = raw30623 := by
      apply Matrix.ext; unfold tripleCharges sourceA2230 sourceB2230 sourceC2230 difference raw30623; decide +kernel
    rw [ha]
    exact (canonical30623 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2230 + difference 0 2) (sourceB2230 + difference 2 0) sourceC2230) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2672) := by
    have ha : (tripleCharges (sourceA2230 + difference 0 2) (sourceB2230 + difference 2 0) sourceC2230) = raw30624 := by
      apply Matrix.ext; unfold tripleCharges sourceA2230 sourceB2230 sourceC2230 difference raw30624; decide +kernel
    rw [ha]
    exact (canonical30624 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2230 + difference 0 3) (sourceB2230 + difference 3 0) sourceC2230) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2672) := by
    have ha : (tripleCharges (sourceA2230 + difference 0 3) (sourceB2230 + difference 3 0) sourceC2230) = raw30625 := by
      apply Matrix.ext; unfold tripleCharges sourceA2230 sourceB2230 sourceC2230 difference raw30625; decide +kernel
    rw [ha]
    exact (canonical30625 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2230 + difference 0 4) (sourceB2230 + difference 4 0) sourceC2230) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3054) := by
    have ha : (tripleCharges (sourceA2230 + difference 0 4) (sourceB2230 + difference 4 0) sourceC2230) = raw5831 := by
      apply Matrix.ext; unfold tripleCharges sourceA2230 sourceB2230 sourceC2230 difference raw5831; decide +kernel
    rw [ha]
    exact (canonical5831 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2230 + difference 0 5) (sourceB2230 + difference 5 0) sourceC2230) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2742) := by
    have ha : (tripleCharges (sourceA2230 + difference 0 5) (sourceB2230 + difference 5 0) sourceC2230) = raw30626 := by
      apply Matrix.ext; unfold tripleCharges sourceA2230 sourceB2230 sourceC2230 difference raw30626; decide +kernel
    rw [ha]
    exact (canonical30626 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2230 + difference 1 0) (sourceB2230 + difference 0 1) sourceC2230) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2683) := by
    have ha : (tripleCharges (sourceA2230 + difference 1 0) (sourceB2230 + difference 0 1) sourceC2230) = raw5851 := by
      apply Matrix.ext; unfold tripleCharges sourceA2230 sourceB2230 sourceC2230 difference raw5851; decide +kernel
    rw [ha]
    exact (canonical5851 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2230 + difference 1 2) (sourceB2230 + difference 2 1) sourceC2230) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2670) := by
    have ha : (tripleCharges (sourceA2230 + difference 1 2) (sourceB2230 + difference 2 1) sourceC2230) = raw5853 := by
      apply Matrix.ext; unfold tripleCharges sourceA2230 sourceB2230 sourceC2230 difference raw5853; decide +kernel
    rw [ha]
    exact (canonical5853 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2230 + difference 1 3) (sourceB2230 + difference 3 1) sourceC2230) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2670) := by
    have ha : (tripleCharges (sourceA2230 + difference 1 3) (sourceB2230 + difference 3 1) sourceC2230) = raw5854 := by
      apply Matrix.ext; unfold tripleCharges sourceA2230 sourceB2230 sourceC2230 difference raw5854; decide +kernel
    rw [ha]
    exact (canonical5854 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2230 + difference 1 4) (sourceB2230 + difference 4 1) sourceC2230) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3052) := by
    have ha : (tripleCharges (sourceA2230 + difference 1 4) (sourceB2230 + difference 4 1) sourceC2230) = raw30627 := by
      apply Matrix.ext; unfold tripleCharges sourceA2230 sourceB2230 sourceC2230 difference raw30627; decide +kernel
    rw [ha]
    exact (canonical30627 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2230 + difference 1 5) (sourceB2230 + difference 5 1) sourceC2230) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2740) := by
    have ha : (tripleCharges (sourceA2230 + difference 1 5) (sourceB2230 + difference 5 1) sourceC2230) = raw5855 := by
      apply Matrix.ext; unfold tripleCharges sourceA2230 sourceB2230 sourceC2230 difference raw5855; decide +kernel
    rw [ha]
    exact (canonical5855 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2230 + difference 2 0) (sourceB2230 + difference 0 2) sourceC2230) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2657) := by
    have ha : (tripleCharges (sourceA2230 + difference 2 0) (sourceB2230 + difference 0 2) sourceC2230) = raw30628 := by
      apply Matrix.ext; unfold tripleCharges sourceA2230 sourceB2230 sourceC2230 difference raw30628; decide +kernel
    rw [ha]
    exact (canonical30628 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2230 + difference 2 1) (sourceB2230 + difference 1 2) sourceC2230) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2658) := by
    have ha : (tripleCharges (sourceA2230 + difference 2 1) (sourceB2230 + difference 1 2) sourceC2230) = raw30629 := by
      apply Matrix.ext; unfold tripleCharges sourceA2230 sourceB2230 sourceC2230 difference raw30629; decide +kernel
    rw [ha]
    exact (canonical30629 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2230 + difference 2 3) (sourceB2230 + difference 3 2) sourceC2230) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2652) := by
    have ha : (tripleCharges (sourceA2230 + difference 2 3) (sourceB2230 + difference 3 2) sourceC2230) = raw30630 := by
      apply Matrix.ext; unfold tripleCharges sourceA2230 sourceB2230 sourceC2230 difference raw30630; decide +kernel
    rw [ha]
    exact (canonical30630 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2230 + difference 2 4) (sourceB2230 + difference 4 2) sourceC2230) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3024) := by
    have ha : (tripleCharges (sourceA2230 + difference 2 4) (sourceB2230 + difference 4 2) sourceC2230) = raw5842 := by
      apply Matrix.ext; unfold tripleCharges sourceA2230 sourceB2230 sourceC2230 difference raw5842; decide +kernel
    rw [ha]
    exact (canonical5842 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2230 + difference 2 5) (sourceB2230 + difference 5 2) sourceC2230) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2704) := by
    have ha : (tripleCharges (sourceA2230 + difference 2 5) (sourceB2230 + difference 5 2) sourceC2230) = raw30631 := by
      apply Matrix.ext; unfold tripleCharges sourceA2230 sourceB2230 sourceC2230 difference raw30631; decide +kernel
    rw [ha]
    exact (canonical30631 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2230 + difference 3 0) (sourceB2230 + difference 0 3) sourceC2230) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2657) := by
    have ha : (tripleCharges (sourceA2230 + difference 3 0) (sourceB2230 + difference 0 3) sourceC2230) = raw30632 := by
      apply Matrix.ext; unfold tripleCharges sourceA2230 sourceB2230 sourceC2230 difference raw30632; decide +kernel
    rw [ha]
    exact (canonical30632 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2230 + difference 3 1) (sourceB2230 + difference 1 3) sourceC2230) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2658) := by
    have ha : (tripleCharges (sourceA2230 + difference 3 1) (sourceB2230 + difference 1 3) sourceC2230) = raw30633 := by
      apply Matrix.ext; unfold tripleCharges sourceA2230 sourceB2230 sourceC2230 difference raw30633; decide +kernel
    rw [ha]
    exact (canonical30633 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2230 + difference 3 2) (sourceB2230 + difference 2 3) sourceC2230) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2652) := by
    have ha : (tripleCharges (sourceA2230 + difference 3 2) (sourceB2230 + difference 2 3) sourceC2230) = raw30634 := by
      apply Matrix.ext; unfold tripleCharges sourceA2230 sourceB2230 sourceC2230 difference raw30634; decide +kernel
    rw [ha]
    exact (canonical30634 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2230 + difference 3 4) (sourceB2230 + difference 4 3) sourceC2230) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3024) := by
    have ha : (tripleCharges (sourceA2230 + difference 3 4) (sourceB2230 + difference 4 3) sourceC2230) = raw5847 := by
      apply Matrix.ext; unfold tripleCharges sourceA2230 sourceB2230 sourceC2230 difference raw5847; decide +kernel
    rw [ha]
    exact (canonical5847 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2230 + difference 3 5) (sourceB2230 + difference 5 3) sourceC2230) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2704) := by
    have ha : (tripleCharges (sourceA2230 + difference 3 5) (sourceB2230 + difference 5 3) sourceC2230) = raw30635 := by
      apply Matrix.ext; unfold tripleCharges sourceA2230 sourceB2230 sourceC2230 difference raw30635; decide +kernel
    rw [ha]
    exact (canonical30635 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2230 + difference 4 0) (sourceB2230 + difference 0 4) sourceC2230) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2167) := by
    have ha : (tripleCharges (sourceA2230 + difference 4 0) (sourceB2230 + difference 0 4) sourceC2230) = raw30636 := by
      apply Matrix.ext; unfold tripleCharges sourceA2230 sourceB2230 sourceC2230 difference raw30636; decide +kernel
    rw [ha]
    exact (canonical30636 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2230 + difference 4 1) (sourceB2230 + difference 1 4) sourceC2230) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2168) := by
    have ha : (tripleCharges (sourceA2230 + difference 4 1) (sourceB2230 + difference 1 4) sourceC2230) = raw30637 := by
      apply Matrix.ext; unfold tripleCharges sourceA2230 sourceB2230 sourceC2230 difference raw30637; decide +kernel
    rw [ha]
    exact (canonical30637 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2230 + difference 4 2) (sourceB2230 + difference 2 4) sourceC2230) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2151) := by
    have ha : (tripleCharges (sourceA2230 + difference 4 2) (sourceB2230 + difference 2 4) sourceC2230) = raw30638 := by
      apply Matrix.ext; unfold tripleCharges sourceA2230 sourceB2230 sourceC2230 difference raw30638; decide +kernel
    rw [ha]
    exact (canonical30638 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2230 + difference 4 3) (sourceB2230 + difference 3 4) sourceC2230) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2151) := by
    have ha : (tripleCharges (sourceA2230 + difference 4 3) (sourceB2230 + difference 3 4) sourceC2230) = raw30639 := by
      apply Matrix.ext; unfold tripleCharges sourceA2230 sourceB2230 sourceC2230 difference raw30639; decide +kernel
    rw [ha]
    exact (canonical30639 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2230 + difference 4 5) (sourceB2230 + difference 5 4) sourceC2230) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2228) := by
    have ha : (tripleCharges (sourceA2230 + difference 4 5) (sourceB2230 + difference 5 4) sourceC2230) = raw30640 := by
      apply Matrix.ext; unfold tripleCharges sourceA2230 sourceB2230 sourceC2230 difference raw30640; decide +kernel
    rw [ha]
    exact (canonical30640 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2230 + difference 5 0) (sourceB2230 + difference 0 5) sourceC2230) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2258) := by
    have ha : (tripleCharges (sourceA2230 + difference 5 0) (sourceB2230 + difference 0 5) sourceC2230) = raw30641 := by
      apply Matrix.ext; unfold tripleCharges sourceA2230 sourceB2230 sourceC2230 difference raw30641; decide +kernel
    rw [ha]
    exact (canonical30641 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2230 + difference 5 1) (sourceB2230 + difference 1 5) sourceC2230) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2286) := by
    have ha : (tripleCharges (sourceA2230 + difference 5 1) (sourceB2230 + difference 1 5) sourceC2230) = raw30642 := by
      apply Matrix.ext; unfold tripleCharges sourceA2230 sourceB2230 sourceC2230 difference raw30642; decide +kernel
    rw [ha]
    exact (canonical30642 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2230 + difference 5 2) (sourceB2230 + difference 2 5) sourceC2230) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2256) := by
    have ha : (tripleCharges (sourceA2230 + difference 5 2) (sourceB2230 + difference 2 5) sourceC2230) = raw30643 := by
      apply Matrix.ext; unfold tripleCharges sourceA2230 sourceB2230 sourceC2230 difference raw30643; decide +kernel
    rw [ha]
    exact (canonical30643 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2230 + difference 5 3) (sourceB2230 + difference 3 5) sourceC2230) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2256) := by
    have ha : (tripleCharges (sourceA2230 + difference 5 3) (sourceB2230 + difference 3 5) sourceC2230) = raw30644 := by
      apply Matrix.ext; unfold tripleCharges sourceA2230 sourceB2230 sourceC2230 difference raw30644; decide +kernel
    rw [ha]
    exact (canonical30644 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2230 + difference 5 4) (sourceB2230 + difference 4 5) sourceC2230) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2267) := by
    have ha : (tripleCharges (sourceA2230 + difference 5 4) (sourceB2230 + difference 4 5) sourceC2230) = raw5857 := by
      apply Matrix.ext; unfold tripleCharges sourceA2230 sourceB2230 sourceC2230 difference raw5857; decide +kernel
    rw [ha]
    exact (canonical5857 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2230 sourceB2230 sourceC2230
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2230, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2231 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2231 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceC2231 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceForm2231 : Integer.Sparse Master := [(Sum.inr 1818, 1), (Sum.inr 2336, 2), (Sum.inr 2346, 1), (Sum.inr 2522, 1), (Sum.inr 3397, 1), (Sum.inr 4084, -1)]

theorem sourceEq2231 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2231 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2231 + difference 0 1) (sourceB2231 + difference 1 0) sourceC2231) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3397) := by
    have ha : (tripleCharges (sourceA2231 + difference 0 1) (sourceB2231 + difference 1 0) sourceC2231) = raw30645 := by
      apply Matrix.ext; unfold tripleCharges sourceA2231 sourceB2231 sourceC2231 difference raw30645; decide +kernel
    rw [ha]
    exact (canonical30645 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2231 + difference 1 1) (sourceB2231 + difference 1 1) sourceC2231) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2522) := by
    have ha : (tripleCharges (sourceA2231 + difference 1 1) (sourceB2231 + difference 1 1) sourceC2231) = raw5879 := by
      apply Matrix.ext; unfold tripleCharges sourceA2231 sourceB2231 sourceC2231 difference raw5879; decide +kernel
    rw [ha]
    exact (canonical5879 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2231 + difference 2 1) (sourceB2231 + difference 1 2) sourceC2231) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2336) := by
    have ha : (tripleCharges (sourceA2231 + difference 2 1) (sourceB2231 + difference 1 2) sourceC2231) = raw30646 := by
      apply Matrix.ext; unfold tripleCharges sourceA2231 sourceB2231 sourceC2231 difference raw30646; decide +kernel
    rw [ha]
    exact (canonical30646 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2231 + difference 3 1) (sourceB2231 + difference 1 3) sourceC2231) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2336) := by
    have ha : (tripleCharges (sourceA2231 + difference 3 1) (sourceB2231 + difference 1 3) sourceC2231) = raw30647 := by
      apply Matrix.ext; unfold tripleCharges sourceA2231 sourceB2231 sourceC2231 difference raw30647; decide +kernel
    rw [ha]
    exact (canonical30647 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2231 + difference 4 1) (sourceB2231 + difference 1 4) sourceC2231) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1818) := by
    have ha : (tripleCharges (sourceA2231 + difference 4 1) (sourceB2231 + difference 1 4) sourceC2231) = raw30648 := by
      apply Matrix.ext; unfold tripleCharges sourceA2231 sourceB2231 sourceC2231 difference raw30648; decide +kernel
    rw [ha]
    exact (canonical30648 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2231 + difference 5 1) (sourceB2231 + difference 1 5) sourceC2231) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2346) := by
    have ha : (tripleCharges (sourceA2231 + difference 5 1) (sourceB2231 + difference 1 5) sourceC2231) = raw30649 := by
      apply Matrix.ext; unfold tripleCharges sourceA2231 sourceB2231 sourceC2231 difference raw30649; decide +kernel
    rw [ha]
    exact (canonical30649 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2231 + sourceB2231) sourceC2231) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA2231 + sourceB2231) sourceC2231) = raw5867 := by
      apply Matrix.ext; unfold doubleCharges sourceA2231 sourceB2231 sourceC2231 raw5867; decide +kernel
    rw [ha]
    exact (canonical5867 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2231 sourceB2231 sourceC2231
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2231, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2232 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2232 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceC2232 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceForm2232 : Integer.Sparse Master := [(Sum.inr 4310, 2), (Sum.inr 4316, 1), (Sum.inr 4319, 1), (Sum.inr 4380, 2), (Sum.inr 4383, 1), (Sum.inr 4490, 1), (Sum.inr 4510, 1), (Sum.inr 4920, 2), (Sum.inr 4925, 1), (Sum.inr 4982, 2), (Sum.inr 5028, 2), (Sum.inr 5094, 2), (Sum.inr 5105, 2), (Sum.inr 5109, 1), (Sum.inr 5110, 2), (Sum.inr 5237, 2), (Sum.inr 5238, 1), (Sum.inr 5304, 1), (Sum.inr 5305, 1), (Sum.inr 5310, 1), (Sum.inr 5451, 1)]

theorem sourceEq2232 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2232 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2232 + difference 0 1) (sourceB2232 + difference 1 0) sourceC2232) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5238) := by
    have ha : (tripleCharges (sourceA2232 + difference 0 1) (sourceB2232 + difference 1 0) sourceC2232) = raw30650 := by
      apply Matrix.ext; unfold tripleCharges sourceA2232 sourceB2232 sourceC2232 difference raw30650; decide +kernel
    rw [ha]
    exact (canonical30650 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2232 + difference 0 2) (sourceB2232 + difference 2 0) sourceC2232) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5237) := by
    have ha : (tripleCharges (sourceA2232 + difference 0 2) (sourceB2232 + difference 2 0) sourceC2232) = raw30651 := by
      apply Matrix.ext; unfold tripleCharges sourceA2232 sourceB2232 sourceC2232 difference raw30651; decide +kernel
    rw [ha]
    exact (canonical30651 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2232 + difference 0 3) (sourceB2232 + difference 3 0) sourceC2232) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5237) := by
    have ha : (tripleCharges (sourceA2232 + difference 0 3) (sourceB2232 + difference 3 0) sourceC2232) = raw30652 := by
      apply Matrix.ext; unfold tripleCharges sourceA2232 sourceB2232 sourceC2232 difference raw30652; decide +kernel
    rw [ha]
    exact (canonical30652 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2232 + difference 0 4) (sourceB2232 + difference 4 0) sourceC2232) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA2232 + difference 0 4) (sourceB2232 + difference 4 0) sourceC2232) = raw2872 := by
      apply Matrix.ext; unfold tripleCharges sourceA2232 sourceB2232 sourceC2232 difference raw2872; decide +kernel
    rw [ha]
    exact (canonical2872 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2232 + difference 0 5) (sourceB2232 + difference 5 0) sourceC2232) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA2232 + difference 0 5) (sourceB2232 + difference 5 0) sourceC2232) = raw3226 := by
      apply Matrix.ext; unfold tripleCharges sourceA2232 sourceB2232 sourceC2232 difference raw3226; decide +kernel
    rw [ha]
    exact (canonical3226 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2232 + difference 1 0) (sourceB2232 + difference 0 1) sourceC2232) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4510) := by
    have ha : (tripleCharges (sourceA2232 + difference 1 0) (sourceB2232 + difference 0 1) sourceC2232) = raw7606 := by
      apply Matrix.ext; unfold tripleCharges sourceA2232 sourceB2232 sourceC2232 difference raw7606; decide +kernel
    rw [ha]
    exact (canonical7606 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2232 + difference 1 2) (sourceB2232 + difference 2 1) sourceC2232) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5110) := by
    have ha : (tripleCharges (sourceA2232 + difference 1 2) (sourceB2232 + difference 2 1) sourceC2232) = raw7608 := by
      apply Matrix.ext; unfold tripleCharges sourceA2232 sourceB2232 sourceC2232 difference raw7608; decide +kernel
    rw [ha]
    exact (canonical7608 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2232 + difference 1 3) (sourceB2232 + difference 3 1) sourceC2232) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5110) := by
    have ha : (tripleCharges (sourceA2232 + difference 1 3) (sourceB2232 + difference 3 1) sourceC2232) = raw7609 := by
      apply Matrix.ext; unfold tripleCharges sourceA2232 sourceB2232 sourceC2232 difference raw7609; decide +kernel
    rw [ha]
    exact (canonical7609 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2232 + difference 1 4) (sourceB2232 + difference 4 1) sourceC2232) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5310) := by
    have ha : (tripleCharges (sourceA2232 + difference 1 4) (sourceB2232 + difference 4 1) sourceC2232) = raw2871 := by
      apply Matrix.ext; unfold tripleCharges sourceA2232 sourceB2232 sourceC2232 difference raw2871; decide +kernel
    rw [ha]
    exact (canonical2871 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2232 + difference 1 5) (sourceB2232 + difference 5 1) sourceC2232) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5305) := by
    have ha : (tripleCharges (sourceA2232 + difference 1 5) (sourceB2232 + difference 5 1) sourceC2232) = raw3225 := by
      apply Matrix.ext; unfold tripleCharges sourceA2232 sourceB2232 sourceC2232 difference raw3225; decide +kernel
    rw [ha]
    exact (canonical3225 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2232 + difference 2 0) (sourceB2232 + difference 0 2) sourceC2232) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4310) := by
    have ha : (tripleCharges (sourceA2232 + difference 2 0) (sourceB2232 + difference 0 2) sourceC2232) = raw23432 := by
      apply Matrix.ext; unfold tripleCharges sourceA2232 sourceB2232 sourceC2232 difference raw23432; decide +kernel
    rw [ha]
    exact (canonical23432 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2232 + difference 2 1) (sourceB2232 + difference 1 2) sourceC2232) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4920) := by
    have ha : (tripleCharges (sourceA2232 + difference 2 1) (sourceB2232 + difference 1 2) sourceC2232) = raw30653 := by
      apply Matrix.ext; unfold tripleCharges sourceA2232 sourceB2232 sourceC2232 difference raw30653; decide +kernel
    rw [ha]
    exact (canonical30653 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2232 + difference 2 3) (sourceB2232 + difference 3 2) sourceC2232) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5028) := by
    have ha : (tripleCharges (sourceA2232 + difference 2 3) (sourceB2232 + difference 3 2) sourceC2232) = raw30654 := by
      apply Matrix.ext; unfold tripleCharges sourceA2232 sourceB2232 sourceC2232 difference raw30654; decide +kernel
    rw [ha]
    exact (canonical30654 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2232 + difference 2 4) (sourceB2232 + difference 4 2) sourceC2232) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5105) := by
    have ha : (tripleCharges (sourceA2232 + difference 2 4) (sourceB2232 + difference 4 2) sourceC2232) = raw7601 := by
      apply Matrix.ext; unfold tripleCharges sourceA2232 sourceB2232 sourceC2232 difference raw7601; decide +kernel
    rw [ha]
    exact (canonical7601 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2232 + difference 2 5) (sourceB2232 + difference 5 2) sourceC2232) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5094) := by
    have ha : (tripleCharges (sourceA2232 + difference 2 5) (sourceB2232 + difference 5 2) sourceC2232) = raw30655 := by
      apply Matrix.ext; unfold tripleCharges sourceA2232 sourceB2232 sourceC2232 difference raw30655; decide +kernel
    rw [ha]
    exact (canonical30655 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2232 + difference 3 0) (sourceB2232 + difference 0 3) sourceC2232) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4310) := by
    have ha : (tripleCharges (sourceA2232 + difference 3 0) (sourceB2232 + difference 0 3) sourceC2232) = raw23436 := by
      apply Matrix.ext; unfold tripleCharges sourceA2232 sourceB2232 sourceC2232 difference raw23436; decide +kernel
    rw [ha]
    exact (canonical23436 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2232 + difference 3 1) (sourceB2232 + difference 1 3) sourceC2232) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4920) := by
    have ha : (tripleCharges (sourceA2232 + difference 3 1) (sourceB2232 + difference 1 3) sourceC2232) = raw30656 := by
      apply Matrix.ext; unfold tripleCharges sourceA2232 sourceB2232 sourceC2232 difference raw30656; decide +kernel
    rw [ha]
    exact (canonical30656 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2232 + difference 3 2) (sourceB2232 + difference 2 3) sourceC2232) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5028) := by
    have ha : (tripleCharges (sourceA2232 + difference 3 2) (sourceB2232 + difference 2 3) sourceC2232) = raw30657 := by
      apply Matrix.ext; unfold tripleCharges sourceA2232 sourceB2232 sourceC2232 difference raw30657; decide +kernel
    rw [ha]
    exact (canonical30657 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2232 + difference 3 4) (sourceB2232 + difference 4 3) sourceC2232) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5105) := by
    have ha : (tripleCharges (sourceA2232 + difference 3 4) (sourceB2232 + difference 4 3) sourceC2232) = raw7604 := by
      apply Matrix.ext; unfold tripleCharges sourceA2232 sourceB2232 sourceC2232 difference raw7604; decide +kernel
    rw [ha]
    exact (canonical7604 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2232 + difference 3 5) (sourceB2232 + difference 5 3) sourceC2232) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5094) := by
    have ha : (tripleCharges (sourceA2232 + difference 3 5) (sourceB2232 + difference 5 3) sourceC2232) = raw30658 := by
      apply Matrix.ext; unfold tripleCharges sourceA2232 sourceB2232 sourceC2232 difference raw30658; decide +kernel
    rw [ha]
    exact (canonical30658 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2232 + difference 4 0) (sourceB2232 + difference 0 4) sourceC2232) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4316) := by
    have ha : (tripleCharges (sourceA2232 + difference 4 0) (sourceB2232 + difference 0 4) sourceC2232) = raw23440 := by
      apply Matrix.ext; unfold tripleCharges sourceA2232 sourceB2232 sourceC2232 difference raw23440; decide +kernel
    rw [ha]
    exact (canonical23440 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2232 + difference 4 1) (sourceB2232 + difference 1 4) sourceC2232) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4383) := by
    have ha : (tripleCharges (sourceA2232 + difference 4 1) (sourceB2232 + difference 1 4) sourceC2232) = raw30659 := by
      apply Matrix.ext; unfold tripleCharges sourceA2232 sourceB2232 sourceC2232 difference raw30659; decide +kernel
    rw [ha]
    exact (canonical30659 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2232 + difference 4 2) (sourceB2232 + difference 2 4) sourceC2232) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4380) := by
    have ha : (tripleCharges (sourceA2232 + difference 4 2) (sourceB2232 + difference 2 4) sourceC2232) = raw30660 := by
      apply Matrix.ext; unfold tripleCharges sourceA2232 sourceB2232 sourceC2232 difference raw30660; decide +kernel
    rw [ha]
    exact (canonical30660 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2232 + difference 4 3) (sourceB2232 + difference 3 4) sourceC2232) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4380) := by
    have ha : (tripleCharges (sourceA2232 + difference 4 3) (sourceB2232 + difference 3 4) sourceC2232) = raw30661 := by
      apply Matrix.ext; unfold tripleCharges sourceA2232 sourceB2232 sourceC2232 difference raw30661; decide +kernel
    rw [ha]
    exact (canonical30661 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2232 + difference 4 5) (sourceB2232 + difference 5 4) sourceC2232) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4490) := by
    have ha : (tripleCharges (sourceA2232 + difference 4 5) (sourceB2232 + difference 5 4) sourceC2232) = raw30662 := by
      apply Matrix.ext; unfold tripleCharges sourceA2232 sourceB2232 sourceC2232 difference raw30662; decide +kernel
    rw [ha]
    exact (canonical30662 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2232 + difference 5 0) (sourceB2232 + difference 0 5) sourceC2232) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4319) := by
    have ha : (tripleCharges (sourceA2232 + difference 5 0) (sourceB2232 + difference 0 5) sourceC2232) = raw21703 := by
      apply Matrix.ext; unfold tripleCharges sourceA2232 sourceB2232 sourceC2232 difference raw21703; decide +kernel
    rw [ha]
    exact (canonical21703 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2232 + difference 5 1) (sourceB2232 + difference 1 5) sourceC2232) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4925) := by
    have ha : (tripleCharges (sourceA2232 + difference 5 1) (sourceB2232 + difference 1 5) sourceC2232) = raw30663 := by
      apply Matrix.ext; unfold tripleCharges sourceA2232 sourceB2232 sourceC2232 difference raw30663; decide +kernel
    rw [ha]
    exact (canonical30663 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2232 + difference 5 2) (sourceB2232 + difference 2 5) sourceC2232) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4982) := by
    have ha : (tripleCharges (sourceA2232 + difference 5 2) (sourceB2232 + difference 2 5) sourceC2232) = raw30664 := by
      apply Matrix.ext; unfold tripleCharges sourceA2232 sourceB2232 sourceC2232 difference raw30664; decide +kernel
    rw [ha]
    exact (canonical30664 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2232 + difference 5 3) (sourceB2232 + difference 3 5) sourceC2232) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4982) := by
    have ha : (tripleCharges (sourceA2232 + difference 5 3) (sourceB2232 + difference 3 5) sourceC2232) = raw30665 := by
      apply Matrix.ext; unfold tripleCharges sourceA2232 sourceB2232 sourceC2232 difference raw30665; decide +kernel
    rw [ha]
    exact (canonical30665 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2232 + difference 5 4) (sourceB2232 + difference 4 5) sourceC2232) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5109) := by
    have ha : (tripleCharges (sourceA2232 + difference 5 4) (sourceB2232 + difference 4 5) sourceC2232) = raw7611 := by
      apply Matrix.ext; unfold tripleCharges sourceA2232 sourceB2232 sourceC2232 difference raw7611; decide +kernel
    rw [ha]
    exact (canonical7611 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2232 sourceB2232 sourceC2232
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2232, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2233 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2233 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceC2233 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceForm2233 : Integer.Sparse Master := [(Sum.inr 888, 2), (Sum.inr 894, 1), (Sum.inr 897, 1), (Sum.inr 1094, 1), (Sum.inr 1546, 2), (Sum.inr 1549, 1), (Sum.inr 1650, 1), (Sum.inr 2311, 2), (Sum.inr 2315, 1), (Sum.inr 2417, 2), (Sum.inr 2421, 2), (Sum.inr 2504, 2), (Sum.inr 2515, 2), (Sum.inr 2519, 1), (Sum.inr 2522, 2), (Sum.inr 2783, 1), (Sum.inr 2788, 1), (Sum.inr 3394, 2), (Sum.inr 3397, 1), (Sum.inr 3583, 1), (Sum.inr 3987, 1)]

theorem sourceEq2233 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2233 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2233 + difference 0 1) (sourceB2233 + difference 1 0) sourceC2233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3397) := by
    have ha : (tripleCharges (sourceA2233 + difference 0 1) (sourceB2233 + difference 1 0) sourceC2233) = raw30666 := by
      apply Matrix.ext; unfold tripleCharges sourceA2233 sourceB2233 sourceC2233 difference raw30666; decide +kernel
    rw [ha]
    exact (canonical30666 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2233 + difference 0 2) (sourceB2233 + difference 2 0) sourceC2233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3394) := by
    have ha : (tripleCharges (sourceA2233 + difference 0 2) (sourceB2233 + difference 2 0) sourceC2233) = raw30667 := by
      apply Matrix.ext; unfold tripleCharges sourceA2233 sourceB2233 sourceC2233 difference raw30667; decide +kernel
    rw [ha]
    exact (canonical30667 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2233 + difference 0 3) (sourceB2233 + difference 3 0) sourceC2233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3394) := by
    have ha : (tripleCharges (sourceA2233 + difference 0 3) (sourceB2233 + difference 3 0) sourceC2233) = raw30668 := by
      apply Matrix.ext; unfold tripleCharges sourceA2233 sourceB2233 sourceC2233 difference raw30668; decide +kernel
    rw [ha]
    exact (canonical30668 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2233 + difference 0 4) (sourceB2233 + difference 4 0) sourceC2233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3987) := by
    have ha : (tripleCharges (sourceA2233 + difference 0 4) (sourceB2233 + difference 4 0) sourceC2233) = raw7614 := by
      apply Matrix.ext; unfold tripleCharges sourceA2233 sourceB2233 sourceC2233 difference raw7614; decide +kernel
    rw [ha]
    exact (canonical7614 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2233 + difference 0 5) (sourceB2233 + difference 5 0) sourceC2233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3583) := by
    have ha : (tripleCharges (sourceA2233 + difference 0 5) (sourceB2233 + difference 5 0) sourceC2233) = raw30669 := by
      apply Matrix.ext; unfold tripleCharges sourceA2233 sourceB2233 sourceC2233 difference raw30669; decide +kernel
    rw [ha]
    exact (canonical30669 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2233 + difference 1 0) (sourceB2233 + difference 0 1) sourceC2233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1094) := by
    have ha : (tripleCharges (sourceA2233 + difference 1 0) (sourceB2233 + difference 0 1) sourceC2233) = raw7634 := by
      apply Matrix.ext; unfold tripleCharges sourceA2233 sourceB2233 sourceC2233 difference raw7634; decide +kernel
    rw [ha]
    exact (canonical7634 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2233 + difference 1 2) (sourceB2233 + difference 2 1) sourceC2233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2522) := by
    have ha : (tripleCharges (sourceA2233 + difference 1 2) (sourceB2233 + difference 2 1) sourceC2233) = raw7636 := by
      apply Matrix.ext; unfold tripleCharges sourceA2233 sourceB2233 sourceC2233 difference raw7636; decide +kernel
    rw [ha]
    exact (canonical7636 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2233 + difference 1 3) (sourceB2233 + difference 3 1) sourceC2233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2522) := by
    have ha : (tripleCharges (sourceA2233 + difference 1 3) (sourceB2233 + difference 3 1) sourceC2233) = raw7637 := by
      apply Matrix.ext; unfold tripleCharges sourceA2233 sourceB2233 sourceC2233 difference raw7637; decide +kernel
    rw [ha]
    exact (canonical7637 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2233 + difference 1 4) (sourceB2233 + difference 4 1) sourceC2233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2788) := by
    have ha : (tripleCharges (sourceA2233 + difference 1 4) (sourceB2233 + difference 4 1) sourceC2233) = raw21711 := by
      apply Matrix.ext; unfold tripleCharges sourceA2233 sourceB2233 sourceC2233 difference raw21711; decide +kernel
    rw [ha]
    exact (canonical21711 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2233 + difference 1 5) (sourceB2233 + difference 5 1) sourceC2233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2783) := by
    have ha : (tripleCharges (sourceA2233 + difference 1 5) (sourceB2233 + difference 5 1) sourceC2233) = raw7638 := by
      apply Matrix.ext; unfold tripleCharges sourceA2233 sourceB2233 sourceC2233 difference raw7638; decide +kernel
    rw [ha]
    exact (canonical7638 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2233 + difference 2 0) (sourceB2233 + difference 0 2) sourceC2233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 888) := by
    have ha : (tripleCharges (sourceA2233 + difference 2 0) (sourceB2233 + difference 0 2) sourceC2233) = raw23449 := by
      apply Matrix.ext; unfold tripleCharges sourceA2233 sourceB2233 sourceC2233 difference raw23449; decide +kernel
    rw [ha]
    exact (canonical23449 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2233 + difference 2 1) (sourceB2233 + difference 1 2) sourceC2233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2311) := by
    have ha : (tripleCharges (sourceA2233 + difference 2 1) (sourceB2233 + difference 1 2) sourceC2233) = raw30670 := by
      apply Matrix.ext; unfold tripleCharges sourceA2233 sourceB2233 sourceC2233 difference raw30670; decide +kernel
    rw [ha]
    exact (canonical30670 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2233 + difference 2 3) (sourceB2233 + difference 3 2) sourceC2233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2417) := by
    have ha : (tripleCharges (sourceA2233 + difference 2 3) (sourceB2233 + difference 3 2) sourceC2233) = raw30671 := by
      apply Matrix.ext; unfold tripleCharges sourceA2233 sourceB2233 sourceC2233 difference raw30671; decide +kernel
    rw [ha]
    exact (canonical30671 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2233 + difference 2 4) (sourceB2233 + difference 4 2) sourceC2233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2515) := by
    have ha : (tripleCharges (sourceA2233 + difference 2 4) (sourceB2233 + difference 4 2) sourceC2233) = raw7625 := by
      apply Matrix.ext; unfold tripleCharges sourceA2233 sourceB2233 sourceC2233 difference raw7625; decide +kernel
    rw [ha]
    exact (canonical7625 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2233 + difference 2 5) (sourceB2233 + difference 5 2) sourceC2233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2504) := by
    have ha : (tripleCharges (sourceA2233 + difference 2 5) (sourceB2233 + difference 5 2) sourceC2233) = raw30672 := by
      apply Matrix.ext; unfold tripleCharges sourceA2233 sourceB2233 sourceC2233 difference raw30672; decide +kernel
    rw [ha]
    exact (canonical30672 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2233 + difference 3 0) (sourceB2233 + difference 0 3) sourceC2233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 888) := by
    have ha : (tripleCharges (sourceA2233 + difference 3 0) (sourceB2233 + difference 0 3) sourceC2233) = raw23453 := by
      apply Matrix.ext; unfold tripleCharges sourceA2233 sourceB2233 sourceC2233 difference raw23453; decide +kernel
    rw [ha]
    exact (canonical23453 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2233 + difference 3 1) (sourceB2233 + difference 1 3) sourceC2233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2311) := by
    have ha : (tripleCharges (sourceA2233 + difference 3 1) (sourceB2233 + difference 1 3) sourceC2233) = raw30673 := by
      apply Matrix.ext; unfold tripleCharges sourceA2233 sourceB2233 sourceC2233 difference raw30673; decide +kernel
    rw [ha]
    exact (canonical30673 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2233 + difference 3 2) (sourceB2233 + difference 2 3) sourceC2233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2417) := by
    have ha : (tripleCharges (sourceA2233 + difference 3 2) (sourceB2233 + difference 2 3) sourceC2233) = raw30674 := by
      apply Matrix.ext; unfold tripleCharges sourceA2233 sourceB2233 sourceC2233 difference raw30674; decide +kernel
    rw [ha]
    exact (canonical30674 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2233 + difference 3 4) (sourceB2233 + difference 4 3) sourceC2233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2515) := by
    have ha : (tripleCharges (sourceA2233 + difference 3 4) (sourceB2233 + difference 4 3) sourceC2233) = raw7630 := by
      apply Matrix.ext; unfold tripleCharges sourceA2233 sourceB2233 sourceC2233 difference raw7630; decide +kernel
    rw [ha]
    exact (canonical7630 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2233 + difference 3 5) (sourceB2233 + difference 5 3) sourceC2233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2504) := by
    have ha : (tripleCharges (sourceA2233 + difference 3 5) (sourceB2233 + difference 5 3) sourceC2233) = raw30675 := by
      apply Matrix.ext; unfold tripleCharges sourceA2233 sourceB2233 sourceC2233 difference raw30675; decide +kernel
    rw [ha]
    exact (canonical30675 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2233 + difference 4 0) (sourceB2233 + difference 0 4) sourceC2233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 894) := by
    have ha : (tripleCharges (sourceA2233 + difference 4 0) (sourceB2233 + difference 0 4) sourceC2233) = raw23457 := by
      apply Matrix.ext; unfold tripleCharges sourceA2233 sourceB2233 sourceC2233 difference raw23457; decide +kernel
    rw [ha]
    exact (canonical23457 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2233 + difference 4 1) (sourceB2233 + difference 1 4) sourceC2233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1549) := by
    have ha : (tripleCharges (sourceA2233 + difference 4 1) (sourceB2233 + difference 1 4) sourceC2233) = raw30676 := by
      apply Matrix.ext; unfold tripleCharges sourceA2233 sourceB2233 sourceC2233 difference raw30676; decide +kernel
    rw [ha]
    exact (canonical30676 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2233 + difference 4 2) (sourceB2233 + difference 2 4) sourceC2233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1546) := by
    have ha : (tripleCharges (sourceA2233 + difference 4 2) (sourceB2233 + difference 2 4) sourceC2233) = raw30677 := by
      apply Matrix.ext; unfold tripleCharges sourceA2233 sourceB2233 sourceC2233 difference raw30677; decide +kernel
    rw [ha]
    exact (canonical30677 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2233 + difference 4 3) (sourceB2233 + difference 3 4) sourceC2233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1546) := by
    have ha : (tripleCharges (sourceA2233 + difference 4 3) (sourceB2233 + difference 3 4) sourceC2233) = raw30678 := by
      apply Matrix.ext; unfold tripleCharges sourceA2233 sourceB2233 sourceC2233 difference raw30678; decide +kernel
    rw [ha]
    exact (canonical30678 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2233 + difference 4 5) (sourceB2233 + difference 5 4) sourceC2233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1650) := by
    have ha : (tripleCharges (sourceA2233 + difference 4 5) (sourceB2233 + difference 5 4) sourceC2233) = raw30679 := by
      apply Matrix.ext; unfold tripleCharges sourceA2233 sourceB2233 sourceC2233 difference raw30679; decide +kernel
    rw [ha]
    exact (canonical30679 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2233 + difference 5 0) (sourceB2233 + difference 0 5) sourceC2233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 897) := by
    have ha : (tripleCharges (sourceA2233 + difference 5 0) (sourceB2233 + difference 0 5) sourceC2233) = raw21725 := by
      apply Matrix.ext; unfold tripleCharges sourceA2233 sourceB2233 sourceC2233 difference raw21725; decide +kernel
    rw [ha]
    exact (canonical21725 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2233 + difference 5 1) (sourceB2233 + difference 1 5) sourceC2233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2315) := by
    have ha : (tripleCharges (sourceA2233 + difference 5 1) (sourceB2233 + difference 1 5) sourceC2233) = raw30680 := by
      apply Matrix.ext; unfold tripleCharges sourceA2233 sourceB2233 sourceC2233 difference raw30680; decide +kernel
    rw [ha]
    exact (canonical30680 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2233 + difference 5 2) (sourceB2233 + difference 2 5) sourceC2233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2421) := by
    have ha : (tripleCharges (sourceA2233 + difference 5 2) (sourceB2233 + difference 2 5) sourceC2233) = raw30681 := by
      apply Matrix.ext; unfold tripleCharges sourceA2233 sourceB2233 sourceC2233 difference raw30681; decide +kernel
    rw [ha]
    exact (canonical30681 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2233 + difference 5 3) (sourceB2233 + difference 3 5) sourceC2233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2421) := by
    have ha : (tripleCharges (sourceA2233 + difference 5 3) (sourceB2233 + difference 3 5) sourceC2233) = raw30682 := by
      apply Matrix.ext; unfold tripleCharges sourceA2233 sourceB2233 sourceC2233 difference raw30682; decide +kernel
    rw [ha]
    exact (canonical30682 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2233 + difference 5 4) (sourceB2233 + difference 4 5) sourceC2233) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2519) := by
    have ha : (tripleCharges (sourceA2233 + difference 5 4) (sourceB2233 + difference 4 5) sourceC2233) = raw7640 := by
      apply Matrix.ext; unfold tripleCharges sourceA2233 sourceB2233 sourceC2233 difference raw7640; decide +kernel
    rw [ha]
    exact (canonical7640 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2233 sourceB2233 sourceC2233
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2233, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2234 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceB2234 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceC2234 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceForm2234 : Integer.Sparse Master := [(Sum.inr 4567, 2), (Sum.inr 4572, 1), (Sum.inr 4574, 1), (Sum.inr 4614, 1), (Sum.inr 4744, 2), (Sum.inr 4753, 1), (Sum.inr 4845, 1), (Sum.inr 5002, 2), (Sum.inr 5014, 2), (Sum.inr 5023, 1), (Sum.inr 5049, 2), (Sum.inr 5079, 2), (Sum.inr 5080, 2), (Sum.inr 5111, 1), (Sum.inr 5140, 2), (Sum.inr 5151, 2), (Sum.inr 5175, 2), (Sum.inr 5176, 2), (Sum.inr 5206, 1)]

theorem sourceEq2234 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2234 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2234 + difference 0 1) (sourceB2234 + difference 1 0) sourceC2234) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5206) := by
    have ha : (tripleCharges (sourceA2234 + difference 0 1) (sourceB2234 + difference 1 0) sourceC2234) = raw30683 := by
      apply Matrix.ext; unfold tripleCharges sourceA2234 sourceB2234 sourceC2234 difference raw30683; decide +kernel
    rw [ha]
    exact (canonical30683 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2234 + difference 0 2) (sourceB2234 + difference 2 0) sourceC2234) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5151) := by
    have ha : (tripleCharges (sourceA2234 + difference 0 2) (sourceB2234 + difference 2 0) sourceC2234) = raw30684 := by
      apply Matrix.ext; unfold tripleCharges sourceA2234 sourceB2234 sourceC2234 difference raw30684; decide +kernel
    rw [ha]
    exact (canonical30684 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2234 + difference 0 3) (sourceB2234 + difference 3 0) sourceC2234) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5151) := by
    have ha : (tripleCharges (sourceA2234 + difference 0 3) (sourceB2234 + difference 3 0) sourceC2234) = raw30685 := by
      apply Matrix.ext; unfold tripleCharges sourceA2234 sourceB2234 sourceC2234 difference raw30685; decide +kernel
    rw [ha]
    exact (canonical30685 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2234 + difference 0 4) (sourceB2234 + difference 4 0) sourceC2234) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5176) := by
    have ha : (tripleCharges (sourceA2234 + difference 0 4) (sourceB2234 + difference 4 0) sourceC2234) = raw30359 := by
      apply Matrix.ext; unfold tripleCharges sourceA2234 sourceB2234 sourceC2234 difference raw30359; decide +kernel
    rw [ha]
    exact (canonical30359 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2234 + difference 0 5) (sourceB2234 + difference 5 0) sourceC2234) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5175) := by
    have ha : (tripleCharges (sourceA2234 + difference 0 5) (sourceB2234 + difference 5 0) sourceC2234) = raw30686 := by
      apply Matrix.ext; unfold tripleCharges sourceA2234 sourceB2234 sourceC2234 difference raw30686; decide +kernel
    rw [ha]
    exact (canonical30686 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2234 + difference 1 0) (sourceB2234 + difference 0 1) sourceC2234) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4845) := by
    have ha : (tripleCharges (sourceA2234 + difference 1 0) (sourceB2234 + difference 0 1) sourceC2234) = raw30687 := by
      apply Matrix.ext; unfold tripleCharges sourceA2234 sourceB2234 sourceC2234 difference raw30687; decide +kernel
    rw [ha]
    exact (canonical30687 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2234 + difference 1 2) (sourceB2234 + difference 2 1) sourceC2234) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5140) := by
    have ha : (tripleCharges (sourceA2234 + difference 1 2) (sourceB2234 + difference 2 1) sourceC2234) = raw30688 := by
      apply Matrix.ext; unfold tripleCharges sourceA2234 sourceB2234 sourceC2234 difference raw30688; decide +kernel
    rw [ha]
    exact (canonical30688 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2234 + difference 1 3) (sourceB2234 + difference 3 1) sourceC2234) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5140) := by
    have ha : (tripleCharges (sourceA2234 + difference 1 3) (sourceB2234 + difference 3 1) sourceC2234) = raw30181 := by
      apply Matrix.ext; unfold tripleCharges sourceA2234 sourceB2234 sourceC2234 difference raw30181; decide +kernel
    rw [ha]
    exact (canonical30181 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2234 + difference 1 4) (sourceB2234 + difference 4 1) sourceC2234) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5176) := by
    have ha : (tripleCharges (sourceA2234 + difference 1 4) (sourceB2234 + difference 4 1) sourceC2234) = raw29694 := by
      apply Matrix.ext; unfold tripleCharges sourceA2234 sourceB2234 sourceC2234 difference raw29694; decide +kernel
    rw [ha]
    exact (canonical29694 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2234 + difference 1 5) (sourceB2234 + difference 5 1) sourceC2234) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5175) := by
    have ha : (tripleCharges (sourceA2234 + difference 1 5) (sourceB2234 + difference 5 1) sourceC2234) = raw30689 := by
      apply Matrix.ext; unfold tripleCharges sourceA2234 sourceB2234 sourceC2234 difference raw30689; decide +kernel
    rw [ha]
    exact (canonical30689 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2234 + difference 2 0) (sourceB2234 + difference 0 2) sourceC2234) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4744) := by
    have ha : (tripleCharges (sourceA2234 + difference 2 0) (sourceB2234 + difference 0 2) sourceC2234) = raw30375 := by
      apply Matrix.ext; unfold tripleCharges sourceA2234 sourceB2234 sourceC2234 difference raw30375; decide +kernel
    rw [ha]
    exact (canonical30375 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2234 + difference 2 1) (sourceB2234 + difference 1 2) sourceC2234) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5002) := by
    have ha : (tripleCharges (sourceA2234 + difference 2 1) (sourceB2234 + difference 1 2) sourceC2234) = raw30376 := by
      apply Matrix.ext; unfold tripleCharges sourceA2234 sourceB2234 sourceC2234 difference raw30376; decide +kernel
    rw [ha]
    exact (canonical30376 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2234 + difference 2 3) (sourceB2234 + difference 3 2) sourceC2234) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5049) := by
    have ha : (tripleCharges (sourceA2234 + difference 2 3) (sourceB2234 + difference 3 2) sourceC2234) = raw30378 := by
      apply Matrix.ext; unfold tripleCharges sourceA2234 sourceB2234 sourceC2234 difference raw30378; decide +kernel
    rw [ha]
    exact (canonical30378 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2234 + difference 2 4) (sourceB2234 + difference 4 2) sourceC2234) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5080) := by
    have ha : (tripleCharges (sourceA2234 + difference 2 4) (sourceB2234 + difference 4 2) sourceC2234) = raw30547 := by
      apply Matrix.ext; unfold tripleCharges sourceA2234 sourceB2234 sourceC2234 difference raw30547; decide +kernel
    rw [ha]
    exact (canonical30547 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2234 + difference 2 5) (sourceB2234 + difference 5 2) sourceC2234) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5079) := by
    have ha : (tripleCharges (sourceA2234 + difference 2 5) (sourceB2234 + difference 5 2) sourceC2234) = raw30379 := by
      apply Matrix.ext; unfold tripleCharges sourceA2234 sourceB2234 sourceC2234 difference raw30379; decide +kernel
    rw [ha]
    exact (canonical30379 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2234 + difference 3 0) (sourceB2234 + difference 0 3) sourceC2234) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4744) := by
    have ha : (tripleCharges (sourceA2234 + difference 3 0) (sourceB2234 + difference 0 3) sourceC2234) = raw30690 := by
      apply Matrix.ext; unfold tripleCharges sourceA2234 sourceB2234 sourceC2234 difference raw30690; decide +kernel
    rw [ha]
    exact (canonical30690 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2234 + difference 3 1) (sourceB2234 + difference 1 3) sourceC2234) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5002) := by
    have ha : (tripleCharges (sourceA2234 + difference 3 1) (sourceB2234 + difference 1 3) sourceC2234) = raw30691 := by
      apply Matrix.ext; unfold tripleCharges sourceA2234 sourceB2234 sourceC2234 difference raw30691; decide +kernel
    rw [ha]
    exact (canonical30691 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2234 + difference 3 2) (sourceB2234 + difference 2 3) sourceC2234) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5049) := by
    have ha : (tripleCharges (sourceA2234 + difference 3 2) (sourceB2234 + difference 2 3) sourceC2234) = raw30692 := by
      apply Matrix.ext; unfold tripleCharges sourceA2234 sourceB2234 sourceC2234 difference raw30692; decide +kernel
    rw [ha]
    exact (canonical30692 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2234 + difference 3 4) (sourceB2234 + difference 4 3) sourceC2234) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5080) := by
    have ha : (tripleCharges (sourceA2234 + difference 3 4) (sourceB2234 + difference 4 3) sourceC2234) = raw30372 := by
      apply Matrix.ext; unfold tripleCharges sourceA2234 sourceB2234 sourceC2234 difference raw30372; decide +kernel
    rw [ha]
    exact (canonical30372 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2234 + difference 3 5) (sourceB2234 + difference 5 3) sourceC2234) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5079) := by
    have ha : (tripleCharges (sourceA2234 + difference 3 5) (sourceB2234 + difference 5 3) sourceC2234) = raw30693 := by
      apply Matrix.ext; unfold tripleCharges sourceA2234 sourceB2234 sourceC2234 difference raw30693; decide +kernel
    rw [ha]
    exact (canonical30693 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2234 + difference 4 0) (sourceB2234 + difference 0 4) sourceC2234) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4572) := by
    have ha : (tripleCharges (sourceA2234 + difference 4 0) (sourceB2234 + difference 0 4) sourceC2234) = raw30694 := by
      apply Matrix.ext; unfold tripleCharges sourceA2234 sourceB2234 sourceC2234 difference raw30694; decide +kernel
    rw [ha]
    exact (canonical30694 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2234 + difference 4 1) (sourceB2234 + difference 1 4) sourceC2234) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4574) := by
    have ha : (tripleCharges (sourceA2234 + difference 4 1) (sourceB2234 + difference 1 4) sourceC2234) = raw30695 := by
      apply Matrix.ext; unfold tripleCharges sourceA2234 sourceB2234 sourceC2234 difference raw30695; decide +kernel
    rw [ha]
    exact (canonical30695 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2234 + difference 4 2) (sourceB2234 + difference 2 4) sourceC2234) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4567) := by
    have ha : (tripleCharges (sourceA2234 + difference 4 2) (sourceB2234 + difference 2 4) sourceC2234) = raw30696 := by
      apply Matrix.ext; unfold tripleCharges sourceA2234 sourceB2234 sourceC2234 difference raw30696; decide +kernel
    rw [ha]
    exact (canonical30696 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2234 + difference 4 3) (sourceB2234 + difference 3 4) sourceC2234) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4567) := by
    have ha : (tripleCharges (sourceA2234 + difference 4 3) (sourceB2234 + difference 3 4) sourceC2234) = raw30697 := by
      apply Matrix.ext; unfold tripleCharges sourceA2234 sourceB2234 sourceC2234 difference raw30697; decide +kernel
    rw [ha]
    exact (canonical30697 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2234 + difference 4 5) (sourceB2234 + difference 5 4) sourceC2234) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4614) := by
    have ha : (tripleCharges (sourceA2234 + difference 4 5) (sourceB2234 + difference 5 4) sourceC2234) = raw30698 := by
      apply Matrix.ext; unfold tripleCharges sourceA2234 sourceB2234 sourceC2234 difference raw30698; decide +kernel
    rw [ha]
    exact (canonical30698 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2234 + difference 5 0) (sourceB2234 + difference 0 5) sourceC2234) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4753) := by
    have ha : (tripleCharges (sourceA2234 + difference 5 0) (sourceB2234 + difference 0 5) sourceC2234) = raw30699 := by
      apply Matrix.ext; unfold tripleCharges sourceA2234 sourceB2234 sourceC2234 difference raw30699; decide +kernel
    rw [ha]
    exact (canonical30699 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2234 + difference 5 1) (sourceB2234 + difference 1 5) sourceC2234) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5023) := by
    have ha : (tripleCharges (sourceA2234 + difference 5 1) (sourceB2234 + difference 1 5) sourceC2234) = raw30700 := by
      apply Matrix.ext; unfold tripleCharges sourceA2234 sourceB2234 sourceC2234 difference raw30700; decide +kernel
    rw [ha]
    exact (canonical30700 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2234 + difference 5 2) (sourceB2234 + difference 2 5) sourceC2234) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5014) := by
    have ha : (tripleCharges (sourceA2234 + difference 5 2) (sourceB2234 + difference 2 5) sourceC2234) = raw30701 := by
      apply Matrix.ext; unfold tripleCharges sourceA2234 sourceB2234 sourceC2234 difference raw30701; decide +kernel
    rw [ha]
    exact (canonical30701 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2234 + difference 5 3) (sourceB2234 + difference 3 5) sourceC2234) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5014) := by
    have ha : (tripleCharges (sourceA2234 + difference 5 3) (sourceB2234 + difference 3 5) sourceC2234) = raw30178 := by
      apply Matrix.ext; unfold tripleCharges sourceA2234 sourceB2234 sourceC2234 difference raw30178; decide +kernel
    rw [ha]
    exact (canonical30178 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2234 + difference 5 4) (sourceB2234 + difference 4 5) sourceC2234) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5111) := by
    have ha : (tripleCharges (sourceA2234 + difference 5 4) (sourceB2234 + difference 4 5) sourceC2234) = raw29691 := by
      apply Matrix.ext; unfold tripleCharges sourceA2234 sourceB2234 sourceC2234 difference raw29691; decide +kernel
    rw [ha]
    exact (canonical29691 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2234 sourceB2234 sourceC2234
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2234, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2235 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2235 : Charge := ![1, 0, 0, 0, 0, -1]
def sourceC2235 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceForm2235 : Integer.Sparse Master := [(Sum.inr 4092, 1), (Sum.inr 4549, 2), (Sum.inr 4558, 1), (Sum.inr 4559, 1), (Sum.inr 4612, 1), (Sum.inr 4943, 2), (Sum.inr 4946, 2), (Sum.inr 4952, 1), (Sum.inr 4953, 1), (Sum.inr 4972, 2), (Sum.inr 5036, 2), (Sum.inr 5101, 2), (Sum.inr 5102, 2), (Sum.inr 5107, 1), (Sum.inr 5109, 1), (Sum.inr 5141, 2), (Sum.inr 5274, 1), (Sum.inr 5275, 1), (Sum.inr 5367, 2), (Sum.inr 5371, 1), (Sum.inr 5413, 1)]

theorem sourceEq2235 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2235 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2235 + difference 0 1) (sourceB2235 + difference 1 0) sourceC2235) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5371) := by
    have ha : (tripleCharges (sourceA2235 + difference 0 1) (sourceB2235 + difference 1 0) sourceC2235) = raw30702 := by
      apply Matrix.ext; unfold tripleCharges sourceA2235 sourceB2235 sourceC2235 difference raw30702; decide +kernel
    rw [ha]
    exact (canonical30702 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2235 + difference 0 2) (sourceB2235 + difference 2 0) sourceC2235) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5367) := by
    have ha : (tripleCharges (sourceA2235 + difference 0 2) (sourceB2235 + difference 2 0) sourceC2235) = raw30703 := by
      apply Matrix.ext; unfold tripleCharges sourceA2235 sourceB2235 sourceC2235 difference raw30703; decide +kernel
    rw [ha]
    exact (canonical30703 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2235 + difference 0 3) (sourceB2235 + difference 3 0) sourceC2235) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5367) := by
    have ha : (tripleCharges (sourceA2235 + difference 0 3) (sourceB2235 + difference 3 0) sourceC2235) = raw30704 := by
      apply Matrix.ext; unfold tripleCharges sourceA2235 sourceB2235 sourceC2235 difference raw30704; decide +kernel
    rw [ha]
    exact (canonical30704 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2235 + difference 0 4) (sourceB2235 + difference 4 0) sourceC2235) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5413) := by
    have ha : (tripleCharges (sourceA2235 + difference 0 4) (sourceB2235 + difference 4 0) sourceC2235) = raw30705 := by
      apply Matrix.ext; unfold tripleCharges sourceA2235 sourceB2235 sourceC2235 difference raw30705; decide +kernel
    rw [ha]
    exact (canonical30705 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2235 + difference 0 5) (sourceB2235 + difference 5 0) sourceC2235) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA2235 + difference 0 5) (sourceB2235 + difference 5 0) sourceC2235) = raw30706 := by
      apply Matrix.ext; unfold tripleCharges sourceA2235 sourceB2235 sourceC2235 difference raw30706; decide +kernel
    rw [ha]
    exact (canonical30706 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2235 + difference 1 0) (sourceB2235 + difference 0 1) sourceC2235) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA2235 + difference 1 0) (sourceB2235 + difference 0 1) sourceC2235) = raw30707 := by
      apply Matrix.ext; unfold tripleCharges sourceA2235 sourceB2235 sourceC2235 difference raw30707; decide +kernel
    rw [ha]
    exact (canonical30707 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2235 + difference 1 2) (sourceB2235 + difference 2 1) sourceC2235) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA2235 + difference 1 2) (sourceB2235 + difference 2 1) sourceC2235) = raw30708 := by
      apply Matrix.ext; unfold tripleCharges sourceA2235 sourceB2235 sourceC2235 difference raw30708; decide +kernel
    rw [ha]
    exact (canonical30708 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2235 + difference 1 3) (sourceB2235 + difference 3 1) sourceC2235) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5141) := by
    have ha : (tripleCharges (sourceA2235 + difference 1 3) (sourceB2235 + difference 3 1) sourceC2235) = raw30709 := by
      apply Matrix.ext; unfold tripleCharges sourceA2235 sourceB2235 sourceC2235 difference raw30709; decide +kernel
    rw [ha]
    exact (canonical30709 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2235 + difference 1 4) (sourceB2235 + difference 4 1) sourceC2235) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5275) := by
    have ha : (tripleCharges (sourceA2235 + difference 1 4) (sourceB2235 + difference 4 1) sourceC2235) = raw3936 := by
      apply Matrix.ext; unfold tripleCharges sourceA2235 sourceB2235 sourceC2235 difference raw3936; decide +kernel
    rw [ha]
    exact (canonical3936 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2235 + difference 1 5) (sourceB2235 + difference 5 1) sourceC2235) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5274) := by
    have ha : (tripleCharges (sourceA2235 + difference 1 5) (sourceB2235 + difference 5 1) sourceC2235) = raw30710 := by
      apply Matrix.ext; unfold tripleCharges sourceA2235 sourceB2235 sourceC2235 difference raw30710; decide +kernel
    rw [ha]
    exact (canonical30710 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2235 + difference 2 0) (sourceB2235 + difference 0 2) sourceC2235) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4549) := by
    have ha : (tripleCharges (sourceA2235 + difference 2 0) (sourceB2235 + difference 0 2) sourceC2235) = raw30711 := by
      apply Matrix.ext; unfold tripleCharges sourceA2235 sourceB2235 sourceC2235 difference raw30711; decide +kernel
    rw [ha]
    exact (canonical30711 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2235 + difference 2 1) (sourceB2235 + difference 1 2) sourceC2235) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4946) := by
    have ha : (tripleCharges (sourceA2235 + difference 2 1) (sourceB2235 + difference 1 2) sourceC2235) = raw30712 := by
      apply Matrix.ext; unfold tripleCharges sourceA2235 sourceB2235 sourceC2235 difference raw30712; decide +kernel
    rw [ha]
    exact (canonical30712 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2235 + difference 2 3) (sourceB2235 + difference 3 2) sourceC2235) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5036) := by
    have ha : (tripleCharges (sourceA2235 + difference 2 3) (sourceB2235 + difference 3 2) sourceC2235) = raw30713 := by
      apply Matrix.ext; unfold tripleCharges sourceA2235 sourceB2235 sourceC2235 difference raw30713; decide +kernel
    rw [ha]
    exact (canonical30713 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2235 + difference 2 4) (sourceB2235 + difference 4 2) sourceC2235) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5102) := by
    have ha : (tripleCharges (sourceA2235 + difference 2 4) (sourceB2235 + difference 4 2) sourceC2235) = raw30714 := by
      apply Matrix.ext; unfold tripleCharges sourceA2235 sourceB2235 sourceC2235 difference raw30714; decide +kernel
    rw [ha]
    exact (canonical30714 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2235 + difference 2 5) (sourceB2235 + difference 5 2) sourceC2235) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5101) := by
    have ha : (tripleCharges (sourceA2235 + difference 2 5) (sourceB2235 + difference 5 2) sourceC2235) = raw30715 := by
      apply Matrix.ext; unfold tripleCharges sourceA2235 sourceB2235 sourceC2235 difference raw30715; decide +kernel
    rw [ha]
    exact (canonical30715 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2235 + difference 3 0) (sourceB2235 + difference 0 3) sourceC2235) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4549) := by
    have ha : (tripleCharges (sourceA2235 + difference 3 0) (sourceB2235 + difference 0 3) sourceC2235) = raw30716 := by
      apply Matrix.ext; unfold tripleCharges sourceA2235 sourceB2235 sourceC2235 difference raw30716; decide +kernel
    rw [ha]
    exact (canonical30716 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2235 + difference 3 1) (sourceB2235 + difference 1 3) sourceC2235) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4946) := by
    have ha : (tripleCharges (sourceA2235 + difference 3 1) (sourceB2235 + difference 1 3) sourceC2235) = raw30717 := by
      apply Matrix.ext; unfold tripleCharges sourceA2235 sourceB2235 sourceC2235 difference raw30717; decide +kernel
    rw [ha]
    exact (canonical30717 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2235 + difference 3 2) (sourceB2235 + difference 2 3) sourceC2235) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5036) := by
    have ha : (tripleCharges (sourceA2235 + difference 3 2) (sourceB2235 + difference 2 3) sourceC2235) = raw30718 := by
      apply Matrix.ext; unfold tripleCharges sourceA2235 sourceB2235 sourceC2235 difference raw30718; decide +kernel
    rw [ha]
    exact (canonical30718 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2235 + difference 3 4) (sourceB2235 + difference 4 3) sourceC2235) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5102) := by
    have ha : (tripleCharges (sourceA2235 + difference 3 4) (sourceB2235 + difference 4 3) sourceC2235) = raw30719 := by
      apply Matrix.ext; unfold tripleCharges sourceA2235 sourceB2235 sourceC2235 difference raw30719; decide +kernel
    rw [ha]
    exact (canonical30719 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2235 + difference 3 5) (sourceB2235 + difference 5 3) sourceC2235) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5101) := by
    have ha : (tripleCharges (sourceA2235 + difference 3 5) (sourceB2235 + difference 5 3) sourceC2235) = raw30720 := by
      apply Matrix.ext; unfold tripleCharges sourceA2235 sourceB2235 sourceC2235 difference raw30720; decide +kernel
    rw [ha]
    exact (canonical30720 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2235 + difference 4 0) (sourceB2235 + difference 0 4) sourceC2235) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4558) := by
    have ha : (tripleCharges (sourceA2235 + difference 4 0) (sourceB2235 + difference 0 4) sourceC2235) = raw30721 := by
      apply Matrix.ext; unfold tripleCharges sourceA2235 sourceB2235 sourceC2235 difference raw30721; decide +kernel
    rw [ha]
    exact (canonical30721 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2235 + difference 4 1) (sourceB2235 + difference 1 4) sourceC2235) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4952) := by
    have ha : (tripleCharges (sourceA2235 + difference 4 1) (sourceB2235 + difference 1 4) sourceC2235) = raw30722 := by
      apply Matrix.ext; unfold tripleCharges sourceA2235 sourceB2235 sourceC2235 difference raw30722; decide +kernel
    rw [ha]
    exact (canonical30722 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2235 + difference 4 2) (sourceB2235 + difference 2 4) sourceC2235) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4943) := by
    have ha : (tripleCharges (sourceA2235 + difference 4 2) (sourceB2235 + difference 2 4) sourceC2235) = raw30723 := by
      apply Matrix.ext; unfold tripleCharges sourceA2235 sourceB2235 sourceC2235 difference raw30723; decide +kernel
    rw [ha]
    exact (canonical30723 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2235 + difference 4 3) (sourceB2235 + difference 3 4) sourceC2235) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4943) := by
    have ha : (tripleCharges (sourceA2235 + difference 4 3) (sourceB2235 + difference 3 4) sourceC2235) = raw30724 := by
      apply Matrix.ext; unfold tripleCharges sourceA2235 sourceB2235 sourceC2235 difference raw30724; decide +kernel
    rw [ha]
    exact (canonical30724 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2235 + difference 4 5) (sourceB2235 + difference 5 4) sourceC2235) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5107) := by
    have ha : (tripleCharges (sourceA2235 + difference 4 5) (sourceB2235 + difference 5 4) sourceC2235) = raw30725 := by
      apply Matrix.ext; unfold tripleCharges sourceA2235 sourceB2235 sourceC2235 difference raw30725; decide +kernel
    rw [ha]
    exact (canonical30725 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2235 + difference 5 0) (sourceB2235 + difference 0 5) sourceC2235) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4559) := by
    have ha : (tripleCharges (sourceA2235 + difference 5 0) (sourceB2235 + difference 0 5) sourceC2235) = raw30726 := by
      apply Matrix.ext; unfold tripleCharges sourceA2235 sourceB2235 sourceC2235 difference raw30726; decide +kernel
    rw [ha]
    exact (canonical30726 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2235 + difference 5 1) (sourceB2235 + difference 1 5) sourceC2235) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4953) := by
    have ha : (tripleCharges (sourceA2235 + difference 5 1) (sourceB2235 + difference 1 5) sourceC2235) = raw30727 := by
      apply Matrix.ext; unfold tripleCharges sourceA2235 sourceB2235 sourceC2235 difference raw30727; decide +kernel
    rw [ha]
    exact (canonical30727 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2235 + difference 5 2) (sourceB2235 + difference 2 5) sourceC2235) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4972) := by
    have ha : (tripleCharges (sourceA2235 + difference 5 2) (sourceB2235 + difference 2 5) sourceC2235) = raw30728 := by
      apply Matrix.ext; unfold tripleCharges sourceA2235 sourceB2235 sourceC2235 difference raw30728; decide +kernel
    rw [ha]
    exact (canonical30728 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2235 + difference 5 3) (sourceB2235 + difference 3 5) sourceC2235) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4972) := by
    have ha : (tripleCharges (sourceA2235 + difference 5 3) (sourceB2235 + difference 3 5) sourceC2235) = raw30729 := by
      apply Matrix.ext; unfold tripleCharges sourceA2235 sourceB2235 sourceC2235 difference raw30729; decide +kernel
    rw [ha]
    exact (canonical30729 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2235 + difference 5 4) (sourceB2235 + difference 4 5) sourceC2235) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5109) := by
    have ha : (tripleCharges (sourceA2235 + difference 5 4) (sourceB2235 + difference 4 5) sourceC2235) = raw3933 := by
      apply Matrix.ext; unfold tripleCharges sourceA2235 sourceB2235 sourceC2235 difference raw3933; decide +kernel
    rw [ha]
    exact (canonical3933 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2235 sourceB2235 sourceC2235
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2235, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2236 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2236 : Charge := ![1, 0, 0, 0, 0, -1]
def sourceC2236 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceForm2236 : Integer.Sparse Master := [(Sum.inr 3265, 2), (Sum.inr 3276, 1), (Sum.inr 3277, 1), (Sum.inr 3301, 1), (Sum.inr 3411, 2), (Sum.inr 3412, 2), (Sum.inr 3422, 1), (Sum.inr 3423, 1), (Sum.inr 3450, 2), (Sum.inr 3457, 2), (Sum.inr 3470, 2), (Sum.inr 3471, 2), (Sum.inr 3484, 1), (Sum.inr 3486, 1), (Sum.inr 3522, 2), (Sum.inr 3547, 1), (Sum.inr 3548, 1), (Sum.inr 3766, 2), (Sum.inr 3775, 1), (Sum.inr 3817, 1), (Sum.inr 4092, 1)]

theorem sourceEq2236 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2236 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2236 + difference 0 1) (sourceB2236 + difference 1 0) sourceC2236) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3775) := by
    have ha : (tripleCharges (sourceA2236 + difference 0 1) (sourceB2236 + difference 1 0) sourceC2236) = raw30730 := by
      apply Matrix.ext; unfold tripleCharges sourceA2236 sourceB2236 sourceC2236 difference raw30730; decide +kernel
    rw [ha]
    exact (canonical30730 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2236 + difference 0 2) (sourceB2236 + difference 2 0) sourceC2236) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3766) := by
    have ha : (tripleCharges (sourceA2236 + difference 0 2) (sourceB2236 + difference 2 0) sourceC2236) = raw30731 := by
      apply Matrix.ext; unfold tripleCharges sourceA2236 sourceB2236 sourceC2236 difference raw30731; decide +kernel
    rw [ha]
    exact (canonical30731 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2236 + difference 0 3) (sourceB2236 + difference 3 0) sourceC2236) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3766) := by
    have ha : (tripleCharges (sourceA2236 + difference 0 3) (sourceB2236 + difference 3 0) sourceC2236) = raw30732 := by
      apply Matrix.ext; unfold tripleCharges sourceA2236 sourceB2236 sourceC2236 difference raw30732; decide +kernel
    rw [ha]
    exact (canonical30732 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2236 + difference 0 4) (sourceB2236 + difference 4 0) sourceC2236) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3817) := by
    have ha : (tripleCharges (sourceA2236 + difference 0 4) (sourceB2236 + difference 4 0) sourceC2236) = raw30733 := by
      apply Matrix.ext; unfold tripleCharges sourceA2236 sourceB2236 sourceC2236 difference raw30733; decide +kernel
    rw [ha]
    exact (canonical30733 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2236 + difference 0 5) (sourceB2236 + difference 5 0) sourceC2236) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (tripleCharges (sourceA2236 + difference 0 5) (sourceB2236 + difference 5 0) sourceC2236) = raw30734 := by
      apply Matrix.ext; unfold tripleCharges sourceA2236 sourceB2236 sourceC2236 difference raw30734; decide +kernel
    rw [ha]
    exact (canonical30734 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2236 + difference 1 0) (sourceB2236 + difference 0 1) sourceC2236) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3301) := by
    have ha : (tripleCharges (sourceA2236 + difference 1 0) (sourceB2236 + difference 0 1) sourceC2236) = raw30735 := by
      apply Matrix.ext; unfold tripleCharges sourceA2236 sourceB2236 sourceC2236 difference raw30735; decide +kernel
    rw [ha]
    exact (canonical30735 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2236 + difference 1 2) (sourceB2236 + difference 2 1) sourceC2236) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3522) := by
    have ha : (tripleCharges (sourceA2236 + difference 1 2) (sourceB2236 + difference 2 1) sourceC2236) = raw30736 := by
      apply Matrix.ext; unfold tripleCharges sourceA2236 sourceB2236 sourceC2236 difference raw30736; decide +kernel
    rw [ha]
    exact (canonical30736 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2236 + difference 1 3) (sourceB2236 + difference 3 1) sourceC2236) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3522) := by
    have ha : (tripleCharges (sourceA2236 + difference 1 3) (sourceB2236 + difference 3 1) sourceC2236) = raw30737 := by
      apply Matrix.ext; unfold tripleCharges sourceA2236 sourceB2236 sourceC2236 difference raw30737; decide +kernel
    rw [ha]
    exact (canonical30737 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2236 + difference 1 4) (sourceB2236 + difference 4 1) sourceC2236) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3548) := by
    have ha : (tripleCharges (sourceA2236 + difference 1 4) (sourceB2236 + difference 4 1) sourceC2236) = raw3996 := by
      apply Matrix.ext; unfold tripleCharges sourceA2236 sourceB2236 sourceC2236 difference raw3996; decide +kernel
    rw [ha]
    exact (canonical3996 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2236 + difference 1 5) (sourceB2236 + difference 5 1) sourceC2236) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3547) := by
    have ha : (tripleCharges (sourceA2236 + difference 1 5) (sourceB2236 + difference 5 1) sourceC2236) = raw30738 := by
      apply Matrix.ext; unfold tripleCharges sourceA2236 sourceB2236 sourceC2236 difference raw30738; decide +kernel
    rw [ha]
    exact (canonical30738 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2236 + difference 2 0) (sourceB2236 + difference 0 2) sourceC2236) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3265) := by
    have ha : (tripleCharges (sourceA2236 + difference 2 0) (sourceB2236 + difference 0 2) sourceC2236) = raw30739 := by
      apply Matrix.ext; unfold tripleCharges sourceA2236 sourceB2236 sourceC2236 difference raw30739; decide +kernel
    rw [ha]
    exact (canonical30739 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2236 + difference 2 1) (sourceB2236 + difference 1 2) sourceC2236) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3412) := by
    have ha : (tripleCharges (sourceA2236 + difference 2 1) (sourceB2236 + difference 1 2) sourceC2236) = raw30740 := by
      apply Matrix.ext; unfold tripleCharges sourceA2236 sourceB2236 sourceC2236 difference raw30740; decide +kernel
    rw [ha]
    exact (canonical30740 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2236 + difference 2 3) (sourceB2236 + difference 3 2) sourceC2236) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3450) := by
    have ha : (tripleCharges (sourceA2236 + difference 2 3) (sourceB2236 + difference 3 2) sourceC2236) = raw30741 := by
      apply Matrix.ext; unfold tripleCharges sourceA2236 sourceB2236 sourceC2236 difference raw30741; decide +kernel
    rw [ha]
    exact (canonical30741 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2236 + difference 2 4) (sourceB2236 + difference 4 2) sourceC2236) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3471) := by
    have ha : (tripleCharges (sourceA2236 + difference 2 4) (sourceB2236 + difference 4 2) sourceC2236) = raw30742 := by
      apply Matrix.ext; unfold tripleCharges sourceA2236 sourceB2236 sourceC2236 difference raw30742; decide +kernel
    rw [ha]
    exact (canonical30742 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2236 + difference 2 5) (sourceB2236 + difference 5 2) sourceC2236) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3470) := by
    have ha : (tripleCharges (sourceA2236 + difference 2 5) (sourceB2236 + difference 5 2) sourceC2236) = raw30743 := by
      apply Matrix.ext; unfold tripleCharges sourceA2236 sourceB2236 sourceC2236 difference raw30743; decide +kernel
    rw [ha]
    exact (canonical30743 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2236 + difference 3 0) (sourceB2236 + difference 0 3) sourceC2236) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3265) := by
    have ha : (tripleCharges (sourceA2236 + difference 3 0) (sourceB2236 + difference 0 3) sourceC2236) = raw30744 := by
      apply Matrix.ext; unfold tripleCharges sourceA2236 sourceB2236 sourceC2236 difference raw30744; decide +kernel
    rw [ha]
    exact (canonical30744 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2236 + difference 3 1) (sourceB2236 + difference 1 3) sourceC2236) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3412) := by
    have ha : (tripleCharges (sourceA2236 + difference 3 1) (sourceB2236 + difference 1 3) sourceC2236) = raw30745 := by
      apply Matrix.ext; unfold tripleCharges sourceA2236 sourceB2236 sourceC2236 difference raw30745; decide +kernel
    rw [ha]
    exact (canonical30745 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2236 + difference 3 2) (sourceB2236 + difference 2 3) sourceC2236) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3450) := by
    have ha : (tripleCharges (sourceA2236 + difference 3 2) (sourceB2236 + difference 2 3) sourceC2236) = raw30746 := by
      apply Matrix.ext; unfold tripleCharges sourceA2236 sourceB2236 sourceC2236 difference raw30746; decide +kernel
    rw [ha]
    exact (canonical30746 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2236 + difference 3 4) (sourceB2236 + difference 4 3) sourceC2236) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3471) := by
    have ha : (tripleCharges (sourceA2236 + difference 3 4) (sourceB2236 + difference 4 3) sourceC2236) = raw30747 := by
      apply Matrix.ext; unfold tripleCharges sourceA2236 sourceB2236 sourceC2236 difference raw30747; decide +kernel
    rw [ha]
    exact (canonical30747 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2236 + difference 3 5) (sourceB2236 + difference 5 3) sourceC2236) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3470) := by
    have ha : (tripleCharges (sourceA2236 + difference 3 5) (sourceB2236 + difference 5 3) sourceC2236) = raw30748 := by
      apply Matrix.ext; unfold tripleCharges sourceA2236 sourceB2236 sourceC2236 difference raw30748; decide +kernel
    rw [ha]
    exact (canonical30748 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2236 + difference 4 0) (sourceB2236 + difference 0 4) sourceC2236) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3276) := by
    have ha : (tripleCharges (sourceA2236 + difference 4 0) (sourceB2236 + difference 0 4) sourceC2236) = raw30749 := by
      apply Matrix.ext; unfold tripleCharges sourceA2236 sourceB2236 sourceC2236 difference raw30749; decide +kernel
    rw [ha]
    exact (canonical30749 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2236 + difference 4 1) (sourceB2236 + difference 1 4) sourceC2236) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3422) := by
    have ha : (tripleCharges (sourceA2236 + difference 4 1) (sourceB2236 + difference 1 4) sourceC2236) = raw30750 := by
      apply Matrix.ext; unfold tripleCharges sourceA2236 sourceB2236 sourceC2236 difference raw30750; decide +kernel
    rw [ha]
    exact (canonical30750 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2236 + difference 4 2) (sourceB2236 + difference 2 4) sourceC2236) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3411) := by
    have ha : (tripleCharges (sourceA2236 + difference 4 2) (sourceB2236 + difference 2 4) sourceC2236) = raw30751 := by
      apply Matrix.ext; unfold tripleCharges sourceA2236 sourceB2236 sourceC2236 difference raw30751; decide +kernel
    rw [ha]
    exact (canonical30751 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2236 + difference 4 3) (sourceB2236 + difference 3 4) sourceC2236) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3411) := by
    have ha : (tripleCharges (sourceA2236 + difference 4 3) (sourceB2236 + difference 3 4) sourceC2236) = raw30752 := by
      apply Matrix.ext; unfold tripleCharges sourceA2236 sourceB2236 sourceC2236 difference raw30752; decide +kernel
    rw [ha]
    exact (canonical30752 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2236 + difference 4 5) (sourceB2236 + difference 5 4) sourceC2236) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3484) := by
    have ha : (tripleCharges (sourceA2236 + difference 4 5) (sourceB2236 + difference 5 4) sourceC2236) = raw30753 := by
      apply Matrix.ext; unfold tripleCharges sourceA2236 sourceB2236 sourceC2236 difference raw30753; decide +kernel
    rw [ha]
    exact (canonical30753 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2236 + difference 5 0) (sourceB2236 + difference 0 5) sourceC2236) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3277) := by
    have ha : (tripleCharges (sourceA2236 + difference 5 0) (sourceB2236 + difference 0 5) sourceC2236) = raw30754 := by
      apply Matrix.ext; unfold tripleCharges sourceA2236 sourceB2236 sourceC2236 difference raw30754; decide +kernel
    rw [ha]
    exact (canonical30754 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2236 + difference 5 1) (sourceB2236 + difference 1 5) sourceC2236) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3423) := by
    have ha : (tripleCharges (sourceA2236 + difference 5 1) (sourceB2236 + difference 1 5) sourceC2236) = raw30755 := by
      apply Matrix.ext; unfold tripleCharges sourceA2236 sourceB2236 sourceC2236 difference raw30755; decide +kernel
    rw [ha]
    exact (canonical30755 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2236 + difference 5 2) (sourceB2236 + difference 2 5) sourceC2236) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3457) := by
    have ha : (tripleCharges (sourceA2236 + difference 5 2) (sourceB2236 + difference 2 5) sourceC2236) = raw30756 := by
      apply Matrix.ext; unfold tripleCharges sourceA2236 sourceB2236 sourceC2236 difference raw30756; decide +kernel
    rw [ha]
    exact (canonical30756 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2236 + difference 5 3) (sourceB2236 + difference 3 5) sourceC2236) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3457) := by
    have ha : (tripleCharges (sourceA2236 + difference 5 3) (sourceB2236 + difference 3 5) sourceC2236) = raw30757 := by
      apply Matrix.ext; unfold tripleCharges sourceA2236 sourceB2236 sourceC2236 difference raw30757; decide +kernel
    rw [ha]
    exact (canonical30757 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2236 + difference 5 4) (sourceB2236 + difference 4 5) sourceC2236) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3486) := by
    have ha : (tripleCharges (sourceA2236 + difference 5 4) (sourceB2236 + difference 4 5) sourceC2236) = raw3993 := by
      apply Matrix.ext; unfold tripleCharges sourceA2236 sourceB2236 sourceC2236 difference raw3993; decide +kernel
    rw [ha]
    exact (canonical3993 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2236 sourceB2236 sourceC2236
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2236, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2237 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2237 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceC2237 : Charge := ![2, 1, 0, 1, -3, -1]
def sourceForm2237 : Integer.Sparse Master := [(Sum.inr 1777, 1), (Sum.inr 2413, 1), (Sum.inr 2421, 1), (Sum.inr 2467, 2), (Sum.inr 3356, 1), (Sum.inr 4080, -1)]

theorem sourceEq2237 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2237 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2237 + difference 0 3) (sourceB2237 + difference 3 0) sourceC2237) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3356) := by
    have ha : (tripleCharges (sourceA2237 + difference 0 3) (sourceB2237 + difference 3 0) sourceC2237) = raw30758 := by
      apply Matrix.ext; unfold tripleCharges sourceA2237 sourceB2237 sourceC2237 difference raw30758; decide +kernel
    rw [ha]
    exact (canonical30758 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2237 + difference 1 3) (sourceB2237 + difference 3 1) sourceC2237) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2467) := by
    have ha : (tripleCharges (sourceA2237 + difference 1 3) (sourceB2237 + difference 3 1) sourceC2237) = raw30759 := by
      apply Matrix.ext; unfold tripleCharges sourceA2237 sourceB2237 sourceC2237 difference raw30759; decide +kernel
    rw [ha]
    exact (canonical30759 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2237 + difference 2 3) (sourceB2237 + difference 3 2) sourceC2237) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2413) := by
    have ha : (tripleCharges (sourceA2237 + difference 2 3) (sourceB2237 + difference 3 2) sourceC2237) = raw30760 := by
      apply Matrix.ext; unfold tripleCharges sourceA2237 sourceB2237 sourceC2237 difference raw30760; decide +kernel
    rw [ha]
    exact (canonical30760 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2237 + difference 3 3) (sourceB2237 + difference 3 3) sourceC2237) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2467) := by
    have ha : (tripleCharges (sourceA2237 + difference 3 3) (sourceB2237 + difference 3 3) sourceC2237) = raw30761 := by
      apply Matrix.ext; unfold tripleCharges sourceA2237 sourceB2237 sourceC2237 difference raw30761; decide +kernel
    rw [ha]
    exact (canonical30761 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2237 + difference 4 3) (sourceB2237 + difference 3 4) sourceC2237) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1777) := by
    have ha : (tripleCharges (sourceA2237 + difference 4 3) (sourceB2237 + difference 3 4) sourceC2237) = raw30762 := by
      apply Matrix.ext; unfold tripleCharges sourceA2237 sourceB2237 sourceC2237 difference raw30762; decide +kernel
    rw [ha]
    exact (canonical30762 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2237 + difference 5 3) (sourceB2237 + difference 3 5) sourceC2237) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2421) := by
    have ha : (tripleCharges (sourceA2237 + difference 5 3) (sourceB2237 + difference 3 5) sourceC2237) = raw30763 := by
      apply Matrix.ext; unfold tripleCharges sourceA2237 sourceB2237 sourceC2237 difference raw30763; decide +kernel
    rw [ha]
    exact (canonical30763 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2237 + sourceB2237) sourceC2237) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA2237 + sourceB2237) sourceC2237) = raw30764 := by
      apply Matrix.ext; unfold doubleCharges sourceA2237 sourceB2237 sourceC2237 raw30764; decide +kernel
    rw [ha]
    exact (canonical30764 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2237 sourceB2237 sourceC2237
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2237, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2238 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2238 : Charge := ![1, 0, 0, -1, 0, 0]
def sourceC2238 : Charge := ![2, 1, 0, 1, -2, -2]
def sourceForm2238 : Integer.Sparse Master := [(Sum.inr 4088, 1), (Sum.inr 4522, 1), (Sum.inr 4526, 2), (Sum.inr 4539, 1), (Sum.inr 4586, 1), (Sum.inr 4902, 2), (Sum.inr 4907, 2), (Sum.inr 4918, 2), (Sum.inr 4926, 1), (Sum.inr 4937, 1), (Sum.inr 5000, 2), (Sum.inr 5025, 1), (Sum.inr 5032, 1), (Sum.inr 5056, 2), (Sum.inr 5063, 1), (Sum.inr 5095, 2), (Sum.inr 5126, 1), (Sum.inr 5248, 2), (Sum.inr 5323, 1), (Sum.inr 5327, 1), (Sum.inr 5367, 2)]

theorem sourceEq2238 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2238 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2238 + difference 0 1) (sourceB2238 + difference 1 0) sourceC2238) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5327) := by
    have ha : (tripleCharges (sourceA2238 + difference 0 1) (sourceB2238 + difference 1 0) sourceC2238) = raw30765 := by
      apply Matrix.ext; unfold tripleCharges sourceA2238 sourceB2238 sourceC2238 difference raw30765; decide +kernel
    rw [ha]
    exact (canonical30765 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2238 + difference 0 2) (sourceB2238 + difference 2 0) sourceC2238) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5323) := by
    have ha : (tripleCharges (sourceA2238 + difference 0 2) (sourceB2238 + difference 2 0) sourceC2238) = raw30766 := by
      apply Matrix.ext; unfold tripleCharges sourceA2238 sourceB2238 sourceC2238 difference raw30766; decide +kernel
    rw [ha]
    exact (canonical30766 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2238 + difference 0 3) (sourceB2238 + difference 3 0) sourceC2238) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2238 + difference 0 3) (sourceB2238 + difference 3 0) sourceC2238) = raw30767 := by
      apply Matrix.ext; unfold tripleCharges sourceA2238 sourceB2238 sourceC2238 difference raw30767; decide +kernel
    rw [ha]
    exact (canonical30767 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2238 + difference 0 4) (sourceB2238 + difference 4 0) sourceC2238) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5367) := by
    have ha : (tripleCharges (sourceA2238 + difference 0 4) (sourceB2238 + difference 4 0) sourceC2238) = raw30768 := by
      apply Matrix.ext; unfold tripleCharges sourceA2238 sourceB2238 sourceC2238 difference raw30768; decide +kernel
    rw [ha]
    exact (canonical30768 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2238 + difference 0 5) (sourceB2238 + difference 5 0) sourceC2238) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5367) := by
    have ha : (tripleCharges (sourceA2238 + difference 0 5) (sourceB2238 + difference 5 0) sourceC2238) = raw30769 := by
      apply Matrix.ext; unfold tripleCharges sourceA2238 sourceB2238 sourceC2238 difference raw30769; decide +kernel
    rw [ha]
    exact (canonical30769 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2238 + difference 1 0) (sourceB2238 + difference 0 1) sourceC2238) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4586) := by
    have ha : (tripleCharges (sourceA2238 + difference 1 0) (sourceB2238 + difference 0 1) sourceC2238) = raw30770 := by
      apply Matrix.ext; unfold tripleCharges sourceA2238 sourceB2238 sourceC2238 difference raw30770; decide +kernel
    rw [ha]
    exact (canonical30770 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2238 + difference 1 2) (sourceB2238 + difference 2 1) sourceC2238) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5126) := by
    have ha : (tripleCharges (sourceA2238 + difference 1 2) (sourceB2238 + difference 2 1) sourceC2238) = raw30771 := by
      apply Matrix.ext; unfold tripleCharges sourceA2238 sourceB2238 sourceC2238 difference raw30771; decide +kernel
    rw [ha]
    exact (canonical30771 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2238 + difference 1 3) (sourceB2238 + difference 3 1) sourceC2238) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5063) := by
    have ha : (tripleCharges (sourceA2238 + difference 1 3) (sourceB2238 + difference 3 1) sourceC2238) = raw30772 := by
      apply Matrix.ext; unfold tripleCharges sourceA2238 sourceB2238 sourceC2238 difference raw30772; decide +kernel
    rw [ha]
    exact (canonical30772 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2238 + difference 1 4) (sourceB2238 + difference 4 1) sourceC2238) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5248) := by
    have ha : (tripleCharges (sourceA2238 + difference 1 4) (sourceB2238 + difference 4 1) sourceC2238) = raw30773 := by
      apply Matrix.ext; unfold tripleCharges sourceA2238 sourceB2238 sourceC2238 difference raw30773; decide +kernel
    rw [ha]
    exact (canonical30773 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2238 + difference 1 5) (sourceB2238 + difference 5 1) sourceC2238) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5248) := by
    have ha : (tripleCharges (sourceA2238 + difference 1 5) (sourceB2238 + difference 5 1) sourceC2238) = raw30774 := by
      apply Matrix.ext; unfold tripleCharges sourceA2238 sourceB2238 sourceC2238 difference raw30774; decide +kernel
    rw [ha]
    exact (canonical30774 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2238 + difference 2 0) (sourceB2238 + difference 0 2) sourceC2238) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4522) := by
    have ha : (tripleCharges (sourceA2238 + difference 2 0) (sourceB2238 + difference 0 2) sourceC2238) = raw30775 := by
      apply Matrix.ext; unfold tripleCharges sourceA2238 sourceB2238 sourceC2238 difference raw30775; decide +kernel
    rw [ha]
    exact (canonical30775 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2238 + difference 2 1) (sourceB2238 + difference 1 2) sourceC2238) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4926) := by
    have ha : (tripleCharges (sourceA2238 + difference 2 1) (sourceB2238 + difference 1 2) sourceC2238) = raw30776 := by
      apply Matrix.ext; unfold tripleCharges sourceA2238 sourceB2238 sourceC2238 difference raw30776; decide +kernel
    rw [ha]
    exact (canonical30776 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2238 + difference 2 3) (sourceB2238 + difference 3 2) sourceC2238) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5025) := by
    have ha : (tripleCharges (sourceA2238 + difference 2 3) (sourceB2238 + difference 3 2) sourceC2238) = raw30777 := by
      apply Matrix.ext; unfold tripleCharges sourceA2238 sourceB2238 sourceC2238 difference raw30777; decide +kernel
    rw [ha]
    exact (canonical30777 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2238 + difference 2 4) (sourceB2238 + difference 4 2) sourceC2238) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5056) := by
    have ha : (tripleCharges (sourceA2238 + difference 2 4) (sourceB2238 + difference 4 2) sourceC2238) = raw30778 := by
      apply Matrix.ext; unfold tripleCharges sourceA2238 sourceB2238 sourceC2238 difference raw30778; decide +kernel
    rw [ha]
    exact (canonical30778 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2238 + difference 2 5) (sourceB2238 + difference 5 2) sourceC2238) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5056) := by
    have ha : (tripleCharges (sourceA2238 + difference 2 5) (sourceB2238 + difference 5 2) sourceC2238) = raw30779 := by
      apply Matrix.ext; unfold tripleCharges sourceA2238 sourceB2238 sourceC2238 difference raw30779; decide +kernel
    rw [ha]
    exact (canonical30779 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2238 + difference 3 0) (sourceB2238 + difference 0 3) sourceC2238) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4539) := by
    have ha : (tripleCharges (sourceA2238 + difference 3 0) (sourceB2238 + difference 0 3) sourceC2238) = raw30780 := by
      apply Matrix.ext; unfold tripleCharges sourceA2238 sourceB2238 sourceC2238 difference raw30780; decide +kernel
    rw [ha]
    exact (canonical30780 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2238 + difference 3 1) (sourceB2238 + difference 1 3) sourceC2238) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4937) := by
    have ha : (tripleCharges (sourceA2238 + difference 3 1) (sourceB2238 + difference 1 3) sourceC2238) = raw30781 := by
      apply Matrix.ext; unfold tripleCharges sourceA2238 sourceB2238 sourceC2238 difference raw30781; decide +kernel
    rw [ha]
    exact (canonical30781 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2238 + difference 3 2) (sourceB2238 + difference 2 3) sourceC2238) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5032) := by
    have ha : (tripleCharges (sourceA2238 + difference 3 2) (sourceB2238 + difference 2 3) sourceC2238) = raw30782 := by
      apply Matrix.ext; unfold tripleCharges sourceA2238 sourceB2238 sourceC2238 difference raw30782; decide +kernel
    rw [ha]
    exact (canonical30782 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2238 + difference 3 4) (sourceB2238 + difference 4 3) sourceC2238) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5095) := by
    have ha : (tripleCharges (sourceA2238 + difference 3 4) (sourceB2238 + difference 4 3) sourceC2238) = raw30783 := by
      apply Matrix.ext; unfold tripleCharges sourceA2238 sourceB2238 sourceC2238 difference raw30783; decide +kernel
    rw [ha]
    exact (canonical30783 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2238 + difference 3 5) (sourceB2238 + difference 5 3) sourceC2238) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5095) := by
    have ha : (tripleCharges (sourceA2238 + difference 3 5) (sourceB2238 + difference 5 3) sourceC2238) = raw30784 := by
      apply Matrix.ext; unfold tripleCharges sourceA2238 sourceB2238 sourceC2238 difference raw30784; decide +kernel
    rw [ha]
    exact (canonical30784 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2238 + difference 4 0) (sourceB2238 + difference 0 4) sourceC2238) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4526) := by
    have ha : (tripleCharges (sourceA2238 + difference 4 0) (sourceB2238 + difference 0 4) sourceC2238) = raw30785 := by
      apply Matrix.ext; unfold tripleCharges sourceA2238 sourceB2238 sourceC2238 difference raw30785; decide +kernel
    rw [ha]
    exact (canonical30785 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2238 + difference 4 1) (sourceB2238 + difference 1 4) sourceC2238) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4907) := by
    have ha : (tripleCharges (sourceA2238 + difference 4 1) (sourceB2238 + difference 1 4) sourceC2238) = raw30786 := by
      apply Matrix.ext; unfold tripleCharges sourceA2238 sourceB2238 sourceC2238 difference raw30786; decide +kernel
    rw [ha]
    exact (canonical30786 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2238 + difference 4 2) (sourceB2238 + difference 2 4) sourceC2238) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4902) := by
    have ha : (tripleCharges (sourceA2238 + difference 4 2) (sourceB2238 + difference 2 4) sourceC2238) = raw30787 := by
      apply Matrix.ext; unfold tripleCharges sourceA2238 sourceB2238 sourceC2238 difference raw30787; decide +kernel
    rw [ha]
    exact (canonical30787 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2238 + difference 4 3) (sourceB2238 + difference 3 4) sourceC2238) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4918) := by
    have ha : (tripleCharges (sourceA2238 + difference 4 3) (sourceB2238 + difference 3 4) sourceC2238) = raw30788 := by
      apply Matrix.ext; unfold tripleCharges sourceA2238 sourceB2238 sourceC2238 difference raw30788; decide +kernel
    rw [ha]
    exact (canonical30788 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2238 + difference 4 5) (sourceB2238 + difference 5 4) sourceC2238) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5000) := by
    have ha : (tripleCharges (sourceA2238 + difference 4 5) (sourceB2238 + difference 5 4) sourceC2238) = raw30789 := by
      apply Matrix.ext; unfold tripleCharges sourceA2238 sourceB2238 sourceC2238 difference raw30789; decide +kernel
    rw [ha]
    exact (canonical30789 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2238 + difference 5 0) (sourceB2238 + difference 0 5) sourceC2238) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4526) := by
    have ha : (tripleCharges (sourceA2238 + difference 5 0) (sourceB2238 + difference 0 5) sourceC2238) = raw30790 := by
      apply Matrix.ext; unfold tripleCharges sourceA2238 sourceB2238 sourceC2238 difference raw30790; decide +kernel
    rw [ha]
    exact (canonical30790 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2238 + difference 5 1) (sourceB2238 + difference 1 5) sourceC2238) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4907) := by
    have ha : (tripleCharges (sourceA2238 + difference 5 1) (sourceB2238 + difference 1 5) sourceC2238) = raw30791 := by
      apply Matrix.ext; unfold tripleCharges sourceA2238 sourceB2238 sourceC2238 difference raw30791; decide +kernel
    rw [ha]
    exact (canonical30791 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2238 + difference 5 2) (sourceB2238 + difference 2 5) sourceC2238) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4902) := by
    have ha : (tripleCharges (sourceA2238 + difference 5 2) (sourceB2238 + difference 2 5) sourceC2238) = raw30792 := by
      apply Matrix.ext; unfold tripleCharges sourceA2238 sourceB2238 sourceC2238 difference raw30792; decide +kernel
    rw [ha]
    exact (canonical30792 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2238 + difference 5 3) (sourceB2238 + difference 3 5) sourceC2238) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4918) := by
    have ha : (tripleCharges (sourceA2238 + difference 5 3) (sourceB2238 + difference 3 5) sourceC2238) = raw30793 := by
      apply Matrix.ext; unfold tripleCharges sourceA2238 sourceB2238 sourceC2238 difference raw30793; decide +kernel
    rw [ha]
    exact (canonical30793 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2238 + difference 5 4) (sourceB2238 + difference 4 5) sourceC2238) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5000) := by
    have ha : (tripleCharges (sourceA2238 + difference 5 4) (sourceB2238 + difference 4 5) sourceC2238) = raw30794 := by
      apply Matrix.ext; unfold tripleCharges sourceA2238 sourceB2238 sourceC2238 difference raw30794; decide +kernel
    rw [ha]
    exact (canonical30794 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2238 sourceB2238 sourceC2238
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2238, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2239 : Charge := ![-3, -1, 0, 0, 2, 2]
def sourceB2239 : Charge := ![1, 0, 0, -1, 0, 0]
def sourceC2239 : Charge := ![2, 1, 0, 1, -2, -2]
def sourceForm2239 : Integer.Sparse Master := [(Sum.inr 3249, 1), (Sum.inr 3252, 2), (Sum.inr 3254, 1), (Sum.inr 3284, 1), (Sum.inr 3315, 2), (Sum.inr 3325, 2), (Sum.inr 3327, 2), (Sum.inr 3353, 2), (Sum.inr 3398, 1), (Sum.inr 3402, 1), (Sum.inr 3424, 1), (Sum.inr 3429, 2), (Sum.inr 3439, 1), (Sum.inr 3440, 1), (Sum.inr 3448, 2), (Sum.inr 3487, 1), (Sum.inr 3498, 2), (Sum.inr 3650, 1), (Sum.inr 3664, 1), (Sum.inr 3704, 2), (Sum.inr 4088, 1)]

theorem sourceEq2239 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2239 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2239 + difference 0 1) (sourceB2239 + difference 1 0) sourceC2239) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3664) := by
    have ha : (tripleCharges (sourceA2239 + difference 0 1) (sourceB2239 + difference 1 0) sourceC2239) = raw30795 := by
      apply Matrix.ext; unfold tripleCharges sourceA2239 sourceB2239 sourceC2239 difference raw30795; decide +kernel
    rw [ha]
    exact (canonical30795 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2239 + difference 0 2) (sourceB2239 + difference 2 0) sourceC2239) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3650) := by
    have ha : (tripleCharges (sourceA2239 + difference 0 2) (sourceB2239 + difference 2 0) sourceC2239) = raw30796 := by
      apply Matrix.ext; unfold tripleCharges sourceA2239 sourceB2239 sourceC2239 difference raw30796; decide +kernel
    rw [ha]
    exact (canonical30796 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2239 + difference 0 3) (sourceB2239 + difference 3 0) sourceC2239) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (tripleCharges (sourceA2239 + difference 0 3) (sourceB2239 + difference 3 0) sourceC2239) = raw30797 := by
      apply Matrix.ext; unfold tripleCharges sourceA2239 sourceB2239 sourceC2239 difference raw30797; decide +kernel
    rw [ha]
    exact (canonical30797 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2239 + difference 0 4) (sourceB2239 + difference 4 0) sourceC2239) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3704) := by
    have ha : (tripleCharges (sourceA2239 + difference 0 4) (sourceB2239 + difference 4 0) sourceC2239) = raw30798 := by
      apply Matrix.ext; unfold tripleCharges sourceA2239 sourceB2239 sourceC2239 difference raw30798; decide +kernel
    rw [ha]
    exact (canonical30798 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2239 + difference 0 5) (sourceB2239 + difference 5 0) sourceC2239) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3704) := by
    have ha : (tripleCharges (sourceA2239 + difference 0 5) (sourceB2239 + difference 5 0) sourceC2239) = raw30799 := by
      apply Matrix.ext; unfold tripleCharges sourceA2239 sourceB2239 sourceC2239 difference raw30799; decide +kernel
    rw [ha]
    exact (canonical30799 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2239 + difference 1 0) (sourceB2239 + difference 0 1) sourceC2239) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3284) := by
    have ha : (tripleCharges (sourceA2239 + difference 1 0) (sourceB2239 + difference 0 1) sourceC2239) = raw30800 := by
      apply Matrix.ext; unfold tripleCharges sourceA2239 sourceB2239 sourceC2239 difference raw30800; decide +kernel
    rw [ha]
    exact (canonical30800 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA2239 + difference 1 2) (sourceB2239 + difference 2 1) sourceC2239) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3487) := by
    have ha : (tripleCharges (sourceA2239 + difference 1 2) (sourceB2239 + difference 2 1) sourceC2239) = raw30801 := by
      apply Matrix.ext; unfold tripleCharges sourceA2239 sourceB2239 sourceC2239 difference raw30801; decide +kernel
    rw [ha]
    exact (canonical30801 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA2239 + difference 1 3) (sourceB2239 + difference 3 1) sourceC2239) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3439) := by
    have ha : (tripleCharges (sourceA2239 + difference 1 3) (sourceB2239 + difference 3 1) sourceC2239) = raw30802 := by
      apply Matrix.ext; unfold tripleCharges sourceA2239 sourceB2239 sourceC2239 difference raw30802; decide +kernel
    rw [ha]
    exact (canonical30802 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA2239 + difference 1 4) (sourceB2239 + difference 4 1) sourceC2239) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3498) := by
    have ha : (tripleCharges (sourceA2239 + difference 1 4) (sourceB2239 + difference 4 1) sourceC2239) = raw30803 := by
      apply Matrix.ext; unfold tripleCharges sourceA2239 sourceB2239 sourceC2239 difference raw30803; decide +kernel
    rw [ha]
    exact (canonical30803 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA2239 + difference 1 5) (sourceB2239 + difference 5 1) sourceC2239) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3498) := by
    have ha : (tripleCharges (sourceA2239 + difference 1 5) (sourceB2239 + difference 5 1) sourceC2239) = raw30804 := by
      apply Matrix.ext; unfold tripleCharges sourceA2239 sourceB2239 sourceC2239 difference raw30804; decide +kernel
    rw [ha]
    exact (canonical30804 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA2239 + difference 2 0) (sourceB2239 + difference 0 2) sourceC2239) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3249) := by
    have ha : (tripleCharges (sourceA2239 + difference 2 0) (sourceB2239 + difference 0 2) sourceC2239) = raw30805 := by
      apply Matrix.ext; unfold tripleCharges sourceA2239 sourceB2239 sourceC2239 difference raw30805; decide +kernel
    rw [ha]
    exact (canonical30805 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA2239 + difference 2 1) (sourceB2239 + difference 1 2) sourceC2239) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3398) := by
    have ha : (tripleCharges (sourceA2239 + difference 2 1) (sourceB2239 + difference 1 2) sourceC2239) = raw30806 := by
      apply Matrix.ext; unfold tripleCharges sourceA2239 sourceB2239 sourceC2239 difference raw30806; decide +kernel
    rw [ha]
    exact (canonical30806 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA2239 + difference 2 3) (sourceB2239 + difference 3 2) sourceC2239) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3424) := by
    have ha : (tripleCharges (sourceA2239 + difference 2 3) (sourceB2239 + difference 3 2) sourceC2239) = raw30807 := by
      apply Matrix.ext; unfold tripleCharges sourceA2239 sourceB2239 sourceC2239 difference raw30807; decide +kernel
    rw [ha]
    exact (canonical30807 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA2239 + difference 2 4) (sourceB2239 + difference 4 2) sourceC2239) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3429) := by
    have ha : (tripleCharges (sourceA2239 + difference 2 4) (sourceB2239 + difference 4 2) sourceC2239) = raw30808 := by
      apply Matrix.ext; unfold tripleCharges sourceA2239 sourceB2239 sourceC2239 difference raw30808; decide +kernel
    rw [ha]
    exact (canonical30808 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA2239 + difference 2 5) (sourceB2239 + difference 5 2) sourceC2239) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3429) := by
    have ha : (tripleCharges (sourceA2239 + difference 2 5) (sourceB2239 + difference 5 2) sourceC2239) = raw30809 := by
      apply Matrix.ext; unfold tripleCharges sourceA2239 sourceB2239 sourceC2239 difference raw30809; decide +kernel
    rw [ha]
    exact (canonical30809 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA2239 + difference 3 0) (sourceB2239 + difference 0 3) sourceC2239) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3254) := by
    have ha : (tripleCharges (sourceA2239 + difference 3 0) (sourceB2239 + difference 0 3) sourceC2239) = raw30810 := by
      apply Matrix.ext; unfold tripleCharges sourceA2239 sourceB2239 sourceC2239 difference raw30810; decide +kernel
    rw [ha]
    exact (canonical30810 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA2239 + difference 3 1) (sourceB2239 + difference 1 3) sourceC2239) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3402) := by
    have ha : (tripleCharges (sourceA2239 + difference 3 1) (sourceB2239 + difference 1 3) sourceC2239) = raw30811 := by
      apply Matrix.ext; unfold tripleCharges sourceA2239 sourceB2239 sourceC2239 difference raw30811; decide +kernel
    rw [ha]
    exact (canonical30811 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA2239 + difference 3 2) (sourceB2239 + difference 2 3) sourceC2239) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3440) := by
    have ha : (tripleCharges (sourceA2239 + difference 3 2) (sourceB2239 + difference 2 3) sourceC2239) = raw30812 := by
      apply Matrix.ext; unfold tripleCharges sourceA2239 sourceB2239 sourceC2239 difference raw30812; decide +kernel
    rw [ha]
    exact (canonical30812 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA2239 + difference 3 4) (sourceB2239 + difference 4 3) sourceC2239) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3448) := by
    have ha : (tripleCharges (sourceA2239 + difference 3 4) (sourceB2239 + difference 4 3) sourceC2239) = raw30813 := by
      apply Matrix.ext; unfold tripleCharges sourceA2239 sourceB2239 sourceC2239 difference raw30813; decide +kernel
    rw [ha]
    exact (canonical30813 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA2239 + difference 3 5) (sourceB2239 + difference 5 3) sourceC2239) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3448) := by
    have ha : (tripleCharges (sourceA2239 + difference 3 5) (sourceB2239 + difference 5 3) sourceC2239) = raw30814 := by
      apply Matrix.ext; unfold tripleCharges sourceA2239 sourceB2239 sourceC2239 difference raw30814; decide +kernel
    rw [ha]
    exact (canonical30814 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA2239 + difference 4 0) (sourceB2239 + difference 0 4) sourceC2239) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3252) := by
    have ha : (tripleCharges (sourceA2239 + difference 4 0) (sourceB2239 + difference 0 4) sourceC2239) = raw30815 := by
      apply Matrix.ext; unfold tripleCharges sourceA2239 sourceB2239 sourceC2239 difference raw30815; decide +kernel
    rw [ha]
    exact (canonical30815 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA2239 + difference 4 1) (sourceB2239 + difference 1 4) sourceC2239) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3325) := by
    have ha : (tripleCharges (sourceA2239 + difference 4 1) (sourceB2239 + difference 1 4) sourceC2239) = raw30816 := by
      apply Matrix.ext; unfold tripleCharges sourceA2239 sourceB2239 sourceC2239 difference raw30816; decide +kernel
    rw [ha]
    exact (canonical30816 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA2239 + difference 4 2) (sourceB2239 + difference 2 4) sourceC2239) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3315) := by
    have ha : (tripleCharges (sourceA2239 + difference 4 2) (sourceB2239 + difference 2 4) sourceC2239) = raw30817 := by
      apply Matrix.ext; unfold tripleCharges sourceA2239 sourceB2239 sourceC2239 difference raw30817; decide +kernel
    rw [ha]
    exact (canonical30817 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA2239 + difference 4 3) (sourceB2239 + difference 3 4) sourceC2239) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3327) := by
    have ha : (tripleCharges (sourceA2239 + difference 4 3) (sourceB2239 + difference 3 4) sourceC2239) = raw30818 := by
      apply Matrix.ext; unfold tripleCharges sourceA2239 sourceB2239 sourceC2239 difference raw30818; decide +kernel
    rw [ha]
    exact (canonical30818 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA2239 + difference 4 5) (sourceB2239 + difference 5 4) sourceC2239) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3353) := by
    have ha : (tripleCharges (sourceA2239 + difference 4 5) (sourceB2239 + difference 5 4) sourceC2239) = raw30819 := by
      apply Matrix.ext; unfold tripleCharges sourceA2239 sourceB2239 sourceC2239 difference raw30819; decide +kernel
    rw [ha]
    exact (canonical30819 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA2239 + difference 5 0) (sourceB2239 + difference 0 5) sourceC2239) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3252) := by
    have ha : (tripleCharges (sourceA2239 + difference 5 0) (sourceB2239 + difference 0 5) sourceC2239) = raw30820 := by
      apply Matrix.ext; unfold tripleCharges sourceA2239 sourceB2239 sourceC2239 difference raw30820; decide +kernel
    rw [ha]
    exact (canonical30820 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA2239 + difference 5 1) (sourceB2239 + difference 1 5) sourceC2239) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3325) := by
    have ha : (tripleCharges (sourceA2239 + difference 5 1) (sourceB2239 + difference 1 5) sourceC2239) = raw30821 := by
      apply Matrix.ext; unfold tripleCharges sourceA2239 sourceB2239 sourceC2239 difference raw30821; decide +kernel
    rw [ha]
    exact (canonical30821 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA2239 + difference 5 2) (sourceB2239 + difference 2 5) sourceC2239) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3315) := by
    have ha : (tripleCharges (sourceA2239 + difference 5 2) (sourceB2239 + difference 2 5) sourceC2239) = raw30822 := by
      apply Matrix.ext; unfold tripleCharges sourceA2239 sourceB2239 sourceC2239 difference raw30822; decide +kernel
    rw [ha]
    exact (canonical30822 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA2239 + difference 5 3) (sourceB2239 + difference 3 5) sourceC2239) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3327) := by
    have ha : (tripleCharges (sourceA2239 + difference 5 3) (sourceB2239 + difference 3 5) sourceC2239) = raw30823 := by
      apply Matrix.ext; unfold tripleCharges sourceA2239 sourceB2239 sourceC2239 difference raw30823; decide +kernel
    rw [ha]
    exact (canonical30823 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA2239 + difference 5 4) (sourceB2239 + difference 4 5) sourceC2239) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3353) := by
    have ha : (tripleCharges (sourceA2239 + difference 5 4) (sourceB2239 + difference 4 5) sourceC2239) = raw30824 := by
      apply Matrix.ext; unfold tripleCharges sourceA2239 sourceB2239 sourceC2239 difference raw30824; decide +kernel
    rw [ha]
    exact (canonical30824 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA2239 sourceB2239 sourceC2239
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm2239, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
