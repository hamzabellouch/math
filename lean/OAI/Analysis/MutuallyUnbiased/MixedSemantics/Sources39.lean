import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical94
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical152
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical153
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical154
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical157
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical158
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical159
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical160

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA1248 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1248 : Charge := ![2, -1, 0, 1, -1, -1]
def sourceC1248 : Charge := ![2, 1, 0, -1, 0, -2]
def sourceForm1248 : Integer.Sparse Master := [(Sum.inr 626, 1), (Sum.inr 1131, 1), (Sum.inr 1148, 1), (Sum.inr 1215, 1), (Sum.inr 1236, 1), (Sum.inr 1242, 1), (Sum.inr 4092, -1)]

theorem sourceEq1248 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1248 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1248 + difference 3 0) (sourceB1248 + difference 0 3) sourceC1248) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 626) := by
    have ha : (tripleCharges (sourceA1248 + difference 3 0) (sourceB1248 + difference 0 3) sourceC1248) = raw20284 := by
      apply Matrix.ext; unfold tripleCharges sourceA1248 sourceB1248 sourceC1248 difference raw20284; decide +kernel
    rw [ha]
    exact (canonical20284 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1248 + difference 3 1) (sourceB1248 + difference 1 3) sourceC1248) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1131) := by
    have ha : (tripleCharges (sourceA1248 + difference 3 1) (sourceB1248 + difference 1 3) sourceC1248) = raw20280 := by
      apply Matrix.ext; unfold tripleCharges sourceA1248 sourceB1248 sourceC1248 difference raw20280; decide +kernel
    rw [ha]
    exact (canonical20280 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1248 + difference 3 2) (sourceB1248 + difference 2 3) sourceC1248) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1148) := by
    have ha : (tripleCharges (sourceA1248 + difference 3 2) (sourceB1248 + difference 2 3) sourceC1248) = raw20285 := by
      apply Matrix.ext; unfold tripleCharges sourceA1248 sourceB1248 sourceC1248 difference raw20285; decide +kernel
    rw [ha]
    exact (canonical20285 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1248 + difference 3 3) (sourceB1248 + difference 3 3) sourceC1248) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1215) := by
    have ha : (tripleCharges (sourceA1248 + difference 3 3) (sourceB1248 + difference 3 3) sourceC1248) = raw20278 := by
      apply Matrix.ext; unfold tripleCharges sourceA1248 sourceB1248 sourceC1248 difference raw20278; decide +kernel
    rw [ha]
    exact (canonical20278 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1248 + difference 3 4) (sourceB1248 + difference 4 3) sourceC1248) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1242) := by
    have ha : (tripleCharges (sourceA1248 + difference 3 4) (sourceB1248 + difference 4 3) sourceC1248) = raw20286 := by
      apply Matrix.ext; unfold tripleCharges sourceA1248 sourceB1248 sourceC1248 difference raw20286; decide +kernel
    rw [ha]
    exact (canonical20286 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1248 + difference 3 5) (sourceB1248 + difference 5 3) sourceC1248) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1236) := by
    have ha : (tripleCharges (sourceA1248 + difference 3 5) (sourceB1248 + difference 5 3) sourceC1248) = raw20287 := by
      apply Matrix.ext; unfold tripleCharges sourceA1248 sourceB1248 sourceC1248 difference raw20287; decide +kernel
    rw [ha]
    exact (canonical20287 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1248 + sourceB1248) sourceC1248) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1248 + sourceB1248) sourceC1248) = raw20283 := by
      apply Matrix.ext; unfold doubleCharges sourceA1248 sourceB1248 sourceC1248 raw20283; decide +kernel
    rw [ha]
    exact (canonical20283 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1248 sourceB1248 sourceC1248
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1248, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1249 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1249 : Charge := ![2, 1, 0, -1, 0, -2]
def sourceC1249 : Charge := ![2, -1, 0, 1, -1, -1]
def sourceForm1249 : Integer.Sparse Master := [(Sum.inr 630, 1), (Sum.inr 1136, 1), (Sum.inr 1150, 1), (Sum.inr 1217, 2), (Sum.inr 1240, 1), (Sum.inr 4091, -1)]

theorem sourceEq1249 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1249 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1249 + difference 1 0) (sourceB1249 + difference 0 1) sourceC1249) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 630) := by
    have ha : (tripleCharges (sourceA1249 + difference 1 0) (sourceB1249 + difference 0 1) sourceC1249) = raw20288 := by
      apply Matrix.ext; unfold tripleCharges sourceA1249 sourceB1249 sourceC1249 difference raw20288; decide +kernel
    rw [ha]
    exact (canonical20288 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1249 + difference 1 1) (sourceB1249 + difference 1 1) sourceC1249) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1217) := by
    have ha : (tripleCharges (sourceA1249 + difference 1 1) (sourceB1249 + difference 1 1) sourceC1249) = raw9831 := by
      apply Matrix.ext; unfold tripleCharges sourceA1249 sourceB1249 sourceC1249 difference raw9831; decide +kernel
    rw [ha]
    exact (canonical9831 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1249 + difference 1 2) (sourceB1249 + difference 2 1) sourceC1249) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1150) := by
    have ha : (tripleCharges (sourceA1249 + difference 1 2) (sourceB1249 + difference 2 1) sourceC1249) = raw20289 := by
      apply Matrix.ext; unfold tripleCharges sourceA1249 sourceB1249 sourceC1249 difference raw20289; decide +kernel
    rw [ha]
    exact (canonical20289 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1249 + difference 1 3) (sourceB1249 + difference 3 1) sourceC1249) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1136) := by
    have ha : (tripleCharges (sourceA1249 + difference 1 3) (sourceB1249 + difference 3 1) sourceC1249) = raw20290 := by
      apply Matrix.ext; unfold tripleCharges sourceA1249 sourceB1249 sourceC1249 difference raw20290; decide +kernel
    rw [ha]
    exact (canonical20290 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1249 + difference 1 4) (sourceB1249 + difference 4 1) sourceC1249) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1217) := by
    have ha : (tripleCharges (sourceA1249 + difference 1 4) (sourceB1249 + difference 4 1) sourceC1249) = raw20291 := by
      apply Matrix.ext; unfold tripleCharges sourceA1249 sourceB1249 sourceC1249 difference raw20291; decide +kernel
    rw [ha]
    exact (canonical20291 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1249 + difference 1 5) (sourceB1249 + difference 5 1) sourceC1249) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1240) := by
    have ha : (tripleCharges (sourceA1249 + difference 1 5) (sourceB1249 + difference 5 1) sourceC1249) = raw9827 := by
      apply Matrix.ext; unfold tripleCharges sourceA1249 sourceB1249 sourceC1249 difference raw9827; decide +kernel
    rw [ha]
    exact (canonical9827 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1249 + sourceB1249) sourceC1249) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1249 + sourceB1249) sourceC1249) = raw9826 := by
      apply Matrix.ext; unfold doubleCharges sourceA1249 sourceB1249 sourceC1249 raw9826; decide +kernel
    rw [ha]
    exact (canonical9826 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1249 sourceB1249 sourceC1249
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1249, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1250 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1250 : Charge := ![2, 1, 0, -1, 0, -2]
def sourceC1250 : Charge := ![2, -1, 0, 1, -1, -1]
def sourceForm1250 : Integer.Sparse Master := [(Sum.inr 1112, 1), (Sum.inr 1118, 1), (Sum.inr 1120, 1), (Sum.inr 1136, 1), (Sum.inr 1217, 1), (Sum.inr 2485, 1), (Sum.inr 4091, -1)]

theorem sourceEq1250 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1250 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1250 + difference 0 3) (sourceB1250 + difference 3 0) sourceC1250) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2485) := by
    have ha : (tripleCharges (sourceA1250 + difference 0 3) (sourceB1250 + difference 3 0) sourceC1250) = raw9845 := by
      apply Matrix.ext; unfold tripleCharges sourceA1250 sourceB1250 sourceC1250 difference raw9845; decide +kernel
    rw [ha]
    exact (canonical9845 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1250 + difference 1 3) (sourceB1250 + difference 3 1) sourceC1250) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1136) := by
    have ha : (tripleCharges (sourceA1250 + difference 1 3) (sourceB1250 + difference 3 1) sourceC1250) = raw20290 := by
      apply Matrix.ext; unfold tripleCharges sourceA1250 sourceB1250 sourceC1250 difference raw20290; decide +kernel
    rw [ha]
    exact (canonical20290 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1250 + difference 2 3) (sourceB1250 + difference 3 2) sourceC1250) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1112) := by
    have ha : (tripleCharges (sourceA1250 + difference 2 3) (sourceB1250 + difference 3 2) sourceC1250) = raw20292 := by
      apply Matrix.ext; unfold tripleCharges sourceA1250 sourceB1250 sourceC1250 difference raw20292; decide +kernel
    rw [ha]
    exact (canonical20292 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1250 + difference 3 3) (sourceB1250 + difference 3 3) sourceC1250) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1217) := by
    have ha : (tripleCharges (sourceA1250 + difference 3 3) (sourceB1250 + difference 3 3) sourceC1250) = raw9831 := by
      apply Matrix.ext; unfold tripleCharges sourceA1250 sourceB1250 sourceC1250 difference raw9831; decide +kernel
    rw [ha]
    exact (canonical9831 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1250 + difference 4 3) (sourceB1250 + difference 3 4) sourceC1250) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1120) := by
    have ha : (tripleCharges (sourceA1250 + difference 4 3) (sourceB1250 + difference 3 4) sourceC1250) = raw20293 := by
      apply Matrix.ext; unfold tripleCharges sourceA1250 sourceB1250 sourceC1250 difference raw20293; decide +kernel
    rw [ha]
    exact (canonical20293 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1250 + difference 5 3) (sourceB1250 + difference 3 5) sourceC1250) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1118) := by
    have ha : (tripleCharges (sourceA1250 + difference 5 3) (sourceB1250 + difference 3 5) sourceC1250) = raw20294 := by
      apply Matrix.ext; unfold tripleCharges sourceA1250 sourceB1250 sourceC1250 difference raw20294; decide +kernel
    rw [ha]
    exact (canonical20294 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1250 + sourceB1250) sourceC1250) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1250 + sourceB1250) sourceC1250) = raw9826 := by
      apply Matrix.ext; unfold doubleCharges sourceA1250 sourceB1250 sourceC1250 raw9826; decide +kernel
    rw [ha]
    exact (canonical9826 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1250 sourceB1250 sourceC1250
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1250, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1251 : Charge := ![2, -1, 0, 1, -1, -1]
def sourceB1251 : Charge := ![2, 1, 0, -1, 0, -2]
def sourceC1251 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1251 : Integer.Sparse Master := [(Sum.inr 1613, 1), (Sum.inr 1617, 1), (Sum.inr 1619, 1), (Sum.inr 1624, 1), (Sum.inr 1750, 1), (Sum.inr 3291, 1), (Sum.inr 4070, -1)]

theorem sourceEq1251 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1251 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1251 + difference 0 0) (sourceB1251 + difference 0 0) sourceC1251) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3291) := by
    have ha : (tripleCharges (sourceA1251 + difference 0 0) (sourceB1251 + difference 0 0) sourceC1251) = raw20295 := by
      apply Matrix.ext; unfold tripleCharges sourceA1251 sourceB1251 sourceC1251 difference raw20295; decide +kernel
    rw [ha]
    exact (canonical20295 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1251 + difference 0 1) (sourceB1251 + difference 1 0) sourceC1251) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1624) := by
    have ha : (tripleCharges (sourceA1251 + difference 0 1) (sourceB1251 + difference 1 0) sourceC1251) = raw20296 := by
      apply Matrix.ext; unfold tripleCharges sourceA1251 sourceB1251 sourceC1251 difference raw20296; decide +kernel
    rw [ha]
    exact (canonical20296 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1251 + difference 0 2) (sourceB1251 + difference 2 0) sourceC1251) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1613) := by
    have ha : (tripleCharges (sourceA1251 + difference 0 2) (sourceB1251 + difference 2 0) sourceC1251) = raw20297 := by
      apply Matrix.ext; unfold tripleCharges sourceA1251 sourceB1251 sourceC1251 difference raw20297; decide +kernel
    rw [ha]
    exact (canonical20297 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1251 + difference 0 3) (sourceB1251 + difference 3 0) sourceC1251) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1750) := by
    have ha : (tripleCharges (sourceA1251 + difference 0 3) (sourceB1251 + difference 3 0) sourceC1251) = raw20298 := by
      apply Matrix.ext; unfold tripleCharges sourceA1251 sourceB1251 sourceC1251 difference raw20298; decide +kernel
    rw [ha]
    exact (canonical20298 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1251 + difference 0 4) (sourceB1251 + difference 4 0) sourceC1251) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1619) := by
    have ha : (tripleCharges (sourceA1251 + difference 0 4) (sourceB1251 + difference 4 0) sourceC1251) = raw20299 := by
      apply Matrix.ext; unfold tripleCharges sourceA1251 sourceB1251 sourceC1251 difference raw20299; decide +kernel
    rw [ha]
    exact (canonical20299 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1251 + difference 0 5) (sourceB1251 + difference 5 0) sourceC1251) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1617) := by
    have ha : (tripleCharges (sourceA1251 + difference 0 5) (sourceB1251 + difference 5 0) sourceC1251) = raw20300 := by
      apply Matrix.ext; unfold tripleCharges sourceA1251 sourceB1251 sourceC1251 difference raw20300; decide +kernel
    rw [ha]
    exact (canonical20300 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1251 + sourceB1251) sourceC1251) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1251 + sourceB1251) sourceC1251) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1251 sourceB1251 sourceC1251 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1251 sourceB1251 sourceC1251
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1251, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1252 : Charge := ![2, -1, 0, 1, -1, -1]
def sourceB1252 : Charge := ![2, 1, 0, -1, 0, -2]
def sourceC1252 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1252 : Integer.Sparse Master := [(Sum.inr 1596, 1), (Sum.inr 1599, 1), (Sum.inr 1604, 1), (Sum.inr 1617, 1), (Sum.inr 1725, 1), (Sum.inr 3291, 1), (Sum.inr 4070, -1)]

theorem sourceEq1252 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1252 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1252 + difference 0 0) (sourceB1252 + difference 0 0) sourceC1252) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3291) := by
    have ha : (tripleCharges (sourceA1252 + difference 0 0) (sourceB1252 + difference 0 0) sourceC1252) = raw20295 := by
      apply Matrix.ext; unfold tripleCharges sourceA1252 sourceB1252 sourceC1252 difference raw20295; decide +kernel
    rw [ha]
    exact (canonical20295 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1252 + difference 1 0) (sourceB1252 + difference 0 1) sourceC1252) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1725) := by
    have ha : (tripleCharges (sourceA1252 + difference 1 0) (sourceB1252 + difference 0 1) sourceC1252) = raw20161 := by
      apply Matrix.ext; unfold tripleCharges sourceA1252 sourceB1252 sourceC1252 difference raw20161; decide +kernel
    rw [ha]
    exact (canonical20161 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1252 + difference 2 0) (sourceB1252 + difference 0 2) sourceC1252) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1596) := by
    have ha : (tripleCharges (sourceA1252 + difference 2 0) (sourceB1252 + difference 0 2) sourceC1252) = raw20212 := by
      apply Matrix.ext; unfold tripleCharges sourceA1252 sourceB1252 sourceC1252 difference raw20212; decide +kernel
    rw [ha]
    exact (canonical20212 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1252 + difference 3 0) (sourceB1252 + difference 0 3) sourceC1252) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1604) := by
    have ha : (tripleCharges (sourceA1252 + difference 3 0) (sourceB1252 + difference 0 3) sourceC1252) = raw20164 := by
      apply Matrix.ext; unfold tripleCharges sourceA1252 sourceB1252 sourceC1252 difference raw20164; decide +kernel
    rw [ha]
    exact (canonical20164 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1252 + difference 4 0) (sourceB1252 + difference 0 4) sourceC1252) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1617) := by
    have ha : (tripleCharges (sourceA1252 + difference 4 0) (sourceB1252 + difference 0 4) sourceC1252) = raw20301 := by
      apply Matrix.ext; unfold tripleCharges sourceA1252 sourceB1252 sourceC1252 difference raw20301; decide +kernel
    rw [ha]
    exact (canonical20301 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1252 + difference 5 0) (sourceB1252 + difference 0 5) sourceC1252) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1599) := by
    have ha : (tripleCharges (sourceA1252 + difference 5 0) (sourceB1252 + difference 0 5) sourceC1252) = raw20302 := by
      apply Matrix.ext; unfold tripleCharges sourceA1252 sourceB1252 sourceC1252 difference raw20302; decide +kernel
    rw [ha]
    exact (canonical20302 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1252 + sourceB1252) sourceC1252) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1252 + sourceB1252) sourceC1252) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1252 sourceB1252 sourceC1252 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1252 sourceB1252 sourceC1252
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1252, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1253 : Charge := ![2, -1, 0, 1, -1, -1]
def sourceB1253 : Charge := ![2, 1, 0, -1, 0, -2]
def sourceC1253 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1253 : Integer.Sparse Master := [(Sum.inr 1750, 1), (Sum.inr 2226, 1), (Sum.inr 3291, 2), (Sum.inr 3300, 1), (Sum.inr 3310, 1), (Sum.inr 4070, -1)]

theorem sourceEq1253 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1253 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1253 + difference 0 3) (sourceB1253 + difference 3 0) sourceC1253) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1750) := by
    have ha : (tripleCharges (sourceA1253 + difference 0 3) (sourceB1253 + difference 3 0) sourceC1253) = raw20298 := by
      apply Matrix.ext; unfold tripleCharges sourceA1253 sourceB1253 sourceC1253 difference raw20298; decide +kernel
    rw [ha]
    exact (canonical20298 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1253 + difference 1 3) (sourceB1253 + difference 3 1) sourceC1253) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3310) := by
    have ha : (tripleCharges (sourceA1253 + difference 1 3) (sourceB1253 + difference 3 1) sourceC1253) = raw20303 := by
      apply Matrix.ext; unfold tripleCharges sourceA1253 sourceB1253 sourceC1253 difference raw20303; decide +kernel
    rw [ha]
    exact (canonical20303 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1253 + difference 2 3) (sourceB1253 + difference 3 2) sourceC1253) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3291) := by
    have ha : (tripleCharges (sourceA1253 + difference 2 3) (sourceB1253 + difference 3 2) sourceC1253) = raw20304 := by
      apply Matrix.ext; unfold tripleCharges sourceA1253 sourceB1253 sourceC1253 difference raw20304; decide +kernel
    rw [ha]
    exact (canonical20304 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1253 + difference 3 3) (sourceB1253 + difference 3 3) sourceC1253) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3291) := by
    have ha : (tripleCharges (sourceA1253 + difference 3 3) (sourceB1253 + difference 3 3) sourceC1253) = raw20295 := by
      apply Matrix.ext; unfold tripleCharges sourceA1253 sourceB1253 sourceC1253 difference raw20295; decide +kernel
    rw [ha]
    exact (canonical20295 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1253 + difference 4 3) (sourceB1253 + difference 3 4) sourceC1253) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3300) := by
    have ha : (tripleCharges (sourceA1253 + difference 4 3) (sourceB1253 + difference 3 4) sourceC1253) = raw20268 := by
      apply Matrix.ext; unfold tripleCharges sourceA1253 sourceB1253 sourceC1253 difference raw20268; decide +kernel
    rw [ha]
    exact (canonical20268 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1253 + difference 5 3) (sourceB1253 + difference 3 5) sourceC1253) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2226) := by
    have ha : (tripleCharges (sourceA1253 + difference 5 3) (sourceB1253 + difference 3 5) sourceC1253) = raw20305 := by
      apply Matrix.ext; unfold tripleCharges sourceA1253 sourceB1253 sourceC1253 difference raw20305; decide +kernel
    rw [ha]
    exact (canonical20305 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1253 + sourceB1253) sourceC1253) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1253 + sourceB1253) sourceC1253) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1253 sourceB1253 sourceC1253 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1253 sourceB1253 sourceC1253
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1253, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1254 : Charge := ![2, -1, 0, 1, -1, -1]
def sourceB1254 : Charge := ![2, 1, 0, -1, 0, -2]
def sourceC1254 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1254 : Integer.Sparse Master := [(Sum.inr 1617, 1), (Sum.inr 3242, 1), (Sum.inr 3279, 1), (Sum.inr 3291, 2), (Sum.inr 3300, 1), (Sum.inr 4070, -1)]

theorem sourceEq1254 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1254 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1254 + difference 4 0) (sourceB1254 + difference 0 4) sourceC1254) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1617) := by
    have ha : (tripleCharges (sourceA1254 + difference 4 0) (sourceB1254 + difference 0 4) sourceC1254) = raw20301 := by
      apply Matrix.ext; unfold tripleCharges sourceA1254 sourceB1254 sourceC1254 difference raw20301; decide +kernel
    rw [ha]
    exact (canonical20301 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1254 + difference 4 1) (sourceB1254 + difference 1 4) sourceC1254) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3242) := by
    have ha : (tripleCharges (sourceA1254 + difference 4 1) (sourceB1254 + difference 1 4) sourceC1254) = raw20306 := by
      apply Matrix.ext; unfold tripleCharges sourceA1254 sourceB1254 sourceC1254 difference raw20306; decide +kernel
    rw [ha]
    exact (canonical20306 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1254 + difference 4 2) (sourceB1254 + difference 2 4) sourceC1254) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3279) := by
    have ha : (tripleCharges (sourceA1254 + difference 4 2) (sourceB1254 + difference 2 4) sourceC1254) = raw20307 := by
      apply Matrix.ext; unfold tripleCharges sourceA1254 sourceB1254 sourceC1254 difference raw20307; decide +kernel
    rw [ha]
    exact (canonical20307 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1254 + difference 4 3) (sourceB1254 + difference 3 4) sourceC1254) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3300) := by
    have ha : (tripleCharges (sourceA1254 + difference 4 3) (sourceB1254 + difference 3 4) sourceC1254) = raw20268 := by
      apply Matrix.ext; unfold tripleCharges sourceA1254 sourceB1254 sourceC1254 difference raw20268; decide +kernel
    rw [ha]
    exact (canonical20268 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1254 + difference 4 4) (sourceB1254 + difference 4 4) sourceC1254) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3291) := by
    have ha : (tripleCharges (sourceA1254 + difference 4 4) (sourceB1254 + difference 4 4) sourceC1254) = raw20295 := by
      apply Matrix.ext; unfold tripleCharges sourceA1254 sourceB1254 sourceC1254 difference raw20295; decide +kernel
    rw [ha]
    exact (canonical20295 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1254 + difference 4 5) (sourceB1254 + difference 5 4) sourceC1254) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3291) := by
    have ha : (tripleCharges (sourceA1254 + difference 4 5) (sourceB1254 + difference 5 4) sourceC1254) = raw20267 := by
      apply Matrix.ext; unfold tripleCharges sourceA1254 sourceB1254 sourceC1254 difference raw20267; decide +kernel
    rw [ha]
    exact (canonical20267 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1254 + sourceB1254) sourceC1254) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1254 + sourceB1254) sourceC1254) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1254 sourceB1254 sourceC1254 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1254 sourceB1254 sourceC1254
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1254, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1255 : Charge := ![2, -1, 0, 1, -1, -1]
def sourceB1255 : Charge := ![2, 1, 0, -1, 0, -2]
def sourceC1255 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1255 : Integer.Sparse Master := [(Sum.inr 1599, 1), (Sum.inr 1995, 1), (Sum.inr 2005, 1), (Sum.inr 2045, 1), (Sum.inr 2226, 1), (Sum.inr 3291, 1), (Sum.inr 4070, -1)]

theorem sourceEq1255 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1255 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1255 + difference 5 0) (sourceB1255 + difference 0 5) sourceC1255) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1599) := by
    have ha : (tripleCharges (sourceA1255 + difference 5 0) (sourceB1255 + difference 0 5) sourceC1255) = raw20302 := by
      apply Matrix.ext; unfold tripleCharges sourceA1255 sourceB1255 sourceC1255 difference raw20302; decide +kernel
    rw [ha]
    exact (canonical20302 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1255 + difference 5 1) (sourceB1255 + difference 1 5) sourceC1255) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2005) := by
    have ha : (tripleCharges (sourceA1255 + difference 5 1) (sourceB1255 + difference 1 5) sourceC1255) = raw20308 := by
      apply Matrix.ext; unfold tripleCharges sourceA1255 sourceB1255 sourceC1255 difference raw20308; decide +kernel
    rw [ha]
    exact (canonical20308 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1255 + difference 5 2) (sourceB1255 + difference 2 5) sourceC1255) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1995) := by
    have ha : (tripleCharges (sourceA1255 + difference 5 2) (sourceB1255 + difference 2 5) sourceC1255) = raw20309 := by
      apply Matrix.ext; unfold tripleCharges sourceA1255 sourceB1255 sourceC1255 difference raw20309; decide +kernel
    rw [ha]
    exact (canonical20309 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1255 + difference 5 3) (sourceB1255 + difference 3 5) sourceC1255) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2226) := by
    have ha : (tripleCharges (sourceA1255 + difference 5 3) (sourceB1255 + difference 3 5) sourceC1255) = raw20305 := by
      apply Matrix.ext; unfold tripleCharges sourceA1255 sourceB1255 sourceC1255 difference raw20305; decide +kernel
    rw [ha]
    exact (canonical20305 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1255 + difference 5 4) (sourceB1255 + difference 4 5) sourceC1255) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2045) := by
    have ha : (tripleCharges (sourceA1255 + difference 5 4) (sourceB1255 + difference 4 5) sourceC1255) = raw20310 := by
      apply Matrix.ext; unfold tripleCharges sourceA1255 sourceB1255 sourceC1255 difference raw20310; decide +kernel
    rw [ha]
    exact (canonical20310 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1255 + difference 5 5) (sourceB1255 + difference 5 5) sourceC1255) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3291) := by
    have ha : (tripleCharges (sourceA1255 + difference 5 5) (sourceB1255 + difference 5 5) sourceC1255) = raw20295 := by
      apply Matrix.ext; unfold tripleCharges sourceA1255 sourceB1255 sourceC1255 difference raw20295; decide +kernel
    rw [ha]
    exact (canonical20295 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1255 + sourceB1255) sourceC1255) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1255 + sourceB1255) sourceC1255) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1255 sourceB1255 sourceC1255 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1255 sourceB1255 sourceC1255
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1255, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1256 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1256 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC1256 : Charge := ![2, -1, 0, 1, 1, -3]
def sourceForm1256 : Integer.Sparse Master := [(Sum.inr 1211, 1), (Sum.inr 2070, 1), (Sum.inr 2079, 1), (Sum.inr 2087, 1), (Sum.inr 2193, 1), (Sum.inr 2719, 1), (Sum.inr 4080, -1)]

theorem sourceEq1256 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1256 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1256 + difference 0 0) (sourceB1256 + difference 0 0) sourceC1256) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1211) := by
    have ha : (tripleCharges (sourceA1256 + difference 0 0) (sourceB1256 + difference 0 0) sourceC1256) = raw19503 := by
      apply Matrix.ext; unfold tripleCharges sourceA1256 sourceB1256 sourceC1256 difference raw19503; decide +kernel
    rw [ha]
    exact (canonical19503 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1256 + difference 0 1) (sourceB1256 + difference 1 0) sourceC1256) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2087) := by
    have ha : (tripleCharges (sourceA1256 + difference 0 1) (sourceB1256 + difference 1 0) sourceC1256) = raw20311 := by
      apply Matrix.ext; unfold tripleCharges sourceA1256 sourceB1256 sourceC1256 difference raw20311; decide +kernel
    rw [ha]
    exact (canonical20311 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1256 + difference 0 2) (sourceB1256 + difference 2 0) sourceC1256) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2070) := by
    have ha : (tripleCharges (sourceA1256 + difference 0 2) (sourceB1256 + difference 2 0) sourceC1256) = raw20312 := by
      apply Matrix.ext; unfold tripleCharges sourceA1256 sourceB1256 sourceC1256 difference raw20312; decide +kernel
    rw [ha]
    exact (canonical20312 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1256 + difference 0 3) (sourceB1256 + difference 3 0) sourceC1256) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2079) := by
    have ha : (tripleCharges (sourceA1256 + difference 0 3) (sourceB1256 + difference 3 0) sourceC1256) = raw20313 := by
      apply Matrix.ext; unfold tripleCharges sourceA1256 sourceB1256 sourceC1256 difference raw20313; decide +kernel
    rw [ha]
    exact (canonical20313 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1256 + difference 0 4) (sourceB1256 + difference 4 0) sourceC1256) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2193) := by
    have ha : (tripleCharges (sourceA1256 + difference 0 4) (sourceB1256 + difference 4 0) sourceC1256) = raw19498 := by
      apply Matrix.ext; unfold tripleCharges sourceA1256 sourceB1256 sourceC1256 difference raw19498; decide +kernel
    rw [ha]
    exact (canonical19498 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1256 + difference 0 5) (sourceB1256 + difference 5 0) sourceC1256) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2719) := by
    have ha : (tripleCharges (sourceA1256 + difference 0 5) (sourceB1256 + difference 5 0) sourceC1256) = raw20314 := by
      apply Matrix.ext; unfold tripleCharges sourceA1256 sourceB1256 sourceC1256 difference raw20314; decide +kernel
    rw [ha]
    exact (canonical20314 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1256 + sourceB1256) sourceC1256) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1256 + sourceB1256) sourceC1256) = raw19499 := by
      apply Matrix.ext; unfold doubleCharges sourceA1256 sourceB1256 sourceC1256 raw19499; decide +kernel
    rw [ha]
    exact (canonical19499 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1256 sourceB1256 sourceC1256
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1256, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1257 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1257 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC1257 : Charge := ![2, -1, 0, 2, -1, -2]
def sourceForm1257 : Integer.Sparse Master := [(Sum.inr 1181, 1), (Sum.inr 2385, 1), (Sum.inr 2453, 1), (Sum.inr 2492, 1), (Sum.inr 2664, 1), (Sum.inr 2672, 1), (Sum.inr 4088, -1)]

theorem sourceEq1257 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1257 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1257 + difference 0 0) (sourceB1257 + difference 0 0) sourceC1257) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1181) := by
    have ha : (tripleCharges (sourceA1257 + difference 0 0) (sourceB1257 + difference 0 0) sourceC1257) = raw20315 := by
      apply Matrix.ext; unfold tripleCharges sourceA1257 sourceB1257 sourceC1257 difference raw20315; decide +kernel
    rw [ha]
    exact (canonical20315 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1257 + difference 0 1) (sourceB1257 + difference 1 0) sourceC1257) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2492) := by
    have ha : (tripleCharges (sourceA1257 + difference 0 1) (sourceB1257 + difference 1 0) sourceC1257) = raw20316 := by
      apply Matrix.ext; unfold tripleCharges sourceA1257 sourceB1257 sourceC1257 difference raw20316; decide +kernel
    rw [ha]
    exact (canonical20316 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1257 + difference 0 2) (sourceB1257 + difference 2 0) sourceC1257) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2453) := by
    have ha : (tripleCharges (sourceA1257 + difference 0 2) (sourceB1257 + difference 2 0) sourceC1257) = raw20317 := by
      apply Matrix.ext; unfold tripleCharges sourceA1257 sourceB1257 sourceC1257 difference raw20317; decide +kernel
    rw [ha]
    exact (canonical20317 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1257 + difference 0 3) (sourceB1257 + difference 3 0) sourceC1257) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2385) := by
    have ha : (tripleCharges (sourceA1257 + difference 0 3) (sourceB1257 + difference 3 0) sourceC1257) = raw20318 := by
      apply Matrix.ext; unfold tripleCharges sourceA1257 sourceB1257 sourceC1257 difference raw20318; decide +kernel
    rw [ha]
    exact (canonical20318 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1257 + difference 0 4) (sourceB1257 + difference 4 0) sourceC1257) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2664) := by
    have ha : (tripleCharges (sourceA1257 + difference 0 4) (sourceB1257 + difference 4 0) sourceC1257) = raw20319 := by
      apply Matrix.ext; unfold tripleCharges sourceA1257 sourceB1257 sourceC1257 difference raw20319; decide +kernel
    rw [ha]
    exact (canonical20319 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1257 + difference 0 5) (sourceB1257 + difference 5 0) sourceC1257) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2672) := by
    have ha : (tripleCharges (sourceA1257 + difference 0 5) (sourceB1257 + difference 5 0) sourceC1257) = raw20320 := by
      apply Matrix.ext; unfold tripleCharges sourceA1257 sourceB1257 sourceC1257 difference raw20320; decide +kernel
    rw [ha]
    exact (canonical20320 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1257 + sourceB1257) sourceC1257) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA1257 + sourceB1257) sourceC1257) = raw20321 := by
      apply Matrix.ext; unfold doubleCharges sourceA1257 sourceB1257 sourceC1257 raw20321; decide +kernel
    rw [ha]
    exact (canonical20321 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1257 sourceB1257 sourceC1257
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1257, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1258 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1258 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC1258 : Charge := ![2, -1, 0, 2, -1, -2]
def sourceForm1258 : Integer.Sparse Master := [(Sum.inr 1178, 1), (Sum.inr 1181, 1), (Sum.inr 1182, 1), (Sum.inr 1188, 1), (Sum.inr 1257, 1), (Sum.inr 2672, 1), (Sum.inr 4088, -1)]

theorem sourceEq1258 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1258 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1258 + difference 0 5) (sourceB1258 + difference 5 0) sourceC1258) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2672) := by
    have ha : (tripleCharges (sourceA1258 + difference 0 5) (sourceB1258 + difference 5 0) sourceC1258) = raw20320 := by
      apply Matrix.ext; unfold tripleCharges sourceA1258 sourceB1258 sourceC1258 difference raw20320; decide +kernel
    rw [ha]
    exact (canonical20320 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1258 + difference 1 5) (sourceB1258 + difference 5 1) sourceC1258) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1188) := by
    have ha : (tripleCharges (sourceA1258 + difference 1 5) (sourceB1258 + difference 5 1) sourceC1258) = raw20322 := by
      apply Matrix.ext; unfold tripleCharges sourceA1258 sourceB1258 sourceC1258 difference raw20322; decide +kernel
    rw [ha]
    exact (canonical20322 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1258 + difference 2 5) (sourceB1258 + difference 5 2) sourceC1258) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1178) := by
    have ha : (tripleCharges (sourceA1258 + difference 2 5) (sourceB1258 + difference 5 2) sourceC1258) = raw20323 := by
      apply Matrix.ext; unfold tripleCharges sourceA1258 sourceB1258 sourceC1258 difference raw20323; decide +kernel
    rw [ha]
    exact (canonical20323 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1258 + difference 3 5) (sourceB1258 + difference 5 3) sourceC1258) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1257) := by
    have ha : (tripleCharges (sourceA1258 + difference 3 5) (sourceB1258 + difference 5 3) sourceC1258) = raw20324 := by
      apply Matrix.ext; unfold tripleCharges sourceA1258 sourceB1258 sourceC1258 difference raw20324; decide +kernel
    rw [ha]
    exact (canonical20324 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1258 + difference 4 5) (sourceB1258 + difference 5 4) sourceC1258) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1182) := by
    have ha : (tripleCharges (sourceA1258 + difference 4 5) (sourceB1258 + difference 5 4) sourceC1258) = raw20325 := by
      apply Matrix.ext; unfold tripleCharges sourceA1258 sourceB1258 sourceC1258 difference raw20325; decide +kernel
    rw [ha]
    exact (canonical20325 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1258 + difference 5 5) (sourceB1258 + difference 5 5) sourceC1258) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1181) := by
    have ha : (tripleCharges (sourceA1258 + difference 5 5) (sourceB1258 + difference 5 5) sourceC1258) = raw20315 := by
      apply Matrix.ext; unfold tripleCharges sourceA1258 sourceB1258 sourceC1258 difference raw20315; decide +kernel
    rw [ha]
    exact (canonical20315 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1258 + sourceB1258) sourceC1258) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA1258 + sourceB1258) sourceC1258) = raw20321 := by
      apply Matrix.ext; unfold doubleCharges sourceA1258 sourceB1258 sourceC1258 raw20321; decide +kernel
    rw [ha]
    exact (canonical20321 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1258 sourceB1258 sourceC1258
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1258, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1259 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1259 : Charge := ![2, 1, 0, -2, -1, 0]
def sourceC1259 : Charge := ![2, -1, 0, 2, 0, -3]
def sourceForm1259 : Integer.Sparse Master := [(Sum.inr 1179, 1), (Sum.inr 1991, 1), (Sum.inr 2003, 1), (Sum.inr 2032, 1), (Sum.inr 2218, 1), (Sum.inr 2670, 1), (Sum.inr 4082, -1)]

theorem sourceEq1259 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1259 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1259 + difference 0 0) (sourceB1259 + difference 0 0) sourceC1259) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1179) := by
    have ha : (tripleCharges (sourceA1259 + difference 0 0) (sourceB1259 + difference 0 0) sourceC1259) = raw20326 := by
      apply Matrix.ext; unfold tripleCharges sourceA1259 sourceB1259 sourceC1259 difference raw20326; decide +kernel
    rw [ha]
    exact (canonical20326 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1259 + difference 0 1) (sourceB1259 + difference 1 0) sourceC1259) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2032) := by
    have ha : (tripleCharges (sourceA1259 + difference 0 1) (sourceB1259 + difference 1 0) sourceC1259) = raw20327 := by
      apply Matrix.ext; unfold tripleCharges sourceA1259 sourceB1259 sourceC1259 difference raw20327; decide +kernel
    rw [ha]
    exact (canonical20327 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1259 + difference 0 2) (sourceB1259 + difference 2 0) sourceC1259) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1991) := by
    have ha : (tripleCharges (sourceA1259 + difference 0 2) (sourceB1259 + difference 2 0) sourceC1259) = raw20328 := by
      apply Matrix.ext; unfold tripleCharges sourceA1259 sourceB1259 sourceC1259 difference raw20328; decide +kernel
    rw [ha]
    exact (canonical20328 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1259 + difference 0 3) (sourceB1259 + difference 3 0) sourceC1259) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2003) := by
    have ha : (tripleCharges (sourceA1259 + difference 0 3) (sourceB1259 + difference 3 0) sourceC1259) = raw20329 := by
      apply Matrix.ext; unfold tripleCharges sourceA1259 sourceB1259 sourceC1259 difference raw20329; decide +kernel
    rw [ha]
    exact (canonical20329 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1259 + difference 0 4) (sourceB1259 + difference 4 0) sourceC1259) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2218) := by
    have ha : (tripleCharges (sourceA1259 + difference 0 4) (sourceB1259 + difference 4 0) sourceC1259) = raw20330 := by
      apply Matrix.ext; unfold tripleCharges sourceA1259 sourceB1259 sourceC1259 difference raw20330; decide +kernel
    rw [ha]
    exact (canonical20330 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1259 + difference 0 5) (sourceB1259 + difference 5 0) sourceC1259) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2670) := by
    have ha : (tripleCharges (sourceA1259 + difference 0 5) (sourceB1259 + difference 5 0) sourceC1259) = raw20331 := by
      apply Matrix.ext; unfold tripleCharges sourceA1259 sourceB1259 sourceC1259 difference raw20331; decide +kernel
    rw [ha]
    exact (canonical20331 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1259 + sourceB1259) sourceC1259) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA1259 + sourceB1259) sourceC1259) = raw20332 := by
      apply Matrix.ext; unfold doubleCharges sourceA1259 sourceB1259 sourceC1259 raw20332; decide +kernel
    rw [ha]
    exact (canonical20332 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1259 sourceB1259 sourceC1259
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1259, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1260 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1260 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceC1260 : Charge := ![2, -1, 1, 1, -1, -2]
def sourceForm1260 : Integer.Sparse Master := [(Sum.inr 1195, 1), (Sum.inr 2449, 2), (Sum.inr 2469, 1), (Sum.inr 2691, 1), (Sum.inr 2694, 1), (Sum.inr 4090, -1)]

theorem sourceEq1260 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1260 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1260 + difference 0 0) (sourceB1260 + difference 0 0) sourceC1260) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1195) := by
    have ha : (tripleCharges (sourceA1260 + difference 0 0) (sourceB1260 + difference 0 0) sourceC1260) = raw20333 := by
      apply Matrix.ext; unfold tripleCharges sourceA1260 sourceB1260 sourceC1260 difference raw20333; decide +kernel
    rw [ha]
    exact (canonical20333 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1260 + difference 0 1) (sourceB1260 + difference 1 0) sourceC1260) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2469) := by
    have ha : (tripleCharges (sourceA1260 + difference 0 1) (sourceB1260 + difference 1 0) sourceC1260) = raw20334 := by
      apply Matrix.ext; unfold tripleCharges sourceA1260 sourceB1260 sourceC1260 difference raw20334; decide +kernel
    rw [ha]
    exact (canonical20334 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1260 + difference 0 2) (sourceB1260 + difference 2 0) sourceC1260) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2449) := by
    have ha : (tripleCharges (sourceA1260 + difference 0 2) (sourceB1260 + difference 2 0) sourceC1260) = raw20335 := by
      apply Matrix.ext; unfold tripleCharges sourceA1260 sourceB1260 sourceC1260 difference raw20335; decide +kernel
    rw [ha]
    exact (canonical20335 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1260 + difference 0 3) (sourceB1260 + difference 3 0) sourceC1260) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2449) := by
    have ha : (tripleCharges (sourceA1260 + difference 0 3) (sourceB1260 + difference 3 0) sourceC1260) = raw20336 := by
      apply Matrix.ext; unfold tripleCharges sourceA1260 sourceB1260 sourceC1260 difference raw20336; decide +kernel
    rw [ha]
    exact (canonical20336 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1260 + difference 0 4) (sourceB1260 + difference 4 0) sourceC1260) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2691) := by
    have ha : (tripleCharges (sourceA1260 + difference 0 4) (sourceB1260 + difference 4 0) sourceC1260) = raw20337 := by
      apply Matrix.ext; unfold tripleCharges sourceA1260 sourceB1260 sourceC1260 difference raw20337; decide +kernel
    rw [ha]
    exact (canonical20337 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1260 + difference 0 5) (sourceB1260 + difference 5 0) sourceC1260) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2694) := by
    have ha : (tripleCharges (sourceA1260 + difference 0 5) (sourceB1260 + difference 5 0) sourceC1260) = raw20338 := by
      apply Matrix.ext; unfold tripleCharges sourceA1260 sourceB1260 sourceC1260 difference raw20338; decide +kernel
    rw [ha]
    exact (canonical20338 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1260 + sourceB1260) sourceC1260) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (doubleCharges (sourceA1260 + sourceB1260) sourceC1260) = raw20339 := by
      apply Matrix.ext; unfold doubleCharges sourceA1260 sourceB1260 sourceC1260 raw20339; decide +kernel
    rw [ha]
    exact (canonical20339 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1260 sourceB1260 sourceC1260
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1260, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1261 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1261 : Charge := ![2, 1, -1, -1, 0, -1]
def sourceC1261 : Charge := ![2, -1, 1, 1, -1, -2]
def sourceForm1261 : Integer.Sparse Master := [(Sum.inr 1195, 1), (Sum.inr 1196, 1), (Sum.inr 1200, 1), (Sum.inr 1210, 2), (Sum.inr 2694, 1), (Sum.inr 4090, -1)]

theorem sourceEq1261 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1261 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1261 + difference 0 5) (sourceB1261 + difference 5 0) sourceC1261) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2694) := by
    have ha : (tripleCharges (sourceA1261 + difference 0 5) (sourceB1261 + difference 5 0) sourceC1261) = raw20338 := by
      apply Matrix.ext; unfold tripleCharges sourceA1261 sourceB1261 sourceC1261 difference raw20338; decide +kernel
    rw [ha]
    exact (canonical20338 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1261 + difference 1 5) (sourceB1261 + difference 5 1) sourceC1261) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1200) := by
    have ha : (tripleCharges (sourceA1261 + difference 1 5) (sourceB1261 + difference 5 1) sourceC1261) = raw20340 := by
      apply Matrix.ext; unfold tripleCharges sourceA1261 sourceB1261 sourceC1261 difference raw20340; decide +kernel
    rw [ha]
    exact (canonical20340 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1261 + difference 2 5) (sourceB1261 + difference 5 2) sourceC1261) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1210) := by
    have ha : (tripleCharges (sourceA1261 + difference 2 5) (sourceB1261 + difference 5 2) sourceC1261) = raw20341 := by
      apply Matrix.ext; unfold tripleCharges sourceA1261 sourceB1261 sourceC1261 difference raw20341; decide +kernel
    rw [ha]
    exact (canonical20341 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1261 + difference 3 5) (sourceB1261 + difference 5 3) sourceC1261) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1210) := by
    have ha : (tripleCharges (sourceA1261 + difference 3 5) (sourceB1261 + difference 5 3) sourceC1261) = raw20342 := by
      apply Matrix.ext; unfold tripleCharges sourceA1261 sourceB1261 sourceC1261 difference raw20342; decide +kernel
    rw [ha]
    exact (canonical20342 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1261 + difference 4 5) (sourceB1261 + difference 5 4) sourceC1261) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1196) := by
    have ha : (tripleCharges (sourceA1261 + difference 4 5) (sourceB1261 + difference 5 4) sourceC1261) = raw20343 := by
      apply Matrix.ext; unfold tripleCharges sourceA1261 sourceB1261 sourceC1261 difference raw20343; decide +kernel
    rw [ha]
    exact (canonical20343 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1261 + difference 5 5) (sourceB1261 + difference 5 5) sourceC1261) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1195) := by
    have ha : (tripleCharges (sourceA1261 + difference 5 5) (sourceB1261 + difference 5 5) sourceC1261) = raw20333 := by
      apply Matrix.ext; unfold tripleCharges sourceA1261 sourceB1261 sourceC1261 difference raw20333; decide +kernel
    rw [ha]
    exact (canonical20333 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1261 + sourceB1261) sourceC1261) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (doubleCharges (sourceA1261 + sourceB1261) sourceC1261) = raw20339 := by
      apply Matrix.ext; unfold doubleCharges sourceA1261 sourceB1261 sourceC1261 raw20339; decide +kernel
    rw [ha]
    exact (canonical20339 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1261 sourceB1261 sourceC1261
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1261, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1262 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1262 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceC1262 : Charge := ![2, -1, 1, 1, 0, -3]
def sourceForm1262 : Integer.Sparse Master := [(Sum.inr 1194, 1), (Sum.inr 1987, 2), (Sum.inr 2008, 1), (Sum.inr 2193, 1), (Sum.inr 2693, 1), (Sum.inr 4080, -1)]

theorem sourceEq1262 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1262 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1262 + difference 0 0) (sourceB1262 + difference 0 0) sourceC1262) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1194) := by
    have ha : (tripleCharges (sourceA1262 + difference 0 0) (sourceB1262 + difference 0 0) sourceC1262) = raw20344 := by
      apply Matrix.ext; unfold tripleCharges sourceA1262 sourceB1262 sourceC1262 difference raw20344; decide +kernel
    rw [ha]
    exact (canonical20344 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1262 + difference 0 1) (sourceB1262 + difference 1 0) sourceC1262) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2008) := by
    have ha : (tripleCharges (sourceA1262 + difference 0 1) (sourceB1262 + difference 1 0) sourceC1262) = raw20345 := by
      apply Matrix.ext; unfold tripleCharges sourceA1262 sourceB1262 sourceC1262 difference raw20345; decide +kernel
    rw [ha]
    exact (canonical20345 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1262 + difference 0 2) (sourceB1262 + difference 2 0) sourceC1262) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1987) := by
    have ha : (tripleCharges (sourceA1262 + difference 0 2) (sourceB1262 + difference 2 0) sourceC1262) = raw20346 := by
      apply Matrix.ext; unfold tripleCharges sourceA1262 sourceB1262 sourceC1262 difference raw20346; decide +kernel
    rw [ha]
    exact (canonical20346 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1262 + difference 0 3) (sourceB1262 + difference 3 0) sourceC1262) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1987) := by
    have ha : (tripleCharges (sourceA1262 + difference 0 3) (sourceB1262 + difference 3 0) sourceC1262) = raw20347 := by
      apply Matrix.ext; unfold tripleCharges sourceA1262 sourceB1262 sourceC1262 difference raw20347; decide +kernel
    rw [ha]
    exact (canonical20347 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1262 + difference 0 4) (sourceB1262 + difference 4 0) sourceC1262) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2193) := by
    have ha : (tripleCharges (sourceA1262 + difference 0 4) (sourceB1262 + difference 4 0) sourceC1262) = raw20348 := by
      apply Matrix.ext; unfold tripleCharges sourceA1262 sourceB1262 sourceC1262 difference raw20348; decide +kernel
    rw [ha]
    exact (canonical20348 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1262 + difference 0 5) (sourceB1262 + difference 5 0) sourceC1262) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2693) := by
    have ha : (tripleCharges (sourceA1262 + difference 0 5) (sourceB1262 + difference 5 0) sourceC1262) = raw20349 := by
      apply Matrix.ext; unfold tripleCharges sourceA1262 sourceB1262 sourceC1262 difference raw20349; decide +kernel
    rw [ha]
    exact (canonical20349 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1262 + sourceB1262) sourceC1262) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1262 + sourceB1262) sourceC1262) = raw20350 := by
      apply Matrix.ext; unfold doubleCharges sourceA1262 sourceB1262 sourceC1262 raw20350; decide +kernel
    rw [ha]
    exact (canonical20350 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1262 sourceB1262 sourceC1262
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1262, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1263 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1263 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC1263 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceForm1263 : Integer.Sparse Master := [(Sum.inr 4183, 3), (Sum.inr 4187, 1), (Sum.inr 4192, 1), (Sum.inr 4551, 6), (Sum.inr 4555, 3), (Sum.inr 4559, 3), (Sum.inr 4623, 3), (Sum.inr 4625, 3), (Sum.inr 4627, 1), (Sum.inr 4629, 1), (Sum.inr 5171, 3), (Sum.inr 5308, 1), (Sum.inr 5312, 1)]

theorem sourceEq1263 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1263 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1263 + difference 0 1) (sourceB1263 + difference 1 0) sourceC1263) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5171) := by
    have ha : (tripleCharges (sourceA1263 + difference 0 1) (sourceB1263 + difference 1 0) sourceC1263) = raw5079 := by
      apply Matrix.ext; unfold tripleCharges sourceA1263 sourceB1263 sourceC1263 difference raw5079; decide +kernel
    rw [ha]
    exact (canonical5079 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1263 + difference 0 2) (sourceB1263 + difference 2 0) sourceC1263) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5171) := by
    have ha : (tripleCharges (sourceA1263 + difference 0 2) (sourceB1263 + difference 2 0) sourceC1263) = raw5080 := by
      apply Matrix.ext; unfold tripleCharges sourceA1263 sourceB1263 sourceC1263 difference raw5080; decide +kernel
    rw [ha]
    exact (canonical5080 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1263 + difference 0 3) (sourceB1263 + difference 3 0) sourceC1263) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5171) := by
    have ha : (tripleCharges (sourceA1263 + difference 0 3) (sourceB1263 + difference 3 0) sourceC1263) = raw5081 := by
      apply Matrix.ext; unfold tripleCharges sourceA1263 sourceB1263 sourceC1263 difference raw5081; decide +kernel
    rw [ha]
    exact (canonical5081 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1263 + difference 0 4) (sourceB1263 + difference 4 0) sourceC1263) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5312) := by
    have ha : (tripleCharges (sourceA1263 + difference 0 4) (sourceB1263 + difference 4 0) sourceC1263) = raw10237 := by
      apply Matrix.ext; unfold tripleCharges sourceA1263 sourceB1263 sourceC1263 difference raw10237; decide +kernel
    rw [ha]
    exact (canonical10237 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1263 + difference 0 5) (sourceB1263 + difference 5 0) sourceC1263) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5308) := by
    have ha : (tripleCharges (sourceA1263 + difference 0 5) (sourceB1263 + difference 5 0) sourceC1263) = raw5082 := by
      apply Matrix.ext; unfold tripleCharges sourceA1263 sourceB1263 sourceC1263 difference raw5082; decide +kernel
    rw [ha]
    exact (canonical5082 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1263 + difference 1 0) (sourceB1263 + difference 0 1) sourceC1263) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4183) := by
    have ha : (tripleCharges (sourceA1263 + difference 1 0) (sourceB1263 + difference 0 1) sourceC1263) = raw20351 := by
      apply Matrix.ext; unfold tripleCharges sourceA1263 sourceB1263 sourceC1263 difference raw20351; decide +kernel
    rw [ha]
    exact (canonical20351 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1263 + difference 1 2) (sourceB1263 + difference 2 1) sourceC1263) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4551) := by
    have ha : (tripleCharges (sourceA1263 + difference 1 2) (sourceB1263 + difference 2 1) sourceC1263) = raw20352 := by
      apply Matrix.ext; unfold tripleCharges sourceA1263 sourceB1263 sourceC1263 difference raw20352; decide +kernel
    rw [ha]
    exact (canonical20352 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1263 + difference 1 3) (sourceB1263 + difference 3 1) sourceC1263) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4551) := by
    have ha : (tripleCharges (sourceA1263 + difference 1 3) (sourceB1263 + difference 3 1) sourceC1263) = raw20353 := by
      apply Matrix.ext; unfold tripleCharges sourceA1263 sourceB1263 sourceC1263 difference raw20353; decide +kernel
    rw [ha]
    exact (canonical20353 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1263 + difference 1 4) (sourceB1263 + difference 4 1) sourceC1263) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4625) := by
    have ha : (tripleCharges (sourceA1263 + difference 1 4) (sourceB1263 + difference 4 1) sourceC1263) = raw5063 := by
      apply Matrix.ext; unfold tripleCharges sourceA1263 sourceB1263 sourceC1263 difference raw5063; decide +kernel
    rw [ha]
    exact (canonical5063 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1263 + difference 1 5) (sourceB1263 + difference 5 1) sourceC1263) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4623) := by
    have ha : (tripleCharges (sourceA1263 + difference 1 5) (sourceB1263 + difference 5 1) sourceC1263) = raw10220 := by
      apply Matrix.ext; unfold tripleCharges sourceA1263 sourceB1263 sourceC1263 difference raw10220; decide +kernel
    rw [ha]
    exact (canonical10220 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1263 + difference 2 0) (sourceB1263 + difference 0 2) sourceC1263) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4183) := by
    have ha : (tripleCharges (sourceA1263 + difference 2 0) (sourceB1263 + difference 0 2) sourceC1263) = raw20354 := by
      apply Matrix.ext; unfold tripleCharges sourceA1263 sourceB1263 sourceC1263 difference raw20354; decide +kernel
    rw [ha]
    exact (canonical20354 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1263 + difference 2 1) (sourceB1263 + difference 1 2) sourceC1263) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4551) := by
    have ha : (tripleCharges (sourceA1263 + difference 2 1) (sourceB1263 + difference 1 2) sourceC1263) = raw20355 := by
      apply Matrix.ext; unfold tripleCharges sourceA1263 sourceB1263 sourceC1263 difference raw20355; decide +kernel
    rw [ha]
    exact (canonical20355 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1263 + difference 2 3) (sourceB1263 + difference 3 2) sourceC1263) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4551) := by
    have ha : (tripleCharges (sourceA1263 + difference 2 3) (sourceB1263 + difference 3 2) sourceC1263) = raw20356 := by
      apply Matrix.ext; unfold tripleCharges sourceA1263 sourceB1263 sourceC1263 difference raw20356; decide +kernel
    rw [ha]
    exact (canonical20356 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1263 + difference 2 4) (sourceB1263 + difference 4 2) sourceC1263) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4625) := by
    have ha : (tripleCharges (sourceA1263 + difference 2 4) (sourceB1263 + difference 4 2) sourceC1263) = raw5068 := by
      apply Matrix.ext; unfold tripleCharges sourceA1263 sourceB1263 sourceC1263 difference raw5068; decide +kernel
    rw [ha]
    exact (canonical5068 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1263 + difference 2 5) (sourceB1263 + difference 5 2) sourceC1263) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4623) := by
    have ha : (tripleCharges (sourceA1263 + difference 2 5) (sourceB1263 + difference 5 2) sourceC1263) = raw10224 := by
      apply Matrix.ext; unfold tripleCharges sourceA1263 sourceB1263 sourceC1263 difference raw10224; decide +kernel
    rw [ha]
    exact (canonical10224 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1263 + difference 3 0) (sourceB1263 + difference 0 3) sourceC1263) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4183) := by
    have ha : (tripleCharges (sourceA1263 + difference 3 0) (sourceB1263 + difference 0 3) sourceC1263) = raw20357 := by
      apply Matrix.ext; unfold tripleCharges sourceA1263 sourceB1263 sourceC1263 difference raw20357; decide +kernel
    rw [ha]
    exact (canonical20357 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1263 + difference 3 1) (sourceB1263 + difference 1 3) sourceC1263) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4551) := by
    have ha : (tripleCharges (sourceA1263 + difference 3 1) (sourceB1263 + difference 1 3) sourceC1263) = raw20358 := by
      apply Matrix.ext; unfold tripleCharges sourceA1263 sourceB1263 sourceC1263 difference raw20358; decide +kernel
    rw [ha]
    exact (canonical20358 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1263 + difference 3 2) (sourceB1263 + difference 2 3) sourceC1263) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4551) := by
    have ha : (tripleCharges (sourceA1263 + difference 3 2) (sourceB1263 + difference 2 3) sourceC1263) = raw20359 := by
      apply Matrix.ext; unfold tripleCharges sourceA1263 sourceB1263 sourceC1263 difference raw20359; decide +kernel
    rw [ha]
    exact (canonical20359 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1263 + difference 3 4) (sourceB1263 + difference 4 3) sourceC1263) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4625) := by
    have ha : (tripleCharges (sourceA1263 + difference 3 4) (sourceB1263 + difference 4 3) sourceC1263) = raw5073 := by
      apply Matrix.ext; unfold tripleCharges sourceA1263 sourceB1263 sourceC1263 difference raw5073; decide +kernel
    rw [ha]
    exact (canonical5073 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1263 + difference 3 5) (sourceB1263 + difference 5 3) sourceC1263) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4623) := by
    have ha : (tripleCharges (sourceA1263 + difference 3 5) (sourceB1263 + difference 5 3) sourceC1263) = raw10228 := by
      apply Matrix.ext; unfold tripleCharges sourceA1263 sourceB1263 sourceC1263 difference raw10228; decide +kernel
    rw [ha]
    exact (canonical10228 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1263 + difference 4 0) (sourceB1263 + difference 0 4) sourceC1263) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4192) := by
    have ha : (tripleCharges (sourceA1263 + difference 4 0) (sourceB1263 + difference 0 4) sourceC1263) = raw20360 := by
      apply Matrix.ext; unfold tripleCharges sourceA1263 sourceB1263 sourceC1263 difference raw20360; decide +kernel
    rw [ha]
    exact (canonical20360 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1263 + difference 4 1) (sourceB1263 + difference 1 4) sourceC1263) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4559) := by
    have ha : (tripleCharges (sourceA1263 + difference 4 1) (sourceB1263 + difference 1 4) sourceC1263) = raw20361 := by
      apply Matrix.ext; unfold tripleCharges sourceA1263 sourceB1263 sourceC1263 difference raw20361; decide +kernel
    rw [ha]
    exact (canonical20361 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1263 + difference 4 2) (sourceB1263 + difference 2 4) sourceC1263) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4559) := by
    have ha : (tripleCharges (sourceA1263 + difference 4 2) (sourceB1263 + difference 2 4) sourceC1263) = raw20362 := by
      apply Matrix.ext; unfold tripleCharges sourceA1263 sourceB1263 sourceC1263 difference raw20362; decide +kernel
    rw [ha]
    exact (canonical20362 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1263 + difference 4 3) (sourceB1263 + difference 3 4) sourceC1263) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4559) := by
    have ha : (tripleCharges (sourceA1263 + difference 4 3) (sourceB1263 + difference 3 4) sourceC1263) = raw20363 := by
      apply Matrix.ext; unfold tripleCharges sourceA1263 sourceB1263 sourceC1263 difference raw20363; decide +kernel
    rw [ha]
    exact (canonical20363 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1263 + difference 4 5) (sourceB1263 + difference 5 4) sourceC1263) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4627) := by
    have ha : (tripleCharges (sourceA1263 + difference 4 5) (sourceB1263 + difference 5 4) sourceC1263) = raw10232 := by
      apply Matrix.ext; unfold tripleCharges sourceA1263 sourceB1263 sourceC1263 difference raw10232; decide +kernel
    rw [ha]
    exact (canonical10232 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1263 + difference 5 0) (sourceB1263 + difference 0 5) sourceC1263) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4187) := by
    have ha : (tripleCharges (sourceA1263 + difference 5 0) (sourceB1263 + difference 0 5) sourceC1263) = raw19516 := by
      apply Matrix.ext; unfold tripleCharges sourceA1263 sourceB1263 sourceC1263 difference raw19516; decide +kernel
    rw [ha]
    exact (canonical19516 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1263 + difference 5 1) (sourceB1263 + difference 1 5) sourceC1263) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4555) := by
    have ha : (tripleCharges (sourceA1263 + difference 5 1) (sourceB1263 + difference 1 5) sourceC1263) = raw19517 := by
      apply Matrix.ext; unfold tripleCharges sourceA1263 sourceB1263 sourceC1263 difference raw19517; decide +kernel
    rw [ha]
    exact (canonical19517 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1263 + difference 5 2) (sourceB1263 + difference 2 5) sourceC1263) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4555) := by
    have ha : (tripleCharges (sourceA1263 + difference 5 2) (sourceB1263 + difference 2 5) sourceC1263) = raw19518 := by
      apply Matrix.ext; unfold tripleCharges sourceA1263 sourceB1263 sourceC1263 difference raw19518; decide +kernel
    rw [ha]
    exact (canonical19518 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1263 + difference 5 3) (sourceB1263 + difference 3 5) sourceC1263) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4555) := by
    have ha : (tripleCharges (sourceA1263 + difference 5 3) (sourceB1263 + difference 3 5) sourceC1263) = raw19519 := by
      apply Matrix.ext; unfold tripleCharges sourceA1263 sourceB1263 sourceC1263 difference raw19519; decide +kernel
    rw [ha]
    exact (canonical19519 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1263 + difference 5 4) (sourceB1263 + difference 4 5) sourceC1263) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4629) := by
    have ha : (tripleCharges (sourceA1263 + difference 5 4) (sourceB1263 + difference 4 5) sourceC1263) = raw5083 := by
      apply Matrix.ext; unfold tripleCharges sourceA1263 sourceB1263 sourceC1263 difference raw5083; decide +kernel
    rw [ha]
    exact (canonical5083 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1263 sourceB1263 sourceC1263
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1263, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1264 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1264 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC1264 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceForm1264 : Integer.Sparse Master := [(Sum.inr 611, 3), (Sum.inr 615, 1), (Sum.inr 620, 1), (Sum.inr 1136, 6), (Sum.inr 1140, 3), (Sum.inr 1145, 3), (Sum.inr 1305, 3), (Sum.inr 1307, 3), (Sum.inr 1311, 1), (Sum.inr 1313, 1), (Sum.inr 2965, 3), (Sum.inr 3124, 1), (Sum.inr 3126, 1)]

theorem sourceEq1264 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1264 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1264 + difference 0 1) (sourceB1264 + difference 1 0) sourceC1264) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2965) := by
    have ha : (tripleCharges (sourceA1264 + difference 0 1) (sourceB1264 + difference 1 0) sourceC1264) = raw20364 := by
      apply Matrix.ext; unfold tripleCharges sourceA1264 sourceB1264 sourceC1264 difference raw20364; decide +kernel
    rw [ha]
    exact (canonical20364 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1264 + difference 0 2) (sourceB1264 + difference 2 0) sourceC1264) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2965) := by
    have ha : (tripleCharges (sourceA1264 + difference 0 2) (sourceB1264 + difference 2 0) sourceC1264) = raw20365 := by
      apply Matrix.ext; unfold tripleCharges sourceA1264 sourceB1264 sourceC1264 difference raw20365; decide +kernel
    rw [ha]
    exact (canonical20365 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1264 + difference 0 3) (sourceB1264 + difference 3 0) sourceC1264) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2965) := by
    have ha : (tripleCharges (sourceA1264 + difference 0 3) (sourceB1264 + difference 3 0) sourceC1264) = raw20366 := by
      apply Matrix.ext; unfold tripleCharges sourceA1264 sourceB1264 sourceC1264 difference raw20366; decide +kernel
    rw [ha]
    exact (canonical20366 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1264 + difference 0 4) (sourceB1264 + difference 4 0) sourceC1264) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3126) := by
    have ha : (tripleCharges (sourceA1264 + difference 0 4) (sourceB1264 + difference 4 0) sourceC1264) = raw19529 := by
      apply Matrix.ext; unfold tripleCharges sourceA1264 sourceB1264 sourceC1264 difference raw19529; decide +kernel
    rw [ha]
    exact (canonical19529 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1264 + difference 0 5) (sourceB1264 + difference 5 0) sourceC1264) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3124) := by
    have ha : (tripleCharges (sourceA1264 + difference 0 5) (sourceB1264 + difference 5 0) sourceC1264) = raw12129 := by
      apply Matrix.ext; unfold tripleCharges sourceA1264 sourceB1264 sourceC1264 difference raw12129; decide +kernel
    rw [ha]
    exact (canonical12129 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1264 + difference 1 0) (sourceB1264 + difference 0 1) sourceC1264) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 611) := by
    have ha : (tripleCharges (sourceA1264 + difference 1 0) (sourceB1264 + difference 0 1) sourceC1264) = raw20367 := by
      apply Matrix.ext; unfold tripleCharges sourceA1264 sourceB1264 sourceC1264 difference raw20367; decide +kernel
    rw [ha]
    exact (canonical20367 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1264 + difference 1 2) (sourceB1264 + difference 2 1) sourceC1264) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1136) := by
    have ha : (tripleCharges (sourceA1264 + difference 1 2) (sourceB1264 + difference 2 1) sourceC1264) = raw20368 := by
      apply Matrix.ext; unfold tripleCharges sourceA1264 sourceB1264 sourceC1264 difference raw20368; decide +kernel
    rw [ha]
    exact (canonical20368 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1264 + difference 1 3) (sourceB1264 + difference 3 1) sourceC1264) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1136) := by
    have ha : (tripleCharges (sourceA1264 + difference 1 3) (sourceB1264 + difference 3 1) sourceC1264) = raw20369 := by
      apply Matrix.ext; unfold tripleCharges sourceA1264 sourceB1264 sourceC1264 difference raw20369; decide +kernel
    rw [ha]
    exact (canonical20369 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1264 + difference 1 4) (sourceB1264 + difference 4 1) sourceC1264) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1307) := by
    have ha : (tripleCharges (sourceA1264 + difference 1 4) (sourceB1264 + difference 4 1) sourceC1264) = raw19534 := by
      apply Matrix.ext; unfold tripleCharges sourceA1264 sourceB1264 sourceC1264 difference raw19534; decide +kernel
    rw [ha]
    exact (canonical19534 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1264 + difference 1 5) (sourceB1264 + difference 5 1) sourceC1264) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1305) := by
    have ha : (tripleCharges (sourceA1264 + difference 1 5) (sourceB1264 + difference 5 1) sourceC1264) = raw20370 := by
      apply Matrix.ext; unfold tripleCharges sourceA1264 sourceB1264 sourceC1264 difference raw20370; decide +kernel
    rw [ha]
    exact (canonical20370 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1264 + difference 2 0) (sourceB1264 + difference 0 2) sourceC1264) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 611) := by
    have ha : (tripleCharges (sourceA1264 + difference 2 0) (sourceB1264 + difference 0 2) sourceC1264) = raw20371 := by
      apply Matrix.ext; unfold tripleCharges sourceA1264 sourceB1264 sourceC1264 difference raw20371; decide +kernel
    rw [ha]
    exact (canonical20371 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1264 + difference 2 1) (sourceB1264 + difference 1 2) sourceC1264) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1136) := by
    have ha : (tripleCharges (sourceA1264 + difference 2 1) (sourceB1264 + difference 1 2) sourceC1264) = raw20372 := by
      apply Matrix.ext; unfold tripleCharges sourceA1264 sourceB1264 sourceC1264 difference raw20372; decide +kernel
    rw [ha]
    exact (canonical20372 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1264 + difference 2 3) (sourceB1264 + difference 3 2) sourceC1264) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1136) := by
    have ha : (tripleCharges (sourceA1264 + difference 2 3) (sourceB1264 + difference 3 2) sourceC1264) = raw20373 := by
      apply Matrix.ext; unfold tripleCharges sourceA1264 sourceB1264 sourceC1264 difference raw20373; decide +kernel
    rw [ha]
    exact (canonical20373 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1264 + difference 2 4) (sourceB1264 + difference 4 2) sourceC1264) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1307) := by
    have ha : (tripleCharges (sourceA1264 + difference 2 4) (sourceB1264 + difference 4 2) sourceC1264) = raw19539 := by
      apply Matrix.ext; unfold tripleCharges sourceA1264 sourceB1264 sourceC1264 difference raw19539; decide +kernel
    rw [ha]
    exact (canonical19539 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1264 + difference 2 5) (sourceB1264 + difference 5 2) sourceC1264) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1305) := by
    have ha : (tripleCharges (sourceA1264 + difference 2 5) (sourceB1264 + difference 5 2) sourceC1264) = raw20374 := by
      apply Matrix.ext; unfold tripleCharges sourceA1264 sourceB1264 sourceC1264 difference raw20374; decide +kernel
    rw [ha]
    exact (canonical20374 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1264 + difference 3 0) (sourceB1264 + difference 0 3) sourceC1264) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 611) := by
    have ha : (tripleCharges (sourceA1264 + difference 3 0) (sourceB1264 + difference 0 3) sourceC1264) = raw20375 := by
      apply Matrix.ext; unfold tripleCharges sourceA1264 sourceB1264 sourceC1264 difference raw20375; decide +kernel
    rw [ha]
    exact (canonical20375 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1264 + difference 3 1) (sourceB1264 + difference 1 3) sourceC1264) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1136) := by
    have ha : (tripleCharges (sourceA1264 + difference 3 1) (sourceB1264 + difference 1 3) sourceC1264) = raw20376 := by
      apply Matrix.ext; unfold tripleCharges sourceA1264 sourceB1264 sourceC1264 difference raw20376; decide +kernel
    rw [ha]
    exact (canonical20376 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1264 + difference 3 2) (sourceB1264 + difference 2 3) sourceC1264) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1136) := by
    have ha : (tripleCharges (sourceA1264 + difference 3 2) (sourceB1264 + difference 2 3) sourceC1264) = raw20377 := by
      apply Matrix.ext; unfold tripleCharges sourceA1264 sourceB1264 sourceC1264 difference raw20377; decide +kernel
    rw [ha]
    exact (canonical20377 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1264 + difference 3 4) (sourceB1264 + difference 4 3) sourceC1264) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1307) := by
    have ha : (tripleCharges (sourceA1264 + difference 3 4) (sourceB1264 + difference 4 3) sourceC1264) = raw19544 := by
      apply Matrix.ext; unfold tripleCharges sourceA1264 sourceB1264 sourceC1264 difference raw19544; decide +kernel
    rw [ha]
    exact (canonical19544 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1264 + difference 3 5) (sourceB1264 + difference 5 3) sourceC1264) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1305) := by
    have ha : (tripleCharges (sourceA1264 + difference 3 5) (sourceB1264 + difference 5 3) sourceC1264) = raw12126 := by
      apply Matrix.ext; unfold tripleCharges sourceA1264 sourceB1264 sourceC1264 difference raw12126; decide +kernel
    rw [ha]
    exact (canonical12126 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1264 + difference 4 0) (sourceB1264 + difference 0 4) sourceC1264) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 620) := by
    have ha : (tripleCharges (sourceA1264 + difference 4 0) (sourceB1264 + difference 0 4) sourceC1264) = raw20378 := by
      apply Matrix.ext; unfold tripleCharges sourceA1264 sourceB1264 sourceC1264 difference raw20378; decide +kernel
    rw [ha]
    exact (canonical20378 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1264 + difference 4 1) (sourceB1264 + difference 1 4) sourceC1264) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1145) := by
    have ha : (tripleCharges (sourceA1264 + difference 4 1) (sourceB1264 + difference 1 4) sourceC1264) = raw20379 := by
      apply Matrix.ext; unfold tripleCharges sourceA1264 sourceB1264 sourceC1264 difference raw20379; decide +kernel
    rw [ha]
    exact (canonical20379 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1264 + difference 4 2) (sourceB1264 + difference 2 4) sourceC1264) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1145) := by
    have ha : (tripleCharges (sourceA1264 + difference 4 2) (sourceB1264 + difference 2 4) sourceC1264) = raw20380 := by
      apply Matrix.ext; unfold tripleCharges sourceA1264 sourceB1264 sourceC1264 difference raw20380; decide +kernel
    rw [ha]
    exact (canonical20380 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1264 + difference 4 3) (sourceB1264 + difference 3 4) sourceC1264) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1145) := by
    have ha : (tripleCharges (sourceA1264 + difference 4 3) (sourceB1264 + difference 3 4) sourceC1264) = raw20381 := by
      apply Matrix.ext; unfold tripleCharges sourceA1264 sourceB1264 sourceC1264 difference raw20381; decide +kernel
    rw [ha]
    exact (canonical20381 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1264 + difference 4 5) (sourceB1264 + difference 5 4) sourceC1264) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1311) := by
    have ha : (tripleCharges (sourceA1264 + difference 4 5) (sourceB1264 + difference 5 4) sourceC1264) = raw20382 := by
      apply Matrix.ext; unfold tripleCharges sourceA1264 sourceB1264 sourceC1264 difference raw20382; decide +kernel
    rw [ha]
    exact (canonical20382 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1264 + difference 5 0) (sourceB1264 + difference 0 5) sourceC1264) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 615) := by
    have ha : (tripleCharges (sourceA1264 + difference 5 0) (sourceB1264 + difference 0 5) sourceC1264) = raw19545 := by
      apply Matrix.ext; unfold tripleCharges sourceA1264 sourceB1264 sourceC1264 difference raw19545; decide +kernel
    rw [ha]
    exact (canonical19545 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1264 + difference 5 1) (sourceB1264 + difference 1 5) sourceC1264) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1140) := by
    have ha : (tripleCharges (sourceA1264 + difference 5 1) (sourceB1264 + difference 1 5) sourceC1264) = raw19546 := by
      apply Matrix.ext; unfold tripleCharges sourceA1264 sourceB1264 sourceC1264 difference raw19546; decide +kernel
    rw [ha]
    exact (canonical19546 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1264 + difference 5 2) (sourceB1264 + difference 2 5) sourceC1264) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1140) := by
    have ha : (tripleCharges (sourceA1264 + difference 5 2) (sourceB1264 + difference 2 5) sourceC1264) = raw19547 := by
      apply Matrix.ext; unfold tripleCharges sourceA1264 sourceB1264 sourceC1264 difference raw19547; decide +kernel
    rw [ha]
    exact (canonical19547 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1264 + difference 5 3) (sourceB1264 + difference 3 5) sourceC1264) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1140) := by
    have ha : (tripleCharges (sourceA1264 + difference 5 3) (sourceB1264 + difference 3 5) sourceC1264) = raw19548 := by
      apply Matrix.ext; unfold tripleCharges sourceA1264 sourceB1264 sourceC1264 difference raw19548; decide +kernel
    rw [ha]
    exact (canonical19548 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1264 + difference 5 4) (sourceB1264 + difference 4 5) sourceC1264) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1313) := by
    have ha : (tripleCharges (sourceA1264 + difference 5 4) (sourceB1264 + difference 4 5) sourceC1264) = raw20383 := by
      apply Matrix.ext; unfold tripleCharges sourceA1264 sourceB1264 sourceC1264 difference raw20383; decide +kernel
    rw [ha]
    exact (canonical20383 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1264 sourceB1264 sourceC1264
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1264, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1265 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1265 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1265 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceForm1265 : Integer.Sparse Master := [(Sum.inr 4177, 3), (Sum.inr 4181, 1), (Sum.inr 4191, 1), (Sum.inr 4356, 3), (Sum.inr 4468, 1), (Sum.inr 4546, 6), (Sum.inr 4558, 3), (Sum.inr 4608, 3), (Sum.inr 4624, 3), (Sum.inr 4628, 1), (Sum.inr 5174, 3), (Sum.inr 5296, 1), (Sum.inr 5309, 1)]

theorem sourceEq1265 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1265 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1265 + difference 0 1) (sourceB1265 + difference 1 0) sourceC1265) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5174) := by
    have ha : (tripleCharges (sourceA1265 + difference 0 1) (sourceB1265 + difference 1 0) sourceC1265) = raw4303 := by
      apply Matrix.ext; unfold tripleCharges sourceA1265 sourceB1265 sourceC1265 difference raw4303; decide +kernel
    rw [ha]
    exact (canonical4303 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1265 + difference 0 2) (sourceB1265 + difference 2 0) sourceC1265) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5174) := by
    have ha : (tripleCharges (sourceA1265 + difference 0 2) (sourceB1265 + difference 2 0) sourceC1265) = raw4304 := by
      apply Matrix.ext; unfold tripleCharges sourceA1265 sourceB1265 sourceC1265 difference raw4304; decide +kernel
    rw [ha]
    exact (canonical4304 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1265 + difference 0 3) (sourceB1265 + difference 3 0) sourceC1265) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5174) := by
    have ha : (tripleCharges (sourceA1265 + difference 0 3) (sourceB1265 + difference 3 0) sourceC1265) = raw4305 := by
      apply Matrix.ext; unfold tripleCharges sourceA1265 sourceB1265 sourceC1265 difference raw4305; decide +kernel
    rw [ha]
    exact (canonical4305 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1265 + difference 0 4) (sourceB1265 + difference 4 0) sourceC1265) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5296) := by
    have ha : (tripleCharges (sourceA1265 + difference 0 4) (sourceB1265 + difference 4 0) sourceC1265) = raw10215 := by
      apply Matrix.ext; unfold tripleCharges sourceA1265 sourceB1265 sourceC1265 difference raw10215; decide +kernel
    rw [ha]
    exact (canonical10215 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1265 + difference 0 5) (sourceB1265 + difference 5 0) sourceC1265) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5309) := by
    have ha : (tripleCharges (sourceA1265 + difference 0 5) (sourceB1265 + difference 5 0) sourceC1265) = raw4306 := by
      apply Matrix.ext; unfold tripleCharges sourceA1265 sourceB1265 sourceC1265 difference raw4306; decide +kernel
    rw [ha]
    exact (canonical4306 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1265 + difference 1 0) (sourceB1265 + difference 0 1) sourceC1265) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4177) := by
    have ha : (tripleCharges (sourceA1265 + difference 1 0) (sourceB1265 + difference 0 1) sourceC1265) = raw20384 := by
      apply Matrix.ext; unfold tripleCharges sourceA1265 sourceB1265 sourceC1265 difference raw20384; decide +kernel
    rw [ha]
    exact (canonical20384 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1265 + difference 1 2) (sourceB1265 + difference 2 1) sourceC1265) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4546) := by
    have ha : (tripleCharges (sourceA1265 + difference 1 2) (sourceB1265 + difference 2 1) sourceC1265) = raw20385 := by
      apply Matrix.ext; unfold tripleCharges sourceA1265 sourceB1265 sourceC1265 difference raw20385; decide +kernel
    rw [ha]
    exact (canonical20385 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1265 + difference 1 3) (sourceB1265 + difference 3 1) sourceC1265) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4546) := by
    have ha : (tripleCharges (sourceA1265 + difference 1 3) (sourceB1265 + difference 3 1) sourceC1265) = raw20386 := by
      apply Matrix.ext; unfold tripleCharges sourceA1265 sourceB1265 sourceC1265 difference raw20386; decide +kernel
    rw [ha]
    exact (canonical20386 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1265 + difference 1 4) (sourceB1265 + difference 4 1) sourceC1265) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4608) := by
    have ha : (tripleCharges (sourceA1265 + difference 1 4) (sourceB1265 + difference 4 1) sourceC1265) = raw4287 := by
      apply Matrix.ext; unfold tripleCharges sourceA1265 sourceB1265 sourceC1265 difference raw4287; decide +kernel
    rw [ha]
    exact (canonical4287 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1265 + difference 1 5) (sourceB1265 + difference 5 1) sourceC1265) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4624) := by
    have ha : (tripleCharges (sourceA1265 + difference 1 5) (sourceB1265 + difference 5 1) sourceC1265) = raw10198 := by
      apply Matrix.ext; unfold tripleCharges sourceA1265 sourceB1265 sourceC1265 difference raw10198; decide +kernel
    rw [ha]
    exact (canonical10198 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1265 + difference 2 0) (sourceB1265 + difference 0 2) sourceC1265) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4177) := by
    have ha : (tripleCharges (sourceA1265 + difference 2 0) (sourceB1265 + difference 0 2) sourceC1265) = raw20387 := by
      apply Matrix.ext; unfold tripleCharges sourceA1265 sourceB1265 sourceC1265 difference raw20387; decide +kernel
    rw [ha]
    exact (canonical20387 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1265 + difference 2 1) (sourceB1265 + difference 1 2) sourceC1265) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4546) := by
    have ha : (tripleCharges (sourceA1265 + difference 2 1) (sourceB1265 + difference 1 2) sourceC1265) = raw20388 := by
      apply Matrix.ext; unfold tripleCharges sourceA1265 sourceB1265 sourceC1265 difference raw20388; decide +kernel
    rw [ha]
    exact (canonical20388 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1265 + difference 2 3) (sourceB1265 + difference 3 2) sourceC1265) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4546) := by
    have ha : (tripleCharges (sourceA1265 + difference 2 3) (sourceB1265 + difference 3 2) sourceC1265) = raw20389 := by
      apply Matrix.ext; unfold tripleCharges sourceA1265 sourceB1265 sourceC1265 difference raw20389; decide +kernel
    rw [ha]
    exact (canonical20389 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1265 + difference 2 4) (sourceB1265 + difference 4 2) sourceC1265) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4608) := by
    have ha : (tripleCharges (sourceA1265 + difference 2 4) (sourceB1265 + difference 4 2) sourceC1265) = raw4292 := by
      apply Matrix.ext; unfold tripleCharges sourceA1265 sourceB1265 sourceC1265 difference raw4292; decide +kernel
    rw [ha]
    exact (canonical4292 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1265 + difference 2 5) (sourceB1265 + difference 5 2) sourceC1265) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4624) := by
    have ha : (tripleCharges (sourceA1265 + difference 2 5) (sourceB1265 + difference 5 2) sourceC1265) = raw10202 := by
      apply Matrix.ext; unfold tripleCharges sourceA1265 sourceB1265 sourceC1265 difference raw10202; decide +kernel
    rw [ha]
    exact (canonical10202 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1265 + difference 3 0) (sourceB1265 + difference 0 3) sourceC1265) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4177) := by
    have ha : (tripleCharges (sourceA1265 + difference 3 0) (sourceB1265 + difference 0 3) sourceC1265) = raw20390 := by
      apply Matrix.ext; unfold tripleCharges sourceA1265 sourceB1265 sourceC1265 difference raw20390; decide +kernel
    rw [ha]
    exact (canonical20390 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1265 + difference 3 1) (sourceB1265 + difference 1 3) sourceC1265) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4546) := by
    have ha : (tripleCharges (sourceA1265 + difference 3 1) (sourceB1265 + difference 1 3) sourceC1265) = raw20391 := by
      apply Matrix.ext; unfold tripleCharges sourceA1265 sourceB1265 sourceC1265 difference raw20391; decide +kernel
    rw [ha]
    exact (canonical20391 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1265 + difference 3 2) (sourceB1265 + difference 2 3) sourceC1265) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4546) := by
    have ha : (tripleCharges (sourceA1265 + difference 3 2) (sourceB1265 + difference 2 3) sourceC1265) = raw20392 := by
      apply Matrix.ext; unfold tripleCharges sourceA1265 sourceB1265 sourceC1265 difference raw20392; decide +kernel
    rw [ha]
    exact (canonical20392 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1265 + difference 3 4) (sourceB1265 + difference 4 3) sourceC1265) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4608) := by
    have ha : (tripleCharges (sourceA1265 + difference 3 4) (sourceB1265 + difference 4 3) sourceC1265) = raw4297 := by
      apply Matrix.ext; unfold tripleCharges sourceA1265 sourceB1265 sourceC1265 difference raw4297; decide +kernel
    rw [ha]
    exact (canonical4297 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1265 + difference 3 5) (sourceB1265 + difference 5 3) sourceC1265) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4624) := by
    have ha : (tripleCharges (sourceA1265 + difference 3 5) (sourceB1265 + difference 5 3) sourceC1265) = raw10206 := by
      apply Matrix.ext; unfold tripleCharges sourceA1265 sourceB1265 sourceC1265 difference raw10206; decide +kernel
    rw [ha]
    exact (canonical10206 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1265 + difference 4 0) (sourceB1265 + difference 0 4) sourceC1265) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4191) := by
    have ha : (tripleCharges (sourceA1265 + difference 4 0) (sourceB1265 + difference 0 4) sourceC1265) = raw20393 := by
      apply Matrix.ext; unfold tripleCharges sourceA1265 sourceB1265 sourceC1265 difference raw20393; decide +kernel
    rw [ha]
    exact (canonical20393 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1265 + difference 4 1) (sourceB1265 + difference 1 4) sourceC1265) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4558) := by
    have ha : (tripleCharges (sourceA1265 + difference 4 1) (sourceB1265 + difference 1 4) sourceC1265) = raw20394 := by
      apply Matrix.ext; unfold tripleCharges sourceA1265 sourceB1265 sourceC1265 difference raw20394; decide +kernel
    rw [ha]
    exact (canonical20394 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1265 + difference 4 2) (sourceB1265 + difference 2 4) sourceC1265) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4558) := by
    have ha : (tripleCharges (sourceA1265 + difference 4 2) (sourceB1265 + difference 2 4) sourceC1265) = raw20395 := by
      apply Matrix.ext; unfold tripleCharges sourceA1265 sourceB1265 sourceC1265 difference raw20395; decide +kernel
    rw [ha]
    exact (canonical20395 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1265 + difference 4 3) (sourceB1265 + difference 3 4) sourceC1265) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4558) := by
    have ha : (tripleCharges (sourceA1265 + difference 4 3) (sourceB1265 + difference 3 4) sourceC1265) = raw20396 := by
      apply Matrix.ext; unfold tripleCharges sourceA1265 sourceB1265 sourceC1265 difference raw20396; decide +kernel
    rw [ha]
    exact (canonical20396 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1265 + difference 4 5) (sourceB1265 + difference 5 4) sourceC1265) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4628) := by
    have ha : (tripleCharges (sourceA1265 + difference 4 5) (sourceB1265 + difference 5 4) sourceC1265) = raw10210 := by
      apply Matrix.ext; unfold tripleCharges sourceA1265 sourceB1265 sourceC1265 difference raw10210; decide +kernel
    rw [ha]
    exact (canonical10210 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1265 + difference 5 0) (sourceB1265 + difference 0 5) sourceC1265) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4181) := by
    have ha : (tripleCharges (sourceA1265 + difference 5 0) (sourceB1265 + difference 0 5) sourceC1265) = raw19719 := by
      apply Matrix.ext; unfold tripleCharges sourceA1265 sourceB1265 sourceC1265 difference raw19719; decide +kernel
    rw [ha]
    exact (canonical19719 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1265 + difference 5 1) (sourceB1265 + difference 1 5) sourceC1265) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4356) := by
    have ha : (tripleCharges (sourceA1265 + difference 5 1) (sourceB1265 + difference 1 5) sourceC1265) = raw19720 := by
      apply Matrix.ext; unfold tripleCharges sourceA1265 sourceB1265 sourceC1265 difference raw19720; decide +kernel
    rw [ha]
    exact (canonical19720 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1265 + difference 5 2) (sourceB1265 + difference 2 5) sourceC1265) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4356) := by
    have ha : (tripleCharges (sourceA1265 + difference 5 2) (sourceB1265 + difference 2 5) sourceC1265) = raw19721 := by
      apply Matrix.ext; unfold tripleCharges sourceA1265 sourceB1265 sourceC1265 difference raw19721; decide +kernel
    rw [ha]
    exact (canonical19721 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1265 + difference 5 3) (sourceB1265 + difference 3 5) sourceC1265) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4356) := by
    have ha : (tripleCharges (sourceA1265 + difference 5 3) (sourceB1265 + difference 3 5) sourceC1265) = raw19722 := by
      apply Matrix.ext; unfold tripleCharges sourceA1265 sourceB1265 sourceC1265 difference raw19722; decide +kernel
    rw [ha]
    exact (canonical19722 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1265 + difference 5 4) (sourceB1265 + difference 4 5) sourceC1265) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4468) := by
    have ha : (tripleCharges (sourceA1265 + difference 5 4) (sourceB1265 + difference 4 5) sourceC1265) = raw4307 := by
      apply Matrix.ext; unfold tripleCharges sourceA1265 sourceB1265 sourceC1265 difference raw4307; decide +kernel
    rw [ha]
    exact (canonical4307 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1265 sourceB1265 sourceC1265
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1265, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1266 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1266 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1266 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceForm1266 : Integer.Sparse Master := [(Sum.inr 605, 3), (Sum.inr 609, 1), (Sum.inr 619, 1), (Sum.inr 934, 3), (Sum.inr 1051, 1), (Sum.inr 1131, 6), (Sum.inr 1144, 3), (Sum.inr 1242, 3), (Sum.inr 1301, 3), (Sum.inr 1312, 1), (Sum.inr 2601, 3), (Sum.inr 2770, 1), (Sum.inr 3123, 1)]

theorem sourceEq1266 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1266 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1266 + difference 0 1) (sourceB1266 + difference 1 0) sourceC1266) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2601) := by
    have ha : (tripleCharges (sourceA1266 + difference 0 1) (sourceB1266 + difference 1 0) sourceC1266) = raw4333 := by
      apply Matrix.ext; unfold tripleCharges sourceA1266 sourceB1266 sourceC1266 difference raw4333; decide +kernel
    rw [ha]
    exact (canonical4333 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1266 + difference 0 2) (sourceB1266 + difference 2 0) sourceC1266) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2601) := by
    have ha : (tripleCharges (sourceA1266 + difference 0 2) (sourceB1266 + difference 2 0) sourceC1266) = raw4334 := by
      apply Matrix.ext; unfold tripleCharges sourceA1266 sourceB1266 sourceC1266 difference raw4334; decide +kernel
    rw [ha]
    exact (canonical4334 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1266 + difference 0 3) (sourceB1266 + difference 3 0) sourceC1266) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2601) := by
    have ha : (tripleCharges (sourceA1266 + difference 0 3) (sourceB1266 + difference 3 0) sourceC1266) = raw4335 := by
      apply Matrix.ext; unfold tripleCharges sourceA1266 sourceB1266 sourceC1266 difference raw4335; decide +kernel
    rw [ha]
    exact (canonical4335 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1266 + difference 0 4) (sourceB1266 + difference 4 0) sourceC1266) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2770) := by
    have ha : (tripleCharges (sourceA1266 + difference 0 4) (sourceB1266 + difference 4 0) sourceC1266) = raw19728 := by
      apply Matrix.ext; unfold tripleCharges sourceA1266 sourceB1266 sourceC1266 difference raw19728; decide +kernel
    rw [ha]
    exact (canonical19728 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1266 + difference 0 5) (sourceB1266 + difference 5 0) sourceC1266) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3123) := by
    have ha : (tripleCharges (sourceA1266 + difference 0 5) (sourceB1266 + difference 5 0) sourceC1266) = raw4336 := by
      apply Matrix.ext; unfold tripleCharges sourceA1266 sourceB1266 sourceC1266 difference raw4336; decide +kernel
    rw [ha]
    exact (canonical4336 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1266 + difference 1 0) (sourceB1266 + difference 0 1) sourceC1266) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 605) := by
    have ha : (tripleCharges (sourceA1266 + difference 1 0) (sourceB1266 + difference 0 1) sourceC1266) = raw20397 := by
      apply Matrix.ext; unfold tripleCharges sourceA1266 sourceB1266 sourceC1266 difference raw20397; decide +kernel
    rw [ha]
    exact (canonical20397 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1266 + difference 1 2) (sourceB1266 + difference 2 1) sourceC1266) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1131) := by
    have ha : (tripleCharges (sourceA1266 + difference 1 2) (sourceB1266 + difference 2 1) sourceC1266) = raw20398 := by
      apply Matrix.ext; unfold tripleCharges sourceA1266 sourceB1266 sourceC1266 difference raw20398; decide +kernel
    rw [ha]
    exact (canonical20398 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1266 + difference 1 3) (sourceB1266 + difference 3 1) sourceC1266) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1131) := by
    have ha : (tripleCharges (sourceA1266 + difference 1 3) (sourceB1266 + difference 3 1) sourceC1266) = raw20399 := by
      apply Matrix.ext; unfold tripleCharges sourceA1266 sourceB1266 sourceC1266 difference raw20399; decide +kernel
    rw [ha]
    exact (canonical20399 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1266 + difference 1 4) (sourceB1266 + difference 4 1) sourceC1266) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1242) := by
    have ha : (tripleCharges (sourceA1266 + difference 1 4) (sourceB1266 + difference 4 1) sourceC1266) = raw4317 := by
      apply Matrix.ext; unfold tripleCharges sourceA1266 sourceB1266 sourceC1266 difference raw4317; decide +kernel
    rw [ha]
    exact (canonical4317 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1266 + difference 1 5) (sourceB1266 + difference 5 1) sourceC1266) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1301) := by
    have ha : (tripleCharges (sourceA1266 + difference 1 5) (sourceB1266 + difference 5 1) sourceC1266) = raw20400 := by
      apply Matrix.ext; unfold tripleCharges sourceA1266 sourceB1266 sourceC1266 difference raw20400; decide +kernel
    rw [ha]
    exact (canonical20400 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1266 + difference 2 0) (sourceB1266 + difference 0 2) sourceC1266) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 605) := by
    have ha : (tripleCharges (sourceA1266 + difference 2 0) (sourceB1266 + difference 0 2) sourceC1266) = raw20401 := by
      apply Matrix.ext; unfold tripleCharges sourceA1266 sourceB1266 sourceC1266 difference raw20401; decide +kernel
    rw [ha]
    exact (canonical20401 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1266 + difference 2 1) (sourceB1266 + difference 1 2) sourceC1266) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1131) := by
    have ha : (tripleCharges (sourceA1266 + difference 2 1) (sourceB1266 + difference 1 2) sourceC1266) = raw20402 := by
      apply Matrix.ext; unfold tripleCharges sourceA1266 sourceB1266 sourceC1266 difference raw20402; decide +kernel
    rw [ha]
    exact (canonical20402 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1266 + difference 2 3) (sourceB1266 + difference 3 2) sourceC1266) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1131) := by
    have ha : (tripleCharges (sourceA1266 + difference 2 3) (sourceB1266 + difference 3 2) sourceC1266) = raw20403 := by
      apply Matrix.ext; unfold tripleCharges sourceA1266 sourceB1266 sourceC1266 difference raw20403; decide +kernel
    rw [ha]
    exact (canonical20403 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1266 + difference 2 4) (sourceB1266 + difference 4 2) sourceC1266) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1242) := by
    have ha : (tripleCharges (sourceA1266 + difference 2 4) (sourceB1266 + difference 4 2) sourceC1266) = raw4322 := by
      apply Matrix.ext; unfold tripleCharges sourceA1266 sourceB1266 sourceC1266 difference raw4322; decide +kernel
    rw [ha]
    exact (canonical4322 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1266 + difference 2 5) (sourceB1266 + difference 5 2) sourceC1266) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1301) := by
    have ha : (tripleCharges (sourceA1266 + difference 2 5) (sourceB1266 + difference 5 2) sourceC1266) = raw20404 := by
      apply Matrix.ext; unfold tripleCharges sourceA1266 sourceB1266 sourceC1266 difference raw20404; decide +kernel
    rw [ha]
    exact (canonical20404 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1266 + difference 3 0) (sourceB1266 + difference 0 3) sourceC1266) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 605) := by
    have ha : (tripleCharges (sourceA1266 + difference 3 0) (sourceB1266 + difference 0 3) sourceC1266) = raw20405 := by
      apply Matrix.ext; unfold tripleCharges sourceA1266 sourceB1266 sourceC1266 difference raw20405; decide +kernel
    rw [ha]
    exact (canonical20405 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1266 + difference 3 1) (sourceB1266 + difference 1 3) sourceC1266) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1131) := by
    have ha : (tripleCharges (sourceA1266 + difference 3 1) (sourceB1266 + difference 1 3) sourceC1266) = raw20406 := by
      apply Matrix.ext; unfold tripleCharges sourceA1266 sourceB1266 sourceC1266 difference raw20406; decide +kernel
    rw [ha]
    exact (canonical20406 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1266 + difference 3 2) (sourceB1266 + difference 2 3) sourceC1266) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1131) := by
    have ha : (tripleCharges (sourceA1266 + difference 3 2) (sourceB1266 + difference 2 3) sourceC1266) = raw20407 := by
      apply Matrix.ext; unfold tripleCharges sourceA1266 sourceB1266 sourceC1266 difference raw20407; decide +kernel
    rw [ha]
    exact (canonical20407 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1266 + difference 3 4) (sourceB1266 + difference 4 3) sourceC1266) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1242) := by
    have ha : (tripleCharges (sourceA1266 + difference 3 4) (sourceB1266 + difference 4 3) sourceC1266) = raw4327 := by
      apply Matrix.ext; unfold tripleCharges sourceA1266 sourceB1266 sourceC1266 difference raw4327; decide +kernel
    rw [ha]
    exact (canonical4327 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1266 + difference 3 5) (sourceB1266 + difference 5 3) sourceC1266) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1301) := by
    have ha : (tripleCharges (sourceA1266 + difference 3 5) (sourceB1266 + difference 5 3) sourceC1266) = raw20408 := by
      apply Matrix.ext; unfold tripleCharges sourceA1266 sourceB1266 sourceC1266 difference raw20408; decide +kernel
    rw [ha]
    exact (canonical20408 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1266 + difference 4 0) (sourceB1266 + difference 0 4) sourceC1266) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 619) := by
    have ha : (tripleCharges (sourceA1266 + difference 4 0) (sourceB1266 + difference 0 4) sourceC1266) = raw20409 := by
      apply Matrix.ext; unfold tripleCharges sourceA1266 sourceB1266 sourceC1266 difference raw20409; decide +kernel
    rw [ha]
    exact (canonical20409 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1266 + difference 4 1) (sourceB1266 + difference 1 4) sourceC1266) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1144) := by
    have ha : (tripleCharges (sourceA1266 + difference 4 1) (sourceB1266 + difference 1 4) sourceC1266) = raw20410 := by
      apply Matrix.ext; unfold tripleCharges sourceA1266 sourceB1266 sourceC1266 difference raw20410; decide +kernel
    rw [ha]
    exact (canonical20410 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1266 + difference 4 2) (sourceB1266 + difference 2 4) sourceC1266) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1144) := by
    have ha : (tripleCharges (sourceA1266 + difference 4 2) (sourceB1266 + difference 2 4) sourceC1266) = raw20411 := by
      apply Matrix.ext; unfold tripleCharges sourceA1266 sourceB1266 sourceC1266 difference raw20411; decide +kernel
    rw [ha]
    exact (canonical20411 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1266 + difference 4 3) (sourceB1266 + difference 3 4) sourceC1266) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1144) := by
    have ha : (tripleCharges (sourceA1266 + difference 4 3) (sourceB1266 + difference 3 4) sourceC1266) = raw20412 := by
      apply Matrix.ext; unfold tripleCharges sourceA1266 sourceB1266 sourceC1266 difference raw20412; decide +kernel
    rw [ha]
    exact (canonical20412 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1266 + difference 4 5) (sourceB1266 + difference 5 4) sourceC1266) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1312) := by
    have ha : (tripleCharges (sourceA1266 + difference 4 5) (sourceB1266 + difference 5 4) sourceC1266) = raw20413 := by
      apply Matrix.ext; unfold tripleCharges sourceA1266 sourceB1266 sourceC1266 difference raw20413; decide +kernel
    rw [ha]
    exact (canonical20413 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1266 + difference 5 0) (sourceB1266 + difference 0 5) sourceC1266) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 609) := by
    have ha : (tripleCharges (sourceA1266 + difference 5 0) (sourceB1266 + difference 0 5) sourceC1266) = raw19741 := by
      apply Matrix.ext; unfold tripleCharges sourceA1266 sourceB1266 sourceC1266 difference raw19741; decide +kernel
    rw [ha]
    exact (canonical19741 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1266 + difference 5 1) (sourceB1266 + difference 1 5) sourceC1266) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 934) := by
    have ha : (tripleCharges (sourceA1266 + difference 5 1) (sourceB1266 + difference 1 5) sourceC1266) = raw19742 := by
      apply Matrix.ext; unfold tripleCharges sourceA1266 sourceB1266 sourceC1266 difference raw19742; decide +kernel
    rw [ha]
    exact (canonical19742 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1266 + difference 5 2) (sourceB1266 + difference 2 5) sourceC1266) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 934) := by
    have ha : (tripleCharges (sourceA1266 + difference 5 2) (sourceB1266 + difference 2 5) sourceC1266) = raw19743 := by
      apply Matrix.ext; unfold tripleCharges sourceA1266 sourceB1266 sourceC1266 difference raw19743; decide +kernel
    rw [ha]
    exact (canonical19743 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1266 + difference 5 3) (sourceB1266 + difference 3 5) sourceC1266) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 934) := by
    have ha : (tripleCharges (sourceA1266 + difference 5 3) (sourceB1266 + difference 3 5) sourceC1266) = raw19744 := by
      apply Matrix.ext; unfold tripleCharges sourceA1266 sourceB1266 sourceC1266 difference raw19744; decide +kernel
    rw [ha]
    exact (canonical19744 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1266 + difference 5 4) (sourceB1266 + difference 4 5) sourceC1266) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1051) := by
    have ha : (tripleCharges (sourceA1266 + difference 5 4) (sourceB1266 + difference 4 5) sourceC1266) = raw4337 := by
      apply Matrix.ext; unfold tripleCharges sourceA1266 sourceB1266 sourceC1266 difference raw4337; decide +kernel
    rw [ha]
    exact (canonical4337 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1266 sourceB1266 sourceC1266
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1266, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1267 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceB1267 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1267 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1267 : Integer.Sparse Master := [(Sum.inr 4460, 3), (Sum.inr 4463, 3), (Sum.inr 4501, 1), (Sum.inr 4505, 2), (Sum.inr 4507, 1), (Sum.inr 4591, 6), (Sum.inr 4605, 3), (Sum.inr 4608, 6), (Sum.inr 4609, 3), (Sum.inr 4621, 1), (Sum.inr 4625, 1)]

theorem sourceEq1267 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1267 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1267 + difference 0 1) (sourceB1267 + difference 1 0) sourceC1267) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4463) := by
    have ha : (tripleCharges (sourceA1267 + difference 0 1) (sourceB1267 + difference 1 0) sourceC1267) = raw20414 := by
      apply Matrix.ext; unfold tripleCharges sourceA1267 sourceB1267 sourceC1267 difference raw20414; decide +kernel
    rw [ha]
    exact (canonical20414 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1267 + difference 0 2) (sourceB1267 + difference 2 0) sourceC1267) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4463) := by
    have ha : (tripleCharges (sourceA1267 + difference 0 2) (sourceB1267 + difference 2 0) sourceC1267) = raw20415 := by
      apply Matrix.ext; unfold tripleCharges sourceA1267 sourceB1267 sourceC1267 difference raw20415; decide +kernel
    rw [ha]
    exact (canonical20415 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1267 + difference 0 3) (sourceB1267 + difference 3 0) sourceC1267) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4463) := by
    have ha : (tripleCharges (sourceA1267 + difference 0 3) (sourceB1267 + difference 3 0) sourceC1267) = raw20416 := by
      apply Matrix.ext; unfold tripleCharges sourceA1267 sourceB1267 sourceC1267 difference raw20416; decide +kernel
    rw [ha]
    exact (canonical20416 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1267 + difference 0 4) (sourceB1267 + difference 4 0) sourceC1267) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4507) := by
    have ha : (tripleCharges (sourceA1267 + difference 0 4) (sourceB1267 + difference 4 0) sourceC1267) = raw20417 := by
      apply Matrix.ext; unfold tripleCharges sourceA1267 sourceB1267 sourceC1267 difference raw20417; decide +kernel
    rw [ha]
    exact (canonical20417 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1267 + difference 0 5) (sourceB1267 + difference 5 0) sourceC1267) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4505) := by
    have ha : (tripleCharges (sourceA1267 + difference 0 5) (sourceB1267 + difference 5 0) sourceC1267) = raw20418 := by
      apply Matrix.ext; unfold tripleCharges sourceA1267 sourceB1267 sourceC1267 difference raw20418; decide +kernel
    rw [ha]
    exact (canonical20418 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1267 + difference 1 0) (sourceB1267 + difference 0 1) sourceC1267) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4460) := by
    have ha : (tripleCharges (sourceA1267 + difference 1 0) (sourceB1267 + difference 0 1) sourceC1267) = raw20419 := by
      apply Matrix.ext; unfold tripleCharges sourceA1267 sourceB1267 sourceC1267 difference raw20419; decide +kernel
    rw [ha]
    exact (canonical20419 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1267 + difference 1 2) (sourceB1267 + difference 2 1) sourceC1267) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4591) := by
    have ha : (tripleCharges (sourceA1267 + difference 1 2) (sourceB1267 + difference 2 1) sourceC1267) = raw20420 := by
      apply Matrix.ext; unfold tripleCharges sourceA1267 sourceB1267 sourceC1267 difference raw20420; decide +kernel
    rw [ha]
    exact (canonical20420 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1267 + difference 1 3) (sourceB1267 + difference 3 1) sourceC1267) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4591) := by
    have ha : (tripleCharges (sourceA1267 + difference 1 3) (sourceB1267 + difference 3 1) sourceC1267) = raw20421 := by
      apply Matrix.ext; unfold tripleCharges sourceA1267 sourceB1267 sourceC1267 difference raw20421; decide +kernel
    rw [ha]
    exact (canonical20421 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1267 + difference 1 4) (sourceB1267 + difference 4 1) sourceC1267) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4609) := by
    have ha : (tripleCharges (sourceA1267 + difference 1 4) (sourceB1267 + difference 4 1) sourceC1267) = raw20422 := by
      apply Matrix.ext; unfold tripleCharges sourceA1267 sourceB1267 sourceC1267 difference raw20422; decide +kernel
    rw [ha]
    exact (canonical20422 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1267 + difference 1 5) (sourceB1267 + difference 5 1) sourceC1267) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4608) := by
    have ha : (tripleCharges (sourceA1267 + difference 1 5) (sourceB1267 + difference 5 1) sourceC1267) = raw20423 := by
      apply Matrix.ext; unfold tripleCharges sourceA1267 sourceB1267 sourceC1267 difference raw20423; decide +kernel
    rw [ha]
    exact (canonical20423 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1267 + difference 2 0) (sourceB1267 + difference 0 2) sourceC1267) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4460) := by
    have ha : (tripleCharges (sourceA1267 + difference 2 0) (sourceB1267 + difference 0 2) sourceC1267) = raw20424 := by
      apply Matrix.ext; unfold tripleCharges sourceA1267 sourceB1267 sourceC1267 difference raw20424; decide +kernel
    rw [ha]
    exact (canonical20424 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1267 + difference 2 1) (sourceB1267 + difference 1 2) sourceC1267) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4591) := by
    have ha : (tripleCharges (sourceA1267 + difference 2 1) (sourceB1267 + difference 1 2) sourceC1267) = raw20425 := by
      apply Matrix.ext; unfold tripleCharges sourceA1267 sourceB1267 sourceC1267 difference raw20425; decide +kernel
    rw [ha]
    exact (canonical20425 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1267 + difference 2 3) (sourceB1267 + difference 3 2) sourceC1267) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4591) := by
    have ha : (tripleCharges (sourceA1267 + difference 2 3) (sourceB1267 + difference 3 2) sourceC1267) = raw20426 := by
      apply Matrix.ext; unfold tripleCharges sourceA1267 sourceB1267 sourceC1267 difference raw20426; decide +kernel
    rw [ha]
    exact (canonical20426 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1267 + difference 2 4) (sourceB1267 + difference 4 2) sourceC1267) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4609) := by
    have ha : (tripleCharges (sourceA1267 + difference 2 4) (sourceB1267 + difference 4 2) sourceC1267) = raw20427 := by
      apply Matrix.ext; unfold tripleCharges sourceA1267 sourceB1267 sourceC1267 difference raw20427; decide +kernel
    rw [ha]
    exact (canonical20427 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1267 + difference 2 5) (sourceB1267 + difference 5 2) sourceC1267) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4608) := by
    have ha : (tripleCharges (sourceA1267 + difference 2 5) (sourceB1267 + difference 5 2) sourceC1267) = raw20428 := by
      apply Matrix.ext; unfold tripleCharges sourceA1267 sourceB1267 sourceC1267 difference raw20428; decide +kernel
    rw [ha]
    exact (canonical20428 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1267 + difference 3 0) (sourceB1267 + difference 0 3) sourceC1267) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4460) := by
    have ha : (tripleCharges (sourceA1267 + difference 3 0) (sourceB1267 + difference 0 3) sourceC1267) = raw20429 := by
      apply Matrix.ext; unfold tripleCharges sourceA1267 sourceB1267 sourceC1267 difference raw20429; decide +kernel
    rw [ha]
    exact (canonical20429 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1267 + difference 3 1) (sourceB1267 + difference 1 3) sourceC1267) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4591) := by
    have ha : (tripleCharges (sourceA1267 + difference 3 1) (sourceB1267 + difference 1 3) sourceC1267) = raw20430 := by
      apply Matrix.ext; unfold tripleCharges sourceA1267 sourceB1267 sourceC1267 difference raw20430; decide +kernel
    rw [ha]
    exact (canonical20430 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1267 + difference 3 2) (sourceB1267 + difference 2 3) sourceC1267) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4591) := by
    have ha : (tripleCharges (sourceA1267 + difference 3 2) (sourceB1267 + difference 2 3) sourceC1267) = raw20431 := by
      apply Matrix.ext; unfold tripleCharges sourceA1267 sourceB1267 sourceC1267 difference raw20431; decide +kernel
    rw [ha]
    exact (canonical20431 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1267 + difference 3 4) (sourceB1267 + difference 4 3) sourceC1267) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4609) := by
    have ha : (tripleCharges (sourceA1267 + difference 3 4) (sourceB1267 + difference 4 3) sourceC1267) = raw20432 := by
      apply Matrix.ext; unfold tripleCharges sourceA1267 sourceB1267 sourceC1267 difference raw20432; decide +kernel
    rw [ha]
    exact (canonical20432 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1267 + difference 3 5) (sourceB1267 + difference 5 3) sourceC1267) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4608) := by
    have ha : (tripleCharges (sourceA1267 + difference 3 5) (sourceB1267 + difference 5 3) sourceC1267) = raw20433 := by
      apply Matrix.ext; unfold tripleCharges sourceA1267 sourceB1267 sourceC1267 difference raw20433; decide +kernel
    rw [ha]
    exact (canonical20433 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1267 + difference 4 0) (sourceB1267 + difference 0 4) sourceC1267) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4505) := by
    have ha : (tripleCharges (sourceA1267 + difference 4 0) (sourceB1267 + difference 0 4) sourceC1267) = raw20434 := by
      apply Matrix.ext; unfold tripleCharges sourceA1267 sourceB1267 sourceC1267 difference raw20434; decide +kernel
    rw [ha]
    exact (canonical20434 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1267 + difference 4 1) (sourceB1267 + difference 1 4) sourceC1267) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4608) := by
    have ha : (tripleCharges (sourceA1267 + difference 4 1) (sourceB1267 + difference 1 4) sourceC1267) = raw20435 := by
      apply Matrix.ext; unfold tripleCharges sourceA1267 sourceB1267 sourceC1267 difference raw20435; decide +kernel
    rw [ha]
    exact (canonical20435 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1267 + difference 4 2) (sourceB1267 + difference 2 4) sourceC1267) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4608) := by
    have ha : (tripleCharges (sourceA1267 + difference 4 2) (sourceB1267 + difference 2 4) sourceC1267) = raw20436 := by
      apply Matrix.ext; unfold tripleCharges sourceA1267 sourceB1267 sourceC1267 difference raw20436; decide +kernel
    rw [ha]
    exact (canonical20436 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1267 + difference 4 3) (sourceB1267 + difference 3 4) sourceC1267) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4608) := by
    have ha : (tripleCharges (sourceA1267 + difference 4 3) (sourceB1267 + difference 3 4) sourceC1267) = raw20437 := by
      apply Matrix.ext; unfold tripleCharges sourceA1267 sourceB1267 sourceC1267 difference raw20437; decide +kernel
    rw [ha]
    exact (canonical20437 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1267 + difference 4 5) (sourceB1267 + difference 5 4) sourceC1267) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4625) := by
    have ha : (tripleCharges (sourceA1267 + difference 4 5) (sourceB1267 + difference 5 4) sourceC1267) = raw20438 := by
      apply Matrix.ext; unfold tripleCharges sourceA1267 sourceB1267 sourceC1267 difference raw20438; decide +kernel
    rw [ha]
    exact (canonical20438 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1267 + difference 5 0) (sourceB1267 + difference 0 5) sourceC1267) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4501) := by
    have ha : (tripleCharges (sourceA1267 + difference 5 0) (sourceB1267 + difference 0 5) sourceC1267) = raw20439 := by
      apply Matrix.ext; unfold tripleCharges sourceA1267 sourceB1267 sourceC1267 difference raw20439; decide +kernel
    rw [ha]
    exact (canonical20439 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1267 + difference 5 1) (sourceB1267 + difference 1 5) sourceC1267) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4605) := by
    have ha : (tripleCharges (sourceA1267 + difference 5 1) (sourceB1267 + difference 1 5) sourceC1267) = raw20440 := by
      apply Matrix.ext; unfold tripleCharges sourceA1267 sourceB1267 sourceC1267 difference raw20440; decide +kernel
    rw [ha]
    exact (canonical20440 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1267 + difference 5 2) (sourceB1267 + difference 2 5) sourceC1267) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4605) := by
    have ha : (tripleCharges (sourceA1267 + difference 5 2) (sourceB1267 + difference 2 5) sourceC1267) = raw20441 := by
      apply Matrix.ext; unfold tripleCharges sourceA1267 sourceB1267 sourceC1267 difference raw20441; decide +kernel
    rw [ha]
    exact (canonical20441 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1267 + difference 5 3) (sourceB1267 + difference 3 5) sourceC1267) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4605) := by
    have ha : (tripleCharges (sourceA1267 + difference 5 3) (sourceB1267 + difference 3 5) sourceC1267) = raw20442 := by
      apply Matrix.ext; unfold tripleCharges sourceA1267 sourceB1267 sourceC1267 difference raw20442; decide +kernel
    rw [ha]
    exact (canonical20442 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1267 + difference 5 4) (sourceB1267 + difference 4 5) sourceC1267) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4621) := by
    have ha : (tripleCharges (sourceA1267 + difference 5 4) (sourceB1267 + difference 4 5) sourceC1267) = raw20443 := by
      apply Matrix.ext; unfold tripleCharges sourceA1267 sourceB1267 sourceC1267 difference raw20443; decide +kernel
    rw [ha]
    exact (canonical20443 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1267 sourceB1267 sourceC1267
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1267, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1268 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceB1268 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1268 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1268 : Integer.Sparse Master := [(Sum.inr 1046, 3), (Sum.inr 1089, 1), (Sum.inr 1091, 1), (Sum.inr 1217, 6), (Sum.inr 1242, 3), (Sum.inr 1243, 3), (Sum.inr 1269, 3), (Sum.inr 1271, 3), (Sum.inr 1304, 1), (Sum.inr 1308, 1), (Sum.inr 1416, 3), (Sum.inr 1450, 1), (Sum.inr 1452, 1)]

theorem sourceEq1268 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1268 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1268 + difference 0 1) (sourceB1268 + difference 1 0) sourceC1268) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1046) := by
    have ha : (tripleCharges (sourceA1268 + difference 0 1) (sourceB1268 + difference 1 0) sourceC1268) = raw20444 := by
      apply Matrix.ext; unfold tripleCharges sourceA1268 sourceB1268 sourceC1268 difference raw20444; decide +kernel
    rw [ha]
    exact (canonical20444 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1268 + difference 0 2) (sourceB1268 + difference 2 0) sourceC1268) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1046) := by
    have ha : (tripleCharges (sourceA1268 + difference 0 2) (sourceB1268 + difference 2 0) sourceC1268) = raw20445 := by
      apply Matrix.ext; unfold tripleCharges sourceA1268 sourceB1268 sourceC1268 difference raw20445; decide +kernel
    rw [ha]
    exact (canonical20445 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1268 + difference 0 3) (sourceB1268 + difference 3 0) sourceC1268) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1046) := by
    have ha : (tripleCharges (sourceA1268 + difference 0 3) (sourceB1268 + difference 3 0) sourceC1268) = raw20446 := by
      apply Matrix.ext; unfold tripleCharges sourceA1268 sourceB1268 sourceC1268 difference raw20446; decide +kernel
    rw [ha]
    exact (canonical20446 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1268 + difference 0 4) (sourceB1268 + difference 4 0) sourceC1268) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1091) := by
    have ha : (tripleCharges (sourceA1268 + difference 0 4) (sourceB1268 + difference 4 0) sourceC1268) = raw20447 := by
      apply Matrix.ext; unfold tripleCharges sourceA1268 sourceB1268 sourceC1268 difference raw20447; decide +kernel
    rw [ha]
    exact (canonical20447 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1268 + difference 0 5) (sourceB1268 + difference 5 0) sourceC1268) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1089) := by
    have ha : (tripleCharges (sourceA1268 + difference 0 5) (sourceB1268 + difference 5 0) sourceC1268) = raw20448 := by
      apply Matrix.ext; unfold tripleCharges sourceA1268 sourceB1268 sourceC1268 difference raw20448; decide +kernel
    rw [ha]
    exact (canonical20448 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1268 + difference 1 0) (sourceB1268 + difference 0 1) sourceC1268) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1416) := by
    have ha : (tripleCharges (sourceA1268 + difference 1 0) (sourceB1268 + difference 0 1) sourceC1268) = raw20449 := by
      apply Matrix.ext; unfold tripleCharges sourceA1268 sourceB1268 sourceC1268 difference raw20449; decide +kernel
    rw [ha]
    exact (canonical20449 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1268 + difference 1 2) (sourceB1268 + difference 2 1) sourceC1268) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1217) := by
    have ha : (tripleCharges (sourceA1268 + difference 1 2) (sourceB1268 + difference 2 1) sourceC1268) = raw20450 := by
      apply Matrix.ext; unfold tripleCharges sourceA1268 sourceB1268 sourceC1268 difference raw20450; decide +kernel
    rw [ha]
    exact (canonical20450 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1268 + difference 1 3) (sourceB1268 + difference 3 1) sourceC1268) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1217) := by
    have ha : (tripleCharges (sourceA1268 + difference 1 3) (sourceB1268 + difference 3 1) sourceC1268) = raw20451 := by
      apply Matrix.ext; unfold tripleCharges sourceA1268 sourceB1268 sourceC1268 difference raw20451; decide +kernel
    rw [ha]
    exact (canonical20451 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1268 + difference 1 4) (sourceB1268 + difference 4 1) sourceC1268) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1243) := by
    have ha : (tripleCharges (sourceA1268 + difference 1 4) (sourceB1268 + difference 4 1) sourceC1268) = raw20452 := by
      apply Matrix.ext; unfold tripleCharges sourceA1268 sourceB1268 sourceC1268 difference raw20452; decide +kernel
    rw [ha]
    exact (canonical20452 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1268 + difference 1 5) (sourceB1268 + difference 5 1) sourceC1268) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1242) := by
    have ha : (tripleCharges (sourceA1268 + difference 1 5) (sourceB1268 + difference 5 1) sourceC1268) = raw20453 := by
      apply Matrix.ext; unfold tripleCharges sourceA1268 sourceB1268 sourceC1268 difference raw20453; decide +kernel
    rw [ha]
    exact (canonical20453 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1268 + difference 2 0) (sourceB1268 + difference 0 2) sourceC1268) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1416) := by
    have ha : (tripleCharges (sourceA1268 + difference 2 0) (sourceB1268 + difference 0 2) sourceC1268) = raw20454 := by
      apply Matrix.ext; unfold tripleCharges sourceA1268 sourceB1268 sourceC1268 difference raw20454; decide +kernel
    rw [ha]
    exact (canonical20454 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1268 + difference 2 1) (sourceB1268 + difference 1 2) sourceC1268) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1217) := by
    have ha : (tripleCharges (sourceA1268 + difference 2 1) (sourceB1268 + difference 1 2) sourceC1268) = raw20455 := by
      apply Matrix.ext; unfold tripleCharges sourceA1268 sourceB1268 sourceC1268 difference raw20455; decide +kernel
    rw [ha]
    exact (canonical20455 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1268 + difference 2 3) (sourceB1268 + difference 3 2) sourceC1268) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1217) := by
    have ha : (tripleCharges (sourceA1268 + difference 2 3) (sourceB1268 + difference 3 2) sourceC1268) = raw20456 := by
      apply Matrix.ext; unfold tripleCharges sourceA1268 sourceB1268 sourceC1268 difference raw20456; decide +kernel
    rw [ha]
    exact (canonical20456 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1268 + difference 2 4) (sourceB1268 + difference 4 2) sourceC1268) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1243) := by
    have ha : (tripleCharges (sourceA1268 + difference 2 4) (sourceB1268 + difference 4 2) sourceC1268) = raw20457 := by
      apply Matrix.ext; unfold tripleCharges sourceA1268 sourceB1268 sourceC1268 difference raw20457; decide +kernel
    rw [ha]
    exact (canonical20457 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1268 + difference 2 5) (sourceB1268 + difference 5 2) sourceC1268) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1242) := by
    have ha : (tripleCharges (sourceA1268 + difference 2 5) (sourceB1268 + difference 5 2) sourceC1268) = raw20458 := by
      apply Matrix.ext; unfold tripleCharges sourceA1268 sourceB1268 sourceC1268 difference raw20458; decide +kernel
    rw [ha]
    exact (canonical20458 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1268 + difference 3 0) (sourceB1268 + difference 0 3) sourceC1268) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1416) := by
    have ha : (tripleCharges (sourceA1268 + difference 3 0) (sourceB1268 + difference 0 3) sourceC1268) = raw20459 := by
      apply Matrix.ext; unfold tripleCharges sourceA1268 sourceB1268 sourceC1268 difference raw20459; decide +kernel
    rw [ha]
    exact (canonical20459 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1268 + difference 3 1) (sourceB1268 + difference 1 3) sourceC1268) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1217) := by
    have ha : (tripleCharges (sourceA1268 + difference 3 1) (sourceB1268 + difference 1 3) sourceC1268) = raw20460 := by
      apply Matrix.ext; unfold tripleCharges sourceA1268 sourceB1268 sourceC1268 difference raw20460; decide +kernel
    rw [ha]
    exact (canonical20460 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1268 + difference 3 2) (sourceB1268 + difference 2 3) sourceC1268) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1217) := by
    have ha : (tripleCharges (sourceA1268 + difference 3 2) (sourceB1268 + difference 2 3) sourceC1268) = raw20461 := by
      apply Matrix.ext; unfold tripleCharges sourceA1268 sourceB1268 sourceC1268 difference raw20461; decide +kernel
    rw [ha]
    exact (canonical20461 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1268 + difference 3 4) (sourceB1268 + difference 4 3) sourceC1268) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1243) := by
    have ha : (tripleCharges (sourceA1268 + difference 3 4) (sourceB1268 + difference 4 3) sourceC1268) = raw20462 := by
      apply Matrix.ext; unfold tripleCharges sourceA1268 sourceB1268 sourceC1268 difference raw20462; decide +kernel
    rw [ha]
    exact (canonical20462 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1268 + difference 3 5) (sourceB1268 + difference 5 3) sourceC1268) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1242) := by
    have ha : (tripleCharges (sourceA1268 + difference 3 5) (sourceB1268 + difference 5 3) sourceC1268) = raw20463 := by
      apply Matrix.ext; unfold tripleCharges sourceA1268 sourceB1268 sourceC1268 difference raw20463; decide +kernel
    rw [ha]
    exact (canonical20463 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1268 + difference 4 0) (sourceB1268 + difference 0 4) sourceC1268) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1450) := by
    have ha : (tripleCharges (sourceA1268 + difference 4 0) (sourceB1268 + difference 0 4) sourceC1268) = raw20464 := by
      apply Matrix.ext; unfold tripleCharges sourceA1268 sourceB1268 sourceC1268 difference raw20464; decide +kernel
    rw [ha]
    exact (canonical20464 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1268 + difference 4 1) (sourceB1268 + difference 1 4) sourceC1268) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1269) := by
    have ha : (tripleCharges (sourceA1268 + difference 4 1) (sourceB1268 + difference 1 4) sourceC1268) = raw20465 := by
      apply Matrix.ext; unfold tripleCharges sourceA1268 sourceB1268 sourceC1268 difference raw20465; decide +kernel
    rw [ha]
    exact (canonical20465 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1268 + difference 4 2) (sourceB1268 + difference 2 4) sourceC1268) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1269) := by
    have ha : (tripleCharges (sourceA1268 + difference 4 2) (sourceB1268 + difference 2 4) sourceC1268) = raw20466 := by
      apply Matrix.ext; unfold tripleCharges sourceA1268 sourceB1268 sourceC1268 difference raw20466; decide +kernel
    rw [ha]
    exact (canonical20466 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1268 + difference 4 3) (sourceB1268 + difference 3 4) sourceC1268) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1269) := by
    have ha : (tripleCharges (sourceA1268 + difference 4 3) (sourceB1268 + difference 3 4) sourceC1268) = raw20467 := by
      apply Matrix.ext; unfold tripleCharges sourceA1268 sourceB1268 sourceC1268 difference raw20467; decide +kernel
    rw [ha]
    exact (canonical20467 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1268 + difference 4 5) (sourceB1268 + difference 5 4) sourceC1268) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1304) := by
    have ha : (tripleCharges (sourceA1268 + difference 4 5) (sourceB1268 + difference 5 4) sourceC1268) = raw20468 := by
      apply Matrix.ext; unfold tripleCharges sourceA1268 sourceB1268 sourceC1268 difference raw20468; decide +kernel
    rw [ha]
    exact (canonical20468 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1268 + difference 5 0) (sourceB1268 + difference 0 5) sourceC1268) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1452) := by
    have ha : (tripleCharges (sourceA1268 + difference 5 0) (sourceB1268 + difference 0 5) sourceC1268) = raw20469 := by
      apply Matrix.ext; unfold tripleCharges sourceA1268 sourceB1268 sourceC1268 difference raw20469; decide +kernel
    rw [ha]
    exact (canonical20469 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1268 + difference 5 1) (sourceB1268 + difference 1 5) sourceC1268) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1271) := by
    have ha : (tripleCharges (sourceA1268 + difference 5 1) (sourceB1268 + difference 1 5) sourceC1268) = raw20470 := by
      apply Matrix.ext; unfold tripleCharges sourceA1268 sourceB1268 sourceC1268 difference raw20470; decide +kernel
    rw [ha]
    exact (canonical20470 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1268 + difference 5 2) (sourceB1268 + difference 2 5) sourceC1268) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1271) := by
    have ha : (tripleCharges (sourceA1268 + difference 5 2) (sourceB1268 + difference 2 5) sourceC1268) = raw20471 := by
      apply Matrix.ext; unfold tripleCharges sourceA1268 sourceB1268 sourceC1268 difference raw20471; decide +kernel
    rw [ha]
    exact (canonical20471 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1268 + difference 5 3) (sourceB1268 + difference 3 5) sourceC1268) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1271) := by
    have ha : (tripleCharges (sourceA1268 + difference 5 3) (sourceB1268 + difference 3 5) sourceC1268) = raw20472 := by
      apply Matrix.ext; unfold tripleCharges sourceA1268 sourceB1268 sourceC1268 difference raw20472; decide +kernel
    rw [ha]
    exact (canonical20472 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1268 + difference 5 4) (sourceB1268 + difference 4 5) sourceC1268) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1308) := by
    have ha : (tripleCharges (sourceA1268 + difference 5 4) (sourceB1268 + difference 4 5) sourceC1268) = raw20473 := by
      apply Matrix.ext; unfold tripleCharges sourceA1268 sourceB1268 sourceC1268 difference raw20473; decide +kernel
    rw [ha]
    exact (canonical20473 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1268 sourceB1268 sourceC1268
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1268, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1269 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceB1269 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1269 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1269 : Integer.Sparse Master := [(Sum.inr 1750, 3), (Sum.inr 1754, 1), (Sum.inr 1756, 1), (Sum.inr 3310, 1), (Sum.inr 4070, -1)]

theorem sourceEq1269 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1269 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1269 + difference 0 0) (sourceB1269 + difference 0 0) sourceC1269) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3310) := by
    have ha : (tripleCharges (sourceA1269 + difference 0 0) (sourceB1269 + difference 0 0) sourceC1269) = raw20303 := by
      apply Matrix.ext; unfold tripleCharges sourceA1269 sourceB1269 sourceC1269 difference raw20303; decide +kernel
    rw [ha]
    exact (canonical20303 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1269 + difference 0 1) (sourceB1269 + difference 1 0) sourceC1269) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1750) := by
    have ha : (tripleCharges (sourceA1269 + difference 0 1) (sourceB1269 + difference 1 0) sourceC1269) = raw20298 := by
      apply Matrix.ext; unfold tripleCharges sourceA1269 sourceB1269 sourceC1269 difference raw20298; decide +kernel
    rw [ha]
    exact (canonical20298 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1269 + difference 0 2) (sourceB1269 + difference 2 0) sourceC1269) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1750) := by
    have ha : (tripleCharges (sourceA1269 + difference 0 2) (sourceB1269 + difference 2 0) sourceC1269) = raw20474 := by
      apply Matrix.ext; unfold tripleCharges sourceA1269 sourceB1269 sourceC1269 difference raw20474; decide +kernel
    rw [ha]
    exact (canonical20474 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1269 + difference 0 3) (sourceB1269 + difference 3 0) sourceC1269) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1750) := by
    have ha : (tripleCharges (sourceA1269 + difference 0 3) (sourceB1269 + difference 3 0) sourceC1269) = raw20475 := by
      apply Matrix.ext; unfold tripleCharges sourceA1269 sourceB1269 sourceC1269 difference raw20475; decide +kernel
    rw [ha]
    exact (canonical20475 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1269 + difference 0 4) (sourceB1269 + difference 4 0) sourceC1269) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1756) := by
    have ha : (tripleCharges (sourceA1269 + difference 0 4) (sourceB1269 + difference 4 0) sourceC1269) = raw20476 := by
      apply Matrix.ext; unfold tripleCharges sourceA1269 sourceB1269 sourceC1269 difference raw20476; decide +kernel
    rw [ha]
    exact (canonical20476 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1269 + difference 0 5) (sourceB1269 + difference 5 0) sourceC1269) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1754) := by
    have ha : (tripleCharges (sourceA1269 + difference 0 5) (sourceB1269 + difference 5 0) sourceC1269) = raw20477 := by
      apply Matrix.ext; unfold tripleCharges sourceA1269 sourceB1269 sourceC1269 difference raw20477; decide +kernel
    rw [ha]
    exact (canonical20477 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1269 + sourceB1269) sourceC1269) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1269 + sourceB1269) sourceC1269) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1269 sourceB1269 sourceC1269 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1269 sourceB1269 sourceC1269
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1269, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1270 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceB1270 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1270 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1270 : Integer.Sparse Master := [(Sum.inr 1725, 3), (Sum.inr 1730, 1), (Sum.inr 1754, 1), (Sum.inr 3310, 1), (Sum.inr 4070, -1)]

theorem sourceEq1270 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1270 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1270 + difference 0 0) (sourceB1270 + difference 0 0) sourceC1270) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3310) := by
    have ha : (tripleCharges (sourceA1270 + difference 0 0) (sourceB1270 + difference 0 0) sourceC1270) = raw20303 := by
      apply Matrix.ext; unfold tripleCharges sourceA1270 sourceB1270 sourceC1270 difference raw20303; decide +kernel
    rw [ha]
    exact (canonical20303 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1270 + difference 1 0) (sourceB1270 + difference 0 1) sourceC1270) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1725) := by
    have ha : (tripleCharges (sourceA1270 + difference 1 0) (sourceB1270 + difference 0 1) sourceC1270) = raw20478 := by
      apply Matrix.ext; unfold tripleCharges sourceA1270 sourceB1270 sourceC1270 difference raw20478; decide +kernel
    rw [ha]
    exact (canonical20478 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1270 + difference 2 0) (sourceB1270 + difference 0 2) sourceC1270) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1725) := by
    have ha : (tripleCharges (sourceA1270 + difference 2 0) (sourceB1270 + difference 0 2) sourceC1270) = raw20213 := by
      apply Matrix.ext; unfold tripleCharges sourceA1270 sourceB1270 sourceC1270 difference raw20213; decide +kernel
    rw [ha]
    exact (canonical20213 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1270 + difference 3 0) (sourceB1270 + difference 0 3) sourceC1270) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1725) := by
    have ha : (tripleCharges (sourceA1270 + difference 3 0) (sourceB1270 + difference 0 3) sourceC1270) = raw20161 := by
      apply Matrix.ext; unfold tripleCharges sourceA1270 sourceB1270 sourceC1270 difference raw20161; decide +kernel
    rw [ha]
    exact (canonical20161 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1270 + difference 4 0) (sourceB1270 + difference 0 4) sourceC1270) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1754) := by
    have ha : (tripleCharges (sourceA1270 + difference 4 0) (sourceB1270 + difference 0 4) sourceC1270) = raw20479 := by
      apply Matrix.ext; unfold tripleCharges sourceA1270 sourceB1270 sourceC1270 difference raw20479; decide +kernel
    rw [ha]
    exact (canonical20479 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1270 + difference 5 0) (sourceB1270 + difference 0 5) sourceC1270) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1730) := by
    have ha : (tripleCharges (sourceA1270 + difference 5 0) (sourceB1270 + difference 0 5) sourceC1270) = raw20480 := by
      apply Matrix.ext; unfold tripleCharges sourceA1270 sourceB1270 sourceC1270 difference raw20480; decide +kernel
    rw [ha]
    exact (canonical20480 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1270 + sourceB1270) sourceC1270) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1270 + sourceB1270) sourceC1270) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1270 sourceB1270 sourceC1270 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1270 sourceB1270 sourceC1270
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1270, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1271 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceB1271 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1271 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1271 : Integer.Sparse Master := [(Sum.inr 1754, 1), (Sum.inr 3300, 3), (Sum.inr 3310, 2), (Sum.inr 4070, -1)]

theorem sourceEq1271 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1271 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1271 + difference 4 0) (sourceB1271 + difference 0 4) sourceC1271) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1754) := by
    have ha : (tripleCharges (sourceA1271 + difference 4 0) (sourceB1271 + difference 0 4) sourceC1271) = raw20479 := by
      apply Matrix.ext; unfold tripleCharges sourceA1271 sourceB1271 sourceC1271 difference raw20479; decide +kernel
    rw [ha]
    exact (canonical20479 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1271 + difference 4 1) (sourceB1271 + difference 1 4) sourceC1271) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3300) := by
    have ha : (tripleCharges (sourceA1271 + difference 4 1) (sourceB1271 + difference 1 4) sourceC1271) = raw20268 := by
      apply Matrix.ext; unfold tripleCharges sourceA1271 sourceB1271 sourceC1271 difference raw20268; decide +kernel
    rw [ha]
    exact (canonical20268 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1271 + difference 4 2) (sourceB1271 + difference 2 4) sourceC1271) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3300) := by
    have ha : (tripleCharges (sourceA1271 + difference 4 2) (sourceB1271 + difference 2 4) sourceC1271) = raw20481 := by
      apply Matrix.ext; unfold tripleCharges sourceA1271 sourceB1271 sourceC1271 difference raw20481; decide +kernel
    rw [ha]
    exact (canonical20481 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1271 + difference 4 3) (sourceB1271 + difference 3 4) sourceC1271) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3300) := by
    have ha : (tripleCharges (sourceA1271 + difference 4 3) (sourceB1271 + difference 3 4) sourceC1271) = raw20482 := by
      apply Matrix.ext; unfold tripleCharges sourceA1271 sourceB1271 sourceC1271 difference raw20482; decide +kernel
    rw [ha]
    exact (canonical20482 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1271 + difference 4 4) (sourceB1271 + difference 4 4) sourceC1271) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3310) := by
    have ha : (tripleCharges (sourceA1271 + difference 4 4) (sourceB1271 + difference 4 4) sourceC1271) = raw20303 := by
      apply Matrix.ext; unfold tripleCharges sourceA1271 sourceB1271 sourceC1271 difference raw20303; decide +kernel
    rw [ha]
    exact (canonical20303 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1271 + difference 4 5) (sourceB1271 + difference 5 4) sourceC1271) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3310) := by
    have ha : (tripleCharges (sourceA1271 + difference 4 5) (sourceB1271 + difference 5 4) sourceC1271) = raw20265 := by
      apply Matrix.ext; unfold tripleCharges sourceA1271 sourceB1271 sourceC1271 difference raw20265; decide +kernel
    rw [ha]
    exact (canonical20265 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1271 + sourceB1271) sourceC1271) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1271 + sourceB1271) sourceC1271) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1271 sourceB1271 sourceC1271 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1271 sourceB1271 sourceC1271
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1271, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1272 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1272 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC1272 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceForm1272 : Integer.Sparse Master := [(Sum.inr 4184, 3), (Sum.inr 4189, 1), (Sum.inr 4193, 1), (Sum.inr 4370, 3), (Sum.inr 4468, 1), (Sum.inr 4552, 6), (Sum.inr 4560, 3), (Sum.inr 4605, 3), (Sum.inr 4617, 3), (Sum.inr 4626, 1), (Sum.inr 4868, 3), (Sum.inr 4897, 1), (Sum.inr 5305, 1)]

theorem sourceEq1272 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1272 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1272 + difference 0 1) (sourceB1272 + difference 1 0) sourceC1272) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4868) := by
    have ha : (tripleCharges (sourceA1272 + difference 0 1) (sourceB1272 + difference 1 0) sourceC1272) = raw5122 := by
      apply Matrix.ext; unfold tripleCharges sourceA1272 sourceB1272 sourceC1272 difference raw5122; decide +kernel
    rw [ha]
    exact (canonical5122 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1272 + difference 0 2) (sourceB1272 + difference 2 0) sourceC1272) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4868) := by
    have ha : (tripleCharges (sourceA1272 + difference 0 2) (sourceB1272 + difference 2 0) sourceC1272) = raw5123 := by
      apply Matrix.ext; unfold tripleCharges sourceA1272 sourceB1272 sourceC1272 difference raw5123; decide +kernel
    rw [ha]
    exact (canonical5123 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1272 + difference 0 3) (sourceB1272 + difference 3 0) sourceC1272) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4868) := by
    have ha : (tripleCharges (sourceA1272 + difference 0 3) (sourceB1272 + difference 3 0) sourceC1272) = raw5124 := by
      apply Matrix.ext; unfold tripleCharges sourceA1272 sourceB1272 sourceC1272 difference raw5124; decide +kernel
    rw [ha]
    exact (canonical5124 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1272 + difference 0 4) (sourceB1272 + difference 4 0) sourceC1272) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4897) := by
    have ha : (tripleCharges (sourceA1272 + difference 0 4) (sourceB1272 + difference 4 0) sourceC1272) = raw10259 := by
      apply Matrix.ext; unfold tripleCharges sourceA1272 sourceB1272 sourceC1272 difference raw10259; decide +kernel
    rw [ha]
    exact (canonical10259 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1272 + difference 0 5) (sourceB1272 + difference 5 0) sourceC1272) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5305) := by
    have ha : (tripleCharges (sourceA1272 + difference 0 5) (sourceB1272 + difference 5 0) sourceC1272) = raw5125 := by
      apply Matrix.ext; unfold tripleCharges sourceA1272 sourceB1272 sourceC1272 difference raw5125; decide +kernel
    rw [ha]
    exact (canonical5125 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1272 + difference 1 0) (sourceB1272 + difference 0 1) sourceC1272) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4184) := by
    have ha : (tripleCharges (sourceA1272 + difference 1 0) (sourceB1272 + difference 0 1) sourceC1272) = raw20483 := by
      apply Matrix.ext; unfold tripleCharges sourceA1272 sourceB1272 sourceC1272 difference raw20483; decide +kernel
    rw [ha]
    exact (canonical20483 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1272 + difference 1 2) (sourceB1272 + difference 2 1) sourceC1272) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4552) := by
    have ha : (tripleCharges (sourceA1272 + difference 1 2) (sourceB1272 + difference 2 1) sourceC1272) = raw20484 := by
      apply Matrix.ext; unfold tripleCharges sourceA1272 sourceB1272 sourceC1272 difference raw20484; decide +kernel
    rw [ha]
    exact (canonical20484 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1272 + difference 1 3) (sourceB1272 + difference 3 1) sourceC1272) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4552) := by
    have ha : (tripleCharges (sourceA1272 + difference 1 3) (sourceB1272 + difference 3 1) sourceC1272) = raw20485 := by
      apply Matrix.ext; unfold tripleCharges sourceA1272 sourceB1272 sourceC1272 difference raw20485; decide +kernel
    rw [ha]
    exact (canonical20485 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1272 + difference 1 4) (sourceB1272 + difference 4 1) sourceC1272) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4605) := by
    have ha : (tripleCharges (sourceA1272 + difference 1 4) (sourceB1272 + difference 4 1) sourceC1272) = raw5106 := by
      apply Matrix.ext; unfold tripleCharges sourceA1272 sourceB1272 sourceC1272 difference raw5106; decide +kernel
    rw [ha]
    exact (canonical5106 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1272 + difference 1 5) (sourceB1272 + difference 5 1) sourceC1272) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4617) := by
    have ha : (tripleCharges (sourceA1272 + difference 1 5) (sourceB1272 + difference 5 1) sourceC1272) = raw10242 := by
      apply Matrix.ext; unfold tripleCharges sourceA1272 sourceB1272 sourceC1272 difference raw10242; decide +kernel
    rw [ha]
    exact (canonical10242 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1272 + difference 2 0) (sourceB1272 + difference 0 2) sourceC1272) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4184) := by
    have ha : (tripleCharges (sourceA1272 + difference 2 0) (sourceB1272 + difference 0 2) sourceC1272) = raw20486 := by
      apply Matrix.ext; unfold tripleCharges sourceA1272 sourceB1272 sourceC1272 difference raw20486; decide +kernel
    rw [ha]
    exact (canonical20486 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1272 + difference 2 1) (sourceB1272 + difference 1 2) sourceC1272) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4552) := by
    have ha : (tripleCharges (sourceA1272 + difference 2 1) (sourceB1272 + difference 1 2) sourceC1272) = raw20487 := by
      apply Matrix.ext; unfold tripleCharges sourceA1272 sourceB1272 sourceC1272 difference raw20487; decide +kernel
    rw [ha]
    exact (canonical20487 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1272 + difference 2 3) (sourceB1272 + difference 3 2) sourceC1272) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4552) := by
    have ha : (tripleCharges (sourceA1272 + difference 2 3) (sourceB1272 + difference 3 2) sourceC1272) = raw20488 := by
      apply Matrix.ext; unfold tripleCharges sourceA1272 sourceB1272 sourceC1272 difference raw20488; decide +kernel
    rw [ha]
    exact (canonical20488 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1272 + difference 2 4) (sourceB1272 + difference 4 2) sourceC1272) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4605) := by
    have ha : (tripleCharges (sourceA1272 + difference 2 4) (sourceB1272 + difference 4 2) sourceC1272) = raw5111 := by
      apply Matrix.ext; unfold tripleCharges sourceA1272 sourceB1272 sourceC1272 difference raw5111; decide +kernel
    rw [ha]
    exact (canonical5111 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1272 + difference 2 5) (sourceB1272 + difference 5 2) sourceC1272) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4617) := by
    have ha : (tripleCharges (sourceA1272 + difference 2 5) (sourceB1272 + difference 5 2) sourceC1272) = raw10246 := by
      apply Matrix.ext; unfold tripleCharges sourceA1272 sourceB1272 sourceC1272 difference raw10246; decide +kernel
    rw [ha]
    exact (canonical10246 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1272 + difference 3 0) (sourceB1272 + difference 0 3) sourceC1272) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4184) := by
    have ha : (tripleCharges (sourceA1272 + difference 3 0) (sourceB1272 + difference 0 3) sourceC1272) = raw20489 := by
      apply Matrix.ext; unfold tripleCharges sourceA1272 sourceB1272 sourceC1272 difference raw20489; decide +kernel
    rw [ha]
    exact (canonical20489 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1272 + difference 3 1) (sourceB1272 + difference 1 3) sourceC1272) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4552) := by
    have ha : (tripleCharges (sourceA1272 + difference 3 1) (sourceB1272 + difference 1 3) sourceC1272) = raw20490 := by
      apply Matrix.ext; unfold tripleCharges sourceA1272 sourceB1272 sourceC1272 difference raw20490; decide +kernel
    rw [ha]
    exact (canonical20490 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1272 + difference 3 2) (sourceB1272 + difference 2 3) sourceC1272) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4552) := by
    have ha : (tripleCharges (sourceA1272 + difference 3 2) (sourceB1272 + difference 2 3) sourceC1272) = raw20491 := by
      apply Matrix.ext; unfold tripleCharges sourceA1272 sourceB1272 sourceC1272 difference raw20491; decide +kernel
    rw [ha]
    exact (canonical20491 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1272 + difference 3 4) (sourceB1272 + difference 4 3) sourceC1272) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4605) := by
    have ha : (tripleCharges (sourceA1272 + difference 3 4) (sourceB1272 + difference 4 3) sourceC1272) = raw5116 := by
      apply Matrix.ext; unfold tripleCharges sourceA1272 sourceB1272 sourceC1272 difference raw5116; decide +kernel
    rw [ha]
    exact (canonical5116 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1272 + difference 3 5) (sourceB1272 + difference 5 3) sourceC1272) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4617) := by
    have ha : (tripleCharges (sourceA1272 + difference 3 5) (sourceB1272 + difference 5 3) sourceC1272) = raw10250 := by
      apply Matrix.ext; unfold tripleCharges sourceA1272 sourceB1272 sourceC1272 difference raw10250; decide +kernel
    rw [ha]
    exact (canonical10250 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1272 + difference 4 0) (sourceB1272 + difference 0 4) sourceC1272) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4193) := by
    have ha : (tripleCharges (sourceA1272 + difference 4 0) (sourceB1272 + difference 0 4) sourceC1272) = raw20492 := by
      apply Matrix.ext; unfold tripleCharges sourceA1272 sourceB1272 sourceC1272 difference raw20492; decide +kernel
    rw [ha]
    exact (canonical20492 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1272 + difference 4 1) (sourceB1272 + difference 1 4) sourceC1272) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4560) := by
    have ha : (tripleCharges (sourceA1272 + difference 4 1) (sourceB1272 + difference 1 4) sourceC1272) = raw20493 := by
      apply Matrix.ext; unfold tripleCharges sourceA1272 sourceB1272 sourceC1272 difference raw20493; decide +kernel
    rw [ha]
    exact (canonical20493 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1272 + difference 4 2) (sourceB1272 + difference 2 4) sourceC1272) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4560) := by
    have ha : (tripleCharges (sourceA1272 + difference 4 2) (sourceB1272 + difference 2 4) sourceC1272) = raw20494 := by
      apply Matrix.ext; unfold tripleCharges sourceA1272 sourceB1272 sourceC1272 difference raw20494; decide +kernel
    rw [ha]
    exact (canonical20494 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1272 + difference 4 3) (sourceB1272 + difference 3 4) sourceC1272) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4560) := by
    have ha : (tripleCharges (sourceA1272 + difference 4 3) (sourceB1272 + difference 3 4) sourceC1272) = raw20495 := by
      apply Matrix.ext; unfold tripleCharges sourceA1272 sourceB1272 sourceC1272 difference raw20495; decide +kernel
    rw [ha]
    exact (canonical20495 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1272 + difference 4 5) (sourceB1272 + difference 5 4) sourceC1272) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4626) := by
    have ha : (tripleCharges (sourceA1272 + difference 4 5) (sourceB1272 + difference 5 4) sourceC1272) = raw10254 := by
      apply Matrix.ext; unfold tripleCharges sourceA1272 sourceB1272 sourceC1272 difference raw10254; decide +kernel
    rw [ha]
    exact (canonical10254 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1272 + difference 5 0) (sourceB1272 + difference 0 5) sourceC1272) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4189) := by
    have ha : (tripleCharges (sourceA1272 + difference 5 0) (sourceB1272 + difference 0 5) sourceC1272) = raw19631 := by
      apply Matrix.ext; unfold tripleCharges sourceA1272 sourceB1272 sourceC1272 difference raw19631; decide +kernel
    rw [ha]
    exact (canonical19631 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1272 + difference 5 1) (sourceB1272 + difference 1 5) sourceC1272) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4370) := by
    have ha : (tripleCharges (sourceA1272 + difference 5 1) (sourceB1272 + difference 1 5) sourceC1272) = raw19632 := by
      apply Matrix.ext; unfold tripleCharges sourceA1272 sourceB1272 sourceC1272 difference raw19632; decide +kernel
    rw [ha]
    exact (canonical19632 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1272 + difference 5 2) (sourceB1272 + difference 2 5) sourceC1272) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4370) := by
    have ha : (tripleCharges (sourceA1272 + difference 5 2) (sourceB1272 + difference 2 5) sourceC1272) = raw19633 := by
      apply Matrix.ext; unfold tripleCharges sourceA1272 sourceB1272 sourceC1272 difference raw19633; decide +kernel
    rw [ha]
    exact (canonical19633 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1272 + difference 5 3) (sourceB1272 + difference 3 5) sourceC1272) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4370) := by
    have ha : (tripleCharges (sourceA1272 + difference 5 3) (sourceB1272 + difference 3 5) sourceC1272) = raw19634 := by
      apply Matrix.ext; unfold tripleCharges sourceA1272 sourceB1272 sourceC1272 difference raw19634; decide +kernel
    rw [ha]
    exact (canonical19634 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1272 + difference 5 4) (sourceB1272 + difference 4 5) sourceC1272) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4468) := by
    have ha : (tripleCharges (sourceA1272 + difference 5 4) (sourceB1272 + difference 4 5) sourceC1272) = raw5126 := by
      apply Matrix.ext; unfold tripleCharges sourceA1272 sourceB1272 sourceC1272 difference raw5126; decide +kernel
    rw [ha]
    exact (canonical5126 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1272 sourceB1272 sourceC1272
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1272, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1273 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1273 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC1273 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceForm1273 : Integer.Sparse Master := [(Sum.inr 612, 3), (Sum.inr 617, 1), (Sum.inr 621, 1), (Sum.inr 1137, 6), (Sum.inr 1142, 3), (Sum.inr 1146, 3), (Sum.inr 1271, 3), (Sum.inr 1275, 1), (Sum.inr 1306, 3), (Sum.inr 1310, 1), (Sum.inr 2966, 3), (Sum.inr 3114, 1), (Sum.inr 3125, 1)]

theorem sourceEq1273 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1273 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1273 + difference 0 1) (sourceB1273 + difference 1 0) sourceC1273) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2966) := by
    have ha : (tripleCharges (sourceA1273 + difference 0 1) (sourceB1273 + difference 1 0) sourceC1273) = raw10286 := by
      apply Matrix.ext; unfold tripleCharges sourceA1273 sourceB1273 sourceC1273 difference raw10286; decide +kernel
    rw [ha]
    exact (canonical10286 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1273 + difference 0 2) (sourceB1273 + difference 2 0) sourceC1273) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2966) := by
    have ha : (tripleCharges (sourceA1273 + difference 0 2) (sourceB1273 + difference 2 0) sourceC1273) = raw10287 := by
      apply Matrix.ext; unfold tripleCharges sourceA1273 sourceB1273 sourceC1273 difference raw10287; decide +kernel
    rw [ha]
    exact (canonical10287 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1273 + difference 0 3) (sourceB1273 + difference 3 0) sourceC1273) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2966) := by
    have ha : (tripleCharges (sourceA1273 + difference 0 3) (sourceB1273 + difference 3 0) sourceC1273) = raw10288 := by
      apply Matrix.ext; unfold tripleCharges sourceA1273 sourceB1273 sourceC1273 difference raw10288; decide +kernel
    rw [ha]
    exact (canonical10288 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1273 + difference 0 4) (sourceB1273 + difference 4 0) sourceC1273) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3114) := by
    have ha : (tripleCharges (sourceA1273 + difference 0 4) (sourceB1273 + difference 4 0) sourceC1273) = raw10289 := by
      apply Matrix.ext; unfold tripleCharges sourceA1273 sourceB1273 sourceC1273 difference raw10289; decide +kernel
    rw [ha]
    exact (canonical10289 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1273 + difference 0 5) (sourceB1273 + difference 5 0) sourceC1273) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3125) := by
    have ha : (tripleCharges (sourceA1273 + difference 0 5) (sourceB1273 + difference 5 0) sourceC1273) = raw20496 := by
      apply Matrix.ext; unfold tripleCharges sourceA1273 sourceB1273 sourceC1273 difference raw20496; decide +kernel
    rw [ha]
    exact (canonical20496 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1273 + difference 1 0) (sourceB1273 + difference 0 1) sourceC1273) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 612) := by
    have ha : (tripleCharges (sourceA1273 + difference 1 0) (sourceB1273 + difference 0 1) sourceC1273) = raw20497 := by
      apply Matrix.ext; unfold tripleCharges sourceA1273 sourceB1273 sourceC1273 difference raw20497; decide +kernel
    rw [ha]
    exact (canonical20497 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1273 + difference 1 2) (sourceB1273 + difference 2 1) sourceC1273) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1137) := by
    have ha : (tripleCharges (sourceA1273 + difference 1 2) (sourceB1273 + difference 2 1) sourceC1273) = raw20498 := by
      apply Matrix.ext; unfold tripleCharges sourceA1273 sourceB1273 sourceC1273 difference raw20498; decide +kernel
    rw [ha]
    exact (canonical20498 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1273 + difference 1 3) (sourceB1273 + difference 3 1) sourceC1273) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1137) := by
    have ha : (tripleCharges (sourceA1273 + difference 1 3) (sourceB1273 + difference 3 1) sourceC1273) = raw20499 := by
      apply Matrix.ext; unfold tripleCharges sourceA1273 sourceB1273 sourceC1273 difference raw20499; decide +kernel
    rw [ha]
    exact (canonical20499 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1273 + difference 1 4) (sourceB1273 + difference 4 1) sourceC1273) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1271) := by
    have ha : (tripleCharges (sourceA1273 + difference 1 4) (sourceB1273 + difference 4 1) sourceC1273) = raw19648 := by
      apply Matrix.ext; unfold tripleCharges sourceA1273 sourceB1273 sourceC1273 difference raw19648; decide +kernel
    rw [ha]
    exact (canonical19648 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1273 + difference 1 5) (sourceB1273 + difference 5 1) sourceC1273) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1306) := by
    have ha : (tripleCharges (sourceA1273 + difference 1 5) (sourceB1273 + difference 5 1) sourceC1273) = raw10265 := by
      apply Matrix.ext; unfold tripleCharges sourceA1273 sourceB1273 sourceC1273 difference raw10265; decide +kernel
    rw [ha]
    exact (canonical10265 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1273 + difference 2 0) (sourceB1273 + difference 0 2) sourceC1273) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 612) := by
    have ha : (tripleCharges (sourceA1273 + difference 2 0) (sourceB1273 + difference 0 2) sourceC1273) = raw20500 := by
      apply Matrix.ext; unfold tripleCharges sourceA1273 sourceB1273 sourceC1273 difference raw20500; decide +kernel
    rw [ha]
    exact (canonical20500 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1273 + difference 2 1) (sourceB1273 + difference 1 2) sourceC1273) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1137) := by
    have ha : (tripleCharges (sourceA1273 + difference 2 1) (sourceB1273 + difference 1 2) sourceC1273) = raw20501 := by
      apply Matrix.ext; unfold tripleCharges sourceA1273 sourceB1273 sourceC1273 difference raw20501; decide +kernel
    rw [ha]
    exact (canonical20501 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1273 + difference 2 3) (sourceB1273 + difference 3 2) sourceC1273) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1137) := by
    have ha : (tripleCharges (sourceA1273 + difference 2 3) (sourceB1273 + difference 3 2) sourceC1273) = raw20502 := by
      apply Matrix.ext; unfold tripleCharges sourceA1273 sourceB1273 sourceC1273 difference raw20502; decide +kernel
    rw [ha]
    exact (canonical20502 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1273 + difference 2 4) (sourceB1273 + difference 4 2) sourceC1273) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1271) := by
    have ha : (tripleCharges (sourceA1273 + difference 2 4) (sourceB1273 + difference 4 2) sourceC1273) = raw19653 := by
      apply Matrix.ext; unfold tripleCharges sourceA1273 sourceB1273 sourceC1273 difference raw19653; decide +kernel
    rw [ha]
    exact (canonical19653 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1273 + difference 2 5) (sourceB1273 + difference 5 2) sourceC1273) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1306) := by
    have ha : (tripleCharges (sourceA1273 + difference 2 5) (sourceB1273 + difference 5 2) sourceC1273) = raw10270 := by
      apply Matrix.ext; unfold tripleCharges sourceA1273 sourceB1273 sourceC1273 difference raw10270; decide +kernel
    rw [ha]
    exact (canonical10270 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1273 + difference 3 0) (sourceB1273 + difference 0 3) sourceC1273) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 612) := by
    have ha : (tripleCharges (sourceA1273 + difference 3 0) (sourceB1273 + difference 0 3) sourceC1273) = raw20503 := by
      apply Matrix.ext; unfold tripleCharges sourceA1273 sourceB1273 sourceC1273 difference raw20503; decide +kernel
    rw [ha]
    exact (canonical20503 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1273 + difference 3 1) (sourceB1273 + difference 1 3) sourceC1273) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1137) := by
    have ha : (tripleCharges (sourceA1273 + difference 3 1) (sourceB1273 + difference 1 3) sourceC1273) = raw20504 := by
      apply Matrix.ext; unfold tripleCharges sourceA1273 sourceB1273 sourceC1273 difference raw20504; decide +kernel
    rw [ha]
    exact (canonical20504 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1273 + difference 3 2) (sourceB1273 + difference 2 3) sourceC1273) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1137) := by
    have ha : (tripleCharges (sourceA1273 + difference 3 2) (sourceB1273 + difference 2 3) sourceC1273) = raw20505 := by
      apply Matrix.ext; unfold tripleCharges sourceA1273 sourceB1273 sourceC1273 difference raw20505; decide +kernel
    rw [ha]
    exact (canonical20505 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1273 + difference 3 4) (sourceB1273 + difference 4 3) sourceC1273) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1271) := by
    have ha : (tripleCharges (sourceA1273 + difference 3 4) (sourceB1273 + difference 4 3) sourceC1273) = raw19658 := by
      apply Matrix.ext; unfold tripleCharges sourceA1273 sourceB1273 sourceC1273 difference raw19658; decide +kernel
    rw [ha]
    exact (canonical19658 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1273 + difference 3 5) (sourceB1273 + difference 5 3) sourceC1273) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1306) := by
    have ha : (tripleCharges (sourceA1273 + difference 3 5) (sourceB1273 + difference 5 3) sourceC1273) = raw10275 := by
      apply Matrix.ext; unfold tripleCharges sourceA1273 sourceB1273 sourceC1273 difference raw10275; decide +kernel
    rw [ha]
    exact (canonical10275 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1273 + difference 4 0) (sourceB1273 + difference 0 4) sourceC1273) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 621) := by
    have ha : (tripleCharges (sourceA1273 + difference 4 0) (sourceB1273 + difference 0 4) sourceC1273) = raw20506 := by
      apply Matrix.ext; unfold tripleCharges sourceA1273 sourceB1273 sourceC1273 difference raw20506; decide +kernel
    rw [ha]
    exact (canonical20506 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1273 + difference 4 1) (sourceB1273 + difference 1 4) sourceC1273) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1146) := by
    have ha : (tripleCharges (sourceA1273 + difference 4 1) (sourceB1273 + difference 1 4) sourceC1273) = raw20507 := by
      apply Matrix.ext; unfold tripleCharges sourceA1273 sourceB1273 sourceC1273 difference raw20507; decide +kernel
    rw [ha]
    exact (canonical20507 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1273 + difference 4 2) (sourceB1273 + difference 2 4) sourceC1273) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1146) := by
    have ha : (tripleCharges (sourceA1273 + difference 4 2) (sourceB1273 + difference 2 4) sourceC1273) = raw20508 := by
      apply Matrix.ext; unfold tripleCharges sourceA1273 sourceB1273 sourceC1273 difference raw20508; decide +kernel
    rw [ha]
    exact (canonical20508 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1273 + difference 4 3) (sourceB1273 + difference 3 4) sourceC1273) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1146) := by
    have ha : (tripleCharges (sourceA1273 + difference 4 3) (sourceB1273 + difference 3 4) sourceC1273) = raw20509 := by
      apply Matrix.ext; unfold tripleCharges sourceA1273 sourceB1273 sourceC1273 difference raw20509; decide +kernel
    rw [ha]
    exact (canonical20509 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1273 + difference 4 5) (sourceB1273 + difference 5 4) sourceC1273) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1310) := by
    have ha : (tripleCharges (sourceA1273 + difference 4 5) (sourceB1273 + difference 5 4) sourceC1273) = raw10280 := by
      apply Matrix.ext; unfold tripleCharges sourceA1273 sourceB1273 sourceC1273 difference raw10280; decide +kernel
    rw [ha]
    exact (canonical10280 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1273 + difference 5 0) (sourceB1273 + difference 0 5) sourceC1273) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 617) := by
    have ha : (tripleCharges (sourceA1273 + difference 5 0) (sourceB1273 + difference 0 5) sourceC1273) = raw19659 := by
      apply Matrix.ext; unfold tripleCharges sourceA1273 sourceB1273 sourceC1273 difference raw19659; decide +kernel
    rw [ha]
    exact (canonical19659 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1273 + difference 5 1) (sourceB1273 + difference 1 5) sourceC1273) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1142) := by
    have ha : (tripleCharges (sourceA1273 + difference 5 1) (sourceB1273 + difference 1 5) sourceC1273) = raw19660 := by
      apply Matrix.ext; unfold tripleCharges sourceA1273 sourceB1273 sourceC1273 difference raw19660; decide +kernel
    rw [ha]
    exact (canonical19660 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1273 + difference 5 2) (sourceB1273 + difference 2 5) sourceC1273) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1142) := by
    have ha : (tripleCharges (sourceA1273 + difference 5 2) (sourceB1273 + difference 2 5) sourceC1273) = raw19661 := by
      apply Matrix.ext; unfold tripleCharges sourceA1273 sourceB1273 sourceC1273 difference raw19661; decide +kernel
    rw [ha]
    exact (canonical19661 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1273 + difference 5 3) (sourceB1273 + difference 3 5) sourceC1273) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1142) := by
    have ha : (tripleCharges (sourceA1273 + difference 5 3) (sourceB1273 + difference 3 5) sourceC1273) = raw19662 := by
      apply Matrix.ext; unfold tripleCharges sourceA1273 sourceB1273 sourceC1273 difference raw19662; decide +kernel
    rw [ha]
    exact (canonical19662 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1273 + difference 5 4) (sourceB1273 + difference 4 5) sourceC1273) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1275) := by
    have ha : (tripleCharges (sourceA1273 + difference 5 4) (sourceB1273 + difference 4 5) sourceC1273) = raw20510 := by
      apply Matrix.ext; unfold tripleCharges sourceA1273 sourceB1273 sourceC1273 difference raw20510; decide +kernel
    rw [ha]
    exact (canonical20510 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1273 sourceB1273 sourceC1273
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1273, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1274 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1274 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC1274 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceForm1274 : Integer.Sparse Master := [(Sum.inr 1530, 3), (Sum.inr 1531, 1), (Sum.inr 1540, 1), (Sum.inr 1722, 3), (Sum.inr 1752, 1), (Sum.inr 2200, 6), (Sum.inr 2226, 3), (Sum.inr 2258, 3), (Sum.inr 2261, 3), (Sum.inr 2292, 1), (Sum.inr 2737, 3), (Sum.inr 2780, 1), (Sum.inr 2783, 1)]

theorem sourceEq1274 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1274 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1274 + difference 0 1) (sourceB1274 + difference 1 0) sourceC1274) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2261) := by
    have ha : (tripleCharges (sourceA1274 + difference 0 1) (sourceB1274 + difference 1 0) sourceC1274) = raw5152 := by
      apply Matrix.ext; unfold tripleCharges sourceA1274 sourceB1274 sourceC1274 difference raw5152; decide +kernel
    rw [ha]
    exact (canonical5152 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1274 + difference 0 2) (sourceB1274 + difference 2 0) sourceC1274) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2261) := by
    have ha : (tripleCharges (sourceA1274 + difference 0 2) (sourceB1274 + difference 2 0) sourceC1274) = raw5153 := by
      apply Matrix.ext; unfold tripleCharges sourceA1274 sourceB1274 sourceC1274 difference raw5153; decide +kernel
    rw [ha]
    exact (canonical5153 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1274 + difference 0 3) (sourceB1274 + difference 3 0) sourceC1274) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2261) := by
    have ha : (tripleCharges (sourceA1274 + difference 0 3) (sourceB1274 + difference 3 0) sourceC1274) = raw5154 := by
      apply Matrix.ext; unfold tripleCharges sourceA1274 sourceB1274 sourceC1274 difference raw5154; decide +kernel
    rw [ha]
    exact (canonical5154 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1274 + difference 0 4) (sourceB1274 + difference 4 0) sourceC1274) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2292) := by
    have ha : (tripleCharges (sourceA1274 + difference 0 4) (sourceB1274 + difference 4 0) sourceC1274) = raw10311 := by
      apply Matrix.ext; unfold tripleCharges sourceA1274 sourceB1274 sourceC1274 difference raw10311; decide +kernel
    rw [ha]
    exact (canonical10311 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1274 + difference 0 5) (sourceB1274 + difference 5 0) sourceC1274) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2783) := by
    have ha : (tripleCharges (sourceA1274 + difference 0 5) (sourceB1274 + difference 5 0) sourceC1274) = raw5155 := by
      apply Matrix.ext; unfold tripleCharges sourceA1274 sourceB1274 sourceC1274 difference raw5155; decide +kernel
    rw [ha]
    exact (canonical5155 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1274 + difference 1 0) (sourceB1274 + difference 0 1) sourceC1274) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1530) := by
    have ha : (tripleCharges (sourceA1274 + difference 1 0) (sourceB1274 + difference 0 1) sourceC1274) = raw20511 := by
      apply Matrix.ext; unfold tripleCharges sourceA1274 sourceB1274 sourceC1274 difference raw20511; decide +kernel
    rw [ha]
    exact (canonical20511 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1274 + difference 1 2) (sourceB1274 + difference 2 1) sourceC1274) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2200) := by
    have ha : (tripleCharges (sourceA1274 + difference 1 2) (sourceB1274 + difference 2 1) sourceC1274) = raw20512 := by
      apply Matrix.ext; unfold tripleCharges sourceA1274 sourceB1274 sourceC1274 difference raw20512; decide +kernel
    rw [ha]
    exact (canonical20512 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1274 + difference 1 3) (sourceB1274 + difference 3 1) sourceC1274) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2200) := by
    have ha : (tripleCharges (sourceA1274 + difference 1 3) (sourceB1274 + difference 3 1) sourceC1274) = raw20513 := by
      apply Matrix.ext; unfold tripleCharges sourceA1274 sourceB1274 sourceC1274 difference raw20513; decide +kernel
    rw [ha]
    exact (canonical20513 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1274 + difference 1 4) (sourceB1274 + difference 4 1) sourceC1274) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2226) := by
    have ha : (tripleCharges (sourceA1274 + difference 1 4) (sourceB1274 + difference 4 1) sourceC1274) = raw5136 := by
      apply Matrix.ext; unfold tripleCharges sourceA1274 sourceB1274 sourceC1274 difference raw5136; decide +kernel
    rw [ha]
    exact (canonical5136 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1274 + difference 1 5) (sourceB1274 + difference 5 1) sourceC1274) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2737) := by
    have ha : (tripleCharges (sourceA1274 + difference 1 5) (sourceB1274 + difference 5 1) sourceC1274) = raw10294 := by
      apply Matrix.ext; unfold tripleCharges sourceA1274 sourceB1274 sourceC1274 difference raw10294; decide +kernel
    rw [ha]
    exact (canonical10294 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1274 + difference 2 0) (sourceB1274 + difference 0 2) sourceC1274) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1530) := by
    have ha : (tripleCharges (sourceA1274 + difference 2 0) (sourceB1274 + difference 0 2) sourceC1274) = raw20514 := by
      apply Matrix.ext; unfold tripleCharges sourceA1274 sourceB1274 sourceC1274 difference raw20514; decide +kernel
    rw [ha]
    exact (canonical20514 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1274 + difference 2 1) (sourceB1274 + difference 1 2) sourceC1274) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2200) := by
    have ha : (tripleCharges (sourceA1274 + difference 2 1) (sourceB1274 + difference 1 2) sourceC1274) = raw20515 := by
      apply Matrix.ext; unfold tripleCharges sourceA1274 sourceB1274 sourceC1274 difference raw20515; decide +kernel
    rw [ha]
    exact (canonical20515 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1274 + difference 2 3) (sourceB1274 + difference 3 2) sourceC1274) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2200) := by
    have ha : (tripleCharges (sourceA1274 + difference 2 3) (sourceB1274 + difference 3 2) sourceC1274) = raw20516 := by
      apply Matrix.ext; unfold tripleCharges sourceA1274 sourceB1274 sourceC1274 difference raw20516; decide +kernel
    rw [ha]
    exact (canonical20516 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1274 + difference 2 4) (sourceB1274 + difference 4 2) sourceC1274) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2226) := by
    have ha : (tripleCharges (sourceA1274 + difference 2 4) (sourceB1274 + difference 4 2) sourceC1274) = raw5141 := by
      apply Matrix.ext; unfold tripleCharges sourceA1274 sourceB1274 sourceC1274 difference raw5141; decide +kernel
    rw [ha]
    exact (canonical5141 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1274 + difference 2 5) (sourceB1274 + difference 5 2) sourceC1274) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2737) := by
    have ha : (tripleCharges (sourceA1274 + difference 2 5) (sourceB1274 + difference 5 2) sourceC1274) = raw10298 := by
      apply Matrix.ext; unfold tripleCharges sourceA1274 sourceB1274 sourceC1274 difference raw10298; decide +kernel
    rw [ha]
    exact (canonical10298 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1274 + difference 3 0) (sourceB1274 + difference 0 3) sourceC1274) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1530) := by
    have ha : (tripleCharges (sourceA1274 + difference 3 0) (sourceB1274 + difference 0 3) sourceC1274) = raw20517 := by
      apply Matrix.ext; unfold tripleCharges sourceA1274 sourceB1274 sourceC1274 difference raw20517; decide +kernel
    rw [ha]
    exact (canonical20517 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1274 + difference 3 1) (sourceB1274 + difference 1 3) sourceC1274) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2200) := by
    have ha : (tripleCharges (sourceA1274 + difference 3 1) (sourceB1274 + difference 1 3) sourceC1274) = raw20518 := by
      apply Matrix.ext; unfold tripleCharges sourceA1274 sourceB1274 sourceC1274 difference raw20518; decide +kernel
    rw [ha]
    exact (canonical20518 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1274 + difference 3 2) (sourceB1274 + difference 2 3) sourceC1274) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2200) := by
    have ha : (tripleCharges (sourceA1274 + difference 3 2) (sourceB1274 + difference 2 3) sourceC1274) = raw20519 := by
      apply Matrix.ext; unfold tripleCharges sourceA1274 sourceB1274 sourceC1274 difference raw20519; decide +kernel
    rw [ha]
    exact (canonical20519 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1274 + difference 3 4) (sourceB1274 + difference 4 3) sourceC1274) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2226) := by
    have ha : (tripleCharges (sourceA1274 + difference 3 4) (sourceB1274 + difference 4 3) sourceC1274) = raw5146 := by
      apply Matrix.ext; unfold tripleCharges sourceA1274 sourceB1274 sourceC1274 difference raw5146; decide +kernel
    rw [ha]
    exact (canonical5146 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1274 + difference 3 5) (sourceB1274 + difference 5 3) sourceC1274) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2737) := by
    have ha : (tripleCharges (sourceA1274 + difference 3 5) (sourceB1274 + difference 5 3) sourceC1274) = raw10302 := by
      apply Matrix.ext; unfold tripleCharges sourceA1274 sourceB1274 sourceC1274 difference raw10302; decide +kernel
    rw [ha]
    exact (canonical10302 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1274 + difference 4 0) (sourceB1274 + difference 0 4) sourceC1274) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1531) := by
    have ha : (tripleCharges (sourceA1274 + difference 4 0) (sourceB1274 + difference 0 4) sourceC1274) = raw20520 := by
      apply Matrix.ext; unfold tripleCharges sourceA1274 sourceB1274 sourceC1274 difference raw20520; decide +kernel
    rw [ha]
    exact (canonical20520 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1274 + difference 4 1) (sourceB1274 + difference 1 4) sourceC1274) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2258) := by
    have ha : (tripleCharges (sourceA1274 + difference 4 1) (sourceB1274 + difference 1 4) sourceC1274) = raw20521 := by
      apply Matrix.ext; unfold tripleCharges sourceA1274 sourceB1274 sourceC1274 difference raw20521; decide +kernel
    rw [ha]
    exact (canonical20521 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1274 + difference 4 2) (sourceB1274 + difference 2 4) sourceC1274) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2258) := by
    have ha : (tripleCharges (sourceA1274 + difference 4 2) (sourceB1274 + difference 2 4) sourceC1274) = raw20522 := by
      apply Matrix.ext; unfold tripleCharges sourceA1274 sourceB1274 sourceC1274 difference raw20522; decide +kernel
    rw [ha]
    exact (canonical20522 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1274 + difference 4 3) (sourceB1274 + difference 3 4) sourceC1274) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2258) := by
    have ha : (tripleCharges (sourceA1274 + difference 4 3) (sourceB1274 + difference 3 4) sourceC1274) = raw20523 := by
      apply Matrix.ext; unfold tripleCharges sourceA1274 sourceB1274 sourceC1274 difference raw20523; decide +kernel
    rw [ha]
    exact (canonical20523 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1274 + difference 4 5) (sourceB1274 + difference 5 4) sourceC1274) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2780) := by
    have ha : (tripleCharges (sourceA1274 + difference 4 5) (sourceB1274 + difference 5 4) sourceC1274) = raw10306 := by
      apply Matrix.ext; unfold tripleCharges sourceA1274 sourceB1274 sourceC1274 difference raw10306; decide +kernel
    rw [ha]
    exact (canonical10306 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1274 + difference 5 0) (sourceB1274 + difference 0 5) sourceC1274) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1540) := by
    have ha : (tripleCharges (sourceA1274 + difference 5 0) (sourceB1274 + difference 0 5) sourceC1274) = raw19680 := by
      apply Matrix.ext; unfold tripleCharges sourceA1274 sourceB1274 sourceC1274 difference raw19680; decide +kernel
    rw [ha]
    exact (canonical19680 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1274 + difference 5 1) (sourceB1274 + difference 1 5) sourceC1274) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1722) := by
    have ha : (tripleCharges (sourceA1274 + difference 5 1) (sourceB1274 + difference 1 5) sourceC1274) = raw19681 := by
      apply Matrix.ext; unfold tripleCharges sourceA1274 sourceB1274 sourceC1274 difference raw19681; decide +kernel
    rw [ha]
    exact (canonical19681 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1274 + difference 5 2) (sourceB1274 + difference 2 5) sourceC1274) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1722) := by
    have ha : (tripleCharges (sourceA1274 + difference 5 2) (sourceB1274 + difference 2 5) sourceC1274) = raw19682 := by
      apply Matrix.ext; unfold tripleCharges sourceA1274 sourceB1274 sourceC1274 difference raw19682; decide +kernel
    rw [ha]
    exact (canonical19682 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1274 + difference 5 3) (sourceB1274 + difference 3 5) sourceC1274) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1722) := by
    have ha : (tripleCharges (sourceA1274 + difference 5 3) (sourceB1274 + difference 3 5) sourceC1274) = raw19683 := by
      apply Matrix.ext; unfold tripleCharges sourceA1274 sourceB1274 sourceC1274 difference raw19683; decide +kernel
    rw [ha]
    exact (canonical19683 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1274 + difference 5 4) (sourceB1274 + difference 4 5) sourceC1274) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1752) := by
    have ha : (tripleCharges (sourceA1274 + difference 5 4) (sourceB1274 + difference 4 5) sourceC1274) = raw5156 := by
      apply Matrix.ext; unfold tripleCharges sourceA1274 sourceB1274 sourceC1274 difference raw5156; decide +kernel
    rw [ha]
    exact (canonical5156 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1274 sourceB1274 sourceC1274
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1274, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1275 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1275 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC1275 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceForm1275 : Integer.Sparse Master := [(Sum.inr 639, 3), (Sum.inr 643, 1), (Sum.inr 654, 1), (Sum.inr 1297, 1), (Sum.inr 4084, -1)]

theorem sourceEq1275 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1275 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1275 + difference 0 0) (sourceB1275 + difference 0 0) sourceC1275) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1297) := by
    have ha : (tripleCharges (sourceA1275 + difference 0 0) (sourceB1275 + difference 0 0) sourceC1275) = raw5165 := by
      apply Matrix.ext; unfold tripleCharges sourceA1275 sourceB1275 sourceC1275 difference raw5165; decide +kernel
    rw [ha]
    exact (canonical5165 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1275 + difference 1 0) (sourceB1275 + difference 0 1) sourceC1275) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 639) := by
    have ha : (tripleCharges (sourceA1275 + difference 1 0) (sourceB1275 + difference 0 1) sourceC1275) = raw20524 := by
      apply Matrix.ext; unfold tripleCharges sourceA1275 sourceB1275 sourceC1275 difference raw20524; decide +kernel
    rw [ha]
    exact (canonical20524 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1275 + difference 2 0) (sourceB1275 + difference 0 2) sourceC1275) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 639) := by
    have ha : (tripleCharges (sourceA1275 + difference 2 0) (sourceB1275 + difference 0 2) sourceC1275) = raw20525 := by
      apply Matrix.ext; unfold tripleCharges sourceA1275 sourceB1275 sourceC1275 difference raw20525; decide +kernel
    rw [ha]
    exact (canonical20525 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1275 + difference 3 0) (sourceB1275 + difference 0 3) sourceC1275) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 639) := by
    have ha : (tripleCharges (sourceA1275 + difference 3 0) (sourceB1275 + difference 0 3) sourceC1275) = raw20526 := by
      apply Matrix.ext; unfold tripleCharges sourceA1275 sourceB1275 sourceC1275 difference raw20526; decide +kernel
    rw [ha]
    exact (canonical20526 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1275 + difference 4 0) (sourceB1275 + difference 0 4) sourceC1275) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 654) := by
    have ha : (tripleCharges (sourceA1275 + difference 4 0) (sourceB1275 + difference 0 4) sourceC1275) = raw20527 := by
      apply Matrix.ext; unfold tripleCharges sourceA1275 sourceB1275 sourceC1275 difference raw20527; decide +kernel
    rw [ha]
    exact (canonical20527 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1275 + difference 5 0) (sourceB1275 + difference 0 5) sourceC1275) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 643) := by
    have ha : (tripleCharges (sourceA1275 + difference 5 0) (sourceB1275 + difference 0 5) sourceC1275) = raw19692 := by
      apply Matrix.ext; unfold tripleCharges sourceA1275 sourceB1275 sourceC1275 difference raw19692; decide +kernel
    rw [ha]
    exact (canonical19692 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1275 + sourceB1275) sourceC1275) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1275 + sourceB1275) sourceC1275) = raw5167 := by
      apply Matrix.ext; unfold doubleCharges sourceA1275 sourceB1275 sourceC1275 raw5167; decide +kernel
    rw [ha]
    exact (canonical5167 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1275 sourceB1275 sourceC1275
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1275, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1276 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1276 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC1276 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceForm1276 : Integer.Sparse Master := [(Sum.inr 639, 1), (Sum.inr 1157, 2), (Sum.inr 1239, 1), (Sum.inr 1292, 1), (Sum.inr 1297, 1), (Sum.inr 4084, -1)]

theorem sourceEq1276 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1276 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1276 + difference 1 0) (sourceB1276 + difference 0 1) sourceC1276) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 639) := by
    have ha : (tripleCharges (sourceA1276 + difference 1 0) (sourceB1276 + difference 0 1) sourceC1276) = raw20524 := by
      apply Matrix.ext; unfold tripleCharges sourceA1276 sourceB1276 sourceC1276 difference raw20524; decide +kernel
    rw [ha]
    exact (canonical20524 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1276 + difference 1 1) (sourceB1276 + difference 1 1) sourceC1276) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1297) := by
    have ha : (tripleCharges (sourceA1276 + difference 1 1) (sourceB1276 + difference 1 1) sourceC1276) = raw5165 := by
      apply Matrix.ext; unfold tripleCharges sourceA1276 sourceB1276 sourceC1276 difference raw5165; decide +kernel
    rw [ha]
    exact (canonical5165 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1276 + difference 1 2) (sourceB1276 + difference 2 1) sourceC1276) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1157) := by
    have ha : (tripleCharges (sourceA1276 + difference 1 2) (sourceB1276 + difference 2 1) sourceC1276) = raw20528 := by
      apply Matrix.ext; unfold tripleCharges sourceA1276 sourceB1276 sourceC1276 difference raw20528; decide +kernel
    rw [ha]
    exact (canonical20528 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1276 + difference 1 3) (sourceB1276 + difference 3 1) sourceC1276) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1157) := by
    have ha : (tripleCharges (sourceA1276 + difference 1 3) (sourceB1276 + difference 3 1) sourceC1276) = raw20529 := by
      apply Matrix.ext; unfold tripleCharges sourceA1276 sourceB1276 sourceC1276 difference raw20529; decide +kernel
    rw [ha]
    exact (canonical20529 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1276 + difference 1 4) (sourceB1276 + difference 4 1) sourceC1276) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1239) := by
    have ha : (tripleCharges (sourceA1276 + difference 1 4) (sourceB1276 + difference 4 1) sourceC1276) = raw5162 := by
      apply Matrix.ext; unfold tripleCharges sourceA1276 sourceB1276 sourceC1276 difference raw5162; decide +kernel
    rw [ha]
    exact (canonical5162 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1276 + difference 1 5) (sourceB1276 + difference 5 1) sourceC1276) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1292) := by
    have ha : (tripleCharges (sourceA1276 + difference 1 5) (sourceB1276 + difference 5 1) sourceC1276) = raw20530 := by
      apply Matrix.ext; unfold tripleCharges sourceA1276 sourceB1276 sourceC1276 difference raw20530; decide +kernel
    rw [ha]
    exact (canonical20530 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1276 + sourceB1276) sourceC1276) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1276 + sourceB1276) sourceC1276) = raw5167 := by
      apply Matrix.ext; unfold doubleCharges sourceA1276 sourceB1276 sourceC1276 raw5167; decide +kernel
    rw [ha]
    exact (canonical5167 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1276 sourceB1276 sourceC1276
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1276, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1277 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1277 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC1277 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceForm1277 : Integer.Sparse Master := [(Sum.inr 948, 1), (Sum.inr 1157, 2), (Sum.inr 1174, 1), (Sum.inr 1297, 1), (Sum.inr 2109, 1), (Sum.inr 4084, -1)]

theorem sourceEq1277 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1277 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1277 + difference 0 1) (sourceB1277 + difference 1 0) sourceC1277) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2109) := by
    have ha : (tripleCharges (sourceA1277 + difference 0 1) (sourceB1277 + difference 1 0) sourceC1277) = raw5175 := by
      apply Matrix.ext; unfold tripleCharges sourceA1277 sourceB1277 sourceC1277 difference raw5175; decide +kernel
    rw [ha]
    exact (canonical5175 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1277 + difference 1 1) (sourceB1277 + difference 1 1) sourceC1277) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1297) := by
    have ha : (tripleCharges (sourceA1277 + difference 1 1) (sourceB1277 + difference 1 1) sourceC1277) = raw5165 := by
      apply Matrix.ext; unfold tripleCharges sourceA1277 sourceB1277 sourceC1277 difference raw5165; decide +kernel
    rw [ha]
    exact (canonical5165 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1277 + difference 2 1) (sourceB1277 + difference 1 2) sourceC1277) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1157) := by
    have ha : (tripleCharges (sourceA1277 + difference 2 1) (sourceB1277 + difference 1 2) sourceC1277) = raw20531 := by
      apply Matrix.ext; unfold tripleCharges sourceA1277 sourceB1277 sourceC1277 difference raw20531; decide +kernel
    rw [ha]
    exact (canonical20531 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1277 + difference 3 1) (sourceB1277 + difference 1 3) sourceC1277) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1157) := by
    have ha : (tripleCharges (sourceA1277 + difference 3 1) (sourceB1277 + difference 1 3) sourceC1277) = raw20532 := by
      apply Matrix.ext; unfold tripleCharges sourceA1277 sourceB1277 sourceC1277 difference raw20532; decide +kernel
    rw [ha]
    exact (canonical20532 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1277 + difference 4 1) (sourceB1277 + difference 1 4) sourceC1277) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1174) := by
    have ha : (tripleCharges (sourceA1277 + difference 4 1) (sourceB1277 + difference 1 4) sourceC1277) = raw20533 := by
      apply Matrix.ext; unfold tripleCharges sourceA1277 sourceB1277 sourceC1277 difference raw20533; decide +kernel
    rw [ha]
    exact (canonical20533 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1277 + difference 5 1) (sourceB1277 + difference 1 5) sourceC1277) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 948) := by
    have ha : (tripleCharges (sourceA1277 + difference 5 1) (sourceB1277 + difference 1 5) sourceC1277) = raw19699 := by
      apply Matrix.ext; unfold tripleCharges sourceA1277 sourceB1277 sourceC1277 difference raw19699; decide +kernel
    rw [ha]
    exact (canonical19699 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1277 + sourceB1277) sourceC1277) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1277 + sourceB1277) sourceC1277) = raw5167 := by
      apply Matrix.ext; unfold doubleCharges sourceA1277 sourceB1277 sourceC1277 raw5167; decide +kernel
    rw [ha]
    exact (canonical5167 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1277 sourceB1277 sourceC1277
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1277, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1278 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1278 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceC1278 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceForm1278 : Integer.Sparse Master := [(Sum.inr 4166, 3), (Sum.inr 4168, 1), (Sum.inr 4190, 1), (Sum.inr 4240, 3), (Sum.inr 4280, 1), (Sum.inr 4538, 6), (Sum.inr 4557, 3), (Sum.inr 4572, 3), (Sum.inr 4619, 3), (Sum.inr 4627, 1), (Sum.inr 4871, 3), (Sum.inr 4899, 1), (Sum.inr 5310, 1)]

theorem sourceEq1278 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1278 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1278 + difference 0 1) (sourceB1278 + difference 1 0) sourceC1278) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4871) := by
    have ha : (tripleCharges (sourceA1278 + difference 0 1) (sourceB1278 + difference 1 0) sourceC1278) = raw4393 := by
      apply Matrix.ext; unfold tripleCharges sourceA1278 sourceB1278 sourceC1278 difference raw4393; decide +kernel
    rw [ha]
    exact (canonical4393 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1278 + difference 0 2) (sourceB1278 + difference 2 0) sourceC1278) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4871) := by
    have ha : (tripleCharges (sourceA1278 + difference 0 2) (sourceB1278 + difference 2 0) sourceC1278) = raw4394 := by
      apply Matrix.ext; unfold tripleCharges sourceA1278 sourceB1278 sourceC1278 difference raw4394; decide +kernel
    rw [ha]
    exact (canonical4394 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1278 + difference 0 3) (sourceB1278 + difference 3 0) sourceC1278) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4871) := by
    have ha : (tripleCharges (sourceA1278 + difference 0 3) (sourceB1278 + difference 3 0) sourceC1278) = raw4395 := by
      apply Matrix.ext; unfold tripleCharges sourceA1278 sourceB1278 sourceC1278 difference raw4395; decide +kernel
    rw [ha]
    exact (canonical4395 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1278 + difference 0 4) (sourceB1278 + difference 4 0) sourceC1278) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4899) := by
    have ha : (tripleCharges (sourceA1278 + difference 0 4) (sourceB1278 + difference 4 0) sourceC1278) = raw2656 := by
      apply Matrix.ext; unfold tripleCharges sourceA1278 sourceB1278 sourceC1278 difference raw2656; decide +kernel
    rw [ha]
    exact (canonical2656 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1278 + difference 0 5) (sourceB1278 + difference 5 0) sourceC1278) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5310) := by
    have ha : (tripleCharges (sourceA1278 + difference 0 5) (sourceB1278 + difference 5 0) sourceC1278) = raw2651 := by
      apply Matrix.ext; unfold tripleCharges sourceA1278 sourceB1278 sourceC1278 difference raw2651; decide +kernel
    rw [ha]
    exact (canonical2651 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1278 + difference 1 0) (sourceB1278 + difference 0 1) sourceC1278) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4166) := by
    have ha : (tripleCharges (sourceA1278 + difference 1 0) (sourceB1278 + difference 0 1) sourceC1278) = raw20534 := by
      apply Matrix.ext; unfold tripleCharges sourceA1278 sourceB1278 sourceC1278 difference raw20534; decide +kernel
    rw [ha]
    exact (canonical20534 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1278 + difference 1 2) (sourceB1278 + difference 2 1) sourceC1278) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4538) := by
    have ha : (tripleCharges (sourceA1278 + difference 1 2) (sourceB1278 + difference 2 1) sourceC1278) = raw20535 := by
      apply Matrix.ext; unfold tripleCharges sourceA1278 sourceB1278 sourceC1278 difference raw20535; decide +kernel
    rw [ha]
    exact (canonical20535 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1278 + difference 1 3) (sourceB1278 + difference 3 1) sourceC1278) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4538) := by
    have ha : (tripleCharges (sourceA1278 + difference 1 3) (sourceB1278 + difference 3 1) sourceC1278) = raw20536 := by
      apply Matrix.ext; unfold tripleCharges sourceA1278 sourceB1278 sourceC1278 difference raw20536; decide +kernel
    rw [ha]
    exact (canonical20536 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1278 + difference 1 4) (sourceB1278 + difference 4 1) sourceC1278) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4572) := by
    have ha : (tripleCharges (sourceA1278 + difference 1 4) (sourceB1278 + difference 4 1) sourceC1278) = raw4380 := by
      apply Matrix.ext; unfold tripleCharges sourceA1278 sourceB1278 sourceC1278 difference raw4380; decide +kernel
    rw [ha]
    exact (canonical4380 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1278 + difference 1 5) (sourceB1278 + difference 5 1) sourceC1278) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4619) := by
    have ha : (tripleCharges (sourceA1278 + difference 1 5) (sourceB1278 + difference 5 1) sourceC1278) = raw7558 := by
      apply Matrix.ext; unfold tripleCharges sourceA1278 sourceB1278 sourceC1278 difference raw7558; decide +kernel
    rw [ha]
    exact (canonical7558 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1278 + difference 2 0) (sourceB1278 + difference 0 2) sourceC1278) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4166) := by
    have ha : (tripleCharges (sourceA1278 + difference 2 0) (sourceB1278 + difference 0 2) sourceC1278) = raw20537 := by
      apply Matrix.ext; unfold tripleCharges sourceA1278 sourceB1278 sourceC1278 difference raw20537; decide +kernel
    rw [ha]
    exact (canonical20537 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1278 + difference 2 1) (sourceB1278 + difference 1 2) sourceC1278) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4538) := by
    have ha : (tripleCharges (sourceA1278 + difference 2 1) (sourceB1278 + difference 1 2) sourceC1278) = raw20538 := by
      apply Matrix.ext; unfold tripleCharges sourceA1278 sourceB1278 sourceC1278 difference raw20538; decide +kernel
    rw [ha]
    exact (canonical20538 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1278 + difference 2 3) (sourceB1278 + difference 3 2) sourceC1278) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4538) := by
    have ha : (tripleCharges (sourceA1278 + difference 2 3) (sourceB1278 + difference 3 2) sourceC1278) = raw20539 := by
      apply Matrix.ext; unfold tripleCharges sourceA1278 sourceB1278 sourceC1278 difference raw20539; decide +kernel
    rw [ha]
    exact (canonical20539 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1278 + difference 2 4) (sourceB1278 + difference 4 2) sourceC1278) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4572) := by
    have ha : (tripleCharges (sourceA1278 + difference 2 4) (sourceB1278 + difference 4 2) sourceC1278) = raw4384 := by
      apply Matrix.ext; unfold tripleCharges sourceA1278 sourceB1278 sourceC1278 difference raw4384; decide +kernel
    rw [ha]
    exact (canonical4384 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1278 + difference 2 5) (sourceB1278 + difference 5 2) sourceC1278) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4619) := by
    have ha : (tripleCharges (sourceA1278 + difference 2 5) (sourceB1278 + difference 5 2) sourceC1278) = raw7562 := by
      apply Matrix.ext; unfold tripleCharges sourceA1278 sourceB1278 sourceC1278 difference raw7562; decide +kernel
    rw [ha]
    exact (canonical7562 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1278 + difference 3 0) (sourceB1278 + difference 0 3) sourceC1278) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4166) := by
    have ha : (tripleCharges (sourceA1278 + difference 3 0) (sourceB1278 + difference 0 3) sourceC1278) = raw20540 := by
      apply Matrix.ext; unfold tripleCharges sourceA1278 sourceB1278 sourceC1278 difference raw20540; decide +kernel
    rw [ha]
    exact (canonical20540 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1278 + difference 3 1) (sourceB1278 + difference 1 3) sourceC1278) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4538) := by
    have ha : (tripleCharges (sourceA1278 + difference 3 1) (sourceB1278 + difference 1 3) sourceC1278) = raw20541 := by
      apply Matrix.ext; unfold tripleCharges sourceA1278 sourceB1278 sourceC1278 difference raw20541; decide +kernel
    rw [ha]
    exact (canonical20541 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1278 + difference 3 2) (sourceB1278 + difference 2 3) sourceC1278) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4538) := by
    have ha : (tripleCharges (sourceA1278 + difference 3 2) (sourceB1278 + difference 2 3) sourceC1278) = raw20542 := by
      apply Matrix.ext; unfold tripleCharges sourceA1278 sourceB1278 sourceC1278 difference raw20542; decide +kernel
    rw [ha]
    exact (canonical20542 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1278 + difference 3 4) (sourceB1278 + difference 4 3) sourceC1278) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4572) := by
    have ha : (tripleCharges (sourceA1278 + difference 3 4) (sourceB1278 + difference 4 3) sourceC1278) = raw4388 := by
      apply Matrix.ext; unfold tripleCharges sourceA1278 sourceB1278 sourceC1278 difference raw4388; decide +kernel
    rw [ha]
    exact (canonical4388 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1278 + difference 3 5) (sourceB1278 + difference 5 3) sourceC1278) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4619) := by
    have ha : (tripleCharges (sourceA1278 + difference 3 5) (sourceB1278 + difference 5 3) sourceC1278) = raw7566 := by
      apply Matrix.ext; unfold tripleCharges sourceA1278 sourceB1278 sourceC1278 difference raw7566; decide +kernel
    rw [ha]
    exact (canonical7566 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1278 + difference 4 0) (sourceB1278 + difference 0 4) sourceC1278) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4190) := by
    have ha : (tripleCharges (sourceA1278 + difference 4 0) (sourceB1278 + difference 0 4) sourceC1278) = raw20543 := by
      apply Matrix.ext; unfold tripleCharges sourceA1278 sourceB1278 sourceC1278 difference raw20543; decide +kernel
    rw [ha]
    exact (canonical20543 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1278 + difference 4 1) (sourceB1278 + difference 1 4) sourceC1278) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4557) := by
    have ha : (tripleCharges (sourceA1278 + difference 4 1) (sourceB1278 + difference 1 4) sourceC1278) = raw20544 := by
      apply Matrix.ext; unfold tripleCharges sourceA1278 sourceB1278 sourceC1278 difference raw20544; decide +kernel
    rw [ha]
    exact (canonical20544 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1278 + difference 4 2) (sourceB1278 + difference 2 4) sourceC1278) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4557) := by
    have ha : (tripleCharges (sourceA1278 + difference 4 2) (sourceB1278 + difference 2 4) sourceC1278) = raw20545 := by
      apply Matrix.ext; unfold tripleCharges sourceA1278 sourceB1278 sourceC1278 difference raw20545; decide +kernel
    rw [ha]
    exact (canonical20545 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1278 + difference 4 3) (sourceB1278 + difference 3 4) sourceC1278) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4557) := by
    have ha : (tripleCharges (sourceA1278 + difference 4 3) (sourceB1278 + difference 3 4) sourceC1278) = raw20546 := by
      apply Matrix.ext; unfold tripleCharges sourceA1278 sourceB1278 sourceC1278 difference raw20546; decide +kernel
    rw [ha]
    exact (canonical20546 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1278 + difference 4 5) (sourceB1278 + difference 5 4) sourceC1278) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4627) := by
    have ha : (tripleCharges (sourceA1278 + difference 4 5) (sourceB1278 + difference 5 4) sourceC1278) = raw7570 := by
      apply Matrix.ext; unfold tripleCharges sourceA1278 sourceB1278 sourceC1278 difference raw7570; decide +kernel
    rw [ha]
    exact (canonical7570 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1278 + difference 5 0) (sourceB1278 + difference 0 5) sourceC1278) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4168) := by
    have ha : (tripleCharges (sourceA1278 + difference 5 0) (sourceB1278 + difference 0 5) sourceC1278) = raw20547 := by
      apply Matrix.ext; unfold tripleCharges sourceA1278 sourceB1278 sourceC1278 difference raw20547; decide +kernel
    rw [ha]
    exact (canonical20547 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1278 + difference 5 1) (sourceB1278 + difference 1 5) sourceC1278) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4240) := by
    have ha : (tripleCharges (sourceA1278 + difference 5 1) (sourceB1278 + difference 1 5) sourceC1278) = raw20548 := by
      apply Matrix.ext; unfold tripleCharges sourceA1278 sourceB1278 sourceC1278 difference raw20548; decide +kernel
    rw [ha]
    exact (canonical20548 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1278 + difference 5 2) (sourceB1278 + difference 2 5) sourceC1278) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4240) := by
    have ha : (tripleCharges (sourceA1278 + difference 5 2) (sourceB1278 + difference 2 5) sourceC1278) = raw20549 := by
      apply Matrix.ext; unfold tripleCharges sourceA1278 sourceB1278 sourceC1278 difference raw20549; decide +kernel
    rw [ha]
    exact (canonical20549 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1278 + difference 5 3) (sourceB1278 + difference 3 5) sourceC1278) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4240) := by
    have ha : (tripleCharges (sourceA1278 + difference 5 3) (sourceB1278 + difference 3 5) sourceC1278) = raw20550 := by
      apply Matrix.ext; unfold tripleCharges sourceA1278 sourceB1278 sourceC1278 difference raw20550; decide +kernel
    rw [ha]
    exact (canonical20550 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1278 + difference 5 4) (sourceB1278 + difference 4 5) sourceC1278) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4280) := by
    have ha : (tripleCharges (sourceA1278 + difference 5 4) (sourceB1278 + difference 4 5) sourceC1278) = raw4396 := by
      apply Matrix.ext; unfold tripleCharges sourceA1278 sourceB1278 sourceC1278 difference raw4396; decide +kernel
    rw [ha]
    exact (canonical4396 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1278 sourceB1278 sourceC1278
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1278, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1279 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1279 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceC1279 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceForm1279 : Integer.Sparse Master := [(Sum.inr 594, 3), (Sum.inr 596, 1), (Sum.inr 618, 1), (Sum.inr 740, 3), (Sum.inr 832, 1), (Sum.inr 1123, 6), (Sum.inr 1143, 3), (Sum.inr 1190, 3), (Sum.inr 1294, 3), (Sum.inr 1311, 1), (Sum.inr 2112, 3), (Sum.inr 2281, 1), (Sum.inr 3121, 1)]

theorem sourceEq1279 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1279 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1279 + difference 0 1) (sourceB1279 + difference 1 0) sourceC1279) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2112) := by
    have ha : (tripleCharges (sourceA1279 + difference 0 1) (sourceB1279 + difference 1 0) sourceC1279) = raw4422 := by
      apply Matrix.ext; unfold tripleCharges sourceA1279 sourceB1279 sourceC1279 difference raw4422; decide +kernel
    rw [ha]
    exact (canonical4422 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1279 + difference 0 2) (sourceB1279 + difference 2 0) sourceC1279) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2112) := by
    have ha : (tripleCharges (sourceA1279 + difference 0 2) (sourceB1279 + difference 2 0) sourceC1279) = raw4423 := by
      apply Matrix.ext; unfold tripleCharges sourceA1279 sourceB1279 sourceC1279 difference raw4423; decide +kernel
    rw [ha]
    exact (canonical4423 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1279 + difference 0 3) (sourceB1279 + difference 3 0) sourceC1279) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2112) := by
    have ha : (tripleCharges (sourceA1279 + difference 0 3) (sourceB1279 + difference 3 0) sourceC1279) = raw4424 := by
      apply Matrix.ext; unfold tripleCharges sourceA1279 sourceB1279 sourceC1279 difference raw4424; decide +kernel
    rw [ha]
    exact (canonical4424 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1279 + difference 0 4) (sourceB1279 + difference 4 0) sourceC1279) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2281) := by
    have ha : (tripleCharges (sourceA1279 + difference 0 4) (sourceB1279 + difference 4 0) sourceC1279) = raw7596 := by
      apply Matrix.ext; unfold tripleCharges sourceA1279 sourceB1279 sourceC1279 difference raw7596; decide +kernel
    rw [ha]
    exact (canonical7596 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1279 + difference 0 5) (sourceB1279 + difference 5 0) sourceC1279) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3121) := by
    have ha : (tripleCharges (sourceA1279 + difference 0 5) (sourceB1279 + difference 5 0) sourceC1279) = raw4425 := by
      apply Matrix.ext; unfold tripleCharges sourceA1279 sourceB1279 sourceC1279 difference raw4425; decide +kernel
    rw [ha]
    exact (canonical4425 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1279 + difference 1 0) (sourceB1279 + difference 0 1) sourceC1279) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 594) := by
    have ha : (tripleCharges (sourceA1279 + difference 1 0) (sourceB1279 + difference 0 1) sourceC1279) = raw20551 := by
      apply Matrix.ext; unfold tripleCharges sourceA1279 sourceB1279 sourceC1279 difference raw20551; decide +kernel
    rw [ha]
    exact (canonical20551 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1279 + difference 1 2) (sourceB1279 + difference 2 1) sourceC1279) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1123) := by
    have ha : (tripleCharges (sourceA1279 + difference 1 2) (sourceB1279 + difference 2 1) sourceC1279) = raw20552 := by
      apply Matrix.ext; unfold tripleCharges sourceA1279 sourceB1279 sourceC1279 difference raw20552; decide +kernel
    rw [ha]
    exact (canonical20552 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1279 + difference 1 3) (sourceB1279 + difference 3 1) sourceC1279) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1123) := by
    have ha : (tripleCharges (sourceA1279 + difference 1 3) (sourceB1279 + difference 3 1) sourceC1279) = raw20553 := by
      apply Matrix.ext; unfold tripleCharges sourceA1279 sourceB1279 sourceC1279 difference raw20553; decide +kernel
    rw [ha]
    exact (canonical20553 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1279 + difference 1 4) (sourceB1279 + difference 4 1) sourceC1279) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1190) := by
    have ha : (tripleCharges (sourceA1279 + difference 1 4) (sourceB1279 + difference 4 1) sourceC1279) = raw4406 := by
      apply Matrix.ext; unfold tripleCharges sourceA1279 sourceB1279 sourceC1279 difference raw4406; decide +kernel
    rw [ha]
    exact (canonical4406 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1279 + difference 1 5) (sourceB1279 + difference 5 1) sourceC1279) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1294) := by
    have ha : (tripleCharges (sourceA1279 + difference 1 5) (sourceB1279 + difference 5 1) sourceC1279) = raw7579 := by
      apply Matrix.ext; unfold tripleCharges sourceA1279 sourceB1279 sourceC1279 difference raw7579; decide +kernel
    rw [ha]
    exact (canonical7579 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1279 + difference 2 0) (sourceB1279 + difference 0 2) sourceC1279) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 594) := by
    have ha : (tripleCharges (sourceA1279 + difference 2 0) (sourceB1279 + difference 0 2) sourceC1279) = raw20554 := by
      apply Matrix.ext; unfold tripleCharges sourceA1279 sourceB1279 sourceC1279 difference raw20554; decide +kernel
    rw [ha]
    exact (canonical20554 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1279 + difference 2 1) (sourceB1279 + difference 1 2) sourceC1279) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1123) := by
    have ha : (tripleCharges (sourceA1279 + difference 2 1) (sourceB1279 + difference 1 2) sourceC1279) = raw20555 := by
      apply Matrix.ext; unfold tripleCharges sourceA1279 sourceB1279 sourceC1279 difference raw20555; decide +kernel
    rw [ha]
    exact (canonical20555 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1279 + difference 2 3) (sourceB1279 + difference 3 2) sourceC1279) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1123) := by
    have ha : (tripleCharges (sourceA1279 + difference 2 3) (sourceB1279 + difference 3 2) sourceC1279) = raw20556 := by
      apply Matrix.ext; unfold tripleCharges sourceA1279 sourceB1279 sourceC1279 difference raw20556; decide +kernel
    rw [ha]
    exact (canonical20556 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1279 + difference 2 4) (sourceB1279 + difference 4 2) sourceC1279) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1190) := by
    have ha : (tripleCharges (sourceA1279 + difference 2 4) (sourceB1279 + difference 4 2) sourceC1279) = raw4411 := by
      apply Matrix.ext; unfold tripleCharges sourceA1279 sourceB1279 sourceC1279 difference raw4411; decide +kernel
    rw [ha]
    exact (canonical4411 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1279 + difference 2 5) (sourceB1279 + difference 5 2) sourceC1279) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1294) := by
    have ha : (tripleCharges (sourceA1279 + difference 2 5) (sourceB1279 + difference 5 2) sourceC1279) = raw7583 := by
      apply Matrix.ext; unfold tripleCharges sourceA1279 sourceB1279 sourceC1279 difference raw7583; decide +kernel
    rw [ha]
    exact (canonical7583 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1279 + difference 3 0) (sourceB1279 + difference 0 3) sourceC1279) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 594) := by
    have ha : (tripleCharges (sourceA1279 + difference 3 0) (sourceB1279 + difference 0 3) sourceC1279) = raw20557 := by
      apply Matrix.ext; unfold tripleCharges sourceA1279 sourceB1279 sourceC1279 difference raw20557; decide +kernel
    rw [ha]
    exact (canonical20557 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1279 + difference 3 1) (sourceB1279 + difference 1 3) sourceC1279) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1123) := by
    have ha : (tripleCharges (sourceA1279 + difference 3 1) (sourceB1279 + difference 1 3) sourceC1279) = raw20558 := by
      apply Matrix.ext; unfold tripleCharges sourceA1279 sourceB1279 sourceC1279 difference raw20558; decide +kernel
    rw [ha]
    exact (canonical20558 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1279 + difference 3 2) (sourceB1279 + difference 2 3) sourceC1279) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1123) := by
    have ha : (tripleCharges (sourceA1279 + difference 3 2) (sourceB1279 + difference 2 3) sourceC1279) = raw20559 := by
      apply Matrix.ext; unfold tripleCharges sourceA1279 sourceB1279 sourceC1279 difference raw20559; decide +kernel
    rw [ha]
    exact (canonical20559 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1279 + difference 3 4) (sourceB1279 + difference 4 3) sourceC1279) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1190) := by
    have ha : (tripleCharges (sourceA1279 + difference 3 4) (sourceB1279 + difference 4 3) sourceC1279) = raw4416 := by
      apply Matrix.ext; unfold tripleCharges sourceA1279 sourceB1279 sourceC1279 difference raw4416; decide +kernel
    rw [ha]
    exact (canonical4416 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1279 + difference 3 5) (sourceB1279 + difference 5 3) sourceC1279) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1294) := by
    have ha : (tripleCharges (sourceA1279 + difference 3 5) (sourceB1279 + difference 5 3) sourceC1279) = raw7587 := by
      apply Matrix.ext; unfold tripleCharges sourceA1279 sourceB1279 sourceC1279 difference raw7587; decide +kernel
    rw [ha]
    exact (canonical7587 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1279 + difference 4 0) (sourceB1279 + difference 0 4) sourceC1279) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 618) := by
    have ha : (tripleCharges (sourceA1279 + difference 4 0) (sourceB1279 + difference 0 4) sourceC1279) = raw20560 := by
      apply Matrix.ext; unfold tripleCharges sourceA1279 sourceB1279 sourceC1279 difference raw20560; decide +kernel
    rw [ha]
    exact (canonical20560 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1279 + difference 4 1) (sourceB1279 + difference 1 4) sourceC1279) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1143) := by
    have ha : (tripleCharges (sourceA1279 + difference 4 1) (sourceB1279 + difference 1 4) sourceC1279) = raw20561 := by
      apply Matrix.ext; unfold tripleCharges sourceA1279 sourceB1279 sourceC1279 difference raw20561; decide +kernel
    rw [ha]
    exact (canonical20561 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1279 + difference 4 2) (sourceB1279 + difference 2 4) sourceC1279) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1143) := by
    have ha : (tripleCharges (sourceA1279 + difference 4 2) (sourceB1279 + difference 2 4) sourceC1279) = raw20562 := by
      apply Matrix.ext; unfold tripleCharges sourceA1279 sourceB1279 sourceC1279 difference raw20562; decide +kernel
    rw [ha]
    exact (canonical20562 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1279 + difference 4 3) (sourceB1279 + difference 3 4) sourceC1279) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1143) := by
    have ha : (tripleCharges (sourceA1279 + difference 4 3) (sourceB1279 + difference 3 4) sourceC1279) = raw20563 := by
      apply Matrix.ext; unfold tripleCharges sourceA1279 sourceB1279 sourceC1279 difference raw20563; decide +kernel
    rw [ha]
    exact (canonical20563 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1279 + difference 4 5) (sourceB1279 + difference 5 4) sourceC1279) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1311) := by
    have ha : (tripleCharges (sourceA1279 + difference 4 5) (sourceB1279 + difference 5 4) sourceC1279) = raw7591 := by
      apply Matrix.ext; unfold tripleCharges sourceA1279 sourceB1279 sourceC1279 difference raw7591; decide +kernel
    rw [ha]
    exact (canonical7591 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1279 + difference 5 0) (sourceB1279 + difference 0 5) sourceC1279) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 596) := by
    have ha : (tripleCharges (sourceA1279 + difference 5 0) (sourceB1279 + difference 0 5) sourceC1279) = raw20564 := by
      apply Matrix.ext; unfold tripleCharges sourceA1279 sourceB1279 sourceC1279 difference raw20564; decide +kernel
    rw [ha]
    exact (canonical20564 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1279 + difference 5 1) (sourceB1279 + difference 1 5) sourceC1279) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 740) := by
    have ha : (tripleCharges (sourceA1279 + difference 5 1) (sourceB1279 + difference 1 5) sourceC1279) = raw20565 := by
      apply Matrix.ext; unfold tripleCharges sourceA1279 sourceB1279 sourceC1279 difference raw20565; decide +kernel
    rw [ha]
    exact (canonical20565 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1279 + difference 5 2) (sourceB1279 + difference 2 5) sourceC1279) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 740) := by
    have ha : (tripleCharges (sourceA1279 + difference 5 2) (sourceB1279 + difference 2 5) sourceC1279) = raw20566 := by
      apply Matrix.ext; unfold tripleCharges sourceA1279 sourceB1279 sourceC1279 difference raw20566; decide +kernel
    rw [ha]
    exact (canonical20566 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1279 + difference 5 3) (sourceB1279 + difference 3 5) sourceC1279) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 740) := by
    have ha : (tripleCharges (sourceA1279 + difference 5 3) (sourceB1279 + difference 3 5) sourceC1279) = raw20567 := by
      apply Matrix.ext; unfold tripleCharges sourceA1279 sourceB1279 sourceC1279 difference raw20567; decide +kernel
    rw [ha]
    exact (canonical20567 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1279 + difference 5 4) (sourceB1279 + difference 4 5) sourceC1279) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 832) := by
    have ha : (tripleCharges (sourceA1279 + difference 5 4) (sourceB1279 + difference 4 5) sourceC1279) = raw4426 := by
      apply Matrix.ext; unfold tripleCharges sourceA1279 sourceB1279 sourceC1279 difference raw4426; decide +kernel
    rw [ha]
    exact (canonical4426 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1279 sourceB1279 sourceC1279
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1279, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
