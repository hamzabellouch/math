import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical50

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA256 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB256 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC256 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceForm256 : Integer.Sparse Master := [(Sum.inr 1214, 1), (Sum.inr 1218, 1), (Sum.inr 1219, 1), (Sum.inr 1241, 1), (Sum.inr 1263, 1), (Sum.inr 2724, 1), (Sum.inr 4092, -1)]

theorem sourceEq256 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm256 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA256 + difference 0 0) (sourceB256 + difference 0 0) sourceC256) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2724) := by
    have ha : (tripleCharges (sourceA256 + difference 0 0) (sourceB256 + difference 0 0) sourceC256) = raw6216 := by
      apply Matrix.ext; unfold tripleCharges sourceA256 sourceB256 sourceC256 difference raw6216; decide +kernel
    rw [ha]
    exact (canonical6216 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA256 + difference 1 0) (sourceB256 + difference 0 1) sourceC256) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1263) := by
    have ha : (tripleCharges (sourceA256 + difference 1 0) (sourceB256 + difference 0 1) sourceC256) = raw6223 := by
      apply Matrix.ext; unfold tripleCharges sourceA256 sourceB256 sourceC256 difference raw6223; decide +kernel
    rw [ha]
    exact (canonical6223 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA256 + difference 2 0) (sourceB256 + difference 0 2) sourceC256) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1214) := by
    have ha : (tripleCharges (sourceA256 + difference 2 0) (sourceB256 + difference 0 2) sourceC256) = raw6224 := by
      apply Matrix.ext; unfold tripleCharges sourceA256 sourceB256 sourceC256 difference raw6224; decide +kernel
    rw [ha]
    exact (canonical6224 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA256 + difference 3 0) (sourceB256 + difference 0 3) sourceC256) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1241) := by
    have ha : (tripleCharges (sourceA256 + difference 3 0) (sourceB256 + difference 0 3) sourceC256) = raw6225 := by
      apply Matrix.ext; unfold tripleCharges sourceA256 sourceB256 sourceC256 difference raw6225; decide +kernel
    rw [ha]
    exact (canonical6225 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA256 + difference 4 0) (sourceB256 + difference 0 4) sourceC256) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1219) := by
    have ha : (tripleCharges (sourceA256 + difference 4 0) (sourceB256 + difference 0 4) sourceC256) = raw6226 := by
      apply Matrix.ext; unfold tripleCharges sourceA256 sourceB256 sourceC256 difference raw6226; decide +kernel
    rw [ha]
    exact (canonical6226 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA256 + difference 5 0) (sourceB256 + difference 0 5) sourceC256) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1218) := by
    have ha : (tripleCharges (sourceA256 + difference 5 0) (sourceB256 + difference 0 5) sourceC256) = raw6227 := by
      apply Matrix.ext; unfold tripleCharges sourceA256 sourceB256 sourceC256 difference raw6227; decide +kernel
    rw [ha]
    exact (canonical6227 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA256 + sourceB256) sourceC256) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA256 + sourceB256) sourceC256) = raw6222 := by
      apply Matrix.ext; unfold doubleCharges sourceA256 sourceB256 sourceC256 raw6222; decide +kernel
    rw [ha]
    exact (canonical6222 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA256 sourceB256 sourceC256
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm256, Integer.Sparse.eval]
  linarith only [hs]

def sourceA257 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB257 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC257 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceForm257 : Integer.Sparse Master := [(Sum.inr 1263, 1), (Sum.inr 2568, 1), (Sum.inr 2634, 1), (Sum.inr 2724, 1), (Sum.inr 2758, 1), (Sum.inr 2763, 1), (Sum.inr 4092, -1)]

theorem sourceEq257 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm257 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA257 + difference 1 0) (sourceB257 + difference 0 1) sourceC257) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1263) := by
    have ha : (tripleCharges (sourceA257 + difference 1 0) (sourceB257 + difference 0 1) sourceC257) = raw6223 := by
      apply Matrix.ext; unfold tripleCharges sourceA257 sourceB257 sourceC257 difference raw6223; decide +kernel
    rw [ha]
    exact (canonical6223 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA257 + difference 1 1) (sourceB257 + difference 1 1) sourceC257) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2724) := by
    have ha : (tripleCharges (sourceA257 + difference 1 1) (sourceB257 + difference 1 1) sourceC257) = raw6216 := by
      apply Matrix.ext; unfold tripleCharges sourceA257 sourceB257 sourceC257 difference raw6216; decide +kernel
    rw [ha]
    exact (canonical6216 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA257 + difference 1 2) (sourceB257 + difference 2 1) sourceC257) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2568) := by
    have ha : (tripleCharges (sourceA257 + difference 1 2) (sourceB257 + difference 2 1) sourceC257) = raw6228 := by
      apply Matrix.ext; unfold tripleCharges sourceA257 sourceB257 sourceC257 difference raw6228; decide +kernel
    rw [ha]
    exact (canonical6228 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA257 + difference 1 3) (sourceB257 + difference 3 1) sourceC257) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2634) := by
    have ha : (tripleCharges (sourceA257 + difference 1 3) (sourceB257 + difference 3 1) sourceC257) = raw6229 := by
      apply Matrix.ext; unfold tripleCharges sourceA257 sourceB257 sourceC257 difference raw6229; decide +kernel
    rw [ha]
    exact (canonical6229 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA257 + difference 1 4) (sourceB257 + difference 4 1) sourceC257) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2758) := by
    have ha : (tripleCharges (sourceA257 + difference 1 4) (sourceB257 + difference 4 1) sourceC257) = raw6230 := by
      apply Matrix.ext; unfold tripleCharges sourceA257 sourceB257 sourceC257 difference raw6230; decide +kernel
    rw [ha]
    exact (canonical6230 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA257 + difference 1 5) (sourceB257 + difference 5 1) sourceC257) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2763) := by
    have ha : (tripleCharges (sourceA257 + difference 1 5) (sourceB257 + difference 5 1) sourceC257) = raw6231 := by
      apply Matrix.ext; unfold tripleCharges sourceA257 sourceB257 sourceC257 difference raw6231; decide +kernel
    rw [ha]
    exact (canonical6231 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA257 + sourceB257) sourceC257) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA257 + sourceB257) sourceC257) = raw6222 := by
      apply Matrix.ext; unfold doubleCharges sourceA257 sourceB257 sourceC257 raw6222; decide +kernel
    rw [ha]
    exact (canonical6222 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA257 sourceB257 sourceC257
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm257, Integer.Sparse.eval]
  linarith only [hs]

def sourceA258 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB258 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC258 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceForm258 : Integer.Sparse Master := [(Sum.inr 2481, 1), (Sum.inr 2486, 1), (Sum.inr 2488, 1), (Sum.inr 2515, 1), (Sum.inr 2724, 1), (Sum.inr 3809, 1), (Sum.inr 4092, -1)]

theorem sourceEq258 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm258 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA258 + difference 0 1) (sourceB258 + difference 1 0) sourceC258) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3809) := by
    have ha : (tripleCharges (sourceA258 + difference 0 1) (sourceB258 + difference 1 0) sourceC258) = raw6217 := by
      apply Matrix.ext; unfold tripleCharges sourceA258 sourceB258 sourceC258 difference raw6217; decide +kernel
    rw [ha]
    exact (canonical6217 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA258 + difference 1 1) (sourceB258 + difference 1 1) sourceC258) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2724) := by
    have ha : (tripleCharges (sourceA258 + difference 1 1) (sourceB258 + difference 1 1) sourceC258) = raw6216 := by
      apply Matrix.ext; unfold tripleCharges sourceA258 sourceB258 sourceC258 difference raw6216; decide +kernel
    rw [ha]
    exact (canonical6216 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA258 + difference 2 1) (sourceB258 + difference 1 2) sourceC258) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2481) := by
    have ha : (tripleCharges (sourceA258 + difference 2 1) (sourceB258 + difference 1 2) sourceC258) = raw6232 := by
      apply Matrix.ext; unfold tripleCharges sourceA258 sourceB258 sourceC258 difference raw6232; decide +kernel
    rw [ha]
    exact (canonical6232 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA258 + difference 3 1) (sourceB258 + difference 1 3) sourceC258) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2515) := by
    have ha : (tripleCharges (sourceA258 + difference 3 1) (sourceB258 + difference 1 3) sourceC258) = raw6233 := by
      apply Matrix.ext; unfold tripleCharges sourceA258 sourceB258 sourceC258 difference raw6233; decide +kernel
    rw [ha]
    exact (canonical6233 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA258 + difference 4 1) (sourceB258 + difference 1 4) sourceC258) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2488) := by
    have ha : (tripleCharges (sourceA258 + difference 4 1) (sourceB258 + difference 1 4) sourceC258) = raw6234 := by
      apply Matrix.ext; unfold tripleCharges sourceA258 sourceB258 sourceC258 difference raw6234; decide +kernel
    rw [ha]
    exact (canonical6234 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA258 + difference 5 1) (sourceB258 + difference 1 5) sourceC258) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2486) := by
    have ha : (tripleCharges (sourceA258 + difference 5 1) (sourceB258 + difference 1 5) sourceC258) = raw6235 := by
      apply Matrix.ext; unfold tripleCharges sourceA258 sourceB258 sourceC258 difference raw6235; decide +kernel
    rw [ha]
    exact (canonical6235 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA258 + sourceB258) sourceC258) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA258 + sourceB258) sourceC258) = raw6222 := by
      apply Matrix.ext; unfold doubleCharges sourceA258 sourceB258 sourceC258 raw6222; decide +kernel
    rw [ha]
    exact (canonical6222 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA258 sourceB258 sourceC258
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm258, Integer.Sparse.eval]
  linarith only [hs]

def sourceA259 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB259 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC259 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceForm259 : Integer.Sparse Master := [(Sum.inr 1214, 1), (Sum.inr 2481, 1), (Sum.inr 2616, 1), (Sum.inr 2714, 1), (Sum.inr 2720, 1), (Sum.inr 2724, 1), (Sum.inr 4092, -1)]

theorem sourceEq259 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm259 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA259 + difference 2 0) (sourceB259 + difference 0 2) sourceC259) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1214) := by
    have ha : (tripleCharges (sourceA259 + difference 2 0) (sourceB259 + difference 0 2) sourceC259) = raw6224 := by
      apply Matrix.ext; unfold tripleCharges sourceA259 sourceB259 sourceC259 difference raw6224; decide +kernel
    rw [ha]
    exact (canonical6224 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA259 + difference 2 1) (sourceB259 + difference 1 2) sourceC259) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2481) := by
    have ha : (tripleCharges (sourceA259 + difference 2 1) (sourceB259 + difference 1 2) sourceC259) = raw6232 := by
      apply Matrix.ext; unfold tripleCharges sourceA259 sourceB259 sourceC259 difference raw6232; decide +kernel
    rw [ha]
    exact (canonical6232 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA259 + difference 2 2) (sourceB259 + difference 2 2) sourceC259) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2724) := by
    have ha : (tripleCharges (sourceA259 + difference 2 2) (sourceB259 + difference 2 2) sourceC259) = raw6216 := by
      apply Matrix.ext; unfold tripleCharges sourceA259 sourceB259 sourceC259 difference raw6216; decide +kernel
    rw [ha]
    exact (canonical6216 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA259 + difference 2 3) (sourceB259 + difference 3 2) sourceC259) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2616) := by
    have ha : (tripleCharges (sourceA259 + difference 2 3) (sourceB259 + difference 3 2) sourceC259) = raw6236 := by
      apply Matrix.ext; unfold tripleCharges sourceA259 sourceB259 sourceC259 difference raw6236; decide +kernel
    rw [ha]
    exact (canonical6236 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA259 + difference 2 4) (sourceB259 + difference 4 2) sourceC259) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2714) := by
    have ha : (tripleCharges (sourceA259 + difference 2 4) (sourceB259 + difference 4 2) sourceC259) = raw6237 := by
      apply Matrix.ext; unfold tripleCharges sourceA259 sourceB259 sourceC259 difference raw6237; decide +kernel
    rw [ha]
    exact (canonical6237 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA259 + difference 2 5) (sourceB259 + difference 5 2) sourceC259) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2720) := by
    have ha : (tripleCharges (sourceA259 + difference 2 5) (sourceB259 + difference 5 2) sourceC259) = raw6238 := by
      apply Matrix.ext; unfold tripleCharges sourceA259 sourceB259 sourceC259 difference raw6238; decide +kernel
    rw [ha]
    exact (canonical6238 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA259 + sourceB259) sourceC259) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA259 + sourceB259) sourceC259) = raw6222 := by
      apply Matrix.ext; unfold doubleCharges sourceA259 sourceB259 sourceC259 raw6222; decide +kernel
    rw [ha]
    exact (canonical6222 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA259 sourceB259 sourceC259
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm259, Integer.Sparse.eval]
  linarith only [hs]

def sourceA260 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB260 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC260 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceForm260 : Integer.Sparse Master := [(Sum.inr 2544, 1), (Sum.inr 2545, 1), (Sum.inr 2557, 1), (Sum.inr 2568, 1), (Sum.inr 2724, 1), (Sum.inr 3839, 1), (Sum.inr 4092, -1)]

theorem sourceEq260 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm260 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA260 + difference 0 2) (sourceB260 + difference 2 0) sourceC260) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3839) := by
    have ha : (tripleCharges (sourceA260 + difference 0 2) (sourceB260 + difference 2 0) sourceC260) = raw6218 := by
      apply Matrix.ext; unfold tripleCharges sourceA260 sourceB260 sourceC260 difference raw6218; decide +kernel
    rw [ha]
    exact (canonical6218 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA260 + difference 1 2) (sourceB260 + difference 2 1) sourceC260) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2568) := by
    have ha : (tripleCharges (sourceA260 + difference 1 2) (sourceB260 + difference 2 1) sourceC260) = raw6228 := by
      apply Matrix.ext; unfold tripleCharges sourceA260 sourceB260 sourceC260 difference raw6228; decide +kernel
    rw [ha]
    exact (canonical6228 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA260 + difference 2 2) (sourceB260 + difference 2 2) sourceC260) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2724) := by
    have ha : (tripleCharges (sourceA260 + difference 2 2) (sourceB260 + difference 2 2) sourceC260) = raw6216 := by
      apply Matrix.ext; unfold tripleCharges sourceA260 sourceB260 sourceC260 difference raw6216; decide +kernel
    rw [ha]
    exact (canonical6216 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA260 + difference 3 2) (sourceB260 + difference 2 3) sourceC260) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2557) := by
    have ha : (tripleCharges (sourceA260 + difference 3 2) (sourceB260 + difference 2 3) sourceC260) = raw6239 := by
      apply Matrix.ext; unfold tripleCharges sourceA260 sourceB260 sourceC260 difference raw6239; decide +kernel
    rw [ha]
    exact (canonical6239 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA260 + difference 4 2) (sourceB260 + difference 2 4) sourceC260) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2545) := by
    have ha : (tripleCharges (sourceA260 + difference 4 2) (sourceB260 + difference 2 4) sourceC260) = raw6240 := by
      apply Matrix.ext; unfold tripleCharges sourceA260 sourceB260 sourceC260 difference raw6240; decide +kernel
    rw [ha]
    exact (canonical6240 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA260 + difference 5 2) (sourceB260 + difference 2 5) sourceC260) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2544) := by
    have ha : (tripleCharges (sourceA260 + difference 5 2) (sourceB260 + difference 2 5) sourceC260) = raw6241 := by
      apply Matrix.ext; unfold tripleCharges sourceA260 sourceB260 sourceC260 difference raw6241; decide +kernel
    rw [ha]
    exact (canonical6241 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA260 + sourceB260) sourceC260) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA260 + sourceB260) sourceC260) = raw6222 := by
      apply Matrix.ext; unfold doubleCharges sourceA260 sourceB260 sourceC260 raw6222; decide +kernel
    rw [ha]
    exact (canonical6222 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA260 sourceB260 sourceC260
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm260, Integer.Sparse.eval]
  linarith only [hs]

def sourceA261 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB261 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC261 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceForm261 : Integer.Sparse Master := [(Sum.inr 1241, 1), (Sum.inr 2515, 1), (Sum.inr 2557, 1), (Sum.inr 2724, 1), (Sum.inr 2732, 1), (Sum.inr 2739, 1), (Sum.inr 4092, -1)]

theorem sourceEq261 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm261 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA261 + difference 3 0) (sourceB261 + difference 0 3) sourceC261) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1241) := by
    have ha : (tripleCharges (sourceA261 + difference 3 0) (sourceB261 + difference 0 3) sourceC261) = raw6225 := by
      apply Matrix.ext; unfold tripleCharges sourceA261 sourceB261 sourceC261 difference raw6225; decide +kernel
    rw [ha]
    exact (canonical6225 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA261 + difference 3 1) (sourceB261 + difference 1 3) sourceC261) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2515) := by
    have ha : (tripleCharges (sourceA261 + difference 3 1) (sourceB261 + difference 1 3) sourceC261) = raw6233 := by
      apply Matrix.ext; unfold tripleCharges sourceA261 sourceB261 sourceC261 difference raw6233; decide +kernel
    rw [ha]
    exact (canonical6233 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA261 + difference 3 2) (sourceB261 + difference 2 3) sourceC261) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2557) := by
    have ha : (tripleCharges (sourceA261 + difference 3 2) (sourceB261 + difference 2 3) sourceC261) = raw6239 := by
      apply Matrix.ext; unfold tripleCharges sourceA261 sourceB261 sourceC261 difference raw6239; decide +kernel
    rw [ha]
    exact (canonical6239 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA261 + difference 3 3) (sourceB261 + difference 3 3) sourceC261) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2724) := by
    have ha : (tripleCharges (sourceA261 + difference 3 3) (sourceB261 + difference 3 3) sourceC261) = raw6216 := by
      apply Matrix.ext; unfold tripleCharges sourceA261 sourceB261 sourceC261 difference raw6216; decide +kernel
    rw [ha]
    exact (canonical6216 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA261 + difference 3 4) (sourceB261 + difference 4 3) sourceC261) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2732) := by
    have ha : (tripleCharges (sourceA261 + difference 3 4) (sourceB261 + difference 4 3) sourceC261) = raw6242 := by
      apply Matrix.ext; unfold tripleCharges sourceA261 sourceB261 sourceC261 difference raw6242; decide +kernel
    rw [ha]
    exact (canonical6242 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA261 + difference 3 5) (sourceB261 + difference 5 3) sourceC261) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2739) := by
    have ha : (tripleCharges (sourceA261 + difference 3 5) (sourceB261 + difference 5 3) sourceC261) = raw6243 := by
      apply Matrix.ext; unfold tripleCharges sourceA261 sourceB261 sourceC261 difference raw6243; decide +kernel
    rw [ha]
    exact (canonical6243 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA261 + sourceB261) sourceC261) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA261 + sourceB261) sourceC261) = raw6222 := by
      apply Matrix.ext; unfold doubleCharges sourceA261 sourceB261 sourceC261 raw6222; decide +kernel
    rw [ha]
    exact (canonical6222 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA261 sourceB261 sourceC261
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm261, Integer.Sparse.eval]
  linarith only [hs]

def sourceA262 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB262 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC262 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceForm262 : Integer.Sparse Master := [(Sum.inr 2616, 1), (Sum.inr 2619, 1), (Sum.inr 2620, 1), (Sum.inr 2634, 1), (Sum.inr 2724, 1), (Sum.inr 3877, 1), (Sum.inr 4092, -1)]

theorem sourceEq262 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm262 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA262 + difference 0 3) (sourceB262 + difference 3 0) sourceC262) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3877) := by
    have ha : (tripleCharges (sourceA262 + difference 0 3) (sourceB262 + difference 3 0) sourceC262) = raw6219 := by
      apply Matrix.ext; unfold tripleCharges sourceA262 sourceB262 sourceC262 difference raw6219; decide +kernel
    rw [ha]
    exact (canonical6219 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA262 + difference 1 3) (sourceB262 + difference 3 1) sourceC262) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2634) := by
    have ha : (tripleCharges (sourceA262 + difference 1 3) (sourceB262 + difference 3 1) sourceC262) = raw6229 := by
      apply Matrix.ext; unfold tripleCharges sourceA262 sourceB262 sourceC262 difference raw6229; decide +kernel
    rw [ha]
    exact (canonical6229 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA262 + difference 2 3) (sourceB262 + difference 3 2) sourceC262) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2616) := by
    have ha : (tripleCharges (sourceA262 + difference 2 3) (sourceB262 + difference 3 2) sourceC262) = raw6236 := by
      apply Matrix.ext; unfold tripleCharges sourceA262 sourceB262 sourceC262 difference raw6236; decide +kernel
    rw [ha]
    exact (canonical6236 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA262 + difference 3 3) (sourceB262 + difference 3 3) sourceC262) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2724) := by
    have ha : (tripleCharges (sourceA262 + difference 3 3) (sourceB262 + difference 3 3) sourceC262) = raw6216 := by
      apply Matrix.ext; unfold tripleCharges sourceA262 sourceB262 sourceC262 difference raw6216; decide +kernel
    rw [ha]
    exact (canonical6216 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA262 + difference 4 3) (sourceB262 + difference 3 4) sourceC262) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2620) := by
    have ha : (tripleCharges (sourceA262 + difference 4 3) (sourceB262 + difference 3 4) sourceC262) = raw6244 := by
      apply Matrix.ext; unfold tripleCharges sourceA262 sourceB262 sourceC262 difference raw6244; decide +kernel
    rw [ha]
    exact (canonical6244 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA262 + difference 5 3) (sourceB262 + difference 3 5) sourceC262) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2619) := by
    have ha : (tripleCharges (sourceA262 + difference 5 3) (sourceB262 + difference 3 5) sourceC262) = raw6245 := by
      apply Matrix.ext; unfold tripleCharges sourceA262 sourceB262 sourceC262 difference raw6245; decide +kernel
    rw [ha]
    exact (canonical6245 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA262 + sourceB262) sourceC262) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA262 + sourceB262) sourceC262) = raw6222 := by
      apply Matrix.ext; unfold doubleCharges sourceA262 sourceB262 sourceC262 raw6222; decide +kernel
    rw [ha]
    exact (canonical6222 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA262 sourceB262 sourceC262
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm262, Integer.Sparse.eval]
  linarith only [hs]

def sourceA263 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB263 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC263 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceForm263 : Integer.Sparse Master := [(Sum.inr 1219, 1), (Sum.inr 2488, 1), (Sum.inr 2545, 1), (Sum.inr 2620, 1), (Sum.inr 2722, 1), (Sum.inr 2724, 1), (Sum.inr 4092, -1)]

theorem sourceEq263 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm263 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA263 + difference 4 0) (sourceB263 + difference 0 4) sourceC263) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1219) := by
    have ha : (tripleCharges (sourceA263 + difference 4 0) (sourceB263 + difference 0 4) sourceC263) = raw6226 := by
      apply Matrix.ext; unfold tripleCharges sourceA263 sourceB263 sourceC263 difference raw6226; decide +kernel
    rw [ha]
    exact (canonical6226 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA263 + difference 4 1) (sourceB263 + difference 1 4) sourceC263) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2488) := by
    have ha : (tripleCharges (sourceA263 + difference 4 1) (sourceB263 + difference 1 4) sourceC263) = raw6234 := by
      apply Matrix.ext; unfold tripleCharges sourceA263 sourceB263 sourceC263 difference raw6234; decide +kernel
    rw [ha]
    exact (canonical6234 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA263 + difference 4 2) (sourceB263 + difference 2 4) sourceC263) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2545) := by
    have ha : (tripleCharges (sourceA263 + difference 4 2) (sourceB263 + difference 2 4) sourceC263) = raw6240 := by
      apply Matrix.ext; unfold tripleCharges sourceA263 sourceB263 sourceC263 difference raw6240; decide +kernel
    rw [ha]
    exact (canonical6240 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA263 + difference 4 3) (sourceB263 + difference 3 4) sourceC263) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2620) := by
    have ha : (tripleCharges (sourceA263 + difference 4 3) (sourceB263 + difference 3 4) sourceC263) = raw6244 := by
      apply Matrix.ext; unfold tripleCharges sourceA263 sourceB263 sourceC263 difference raw6244; decide +kernel
    rw [ha]
    exact (canonical6244 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA263 + difference 4 4) (sourceB263 + difference 4 4) sourceC263) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2724) := by
    have ha : (tripleCharges (sourceA263 + difference 4 4) (sourceB263 + difference 4 4) sourceC263) = raw6216 := by
      apply Matrix.ext; unfold tripleCharges sourceA263 sourceB263 sourceC263 difference raw6216; decide +kernel
    rw [ha]
    exact (canonical6216 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA263 + difference 4 5) (sourceB263 + difference 5 4) sourceC263) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA263 + difference 4 5) (sourceB263 + difference 5 4) sourceC263) = raw6246 := by
      apply Matrix.ext; unfold tripleCharges sourceA263 sourceB263 sourceC263 difference raw6246; decide +kernel
    rw [ha]
    exact (canonical6246 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA263 + sourceB263) sourceC263) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA263 + sourceB263) sourceC263) = raw6222 := by
      apply Matrix.ext; unfold doubleCharges sourceA263 sourceB263 sourceC263 raw6222; decide +kernel
    rw [ha]
    exact (canonical6222 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA263 sourceB263 sourceC263
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm263, Integer.Sparse.eval]
  linarith only [hs]

def sourceA264 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB264 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC264 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceForm264 : Integer.Sparse Master := [(Sum.inr 2714, 1), (Sum.inr 2716, 1), (Sum.inr 2724, 1), (Sum.inr 2732, 1), (Sum.inr 2758, 1), (Sum.inr 3814, 1), (Sum.inr 4092, -1)]

theorem sourceEq264 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm264 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA264 + difference 0 4) (sourceB264 + difference 4 0) sourceC264) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3814) := by
    have ha : (tripleCharges (sourceA264 + difference 0 4) (sourceB264 + difference 4 0) sourceC264) = raw6220 := by
      apply Matrix.ext; unfold tripleCharges sourceA264 sourceB264 sourceC264 difference raw6220; decide +kernel
    rw [ha]
    exact (canonical6220 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA264 + difference 1 4) (sourceB264 + difference 4 1) sourceC264) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2758) := by
    have ha : (tripleCharges (sourceA264 + difference 1 4) (sourceB264 + difference 4 1) sourceC264) = raw6230 := by
      apply Matrix.ext; unfold tripleCharges sourceA264 sourceB264 sourceC264 difference raw6230; decide +kernel
    rw [ha]
    exact (canonical6230 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA264 + difference 2 4) (sourceB264 + difference 4 2) sourceC264) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2714) := by
    have ha : (tripleCharges (sourceA264 + difference 2 4) (sourceB264 + difference 4 2) sourceC264) = raw6237 := by
      apply Matrix.ext; unfold tripleCharges sourceA264 sourceB264 sourceC264 difference raw6237; decide +kernel
    rw [ha]
    exact (canonical6237 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA264 + difference 3 4) (sourceB264 + difference 4 3) sourceC264) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2732) := by
    have ha : (tripleCharges (sourceA264 + difference 3 4) (sourceB264 + difference 4 3) sourceC264) = raw6242 := by
      apply Matrix.ext; unfold tripleCharges sourceA264 sourceB264 sourceC264 difference raw6242; decide +kernel
    rw [ha]
    exact (canonical6242 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA264 + difference 4 4) (sourceB264 + difference 4 4) sourceC264) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2724) := by
    have ha : (tripleCharges (sourceA264 + difference 4 4) (sourceB264 + difference 4 4) sourceC264) = raw6216 := by
      apply Matrix.ext; unfold tripleCharges sourceA264 sourceB264 sourceC264 difference raw6216; decide +kernel
    rw [ha]
    exact (canonical6216 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA264 + difference 5 4) (sourceB264 + difference 4 5) sourceC264) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2716) := by
    have ha : (tripleCharges (sourceA264 + difference 5 4) (sourceB264 + difference 4 5) sourceC264) = raw6247 := by
      apply Matrix.ext; unfold tripleCharges sourceA264 sourceB264 sourceC264 difference raw6247; decide +kernel
    rw [ha]
    exact (canonical6247 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA264 + sourceB264) sourceC264) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA264 + sourceB264) sourceC264) = raw6222 := by
      apply Matrix.ext; unfold doubleCharges sourceA264 sourceB264 sourceC264 raw6222; decide +kernel
    rw [ha]
    exact (canonical6222 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA264 sourceB264 sourceC264
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm264, Integer.Sparse.eval]
  linarith only [hs]

def sourceA265 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB265 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC265 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceForm265 : Integer.Sparse Master := [(Sum.inr 1218, 1), (Sum.inr 2486, 1), (Sum.inr 2544, 1), (Sum.inr 2619, 1), (Sum.inr 2716, 1), (Sum.inr 2724, 1), (Sum.inr 4092, -1)]

theorem sourceEq265 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm265 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA265 + difference 5 0) (sourceB265 + difference 0 5) sourceC265) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1218) := by
    have ha : (tripleCharges (sourceA265 + difference 5 0) (sourceB265 + difference 0 5) sourceC265) = raw6227 := by
      apply Matrix.ext; unfold tripleCharges sourceA265 sourceB265 sourceC265 difference raw6227; decide +kernel
    rw [ha]
    exact (canonical6227 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA265 + difference 5 1) (sourceB265 + difference 1 5) sourceC265) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2486) := by
    have ha : (tripleCharges (sourceA265 + difference 5 1) (sourceB265 + difference 1 5) sourceC265) = raw6235 := by
      apply Matrix.ext; unfold tripleCharges sourceA265 sourceB265 sourceC265 difference raw6235; decide +kernel
    rw [ha]
    exact (canonical6235 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA265 + difference 5 2) (sourceB265 + difference 2 5) sourceC265) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2544) := by
    have ha : (tripleCharges (sourceA265 + difference 5 2) (sourceB265 + difference 2 5) sourceC265) = raw6241 := by
      apply Matrix.ext; unfold tripleCharges sourceA265 sourceB265 sourceC265 difference raw6241; decide +kernel
    rw [ha]
    exact (canonical6241 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA265 + difference 5 3) (sourceB265 + difference 3 5) sourceC265) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2619) := by
    have ha : (tripleCharges (sourceA265 + difference 5 3) (sourceB265 + difference 3 5) sourceC265) = raw6245 := by
      apply Matrix.ext; unfold tripleCharges sourceA265 sourceB265 sourceC265 difference raw6245; decide +kernel
    rw [ha]
    exact (canonical6245 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA265 + difference 5 4) (sourceB265 + difference 4 5) sourceC265) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2716) := by
    have ha : (tripleCharges (sourceA265 + difference 5 4) (sourceB265 + difference 4 5) sourceC265) = raw6247 := by
      apply Matrix.ext; unfold tripleCharges sourceA265 sourceB265 sourceC265 difference raw6247; decide +kernel
    rw [ha]
    exact (canonical6247 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA265 + difference 5 5) (sourceB265 + difference 5 5) sourceC265) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2724) := by
    have ha : (tripleCharges (sourceA265 + difference 5 5) (sourceB265 + difference 5 5) sourceC265) = raw6216 := by
      apply Matrix.ext; unfold tripleCharges sourceA265 sourceB265 sourceC265 difference raw6216; decide +kernel
    rw [ha]
    exact (canonical6216 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA265 + sourceB265) sourceC265) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA265 + sourceB265) sourceC265) = raw6222 := by
      apply Matrix.ext; unfold doubleCharges sourceA265 sourceB265 sourceC265 raw6222; decide +kernel
    rw [ha]
    exact (canonical6222 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA265 sourceB265 sourceC265
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm265, Integer.Sparse.eval]
  linarith only [hs]

def sourceA266 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB266 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC266 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceForm266 : Integer.Sparse Master := [(Sum.inr 4400, 1), (Sum.inr 4402, 1), (Sum.inr 4403, 1), (Sum.inr 4427, 1), (Sum.inr 4459, 1), (Sum.inr 4999, 1), (Sum.inr 5001, 1), (Sum.inr 5002, 1), (Sum.inr 5020, 1), (Sum.inr 5048, 1), (Sum.inr 5049, 1), (Sum.inr 5061, 1), (Sum.inr 5074, 1), (Sum.inr 5138, 1), (Sum.inr 5139, 1), (Sum.inr 5140, 1), (Sum.inr 5161, 1), (Sum.inr 5170, 1), (Sum.inr 5251, 1), (Sum.inr 5252, 1), (Sum.inr 5255, 1), (Sum.inr 5260, 1), (Sum.inr 5269, 1), (Sum.inr 5284, 1), (Sum.inr 5289, 1), (Sum.inr 5430, 1), (Sum.inr 5438, 1), (Sum.inr 5439, 1), (Sum.inr 5446, 1), (Sum.inr 5484, 1)]

theorem sourceEq266 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm266 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA266 + difference 0 1) (sourceB266 + difference 1 0) sourceC266) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5446) := by
    have ha : (tripleCharges (sourceA266 + difference 0 1) (sourceB266 + difference 1 0) sourceC266) = raw6248 := by
      apply Matrix.ext; unfold tripleCharges sourceA266 sourceB266 sourceC266 difference raw6248; decide +kernel
    rw [ha]
    exact (canonical6248 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA266 + difference 0 2) (sourceB266 + difference 2 0) sourceC266) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA266 + difference 0 2) (sourceB266 + difference 2 0) sourceC266) = raw6249 := by
      apply Matrix.ext; unfold tripleCharges sourceA266 sourceB266 sourceC266 difference raw6249; decide +kernel
    rw [ha]
    exact (canonical6249 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA266 + difference 0 3) (sourceB266 + difference 3 0) sourceC266) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA266 + difference 0 3) (sourceB266 + difference 3 0) sourceC266) = raw6250 := by
      apply Matrix.ext; unfold tripleCharges sourceA266 sourceB266 sourceC266 difference raw6250; decide +kernel
    rw [ha]
    exact (canonical6250 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA266 + difference 0 4) (sourceB266 + difference 4 0) sourceC266) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA266 + difference 0 4) (sourceB266 + difference 4 0) sourceC266) = raw6251 := by
      apply Matrix.ext; unfold tripleCharges sourceA266 sourceB266 sourceC266 difference raw6251; decide +kernel
    rw [ha]
    exact (canonical6251 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA266 + difference 0 5) (sourceB266 + difference 5 0) sourceC266) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5484) := by
    have ha : (tripleCharges (sourceA266 + difference 0 5) (sourceB266 + difference 5 0) sourceC266) = raw6252 := by
      apply Matrix.ext; unfold tripleCharges sourceA266 sourceB266 sourceC266 difference raw6252; decide +kernel
    rw [ha]
    exact (canonical6252 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA266 + difference 1 0) (sourceB266 + difference 0 1) sourceC266) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4459) := by
    have ha : (tripleCharges (sourceA266 + difference 1 0) (sourceB266 + difference 0 1) sourceC266) = raw6253 := by
      apply Matrix.ext; unfold tripleCharges sourceA266 sourceB266 sourceC266 difference raw6253; decide +kernel
    rw [ha]
    exact (canonical6253 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA266 + difference 1 2) (sourceB266 + difference 2 1) sourceC266) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5074) := by
    have ha : (tripleCharges (sourceA266 + difference 1 2) (sourceB266 + difference 2 1) sourceC266) = raw6254 := by
      apply Matrix.ext; unfold tripleCharges sourceA266 sourceB266 sourceC266 difference raw6254; decide +kernel
    rw [ha]
    exact (canonical6254 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA266 + difference 1 3) (sourceB266 + difference 3 1) sourceC266) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5170) := by
    have ha : (tripleCharges (sourceA266 + difference 1 3) (sourceB266 + difference 3 1) sourceC266) = raw6255 := by
      apply Matrix.ext; unfold tripleCharges sourceA266 sourceB266 sourceC266 difference raw6255; decide +kernel
    rw [ha]
    exact (canonical6255 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA266 + difference 1 4) (sourceB266 + difference 4 1) sourceC266) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA266 + difference 1 4) (sourceB266 + difference 4 1) sourceC266) = raw6256 := by
      apply Matrix.ext; unfold tripleCharges sourceA266 sourceB266 sourceC266 difference raw6256; decide +kernel
    rw [ha]
    exact (canonical6256 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA266 + difference 1 5) (sourceB266 + difference 5 1) sourceC266) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA266 + difference 1 5) (sourceB266 + difference 5 1) sourceC266) = raw6257 := by
      apply Matrix.ext; unfold tripleCharges sourceA266 sourceB266 sourceC266 difference raw6257; decide +kernel
    rw [ha]
    exact (canonical6257 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA266 + difference 2 0) (sourceB266 + difference 0 2) sourceC266) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4400) := by
    have ha : (tripleCharges (sourceA266 + difference 2 0) (sourceB266 + difference 0 2) sourceC266) = raw6258 := by
      apply Matrix.ext; unfold tripleCharges sourceA266 sourceB266 sourceC266 difference raw6258; decide +kernel
    rw [ha]
    exact (canonical6258 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA266 + difference 2 1) (sourceB266 + difference 1 2) sourceC266) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4999) := by
    have ha : (tripleCharges (sourceA266 + difference 2 1) (sourceB266 + difference 1 2) sourceC266) = raw6259 := by
      apply Matrix.ext; unfold tripleCharges sourceA266 sourceB266 sourceC266 difference raw6259; decide +kernel
    rw [ha]
    exact (canonical6259 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA266 + difference 2 3) (sourceB266 + difference 3 2) sourceC266) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5138) := by
    have ha : (tripleCharges (sourceA266 + difference 2 3) (sourceB266 + difference 3 2) sourceC266) = raw6260 := by
      apply Matrix.ext; unfold tripleCharges sourceA266 sourceB266 sourceC266 difference raw6260; decide +kernel
    rw [ha]
    exact (canonical6260 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA266 + difference 2 4) (sourceB266 + difference 4 2) sourceC266) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5251) := by
    have ha : (tripleCharges (sourceA266 + difference 2 4) (sourceB266 + difference 4 2) sourceC266) = raw6261 := by
      apply Matrix.ext; unfold tripleCharges sourceA266 sourceB266 sourceC266 difference raw6261; decide +kernel
    rw [ha]
    exact (canonical6261 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA266 + difference 2 5) (sourceB266 + difference 5 2) sourceC266) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5255) := by
    have ha : (tripleCharges (sourceA266 + difference 2 5) (sourceB266 + difference 5 2) sourceC266) = raw6262 := by
      apply Matrix.ext; unfold tripleCharges sourceA266 sourceB266 sourceC266 difference raw6262; decide +kernel
    rw [ha]
    exact (canonical6262 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA266 + difference 3 0) (sourceB266 + difference 0 3) sourceC266) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4427) := by
    have ha : (tripleCharges (sourceA266 + difference 3 0) (sourceB266 + difference 0 3) sourceC266) = raw6263 := by
      apply Matrix.ext; unfold tripleCharges sourceA266 sourceB266 sourceC266 difference raw6263; decide +kernel
    rw [ha]
    exact (canonical6263 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA266 + difference 3 1) (sourceB266 + difference 1 3) sourceC266) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5020) := by
    have ha : (tripleCharges (sourceA266 + difference 3 1) (sourceB266 + difference 1 3) sourceC266) = raw6264 := by
      apply Matrix.ext; unfold tripleCharges sourceA266 sourceB266 sourceC266 difference raw6264; decide +kernel
    rw [ha]
    exact (canonical6264 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA266 + difference 3 2) (sourceB266 + difference 2 3) sourceC266) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5061) := by
    have ha : (tripleCharges (sourceA266 + difference 3 2) (sourceB266 + difference 2 3) sourceC266) = raw6265 := by
      apply Matrix.ext; unfold tripleCharges sourceA266 sourceB266 sourceC266 difference raw6265; decide +kernel
    rw [ha]
    exact (canonical6265 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA266 + difference 3 4) (sourceB266 + difference 4 3) sourceC266) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5260) := by
    have ha : (tripleCharges (sourceA266 + difference 3 4) (sourceB266 + difference 4 3) sourceC266) = raw6266 := by
      apply Matrix.ext; unfold tripleCharges sourceA266 sourceB266 sourceC266 difference raw6266; decide +kernel
    rw [ha]
    exact (canonical6266 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA266 + difference 3 5) (sourceB266 + difference 5 3) sourceC266) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5269) := by
    have ha : (tripleCharges (sourceA266 + difference 3 5) (sourceB266 + difference 5 3) sourceC266) = raw6267 := by
      apply Matrix.ext; unfold tripleCharges sourceA266 sourceB266 sourceC266 difference raw6267; decide +kernel
    rw [ha]
    exact (canonical6267 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA266 + difference 4 0) (sourceB266 + difference 0 4) sourceC266) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4403) := by
    have ha : (tripleCharges (sourceA266 + difference 4 0) (sourceB266 + difference 0 4) sourceC266) = raw6268 := by
      apply Matrix.ext; unfold tripleCharges sourceA266 sourceB266 sourceC266 difference raw6268; decide +kernel
    rw [ha]
    exact (canonical6268 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA266 + difference 4 1) (sourceB266 + difference 1 4) sourceC266) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5002) := by
    have ha : (tripleCharges (sourceA266 + difference 4 1) (sourceB266 + difference 1 4) sourceC266) = raw6269 := by
      apply Matrix.ext; unfold tripleCharges sourceA266 sourceB266 sourceC266 difference raw6269; decide +kernel
    rw [ha]
    exact (canonical6269 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA266 + difference 4 2) (sourceB266 + difference 2 4) sourceC266) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5049) := by
    have ha : (tripleCharges (sourceA266 + difference 4 2) (sourceB266 + difference 2 4) sourceC266) = raw6270 := by
      apply Matrix.ext; unfold tripleCharges sourceA266 sourceB266 sourceC266 difference raw6270; decide +kernel
    rw [ha]
    exact (canonical6270 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA266 + difference 4 3) (sourceB266 + difference 3 4) sourceC266) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5140) := by
    have ha : (tripleCharges (sourceA266 + difference 4 3) (sourceB266 + difference 3 4) sourceC266) = raw6271 := by
      apply Matrix.ext; unfold tripleCharges sourceA266 sourceB266 sourceC266 difference raw6271; decide +kernel
    rw [ha]
    exact (canonical6271 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA266 + difference 4 5) (sourceB266 + difference 5 4) sourceC266) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5161) := by
    have ha : (tripleCharges (sourceA266 + difference 4 5) (sourceB266 + difference 5 4) sourceC266) = raw6272 := by
      apply Matrix.ext; unfold tripleCharges sourceA266 sourceB266 sourceC266 difference raw6272; decide +kernel
    rw [ha]
    exact (canonical6272 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA266 + difference 5 0) (sourceB266 + difference 0 5) sourceC266) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4402) := by
    have ha : (tripleCharges (sourceA266 + difference 5 0) (sourceB266 + difference 0 5) sourceC266) = raw6273 := by
      apply Matrix.ext; unfold tripleCharges sourceA266 sourceB266 sourceC266 difference raw6273; decide +kernel
    rw [ha]
    exact (canonical6273 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA266 + difference 5 1) (sourceB266 + difference 1 5) sourceC266) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5001) := by
    have ha : (tripleCharges (sourceA266 + difference 5 1) (sourceB266 + difference 1 5) sourceC266) = raw6274 := by
      apply Matrix.ext; unfold tripleCharges sourceA266 sourceB266 sourceC266 difference raw6274; decide +kernel
    rw [ha]
    exact (canonical6274 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA266 + difference 5 2) (sourceB266 + difference 2 5) sourceC266) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5048) := by
    have ha : (tripleCharges (sourceA266 + difference 5 2) (sourceB266 + difference 2 5) sourceC266) = raw6275 := by
      apply Matrix.ext; unfold tripleCharges sourceA266 sourceB266 sourceC266 difference raw6275; decide +kernel
    rw [ha]
    exact (canonical6275 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA266 + difference 5 3) (sourceB266 + difference 3 5) sourceC266) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5139) := by
    have ha : (tripleCharges (sourceA266 + difference 5 3) (sourceB266 + difference 3 5) sourceC266) = raw6276 := by
      apply Matrix.ext; unfold tripleCharges sourceA266 sourceB266 sourceC266 difference raw6276; decide +kernel
    rw [ha]
    exact (canonical6276 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA266 + difference 5 4) (sourceB266 + difference 4 5) sourceC266) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5252) := by
    have ha : (tripleCharges (sourceA266 + difference 5 4) (sourceB266 + difference 4 5) sourceC266) = raw6277 := by
      apply Matrix.ext; unfold tripleCharges sourceA266 sourceB266 sourceC266 difference raw6277; decide +kernel
    rw [ha]
    exact (canonical6277 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA266 sourceB266 sourceC266
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm266, Integer.Sparse.eval]
  linarith only [hs]

def sourceA267 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB267 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC267 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceForm267 : Integer.Sparse Master := [(Sum.inr 981, 1), (Sum.inr 983, 1), (Sum.inr 984, 1), (Sum.inr 1008, 1), (Sum.inr 1042, 1), (Sum.inr 2384, 1), (Sum.inr 2386, 1), (Sum.inr 2387, 1), (Sum.inr 2406, 1), (Sum.inr 2450, 1), (Sum.inr 2451, 1), (Sum.inr 2464, 1), (Sum.inr 2481, 1), (Sum.inr 2557, 1), (Sum.inr 2558, 1), (Sum.inr 2560, 1), (Sum.inr 2596, 1), (Sum.inr 2710, 1), (Sum.inr 2712, 1), (Sum.inr 2718, 1), (Sum.inr 2719, 1), (Sum.inr 2724, 1), (Sum.inr 2736, 1), (Sum.inr 2753, 1), (Sum.inr 2763, 1), (Sum.inr 3959, 1), (Sum.inr 3972, 1), (Sum.inr 3983, 1), (Sum.inr 3993, 1), (Sum.inr 4012, 1)]

theorem sourceEq267 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm267 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA267 + difference 0 1) (sourceB267 + difference 1 0) sourceC267) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3959) := by
    have ha : (tripleCharges (sourceA267 + difference 0 1) (sourceB267 + difference 1 0) sourceC267) = raw6278 := by
      apply Matrix.ext; unfold tripleCharges sourceA267 sourceB267 sourceC267 difference raw6278; decide +kernel
    rw [ha]
    exact (canonical6278 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA267 + difference 0 2) (sourceB267 + difference 2 0) sourceC267) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3972) := by
    have ha : (tripleCharges (sourceA267 + difference 0 2) (sourceB267 + difference 2 0) sourceC267) = raw6279 := by
      apply Matrix.ext; unfold tripleCharges sourceA267 sourceB267 sourceC267 difference raw6279; decide +kernel
    rw [ha]
    exact (canonical6279 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA267 + difference 0 3) (sourceB267 + difference 3 0) sourceC267) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3993) := by
    have ha : (tripleCharges (sourceA267 + difference 0 3) (sourceB267 + difference 3 0) sourceC267) = raw6280 := by
      apply Matrix.ext; unfold tripleCharges sourceA267 sourceB267 sourceC267 difference raw6280; decide +kernel
    rw [ha]
    exact (canonical6280 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA267 + difference 0 4) (sourceB267 + difference 4 0) sourceC267) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4012) := by
    have ha : (tripleCharges (sourceA267 + difference 0 4) (sourceB267 + difference 4 0) sourceC267) = raw6281 := by
      apply Matrix.ext; unfold tripleCharges sourceA267 sourceB267 sourceC267 difference raw6281; decide +kernel
    rw [ha]
    exact (canonical6281 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA267 + difference 0 5) (sourceB267 + difference 5 0) sourceC267) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3983) := by
    have ha : (tripleCharges (sourceA267 + difference 0 5) (sourceB267 + difference 5 0) sourceC267) = raw6282 := by
      apply Matrix.ext; unfold tripleCharges sourceA267 sourceB267 sourceC267 difference raw6282; decide +kernel
    rw [ha]
    exact (canonical6282 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA267 + difference 1 0) (sourceB267 + difference 0 1) sourceC267) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1042) := by
    have ha : (tripleCharges (sourceA267 + difference 1 0) (sourceB267 + difference 0 1) sourceC267) = raw6283 := by
      apply Matrix.ext; unfold tripleCharges sourceA267 sourceB267 sourceC267 difference raw6283; decide +kernel
    rw [ha]
    exact (canonical6283 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA267 + difference 1 2) (sourceB267 + difference 2 1) sourceC267) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2481) := by
    have ha : (tripleCharges (sourceA267 + difference 1 2) (sourceB267 + difference 2 1) sourceC267) = raw6284 := by
      apply Matrix.ext; unfold tripleCharges sourceA267 sourceB267 sourceC267 difference raw6284; decide +kernel
    rw [ha]
    exact (canonical6284 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA267 + difference 1 3) (sourceB267 + difference 3 1) sourceC267) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2596) := by
    have ha : (tripleCharges (sourceA267 + difference 1 3) (sourceB267 + difference 3 1) sourceC267) = raw6285 := by
      apply Matrix.ext; unfold tripleCharges sourceA267 sourceB267 sourceC267 difference raw6285; decide +kernel
    rw [ha]
    exact (canonical6285 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA267 + difference 1 4) (sourceB267 + difference 4 1) sourceC267) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2753) := by
    have ha : (tripleCharges (sourceA267 + difference 1 4) (sourceB267 + difference 4 1) sourceC267) = raw6286 := by
      apply Matrix.ext; unfold tripleCharges sourceA267 sourceB267 sourceC267 difference raw6286; decide +kernel
    rw [ha]
    exact (canonical6286 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA267 + difference 1 5) (sourceB267 + difference 5 1) sourceC267) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2763) := by
    have ha : (tripleCharges (sourceA267 + difference 1 5) (sourceB267 + difference 5 1) sourceC267) = raw6287 := by
      apply Matrix.ext; unfold tripleCharges sourceA267 sourceB267 sourceC267 difference raw6287; decide +kernel
    rw [ha]
    exact (canonical6287 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA267 + difference 2 0) (sourceB267 + difference 0 2) sourceC267) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 981) := by
    have ha : (tripleCharges (sourceA267 + difference 2 0) (sourceB267 + difference 0 2) sourceC267) = raw6288 := by
      apply Matrix.ext; unfold tripleCharges sourceA267 sourceB267 sourceC267 difference raw6288; decide +kernel
    rw [ha]
    exact (canonical6288 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA267 + difference 2 1) (sourceB267 + difference 1 2) sourceC267) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2384) := by
    have ha : (tripleCharges (sourceA267 + difference 2 1) (sourceB267 + difference 1 2) sourceC267) = raw6289 := by
      apply Matrix.ext; unfold tripleCharges sourceA267 sourceB267 sourceC267 difference raw6289; decide +kernel
    rw [ha]
    exact (canonical6289 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA267 + difference 2 3) (sourceB267 + difference 3 2) sourceC267) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2557) := by
    have ha : (tripleCharges (sourceA267 + difference 2 3) (sourceB267 + difference 3 2) sourceC267) = raw6290 := by
      apply Matrix.ext; unfold tripleCharges sourceA267 sourceB267 sourceC267 difference raw6290; decide +kernel
    rw [ha]
    exact (canonical6290 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA267 + difference 2 4) (sourceB267 + difference 4 2) sourceC267) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2710) := by
    have ha : (tripleCharges (sourceA267 + difference 2 4) (sourceB267 + difference 4 2) sourceC267) = raw6291 := by
      apply Matrix.ext; unfold tripleCharges sourceA267 sourceB267 sourceC267 difference raw6291; decide +kernel
    rw [ha]
    exact (canonical6291 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA267 + difference 2 5) (sourceB267 + difference 5 2) sourceC267) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2718) := by
    have ha : (tripleCharges (sourceA267 + difference 2 5) (sourceB267 + difference 5 2) sourceC267) = raw6292 := by
      apply Matrix.ext; unfold tripleCharges sourceA267 sourceB267 sourceC267 difference raw6292; decide +kernel
    rw [ha]
    exact (canonical6292 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA267 + difference 3 0) (sourceB267 + difference 0 3) sourceC267) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1008) := by
    have ha : (tripleCharges (sourceA267 + difference 3 0) (sourceB267 + difference 0 3) sourceC267) = raw6293 := by
      apply Matrix.ext; unfold tripleCharges sourceA267 sourceB267 sourceC267 difference raw6293; decide +kernel
    rw [ha]
    exact (canonical6293 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA267 + difference 3 1) (sourceB267 + difference 1 3) sourceC267) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2406) := by
    have ha : (tripleCharges (sourceA267 + difference 3 1) (sourceB267 + difference 1 3) sourceC267) = raw6294 := by
      apply Matrix.ext; unfold tripleCharges sourceA267 sourceB267 sourceC267 difference raw6294; decide +kernel
    rw [ha]
    exact (canonical6294 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA267 + difference 3 2) (sourceB267 + difference 2 3) sourceC267) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2464) := by
    have ha : (tripleCharges (sourceA267 + difference 3 2) (sourceB267 + difference 2 3) sourceC267) = raw6295 := by
      apply Matrix.ext; unfold tripleCharges sourceA267 sourceB267 sourceC267 difference raw6295; decide +kernel
    rw [ha]
    exact (canonical6295 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA267 + difference 3 4) (sourceB267 + difference 4 3) sourceC267) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2724) := by
    have ha : (tripleCharges (sourceA267 + difference 3 4) (sourceB267 + difference 4 3) sourceC267) = raw6296 := by
      apply Matrix.ext; unfold tripleCharges sourceA267 sourceB267 sourceC267 difference raw6296; decide +kernel
    rw [ha]
    exact (canonical6296 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA267 + difference 3 5) (sourceB267 + difference 5 3) sourceC267) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2736) := by
    have ha : (tripleCharges (sourceA267 + difference 3 5) (sourceB267 + difference 5 3) sourceC267) = raw6297 := by
      apply Matrix.ext; unfold tripleCharges sourceA267 sourceB267 sourceC267 difference raw6297; decide +kernel
    rw [ha]
    exact (canonical6297 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA267 + difference 4 0) (sourceB267 + difference 0 4) sourceC267) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 984) := by
    have ha : (tripleCharges (sourceA267 + difference 4 0) (sourceB267 + difference 0 4) sourceC267) = raw6298 := by
      apply Matrix.ext; unfold tripleCharges sourceA267 sourceB267 sourceC267 difference raw6298; decide +kernel
    rw [ha]
    exact (canonical6298 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA267 + difference 4 1) (sourceB267 + difference 1 4) sourceC267) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2387) := by
    have ha : (tripleCharges (sourceA267 + difference 4 1) (sourceB267 + difference 1 4) sourceC267) = raw6299 := by
      apply Matrix.ext; unfold tripleCharges sourceA267 sourceB267 sourceC267 difference raw6299; decide +kernel
    rw [ha]
    exact (canonical6299 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA267 + difference 4 2) (sourceB267 + difference 2 4) sourceC267) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2451) := by
    have ha : (tripleCharges (sourceA267 + difference 4 2) (sourceB267 + difference 2 4) sourceC267) = raw6300 := by
      apply Matrix.ext; unfold tripleCharges sourceA267 sourceB267 sourceC267 difference raw6300; decide +kernel
    rw [ha]
    exact (canonical6300 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA267 + difference 4 3) (sourceB267 + difference 3 4) sourceC267) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2560) := by
    have ha : (tripleCharges (sourceA267 + difference 4 3) (sourceB267 + difference 3 4) sourceC267) = raw6301 := by
      apply Matrix.ext; unfold tripleCharges sourceA267 sourceB267 sourceC267 difference raw6301; decide +kernel
    rw [ha]
    exact (canonical6301 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA267 + difference 4 5) (sourceB267 + difference 5 4) sourceC267) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2719) := by
    have ha : (tripleCharges (sourceA267 + difference 4 5) (sourceB267 + difference 5 4) sourceC267) = raw6302 := by
      apply Matrix.ext; unfold tripleCharges sourceA267 sourceB267 sourceC267 difference raw6302; decide +kernel
    rw [ha]
    exact (canonical6302 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA267 + difference 5 0) (sourceB267 + difference 0 5) sourceC267) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 983) := by
    have ha : (tripleCharges (sourceA267 + difference 5 0) (sourceB267 + difference 0 5) sourceC267) = raw6303 := by
      apply Matrix.ext; unfold tripleCharges sourceA267 sourceB267 sourceC267 difference raw6303; decide +kernel
    rw [ha]
    exact (canonical6303 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA267 + difference 5 1) (sourceB267 + difference 1 5) sourceC267) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2386) := by
    have ha : (tripleCharges (sourceA267 + difference 5 1) (sourceB267 + difference 1 5) sourceC267) = raw6304 := by
      apply Matrix.ext; unfold tripleCharges sourceA267 sourceB267 sourceC267 difference raw6304; decide +kernel
    rw [ha]
    exact (canonical6304 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA267 + difference 5 2) (sourceB267 + difference 2 5) sourceC267) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2450) := by
    have ha : (tripleCharges (sourceA267 + difference 5 2) (sourceB267 + difference 2 5) sourceC267) = raw6305 := by
      apply Matrix.ext; unfold tripleCharges sourceA267 sourceB267 sourceC267 difference raw6305; decide +kernel
    rw [ha]
    exact (canonical6305 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA267 + difference 5 3) (sourceB267 + difference 3 5) sourceC267) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2558) := by
    have ha : (tripleCharges (sourceA267 + difference 5 3) (sourceB267 + difference 3 5) sourceC267) = raw6306 := by
      apply Matrix.ext; unfold tripleCharges sourceA267 sourceB267 sourceC267 difference raw6306; decide +kernel
    rw [ha]
    exact (canonical6306 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA267 + difference 5 4) (sourceB267 + difference 4 5) sourceC267) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2712) := by
    have ha : (tripleCharges (sourceA267 + difference 5 4) (sourceB267 + difference 4 5) sourceC267) = raw6307 := by
      apply Matrix.ext; unfold tripleCharges sourceA267 sourceB267 sourceC267 difference raw6307; decide +kernel
    rw [ha]
    exact (canonical6307 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA267 sourceB267 sourceC267
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm267, Integer.Sparse.eval]
  linarith only [hs]

def sourceA268 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB268 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC268 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceForm268 : Integer.Sparse Master := [(Sum.inr 1607, 1), (Sum.inr 1608, 1), (Sum.inr 1612, 1), (Sum.inr 1619, 1), (Sum.inr 1714, 1), (Sum.inr 2534, 1), (Sum.inr 2538, 1), (Sum.inr 2588, 1), (Sum.inr 2670, 1), (Sum.inr 3346, 1), (Sum.inr 3349, 1), (Sum.inr 3355, 1), (Sum.inr 3431, 1), (Sum.inr 3434, 1), (Sum.inr 3463, 1), (Sum.inr 3503, 1), (Sum.inr 3507, 1), (Sum.inr 3517, 1), (Sum.inr 3523, 1), (Sum.inr 3539, 1), (Sum.inr 3540, 1), (Sum.inr 3543, 1), (Sum.inr 3572, 1), (Sum.inr 3606, 1), (Sum.inr 3625, 1), (Sum.inr 3848, 1), (Sum.inr 3857, 1), (Sum.inr 3858, 1), (Sum.inr 3884, 1), (Sum.inr 3997, 1)]

theorem sourceEq268 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm268 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA268 + difference 0 1) (sourceB268 + difference 1 0) sourceC268) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3884) := by
    have ha : (tripleCharges (sourceA268 + difference 0 1) (sourceB268 + difference 1 0) sourceC268) = raw6308 := by
      apply Matrix.ext; unfold tripleCharges sourceA268 sourceB268 sourceC268 difference raw6308; decide +kernel
    rw [ha]
    exact (canonical6308 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA268 + difference 0 2) (sourceB268 + difference 2 0) sourceC268) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3848) := by
    have ha : (tripleCharges (sourceA268 + difference 0 2) (sourceB268 + difference 2 0) sourceC268) = raw6309 := by
      apply Matrix.ext; unfold tripleCharges sourceA268 sourceB268 sourceC268 difference raw6309; decide +kernel
    rw [ha]
    exact (canonical6309 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA268 + difference 0 3) (sourceB268 + difference 3 0) sourceC268) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3857) := by
    have ha : (tripleCharges (sourceA268 + difference 0 3) (sourceB268 + difference 3 0) sourceC268) = raw6310 := by
      apply Matrix.ext; unfold tripleCharges sourceA268 sourceB268 sourceC268 difference raw6310; decide +kernel
    rw [ha]
    exact (canonical6310 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA268 + difference 0 4) (sourceB268 + difference 4 0) sourceC268) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3858) := by
    have ha : (tripleCharges (sourceA268 + difference 0 4) (sourceB268 + difference 4 0) sourceC268) = raw6311 := by
      apply Matrix.ext; unfold tripleCharges sourceA268 sourceB268 sourceC268 difference raw6311; decide +kernel
    rw [ha]
    exact (canonical6311 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA268 + difference 0 5) (sourceB268 + difference 5 0) sourceC268) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3997) := by
    have ha : (tripleCharges (sourceA268 + difference 0 5) (sourceB268 + difference 5 0) sourceC268) = raw6312 := by
      apply Matrix.ext; unfold tripleCharges sourceA268 sourceB268 sourceC268 difference raw6312; decide +kernel
    rw [ha]
    exact (canonical6312 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA268 + difference 1 0) (sourceB268 + difference 0 1) sourceC268) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1714) := by
    have ha : (tripleCharges (sourceA268 + difference 1 0) (sourceB268 + difference 0 1) sourceC268) = raw6313 := by
      apply Matrix.ext; unfold tripleCharges sourceA268 sourceB268 sourceC268 difference raw6313; decide +kernel
    rw [ha]
    exact (canonical6313 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA268 + difference 1 2) (sourceB268 + difference 2 1) sourceC268) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3463) := by
    have ha : (tripleCharges (sourceA268 + difference 1 2) (sourceB268 + difference 2 1) sourceC268) = raw6314 := by
      apply Matrix.ext; unfold tripleCharges sourceA268 sourceB268 sourceC268 difference raw6314; decide +kernel
    rw [ha]
    exact (canonical6314 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA268 + difference 1 3) (sourceB268 + difference 3 1) sourceC268) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3606) := by
    have ha : (tripleCharges (sourceA268 + difference 1 3) (sourceB268 + difference 3 1) sourceC268) = raw6315 := by
      apply Matrix.ext; unfold tripleCharges sourceA268 sourceB268 sourceC268 difference raw6315; decide +kernel
    rw [ha]
    exact (canonical6315 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA268 + difference 1 4) (sourceB268 + difference 4 1) sourceC268) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3625) := by
    have ha : (tripleCharges (sourceA268 + difference 1 4) (sourceB268 + difference 4 1) sourceC268) = raw6316 := by
      apply Matrix.ext; unfold tripleCharges sourceA268 sourceB268 sourceC268 difference raw6316; decide +kernel
    rw [ha]
    exact (canonical6316 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA268 + difference 1 5) (sourceB268 + difference 5 1) sourceC268) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA268 + difference 1 5) (sourceB268 + difference 5 1) sourceC268) = raw6317 := by
      apply Matrix.ext; unfold tripleCharges sourceA268 sourceB268 sourceC268 difference raw6317; decide +kernel
    rw [ha]
    exact (canonical6317 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA268 + difference 2 0) (sourceB268 + difference 0 2) sourceC268) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1607) := by
    have ha : (tripleCharges (sourceA268 + difference 2 0) (sourceB268 + difference 0 2) sourceC268) = raw6318 := by
      apply Matrix.ext; unfold tripleCharges sourceA268 sourceB268 sourceC268 difference raw6318; decide +kernel
    rw [ha]
    exact (canonical6318 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA268 + difference 2 1) (sourceB268 + difference 1 2) sourceC268) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3346) := by
    have ha : (tripleCharges (sourceA268 + difference 2 1) (sourceB268 + difference 1 2) sourceC268) = raw6319 := by
      apply Matrix.ext; unfold tripleCharges sourceA268 sourceB268 sourceC268 difference raw6319; decide +kernel
    rw [ha]
    exact (canonical6319 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA268 + difference 2 3) (sourceB268 + difference 3 2) sourceC268) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3517) := by
    have ha : (tripleCharges (sourceA268 + difference 2 3) (sourceB268 + difference 3 2) sourceC268) = raw6320 := by
      apply Matrix.ext; unfold tripleCharges sourceA268 sourceB268 sourceC268 difference raw6320; decide +kernel
    rw [ha]
    exact (canonical6320 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA268 + difference 2 4) (sourceB268 + difference 4 2) sourceC268) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3539) := by
    have ha : (tripleCharges (sourceA268 + difference 2 4) (sourceB268 + difference 4 2) sourceC268) = raw6321 := by
      apply Matrix.ext; unfold tripleCharges sourceA268 sourceB268 sourceC268 difference raw6321; decide +kernel
    rw [ha]
    exact (canonical6321 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA268 + difference 2 5) (sourceB268 + difference 5 2) sourceC268) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3503) := by
    have ha : (tripleCharges (sourceA268 + difference 2 5) (sourceB268 + difference 5 2) sourceC268) = raw6322 := by
      apply Matrix.ext; unfold tripleCharges sourceA268 sourceB268 sourceC268 difference raw6322; decide +kernel
    rw [ha]
    exact (canonical6322 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA268 + difference 3 0) (sourceB268 + difference 0 3) sourceC268) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1612) := by
    have ha : (tripleCharges (sourceA268 + difference 3 0) (sourceB268 + difference 0 3) sourceC268) = raw6323 := by
      apply Matrix.ext; unfold tripleCharges sourceA268 sourceB268 sourceC268 difference raw6323; decide +kernel
    rw [ha]
    exact (canonical6323 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA268 + difference 3 1) (sourceB268 + difference 1 3) sourceC268) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3349) := by
    have ha : (tripleCharges (sourceA268 + difference 3 1) (sourceB268 + difference 1 3) sourceC268) = raw6324 := by
      apply Matrix.ext; unfold tripleCharges sourceA268 sourceB268 sourceC268 difference raw6324; decide +kernel
    rw [ha]
    exact (canonical6324 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA268 + difference 3 2) (sourceB268 + difference 2 3) sourceC268) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3431) := by
    have ha : (tripleCharges (sourceA268 + difference 3 2) (sourceB268 + difference 2 3) sourceC268) = raw6325 := by
      apply Matrix.ext; unfold tripleCharges sourceA268 sourceB268 sourceC268 difference raw6325; decide +kernel
    rw [ha]
    exact (canonical6325 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA268 + difference 3 4) (sourceB268 + difference 4 3) sourceC268) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3540) := by
    have ha : (tripleCharges (sourceA268 + difference 3 4) (sourceB268 + difference 4 3) sourceC268) = raw6326 := by
      apply Matrix.ext; unfold tripleCharges sourceA268 sourceB268 sourceC268 difference raw6326; decide +kernel
    rw [ha]
    exact (canonical6326 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA268 + difference 3 5) (sourceB268 + difference 5 3) sourceC268) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3507) := by
    have ha : (tripleCharges (sourceA268 + difference 3 5) (sourceB268 + difference 5 3) sourceC268) = raw6327 := by
      apply Matrix.ext; unfold tripleCharges sourceA268 sourceB268 sourceC268 difference raw6327; decide +kernel
    rw [ha]
    exact (canonical6327 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA268 + difference 4 0) (sourceB268 + difference 0 4) sourceC268) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1608) := by
    have ha : (tripleCharges (sourceA268 + difference 4 0) (sourceB268 + difference 0 4) sourceC268) = raw6328 := by
      apply Matrix.ext; unfold tripleCharges sourceA268 sourceB268 sourceC268 difference raw6328; decide +kernel
    rw [ha]
    exact (canonical6328 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA268 + difference 4 1) (sourceB268 + difference 1 4) sourceC268) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2538) := by
    have ha : (tripleCharges (sourceA268 + difference 4 1) (sourceB268 + difference 1 4) sourceC268) = raw6329 := by
      apply Matrix.ext; unfold tripleCharges sourceA268 sourceB268 sourceC268 difference raw6329; decide +kernel
    rw [ha]
    exact (canonical6329 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA268 + difference 4 2) (sourceB268 + difference 2 4) sourceC268) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2534) := by
    have ha : (tripleCharges (sourceA268 + difference 4 2) (sourceB268 + difference 2 4) sourceC268) = raw6330 := by
      apply Matrix.ext; unfold tripleCharges sourceA268 sourceB268 sourceC268 difference raw6330; decide +kernel
    rw [ha]
    exact (canonical6330 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA268 + difference 4 3) (sourceB268 + difference 3 4) sourceC268) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2670) := by
    have ha : (tripleCharges (sourceA268 + difference 4 3) (sourceB268 + difference 3 4) sourceC268) = raw6331 := by
      apply Matrix.ext; unfold tripleCharges sourceA268 sourceB268 sourceC268 difference raw6331; decide +kernel
    rw [ha]
    exact (canonical6331 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA268 + difference 4 5) (sourceB268 + difference 5 4) sourceC268) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2588) := by
    have ha : (tripleCharges (sourceA268 + difference 4 5) (sourceB268 + difference 5 4) sourceC268) = raw6332 := by
      apply Matrix.ext; unfold tripleCharges sourceA268 sourceB268 sourceC268 difference raw6332; decide +kernel
    rw [ha]
    exact (canonical6332 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA268 + difference 5 0) (sourceB268 + difference 0 5) sourceC268) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1619) := by
    have ha : (tripleCharges (sourceA268 + difference 5 0) (sourceB268 + difference 0 5) sourceC268) = raw6333 := by
      apply Matrix.ext; unfold tripleCharges sourceA268 sourceB268 sourceC268 difference raw6333; decide +kernel
    rw [ha]
    exact (canonical6333 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA268 + difference 5 1) (sourceB268 + difference 1 5) sourceC268) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3355) := by
    have ha : (tripleCharges (sourceA268 + difference 5 1) (sourceB268 + difference 1 5) sourceC268) = raw6334 := by
      apply Matrix.ext; unfold tripleCharges sourceA268 sourceB268 sourceC268 difference raw6334; decide +kernel
    rw [ha]
    exact (canonical6334 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA268 + difference 5 2) (sourceB268 + difference 2 5) sourceC268) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3434) := by
    have ha : (tripleCharges (sourceA268 + difference 5 2) (sourceB268 + difference 2 5) sourceC268) = raw6335 := by
      apply Matrix.ext; unfold tripleCharges sourceA268 sourceB268 sourceC268 difference raw6335; decide +kernel
    rw [ha]
    exact (canonical6335 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA268 + difference 5 3) (sourceB268 + difference 3 5) sourceC268) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3523) := by
    have ha : (tripleCharges (sourceA268 + difference 5 3) (sourceB268 + difference 3 5) sourceC268) = raw6336 := by
      apply Matrix.ext; unfold tripleCharges sourceA268 sourceB268 sourceC268 difference raw6336; decide +kernel
    rw [ha]
    exact (canonical6336 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA268 + difference 5 4) (sourceB268 + difference 4 5) sourceC268) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3543) := by
    have ha : (tripleCharges (sourceA268 + difference 5 4) (sourceB268 + difference 4 5) sourceC268) = raw6337 := by
      apply Matrix.ext; unfold tripleCharges sourceA268 sourceB268 sourceC268 difference raw6337; decide +kernel
    rw [ha]
    exact (canonical6337 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA268 sourceB268 sourceC268
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm268, Integer.Sparse.eval]
  linarith only [hs]

def sourceA269 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB269 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC269 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceForm269 : Integer.Sparse Master := [(Sum.inr 3086, 1), (Sum.inr 3871, 1), (Sum.inr 3876, 1), (Sum.inr 3881, 1), (Sum.inr 3902, 1), (Sum.inr 3983, 1), (Sum.inr 4091, -1)]

theorem sourceEq269 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm269 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA269 + difference 0 0) (sourceB269 + difference 0 0) sourceC269) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3086) := by
    have ha : (tripleCharges (sourceA269 + difference 0 0) (sourceB269 + difference 0 0) sourceC269) = raw6338 := by
      apply Matrix.ext; unfold tripleCharges sourceA269 sourceB269 sourceC269 difference raw6338; decide +kernel
    rw [ha]
    exact (canonical6338 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA269 + difference 0 1) (sourceB269 + difference 1 0) sourceC269) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3881) := by
    have ha : (tripleCharges (sourceA269 + difference 0 1) (sourceB269 + difference 1 0) sourceC269) = raw6339 := by
      apply Matrix.ext; unfold tripleCharges sourceA269 sourceB269 sourceC269 difference raw6339; decide +kernel
    rw [ha]
    exact (canonical6339 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA269 + difference 0 2) (sourceB269 + difference 2 0) sourceC269) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3871) := by
    have ha : (tripleCharges (sourceA269 + difference 0 2) (sourceB269 + difference 2 0) sourceC269) = raw6340 := by
      apply Matrix.ext; unfold tripleCharges sourceA269 sourceB269 sourceC269 difference raw6340; decide +kernel
    rw [ha]
    exact (canonical6340 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA269 + difference 0 3) (sourceB269 + difference 3 0) sourceC269) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3876) := by
    have ha : (tripleCharges (sourceA269 + difference 0 3) (sourceB269 + difference 3 0) sourceC269) = raw6341 := by
      apply Matrix.ext; unfold tripleCharges sourceA269 sourceB269 sourceC269 difference raw6341; decide +kernel
    rw [ha]
    exact (canonical6341 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA269 + difference 0 4) (sourceB269 + difference 4 0) sourceC269) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3902) := by
    have ha : (tripleCharges (sourceA269 + difference 0 4) (sourceB269 + difference 4 0) sourceC269) = raw6342 := by
      apply Matrix.ext; unfold tripleCharges sourceA269 sourceB269 sourceC269 difference raw6342; decide +kernel
    rw [ha]
    exact (canonical6342 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA269 + difference 0 5) (sourceB269 + difference 5 0) sourceC269) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3983) := by
    have ha : (tripleCharges (sourceA269 + difference 0 5) (sourceB269 + difference 5 0) sourceC269) = raw6343 := by
      apply Matrix.ext; unfold tripleCharges sourceA269 sourceB269 sourceC269 difference raw6343; decide +kernel
    rw [ha]
    exact (canonical6343 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA269 + sourceB269) sourceC269) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA269 + sourceB269) sourceC269) = raw6344 := by
      apply Matrix.ext; unfold doubleCharges sourceA269 sourceB269 sourceC269 raw6344; decide +kernel
    rw [ha]
    exact (canonical6344 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA269 sourceB269 sourceC269
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm269, Integer.Sparse.eval]
  linarith only [hs]

def sourceA270 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB270 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC270 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceForm270 : Integer.Sparse Master := [(Sum.inr 1392, 1), (Sum.inr 1394, 1), (Sum.inr 1400, 1), (Sum.inr 1406, 1), (Sum.inr 1425, 1), (Sum.inr 3086, 1), (Sum.inr 4091, -1)]

theorem sourceEq270 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm270 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA270 + difference 0 0) (sourceB270 + difference 0 0) sourceC270) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3086) := by
    have ha : (tripleCharges (sourceA270 + difference 0 0) (sourceB270 + difference 0 0) sourceC270) = raw6338 := by
      apply Matrix.ext; unfold tripleCharges sourceA270 sourceB270 sourceC270 difference raw6338; decide +kernel
    rw [ha]
    exact (canonical6338 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA270 + difference 1 0) (sourceB270 + difference 0 1) sourceC270) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1406) := by
    have ha : (tripleCharges (sourceA270 + difference 1 0) (sourceB270 + difference 0 1) sourceC270) = raw6345 := by
      apply Matrix.ext; unfold tripleCharges sourceA270 sourceB270 sourceC270 difference raw6345; decide +kernel
    rw [ha]
    exact (canonical6345 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA270 + difference 2 0) (sourceB270 + difference 0 2) sourceC270) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1392) := by
    have ha : (tripleCharges (sourceA270 + difference 2 0) (sourceB270 + difference 0 2) sourceC270) = raw6346 := by
      apply Matrix.ext; unfold tripleCharges sourceA270 sourceB270 sourceC270 difference raw6346; decide +kernel
    rw [ha]
    exact (canonical6346 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA270 + difference 3 0) (sourceB270 + difference 0 3) sourceC270) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1425) := by
    have ha : (tripleCharges (sourceA270 + difference 3 0) (sourceB270 + difference 0 3) sourceC270) = raw6347 := by
      apply Matrix.ext; unfold tripleCharges sourceA270 sourceB270 sourceC270 difference raw6347; decide +kernel
    rw [ha]
    exact (canonical6347 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA270 + difference 4 0) (sourceB270 + difference 0 4) sourceC270) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1400) := by
    have ha : (tripleCharges (sourceA270 + difference 4 0) (sourceB270 + difference 0 4) sourceC270) = raw6348 := by
      apply Matrix.ext; unfold tripleCharges sourceA270 sourceB270 sourceC270 difference raw6348; decide +kernel
    rw [ha]
    exact (canonical6348 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA270 + difference 5 0) (sourceB270 + difference 0 5) sourceC270) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1394) := by
    have ha : (tripleCharges (sourceA270 + difference 5 0) (sourceB270 + difference 0 5) sourceC270) = raw6349 := by
      apply Matrix.ext; unfold tripleCharges sourceA270 sourceB270 sourceC270 difference raw6349; decide +kernel
    rw [ha]
    exact (canonical6349 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA270 + sourceB270) sourceC270) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA270 + sourceB270) sourceC270) = raw6344 := by
      apply Matrix.ext; unfold doubleCharges sourceA270 sourceB270 sourceC270 raw6344; decide +kernel
    rw [ha]
    exact (canonical6344 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA270 sourceB270 sourceC270
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm270, Integer.Sparse.eval]
  linarith only [hs]

def sourceA271 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB271 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC271 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceForm271 : Integer.Sparse Master := [(Sum.inr 1406, 1), (Sum.inr 2954, 1), (Sum.inr 2984, 1), (Sum.inr 3077, 1), (Sum.inr 3086, 1), (Sum.inr 3097, 1), (Sum.inr 4091, -1)]

theorem sourceEq271 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm271 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA271 + difference 1 0) (sourceB271 + difference 0 1) sourceC271) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1406) := by
    have ha : (tripleCharges (sourceA271 + difference 1 0) (sourceB271 + difference 0 1) sourceC271) = raw6345 := by
      apply Matrix.ext; unfold tripleCharges sourceA271 sourceB271 sourceC271 difference raw6345; decide +kernel
    rw [ha]
    exact (canonical6345 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA271 + difference 1 1) (sourceB271 + difference 1 1) sourceC271) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3086) := by
    have ha : (tripleCharges (sourceA271 + difference 1 1) (sourceB271 + difference 1 1) sourceC271) = raw6338 := by
      apply Matrix.ext; unfold tripleCharges sourceA271 sourceB271 sourceC271 difference raw6338; decide +kernel
    rw [ha]
    exact (canonical6338 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA271 + difference 1 2) (sourceB271 + difference 2 1) sourceC271) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2984) := by
    have ha : (tripleCharges (sourceA271 + difference 1 2) (sourceB271 + difference 2 1) sourceC271) = raw6350 := by
      apply Matrix.ext; unfold tripleCharges sourceA271 sourceB271 sourceC271 difference raw6350; decide +kernel
    rw [ha]
    exact (canonical6350 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA271 + difference 1 3) (sourceB271 + difference 3 1) sourceC271) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2954) := by
    have ha : (tripleCharges (sourceA271 + difference 1 3) (sourceB271 + difference 3 1) sourceC271) = raw6351 := by
      apply Matrix.ext; unfold tripleCharges sourceA271 sourceB271 sourceC271 difference raw6351; decide +kernel
    rw [ha]
    exact (canonical6351 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA271 + difference 1 4) (sourceB271 + difference 4 1) sourceC271) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3077) := by
    have ha : (tripleCharges (sourceA271 + difference 1 4) (sourceB271 + difference 4 1) sourceC271) = raw6352 := by
      apply Matrix.ext; unfold tripleCharges sourceA271 sourceB271 sourceC271 difference raw6352; decide +kernel
    rw [ha]
    exact (canonical6352 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA271 + difference 1 5) (sourceB271 + difference 5 1) sourceC271) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3097) := by
    have ha : (tripleCharges (sourceA271 + difference 1 5) (sourceB271 + difference 5 1) sourceC271) = raw6353 := by
      apply Matrix.ext; unfold tripleCharges sourceA271 sourceB271 sourceC271 difference raw6353; decide +kernel
    rw [ha]
    exact (canonical6353 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA271 + sourceB271) sourceC271) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA271 + sourceB271) sourceC271) = raw6344 := by
      apply Matrix.ext; unfold doubleCharges sourceA271 sourceB271 sourceC271 raw6344; decide +kernel
    rw [ha]
    exact (canonical6344 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA271 sourceB271 sourceC271
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm271, Integer.Sparse.eval]
  linarith only [hs]

def sourceA272 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB272 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC272 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceForm272 : Integer.Sparse Master := [(Sum.inr 2624, 1), (Sum.inr 2949, 1), (Sum.inr 3013, 1), (Sum.inr 3014, 1), (Sum.inr 3086, 1), (Sum.inr 3881, 1), (Sum.inr 4091, -1)]

theorem sourceEq272 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm272 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA272 + difference 0 1) (sourceB272 + difference 1 0) sourceC272) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3881) := by
    have ha : (tripleCharges (sourceA272 + difference 0 1) (sourceB272 + difference 1 0) sourceC272) = raw6339 := by
      apply Matrix.ext; unfold tripleCharges sourceA272 sourceB272 sourceC272 difference raw6339; decide +kernel
    rw [ha]
    exact (canonical6339 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA272 + difference 1 1) (sourceB272 + difference 1 1) sourceC272) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3086) := by
    have ha : (tripleCharges (sourceA272 + difference 1 1) (sourceB272 + difference 1 1) sourceC272) = raw6338 := by
      apply Matrix.ext; unfold tripleCharges sourceA272 sourceB272 sourceC272 difference raw6338; decide +kernel
    rw [ha]
    exact (canonical6338 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA272 + difference 2 1) (sourceB272 + difference 1 2) sourceC272) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3013) := by
    have ha : (tripleCharges (sourceA272 + difference 2 1) (sourceB272 + difference 1 2) sourceC272) = raw6354 := by
      apply Matrix.ext; unfold tripleCharges sourceA272 sourceB272 sourceC272 difference raw6354; decide +kernel
    rw [ha]
    exact (canonical6354 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA272 + difference 3 1) (sourceB272 + difference 1 3) sourceC272) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3014) := by
    have ha : (tripleCharges (sourceA272 + difference 3 1) (sourceB272 + difference 1 3) sourceC272) = raw6355 := by
      apply Matrix.ext; unfold tripleCharges sourceA272 sourceB272 sourceC272 difference raw6355; decide +kernel
    rw [ha]
    exact (canonical6355 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA272 + difference 4 1) (sourceB272 + difference 1 4) sourceC272) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2949) := by
    have ha : (tripleCharges (sourceA272 + difference 4 1) (sourceB272 + difference 1 4) sourceC272) = raw6356 := by
      apply Matrix.ext; unfold tripleCharges sourceA272 sourceB272 sourceC272 difference raw6356; decide +kernel
    rw [ha]
    exact (canonical6356 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA272 + difference 5 1) (sourceB272 + difference 1 5) sourceC272) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2624) := by
    have ha : (tripleCharges (sourceA272 + difference 5 1) (sourceB272 + difference 1 5) sourceC272) = raw6357 := by
      apply Matrix.ext; unfold tripleCharges sourceA272 sourceB272 sourceC272 difference raw6357; decide +kernel
    rw [ha]
    exact (canonical6357 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA272 + sourceB272) sourceC272) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA272 + sourceB272) sourceC272) = raw6344 := by
      apply Matrix.ext; unfold doubleCharges sourceA272 sourceB272 sourceC272 raw6344; decide +kernel
    rw [ha]
    exact (canonical6344 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA272 sourceB272 sourceC272
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm272, Integer.Sparse.eval]
  linarith only [hs]

def sourceA273 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB273 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC273 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceForm273 : Integer.Sparse Master := [(Sum.inr 1392, 1), (Sum.inr 2933, 1), (Sum.inr 3013, 1), (Sum.inr 3064, 1), (Sum.inr 3084, 1), (Sum.inr 3086, 1), (Sum.inr 4091, -1)]

theorem sourceEq273 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm273 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA273 + difference 2 0) (sourceB273 + difference 0 2) sourceC273) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1392) := by
    have ha : (tripleCharges (sourceA273 + difference 2 0) (sourceB273 + difference 0 2) sourceC273) = raw6346 := by
      apply Matrix.ext; unfold tripleCharges sourceA273 sourceB273 sourceC273 difference raw6346; decide +kernel
    rw [ha]
    exact (canonical6346 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA273 + difference 2 1) (sourceB273 + difference 1 2) sourceC273) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3013) := by
    have ha : (tripleCharges (sourceA273 + difference 2 1) (sourceB273 + difference 1 2) sourceC273) = raw6354 := by
      apply Matrix.ext; unfold tripleCharges sourceA273 sourceB273 sourceC273 difference raw6354; decide +kernel
    rw [ha]
    exact (canonical6354 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA273 + difference 2 2) (sourceB273 + difference 2 2) sourceC273) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3086) := by
    have ha : (tripleCharges (sourceA273 + difference 2 2) (sourceB273 + difference 2 2) sourceC273) = raw6338 := by
      apply Matrix.ext; unfold tripleCharges sourceA273 sourceB273 sourceC273 difference raw6338; decide +kernel
    rw [ha]
    exact (canonical6338 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA273 + difference 2 3) (sourceB273 + difference 3 2) sourceC273) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2933) := by
    have ha : (tripleCharges (sourceA273 + difference 2 3) (sourceB273 + difference 3 2) sourceC273) = raw6358 := by
      apply Matrix.ext; unfold tripleCharges sourceA273 sourceB273 sourceC273 difference raw6358; decide +kernel
    rw [ha]
    exact (canonical6358 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA273 + difference 2 4) (sourceB273 + difference 4 2) sourceC273) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3064) := by
    have ha : (tripleCharges (sourceA273 + difference 2 4) (sourceB273 + difference 4 2) sourceC273) = raw6359 := by
      apply Matrix.ext; unfold tripleCharges sourceA273 sourceB273 sourceC273 difference raw6359; decide +kernel
    rw [ha]
    exact (canonical6359 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA273 + difference 2 5) (sourceB273 + difference 5 2) sourceC273) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3084) := by
    have ha : (tripleCharges (sourceA273 + difference 2 5) (sourceB273 + difference 5 2) sourceC273) = raw6360 := by
      apply Matrix.ext; unfold tripleCharges sourceA273 sourceB273 sourceC273 difference raw6360; decide +kernel
    rw [ha]
    exact (canonical6360 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA273 + sourceB273) sourceC273) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA273 + sourceB273) sourceC273) = raw6344 := by
      apply Matrix.ext; unfold doubleCharges sourceA273 sourceB273 sourceC273 raw6344; decide +kernel
    rw [ha]
    exact (canonical6344 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA273 sourceB273 sourceC273
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm273, Integer.Sparse.eval]
  linarith only [hs]

def sourceA274 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB274 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC274 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceForm274 : Integer.Sparse Master := [(Sum.inr 2610, 1), (Sum.inr 2947, 1), (Sum.inr 2984, 1), (Sum.inr 2992, 1), (Sum.inr 3086, 1), (Sum.inr 3871, 1), (Sum.inr 4091, -1)]

theorem sourceEq274 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm274 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA274 + difference 0 2) (sourceB274 + difference 2 0) sourceC274) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3871) := by
    have ha : (tripleCharges (sourceA274 + difference 0 2) (sourceB274 + difference 2 0) sourceC274) = raw6340 := by
      apply Matrix.ext; unfold tripleCharges sourceA274 sourceB274 sourceC274 difference raw6340; decide +kernel
    rw [ha]
    exact (canonical6340 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA274 + difference 1 2) (sourceB274 + difference 2 1) sourceC274) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2984) := by
    have ha : (tripleCharges (sourceA274 + difference 1 2) (sourceB274 + difference 2 1) sourceC274) = raw6350 := by
      apply Matrix.ext; unfold tripleCharges sourceA274 sourceB274 sourceC274 difference raw6350; decide +kernel
    rw [ha]
    exact (canonical6350 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA274 + difference 2 2) (sourceB274 + difference 2 2) sourceC274) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3086) := by
    have ha : (tripleCharges (sourceA274 + difference 2 2) (sourceB274 + difference 2 2) sourceC274) = raw6338 := by
      apply Matrix.ext; unfold tripleCharges sourceA274 sourceB274 sourceC274 difference raw6338; decide +kernel
    rw [ha]
    exact (canonical6338 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA274 + difference 3 2) (sourceB274 + difference 2 3) sourceC274) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2992) := by
    have ha : (tripleCharges (sourceA274 + difference 3 2) (sourceB274 + difference 2 3) sourceC274) = raw6361 := by
      apply Matrix.ext; unfold tripleCharges sourceA274 sourceB274 sourceC274 difference raw6361; decide +kernel
    rw [ha]
    exact (canonical6361 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA274 + difference 4 2) (sourceB274 + difference 2 4) sourceC274) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2947) := by
    have ha : (tripleCharges (sourceA274 + difference 4 2) (sourceB274 + difference 2 4) sourceC274) = raw6362 := by
      apply Matrix.ext; unfold tripleCharges sourceA274 sourceB274 sourceC274 difference raw6362; decide +kernel
    rw [ha]
    exact (canonical6362 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA274 + difference 5 2) (sourceB274 + difference 2 5) sourceC274) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2610) := by
    have ha : (tripleCharges (sourceA274 + difference 5 2) (sourceB274 + difference 2 5) sourceC274) = raw6363 := by
      apply Matrix.ext; unfold tripleCharges sourceA274 sourceB274 sourceC274 difference raw6363; decide +kernel
    rw [ha]
    exact (canonical6363 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA274 + sourceB274) sourceC274) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA274 + sourceB274) sourceC274) = raw6344 := by
      apply Matrix.ext; unfold doubleCharges sourceA274 sourceB274 sourceC274 raw6344; decide +kernel
    rw [ha]
    exact (canonical6344 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA274 sourceB274 sourceC274
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm274, Integer.Sparse.eval]
  linarith only [hs]

def sourceA275 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB275 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC275 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceForm275 : Integer.Sparse Master := [(Sum.inr 1425, 1), (Sum.inr 2992, 1), (Sum.inr 3014, 1), (Sum.inr 3086, 2), (Sum.inr 3108, 1), (Sum.inr 4091, -1)]

theorem sourceEq275 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm275 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA275 + difference 3 0) (sourceB275 + difference 0 3) sourceC275) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1425) := by
    have ha : (tripleCharges (sourceA275 + difference 3 0) (sourceB275 + difference 0 3) sourceC275) = raw6347 := by
      apply Matrix.ext; unfold tripleCharges sourceA275 sourceB275 sourceC275 difference raw6347; decide +kernel
    rw [ha]
    exact (canonical6347 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA275 + difference 3 1) (sourceB275 + difference 1 3) sourceC275) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3014) := by
    have ha : (tripleCharges (sourceA275 + difference 3 1) (sourceB275 + difference 1 3) sourceC275) = raw6355 := by
      apply Matrix.ext; unfold tripleCharges sourceA275 sourceB275 sourceC275 difference raw6355; decide +kernel
    rw [ha]
    exact (canonical6355 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA275 + difference 3 2) (sourceB275 + difference 2 3) sourceC275) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2992) := by
    have ha : (tripleCharges (sourceA275 + difference 3 2) (sourceB275 + difference 2 3) sourceC275) = raw6361 := by
      apply Matrix.ext; unfold tripleCharges sourceA275 sourceB275 sourceC275 difference raw6361; decide +kernel
    rw [ha]
    exact (canonical6361 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA275 + difference 3 3) (sourceB275 + difference 3 3) sourceC275) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3086) := by
    have ha : (tripleCharges (sourceA275 + difference 3 3) (sourceB275 + difference 3 3) sourceC275) = raw6338 := by
      apply Matrix.ext; unfold tripleCharges sourceA275 sourceB275 sourceC275 difference raw6338; decide +kernel
    rw [ha]
    exact (canonical6338 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA275 + difference 3 4) (sourceB275 + difference 4 3) sourceC275) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3086) := by
    have ha : (tripleCharges (sourceA275 + difference 3 4) (sourceB275 + difference 4 3) sourceC275) = raw6364 := by
      apply Matrix.ext; unfold tripleCharges sourceA275 sourceB275 sourceC275 difference raw6364; decide +kernel
    rw [ha]
    exact (canonical6364 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA275 + difference 3 5) (sourceB275 + difference 5 3) sourceC275) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3108) := by
    have ha : (tripleCharges (sourceA275 + difference 3 5) (sourceB275 + difference 5 3) sourceC275) = raw6365 := by
      apply Matrix.ext; unfold tripleCharges sourceA275 sourceB275 sourceC275 difference raw6365; decide +kernel
    rw [ha]
    exact (canonical6365 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA275 + sourceB275) sourceC275) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA275 + sourceB275) sourceC275) = raw6344 := by
      apply Matrix.ext; unfold doubleCharges sourceA275 sourceB275 sourceC275 raw6344; decide +kernel
    rw [ha]
    exact (canonical6344 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA275 sourceB275 sourceC275
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm275, Integer.Sparse.eval]
  linarith only [hs]

def sourceA276 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB276 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC276 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceForm276 : Integer.Sparse Master := [(Sum.inr 2618, 1), (Sum.inr 2933, 1), (Sum.inr 2942, 1), (Sum.inr 2954, 1), (Sum.inr 3086, 1), (Sum.inr 3876, 1), (Sum.inr 4091, -1)]

theorem sourceEq276 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm276 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA276 + difference 0 3) (sourceB276 + difference 3 0) sourceC276) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3876) := by
    have ha : (tripleCharges (sourceA276 + difference 0 3) (sourceB276 + difference 3 0) sourceC276) = raw6341 := by
      apply Matrix.ext; unfold tripleCharges sourceA276 sourceB276 sourceC276 difference raw6341; decide +kernel
    rw [ha]
    exact (canonical6341 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA276 + difference 1 3) (sourceB276 + difference 3 1) sourceC276) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2954) := by
    have ha : (tripleCharges (sourceA276 + difference 1 3) (sourceB276 + difference 3 1) sourceC276) = raw6351 := by
      apply Matrix.ext; unfold tripleCharges sourceA276 sourceB276 sourceC276 difference raw6351; decide +kernel
    rw [ha]
    exact (canonical6351 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA276 + difference 2 3) (sourceB276 + difference 3 2) sourceC276) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2933) := by
    have ha : (tripleCharges (sourceA276 + difference 2 3) (sourceB276 + difference 3 2) sourceC276) = raw6358 := by
      apply Matrix.ext; unfold tripleCharges sourceA276 sourceB276 sourceC276 difference raw6358; decide +kernel
    rw [ha]
    exact (canonical6358 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA276 + difference 3 3) (sourceB276 + difference 3 3) sourceC276) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3086) := by
    have ha : (tripleCharges (sourceA276 + difference 3 3) (sourceB276 + difference 3 3) sourceC276) = raw6338 := by
      apply Matrix.ext; unfold tripleCharges sourceA276 sourceB276 sourceC276 difference raw6338; decide +kernel
    rw [ha]
    exact (canonical6338 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA276 + difference 4 3) (sourceB276 + difference 3 4) sourceC276) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2942) := by
    have ha : (tripleCharges (sourceA276 + difference 4 3) (sourceB276 + difference 3 4) sourceC276) = raw6366 := by
      apply Matrix.ext; unfold tripleCharges sourceA276 sourceB276 sourceC276 difference raw6366; decide +kernel
    rw [ha]
    exact (canonical6366 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA276 + difference 5 3) (sourceB276 + difference 3 5) sourceC276) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2618) := by
    have ha : (tripleCharges (sourceA276 + difference 5 3) (sourceB276 + difference 3 5) sourceC276) = raw6367 := by
      apply Matrix.ext; unfold tripleCharges sourceA276 sourceB276 sourceC276 difference raw6367; decide +kernel
    rw [ha]
    exact (canonical6367 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA276 + sourceB276) sourceC276) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA276 + sourceB276) sourceC276) = raw6344 := by
      apply Matrix.ext; unfold doubleCharges sourceA276 sourceB276 sourceC276 raw6344; decide +kernel
    rw [ha]
    exact (canonical6344 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA276 sourceB276 sourceC276
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm276, Integer.Sparse.eval]
  linarith only [hs]

def sourceA277 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB277 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC277 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceForm277 : Integer.Sparse Master := [(Sum.inr 1400, 1), (Sum.inr 2942, 1), (Sum.inr 2947, 1), (Sum.inr 2949, 1), (Sum.inr 2964, 1), (Sum.inr 3086, 1), (Sum.inr 4091, -1)]

theorem sourceEq277 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm277 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA277 + difference 4 0) (sourceB277 + difference 0 4) sourceC277) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1400) := by
    have ha : (tripleCharges (sourceA277 + difference 4 0) (sourceB277 + difference 0 4) sourceC277) = raw6348 := by
      apply Matrix.ext; unfold tripleCharges sourceA277 sourceB277 sourceC277 difference raw6348; decide +kernel
    rw [ha]
    exact (canonical6348 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA277 + difference 4 1) (sourceB277 + difference 1 4) sourceC277) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2949) := by
    have ha : (tripleCharges (sourceA277 + difference 4 1) (sourceB277 + difference 1 4) sourceC277) = raw6356 := by
      apply Matrix.ext; unfold tripleCharges sourceA277 sourceB277 sourceC277 difference raw6356; decide +kernel
    rw [ha]
    exact (canonical6356 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA277 + difference 4 2) (sourceB277 + difference 2 4) sourceC277) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2947) := by
    have ha : (tripleCharges (sourceA277 + difference 4 2) (sourceB277 + difference 2 4) sourceC277) = raw6362 := by
      apply Matrix.ext; unfold tripleCharges sourceA277 sourceB277 sourceC277 difference raw6362; decide +kernel
    rw [ha]
    exact (canonical6362 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA277 + difference 4 3) (sourceB277 + difference 3 4) sourceC277) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2942) := by
    have ha : (tripleCharges (sourceA277 + difference 4 3) (sourceB277 + difference 3 4) sourceC277) = raw6366 := by
      apply Matrix.ext; unfold tripleCharges sourceA277 sourceB277 sourceC277 difference raw6366; decide +kernel
    rw [ha]
    exact (canonical6366 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA277 + difference 4 4) (sourceB277 + difference 4 4) sourceC277) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3086) := by
    have ha : (tripleCharges (sourceA277 + difference 4 4) (sourceB277 + difference 4 4) sourceC277) = raw6338 := by
      apply Matrix.ext; unfold tripleCharges sourceA277 sourceB277 sourceC277 difference raw6338; decide +kernel
    rw [ha]
    exact (canonical6338 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA277 + difference 4 5) (sourceB277 + difference 5 4) sourceC277) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2964) := by
    have ha : (tripleCharges (sourceA277 + difference 4 5) (sourceB277 + difference 5 4) sourceC277) = raw6368 := by
      apply Matrix.ext; unfold tripleCharges sourceA277 sourceB277 sourceC277 difference raw6368; decide +kernel
    rw [ha]
    exact (canonical6368 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA277 + sourceB277) sourceC277) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA277 + sourceB277) sourceC277) = raw6344 := by
      apply Matrix.ext; unfold doubleCharges sourceA277 sourceB277 sourceC277 raw6344; decide +kernel
    rw [ha]
    exact (canonical6344 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA277 sourceB277 sourceC277
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm277, Integer.Sparse.eval]
  linarith only [hs]

def sourceA278 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceB278 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC278 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm278 : Integer.Sparse Master := [(Sum.inr 4815, 1), (Sum.inr 4817, 1), (Sum.inr 4821, 1), (Sum.inr 4835, 1), (Sum.inr 4896, 1), (Sum.inr 5088, 1), (Sum.inr 5089, 1), (Sum.inr 5106, 1), (Sum.inr 5159, 1), (Sum.inr 5161, 1), (Sum.inr 5165, 1), (Sum.inr 5221, 1), (Sum.inr 5229, 1), (Sum.inr 5234, 1), (Sum.inr 5242, 1), (Sum.inr 5245, 1), (Sum.inr 5249, 1), (Sum.inr 5251, 1), (Sum.inr 5258, 1), (Sum.inr 5259, 1), (Sum.inr 5260, 2), (Sum.inr 5264, 1), (Sum.inr 5267, 1), (Sum.inr 5275, 1), (Sum.inr 5276, 1), (Sum.inr 5291, 1), (Sum.inr 5294, 1), (Sum.inr 5295, 1), (Sum.inr 5310, 1)]

theorem sourceEq278 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm278 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA278 + difference 0 1) (sourceB278 + difference 1 0) sourceC278) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5264) := by
    have ha : (tripleCharges (sourceA278 + difference 0 1) (sourceB278 + difference 1 0) sourceC278) = raw6369 := by
      apply Matrix.ext; unfold tripleCharges sourceA278 sourceB278 sourceC278 difference raw6369; decide +kernel
    rw [ha]
    exact (canonical6369 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA278 + difference 0 2) (sourceB278 + difference 2 0) sourceC278) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5249) := by
    have ha : (tripleCharges (sourceA278 + difference 0 2) (sourceB278 + difference 2 0) sourceC278) = raw6370 := by
      apply Matrix.ext; unfold tripleCharges sourceA278 sourceB278 sourceC278 difference raw6370; decide +kernel
    rw [ha]
    exact (canonical6370 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA278 + difference 0 3) (sourceB278 + difference 3 0) sourceC278) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5291) := by
    have ha : (tripleCharges (sourceA278 + difference 0 3) (sourceB278 + difference 3 0) sourceC278) = raw6013 := by
      apply Matrix.ext; unfold tripleCharges sourceA278 sourceB278 sourceC278 difference raw6013; decide +kernel
    rw [ha]
    exact (canonical6013 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA278 + difference 0 4) (sourceB278 + difference 4 0) sourceC278) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA278 + difference 0 4) (sourceB278 + difference 4 0) sourceC278) = raw6371 := by
      apply Matrix.ext; unfold tripleCharges sourceA278 sourceB278 sourceC278 difference raw6371; decide +kernel
    rw [ha]
    exact (canonical6371 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA278 + difference 0 5) (sourceB278 + difference 5 0) sourceC278) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5161) := by
    have ha : (tripleCharges (sourceA278 + difference 0 5) (sourceB278 + difference 5 0) sourceC278) = raw6372 := by
      apply Matrix.ext; unfold tripleCharges sourceA278 sourceB278 sourceC278 difference raw6372; decide +kernel
    rw [ha]
    exact (canonical6372 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA278 + difference 1 0) (sourceB278 + difference 0 1) sourceC278) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4896) := by
    have ha : (tripleCharges (sourceA278 + difference 1 0) (sourceB278 + difference 0 1) sourceC278) = raw6373 := by
      apply Matrix.ext; unfold tripleCharges sourceA278 sourceB278 sourceC278 difference raw6373; decide +kernel
    rw [ha]
    exact (canonical6373 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA278 + difference 1 2) (sourceB278 + difference 2 1) sourceC278) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5260) := by
    have ha : (tripleCharges (sourceA278 + difference 1 2) (sourceB278 + difference 2 1) sourceC278) = raw6374 := by
      apply Matrix.ext; unfold tripleCharges sourceA278 sourceB278 sourceC278 difference raw6374; decide +kernel
    rw [ha]
    exact (canonical6374 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA278 + difference 1 3) (sourceB278 + difference 3 1) sourceC278) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5310) := by
    have ha : (tripleCharges (sourceA278 + difference 1 3) (sourceB278 + difference 3 1) sourceC278) = raw6018 := by
      apply Matrix.ext; unfold tripleCharges sourceA278 sourceB278 sourceC278 difference raw6018; decide +kernel
    rw [ha]
    exact (canonical6018 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA278 + difference 1 4) (sourceB278 + difference 4 1) sourceC278) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA278 + difference 1 4) (sourceB278 + difference 4 1) sourceC278) = raw6375 := by
      apply Matrix.ext; unfold tripleCharges sourceA278 sourceB278 sourceC278 difference raw6375; decide +kernel
    rw [ha]
    exact (canonical6375 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA278 + difference 1 5) (sourceB278 + difference 5 1) sourceC278) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5295) := by
    have ha : (tripleCharges (sourceA278 + difference 1 5) (sourceB278 + difference 5 1) sourceC278) = raw6376 := by
      apply Matrix.ext; unfold tripleCharges sourceA278 sourceB278 sourceC278 difference raw6376; decide +kernel
    rw [ha]
    exact (canonical6376 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA278 + difference 2 0) (sourceB278 + difference 0 2) sourceC278) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4815) := by
    have ha : (tripleCharges (sourceA278 + difference 2 0) (sourceB278 + difference 0 2) sourceC278) = raw6377 := by
      apply Matrix.ext; unfold tripleCharges sourceA278 sourceB278 sourceC278 difference raw6377; decide +kernel
    rw [ha]
    exact (canonical6377 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA278 + difference 2 1) (sourceB278 + difference 1 2) sourceC278) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5221) := by
    have ha : (tripleCharges (sourceA278 + difference 2 1) (sourceB278 + difference 1 2) sourceC278) = raw6378 := by
      apply Matrix.ext; unfold tripleCharges sourceA278 sourceB278 sourceC278 difference raw6378; decide +kernel
    rw [ha]
    exact (canonical6378 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA278 + difference 2 3) (sourceB278 + difference 3 2) sourceC278) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5260) := by
    have ha : (tripleCharges (sourceA278 + difference 2 3) (sourceB278 + difference 3 2) sourceC278) = raw6023 := by
      apply Matrix.ext; unfold tripleCharges sourceA278 sourceB278 sourceC278 difference raw6023; decide +kernel
    rw [ha]
    exact (canonical6023 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA278 + difference 2 4) (sourceB278 + difference 4 2) sourceC278) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5251) := by
    have ha : (tripleCharges (sourceA278 + difference 2 4) (sourceB278 + difference 4 2) sourceC278) = raw6379 := by
      apply Matrix.ext; unfold tripleCharges sourceA278 sourceB278 sourceC278 difference raw6379; decide +kernel
    rw [ha]
    exact (canonical6379 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA278 + difference 2 5) (sourceB278 + difference 5 2) sourceC278) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5159) := by
    have ha : (tripleCharges (sourceA278 + difference 2 5) (sourceB278 + difference 5 2) sourceC278) = raw6380 := by
      apply Matrix.ext; unfold tripleCharges sourceA278 sourceB278 sourceC278 difference raw6380; decide +kernel
    rw [ha]
    exact (canonical6380 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA278 + difference 3 0) (sourceB278 + difference 0 3) sourceC278) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4821) := by
    have ha : (tripleCharges (sourceA278 + difference 3 0) (sourceB278 + difference 0 3) sourceC278) = raw6381 := by
      apply Matrix.ext; unfold tripleCharges sourceA278 sourceB278 sourceC278 difference raw6381; decide +kernel
    rw [ha]
    exact (canonical6381 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA278 + difference 3 1) (sourceB278 + difference 1 3) sourceC278) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5234) := by
    have ha : (tripleCharges (sourceA278 + difference 3 1) (sourceB278 + difference 1 3) sourceC278) = raw6382 := by
      apply Matrix.ext; unfold tripleCharges sourceA278 sourceB278 sourceC278 difference raw6382; decide +kernel
    rw [ha]
    exact (canonical6382 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA278 + difference 3 2) (sourceB278 + difference 2 3) sourceC278) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5245) := by
    have ha : (tripleCharges (sourceA278 + difference 3 2) (sourceB278 + difference 2 3) sourceC278) = raw6383 := by
      apply Matrix.ext; unfold tripleCharges sourceA278 sourceB278 sourceC278 difference raw6383; decide +kernel
    rw [ha]
    exact (canonical6383 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA278 + difference 3 4) (sourceB278 + difference 4 3) sourceC278) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5267) := by
    have ha : (tripleCharges (sourceA278 + difference 3 4) (sourceB278 + difference 4 3) sourceC278) = raw6384 := by
      apply Matrix.ext; unfold tripleCharges sourceA278 sourceB278 sourceC278 difference raw6384; decide +kernel
    rw [ha]
    exact (canonical6384 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA278 + difference 3 5) (sourceB278 + difference 5 3) sourceC278) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5165) := by
    have ha : (tripleCharges (sourceA278 + difference 3 5) (sourceB278 + difference 5 3) sourceC278) = raw6385 := by
      apply Matrix.ext; unfold tripleCharges sourceA278 sourceB278 sourceC278 difference raw6385; decide +kernel
    rw [ha]
    exact (canonical6385 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA278 + difference 4 0) (sourceB278 + difference 0 4) sourceC278) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4817) := by
    have ha : (tripleCharges (sourceA278 + difference 4 0) (sourceB278 + difference 0 4) sourceC278) = raw6025 := by
      apply Matrix.ext; unfold tripleCharges sourceA278 sourceB278 sourceC278 difference raw6025; decide +kernel
    rw [ha]
    exact (canonical6025 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA278 + difference 4 1) (sourceB278 + difference 1 4) sourceC278) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5089) := by
    have ha : (tripleCharges (sourceA278 + difference 4 1) (sourceB278 + difference 1 4) sourceC278) = raw6026 := by
      apply Matrix.ext; unfold tripleCharges sourceA278 sourceB278 sourceC278 difference raw6026; decide +kernel
    rw [ha]
    exact (canonical6026 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA278 + difference 4 2) (sourceB278 + difference 2 4) sourceC278) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5088) := by
    have ha : (tripleCharges (sourceA278 + difference 4 2) (sourceB278 + difference 2 4) sourceC278) = raw6027 := by
      apply Matrix.ext; unfold tripleCharges sourceA278 sourceB278 sourceC278 difference raw6027; decide +kernel
    rw [ha]
    exact (canonical6027 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA278 + difference 4 3) (sourceB278 + difference 3 4) sourceC278) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5276) := by
    have ha : (tripleCharges (sourceA278 + difference 4 3) (sourceB278 + difference 3 4) sourceC278) = raw6386 := by
      apply Matrix.ext; unfold tripleCharges sourceA278 sourceB278 sourceC278 difference raw6386; decide +kernel
    rw [ha]
    exact (canonical6386 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA278 + difference 4 5) (sourceB278 + difference 5 4) sourceC278) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5106) := by
    have ha : (tripleCharges (sourceA278 + difference 4 5) (sourceB278 + difference 5 4) sourceC278) = raw6029 := by
      apply Matrix.ext; unfold tripleCharges sourceA278 sourceB278 sourceC278 difference raw6029; decide +kernel
    rw [ha]
    exact (canonical6029 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA278 + difference 5 0) (sourceB278 + difference 0 5) sourceC278) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4835) := by
    have ha : (tripleCharges (sourceA278 + difference 5 0) (sourceB278 + difference 0 5) sourceC278) = raw6387 := by
      apply Matrix.ext; unfold tripleCharges sourceA278 sourceB278 sourceC278 difference raw6387; decide +kernel
    rw [ha]
    exact (canonical6387 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA278 + difference 5 1) (sourceB278 + difference 1 5) sourceC278) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5229) := by
    have ha : (tripleCharges (sourceA278 + difference 5 1) (sourceB278 + difference 1 5) sourceC278) = raw6388 := by
      apply Matrix.ext; unfold tripleCharges sourceA278 sourceB278 sourceC278 difference raw6388; decide +kernel
    rw [ha]
    exact (canonical6388 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA278 + difference 5 2) (sourceB278 + difference 2 5) sourceC278) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5242) := by
    have ha : (tripleCharges (sourceA278 + difference 5 2) (sourceB278 + difference 2 5) sourceC278) = raw6389 := by
      apply Matrix.ext; unfold tripleCharges sourceA278 sourceB278 sourceC278 difference raw6389; decide +kernel
    rw [ha]
    exact (canonical6389 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA278 + difference 5 3) (sourceB278 + difference 3 5) sourceC278) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5275) := by
    have ha : (tripleCharges (sourceA278 + difference 5 3) (sourceB278 + difference 3 5) sourceC278) = raw6039 := by
      apply Matrix.ext; unfold tripleCharges sourceA278 sourceB278 sourceC278 difference raw6039; decide +kernel
    rw [ha]
    exact (canonical6039 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA278 + difference 5 4) (sourceB278 + difference 4 5) sourceC278) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA278 + difference 5 4) (sourceB278 + difference 4 5) sourceC278) = raw6390 := by
      apply Matrix.ext; unfold tripleCharges sourceA278 sourceB278 sourceC278 difference raw6390; decide +kernel
    rw [ha]
    exact (canonical6390 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA278 sourceB278 sourceC278
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm278, Integer.Sparse.eval]
  linarith only [hs]

def sourceA279 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceB279 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC279 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm279 : Integer.Sparse Master := [(Sum.inr 2192, 1), (Sum.inr 2206, 1), (Sum.inr 2207, 1), (Sum.inr 2217, 1), (Sum.inr 2266, 1), (Sum.inr 2663, 1), (Sum.inr 2673, 1), (Sum.inr 2674, 1), (Sum.inr 2679, 1), (Sum.inr 2695, 1), (Sum.inr 2696, 1), (Sum.inr 2699, 1), (Sum.inr 2710, 1), (Sum.inr 2711, 1), (Sum.inr 2723, 1), (Sum.inr 2724, 2), (Sum.inr 2725, 1), (Sum.inr 2732, 1), (Sum.inr 2733, 1), (Sum.inr 2743, 1), (Sum.inr 2744, 1), (Sum.inr 2768, 1), (Sum.inr 2769, 1), (Sum.inr 2788, 1), (Sum.inr 2964, 1), (Sum.inr 3040, 1), (Sum.inr 3066, 1), (Sum.inr 3089, 1), (Sum.inr 3103, 1)]

theorem sourceEq279 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm279 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA279 + difference 0 1) (sourceB279 + difference 1 0) sourceC279) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3040) := by
    have ha : (tripleCharges (sourceA279 + difference 0 1) (sourceB279 + difference 1 0) sourceC279) = raw6391 := by
      apply Matrix.ext; unfold tripleCharges sourceA279 sourceB279 sourceC279 difference raw6391; decide +kernel
    rw [ha]
    exact (canonical6391 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA279 + difference 0 2) (sourceB279 + difference 2 0) sourceC279) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3066) := by
    have ha : (tripleCharges (sourceA279 + difference 0 2) (sourceB279 + difference 2 0) sourceC279) = raw6392 := by
      apply Matrix.ext; unfold tripleCharges sourceA279 sourceB279 sourceC279 difference raw6392; decide +kernel
    rw [ha]
    exact (canonical6392 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA279 + difference 0 3) (sourceB279 + difference 3 0) sourceC279) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3103) := by
    have ha : (tripleCharges (sourceA279 + difference 0 3) (sourceB279 + difference 3 0) sourceC279) = raw6043 := by
      apply Matrix.ext; unfold tripleCharges sourceA279 sourceB279 sourceC279 difference raw6043; decide +kernel
    rw [ha]
    exact (canonical6043 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA279 + difference 0 4) (sourceB279 + difference 4 0) sourceC279) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3089) := by
    have ha : (tripleCharges (sourceA279 + difference 0 4) (sourceB279 + difference 4 0) sourceC279) = raw6393 := by
      apply Matrix.ext; unfold tripleCharges sourceA279 sourceB279 sourceC279 difference raw6393; decide +kernel
    rw [ha]
    exact (canonical6393 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA279 + difference 0 5) (sourceB279 + difference 5 0) sourceC279) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2964) := by
    have ha : (tripleCharges (sourceA279 + difference 0 5) (sourceB279 + difference 5 0) sourceC279) = raw6394 := by
      apply Matrix.ext; unfold tripleCharges sourceA279 sourceB279 sourceC279 difference raw6394; decide +kernel
    rw [ha]
    exact (canonical6394 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA279 + difference 1 0) (sourceB279 + difference 0 1) sourceC279) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2266) := by
    have ha : (tripleCharges (sourceA279 + difference 1 0) (sourceB279 + difference 0 1) sourceC279) = raw6395 := by
      apply Matrix.ext; unfold tripleCharges sourceA279 sourceB279 sourceC279 difference raw6395; decide +kernel
    rw [ha]
    exact (canonical6395 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA279 + difference 1 2) (sourceB279 + difference 2 1) sourceC279) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2724) := by
    have ha : (tripleCharges (sourceA279 + difference 1 2) (sourceB279 + difference 2 1) sourceC279) = raw6396 := by
      apply Matrix.ext; unfold tripleCharges sourceA279 sourceB279 sourceC279 difference raw6396; decide +kernel
    rw [ha]
    exact (canonical6396 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA279 + difference 1 3) (sourceB279 + difference 3 1) sourceC279) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2788) := by
    have ha : (tripleCharges (sourceA279 + difference 1 3) (sourceB279 + difference 3 1) sourceC279) = raw6048 := by
      apply Matrix.ext; unfold tripleCharges sourceA279 sourceB279 sourceC279 difference raw6048; decide +kernel
    rw [ha]
    exact (canonical6048 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA279 + difference 1 4) (sourceB279 + difference 4 1) sourceC279) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2768) := by
    have ha : (tripleCharges (sourceA279 + difference 1 4) (sourceB279 + difference 4 1) sourceC279) = raw6397 := by
      apply Matrix.ext; unfold tripleCharges sourceA279 sourceB279 sourceC279 difference raw6397; decide +kernel
    rw [ha]
    exact (canonical6397 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA279 + difference 1 5) (sourceB279 + difference 5 1) sourceC279) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2769) := by
    have ha : (tripleCharges (sourceA279 + difference 1 5) (sourceB279 + difference 5 1) sourceC279) = raw6398 := by
      apply Matrix.ext; unfold tripleCharges sourceA279 sourceB279 sourceC279 difference raw6398; decide +kernel
    rw [ha]
    exact (canonical6398 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA279 + difference 2 0) (sourceB279 + difference 0 2) sourceC279) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2192) := by
    have ha : (tripleCharges (sourceA279 + difference 2 0) (sourceB279 + difference 0 2) sourceC279) = raw6399 := by
      apply Matrix.ext; unfold tripleCharges sourceA279 sourceB279 sourceC279 difference raw6399; decide +kernel
    rw [ha]
    exact (canonical6399 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA279 + difference 2 1) (sourceB279 + difference 1 2) sourceC279) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2663) := by
    have ha : (tripleCharges (sourceA279 + difference 2 1) (sourceB279 + difference 1 2) sourceC279) = raw6400 := by
      apply Matrix.ext; unfold tripleCharges sourceA279 sourceB279 sourceC279 difference raw6400; decide +kernel
    rw [ha]
    exact (canonical6400 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA279 + difference 2 3) (sourceB279 + difference 3 2) sourceC279) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2724) := by
    have ha : (tripleCharges (sourceA279 + difference 2 3) (sourceB279 + difference 3 2) sourceC279) = raw6053 := by
      apply Matrix.ext; unfold tripleCharges sourceA279 sourceB279 sourceC279 difference raw6053; decide +kernel
    rw [ha]
    exact (canonical6053 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA279 + difference 2 4) (sourceB279 + difference 4 2) sourceC279) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2710) := by
    have ha : (tripleCharges (sourceA279 + difference 2 4) (sourceB279 + difference 4 2) sourceC279) = raw6401 := by
      apply Matrix.ext; unfold tripleCharges sourceA279 sourceB279 sourceC279 difference raw6401; decide +kernel
    rw [ha]
    exact (canonical6401 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA279 + difference 2 5) (sourceB279 + difference 5 2) sourceC279) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2711) := by
    have ha : (tripleCharges (sourceA279 + difference 2 5) (sourceB279 + difference 5 2) sourceC279) = raw6402 := by
      apply Matrix.ext; unfold tripleCharges sourceA279 sourceB279 sourceC279 difference raw6402; decide +kernel
    rw [ha]
    exact (canonical6402 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA279 + difference 3 0) (sourceB279 + difference 0 3) sourceC279) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2217) := by
    have ha : (tripleCharges (sourceA279 + difference 3 0) (sourceB279 + difference 0 3) sourceC279) = raw6403 := by
      apply Matrix.ext; unfold tripleCharges sourceA279 sourceB279 sourceC279 difference raw6403; decide +kernel
    rw [ha]
    exact (canonical6403 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA279 + difference 3 1) (sourceB279 + difference 1 3) sourceC279) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2679) := by
    have ha : (tripleCharges (sourceA279 + difference 3 1) (sourceB279 + difference 1 3) sourceC279) = raw6404 := by
      apply Matrix.ext; unfold tripleCharges sourceA279 sourceB279 sourceC279 difference raw6404; decide +kernel
    rw [ha]
    exact (canonical6404 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA279 + difference 3 2) (sourceB279 + difference 2 3) sourceC279) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2699) := by
    have ha : (tripleCharges (sourceA279 + difference 3 2) (sourceB279 + difference 2 3) sourceC279) = raw6405 := by
      apply Matrix.ext; unfold tripleCharges sourceA279 sourceB279 sourceC279 difference raw6405; decide +kernel
    rw [ha]
    exact (canonical6405 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA279 + difference 3 4) (sourceB279 + difference 4 3) sourceC279) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2732) := by
    have ha : (tripleCharges (sourceA279 + difference 3 4) (sourceB279 + difference 4 3) sourceC279) = raw6406 := by
      apply Matrix.ext; unfold tripleCharges sourceA279 sourceB279 sourceC279 difference raw6406; decide +kernel
    rw [ha]
    exact (canonical6406 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA279 + difference 3 5) (sourceB279 + difference 5 3) sourceC279) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2733) := by
    have ha : (tripleCharges (sourceA279 + difference 3 5) (sourceB279 + difference 5 3) sourceC279) = raw6407 := by
      apply Matrix.ext; unfold tripleCharges sourceA279 sourceB279 sourceC279 difference raw6407; decide +kernel
    rw [ha]
    exact (canonical6407 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA279 + difference 4 0) (sourceB279 + difference 0 4) sourceC279) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2207) := by
    have ha : (tripleCharges (sourceA279 + difference 4 0) (sourceB279 + difference 0 4) sourceC279) = raw6055 := by
      apply Matrix.ext; unfold tripleCharges sourceA279 sourceB279 sourceC279 difference raw6055; decide +kernel
    rw [ha]
    exact (canonical6055 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA279 + difference 4 1) (sourceB279 + difference 1 4) sourceC279) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2674) := by
    have ha : (tripleCharges (sourceA279 + difference 4 1) (sourceB279 + difference 1 4) sourceC279) = raw6056 := by
      apply Matrix.ext; unfold tripleCharges sourceA279 sourceB279 sourceC279 difference raw6056; decide +kernel
    rw [ha]
    exact (canonical6056 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA279 + difference 4 2) (sourceB279 + difference 2 4) sourceC279) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2696) := by
    have ha : (tripleCharges (sourceA279 + difference 4 2) (sourceB279 + difference 2 4) sourceC279) = raw6057 := by
      apply Matrix.ext; unfold tripleCharges sourceA279 sourceB279 sourceC279 difference raw6057; decide +kernel
    rw [ha]
    exact (canonical6057 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA279 + difference 4 3) (sourceB279 + difference 3 4) sourceC279) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2744) := by
    have ha : (tripleCharges (sourceA279 + difference 4 3) (sourceB279 + difference 3 4) sourceC279) = raw6408 := by
      apply Matrix.ext; unfold tripleCharges sourceA279 sourceB279 sourceC279 difference raw6408; decide +kernel
    rw [ha]
    exact (canonical6408 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA279 + difference 4 5) (sourceB279 + difference 5 4) sourceC279) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2725) := by
    have ha : (tripleCharges (sourceA279 + difference 4 5) (sourceB279 + difference 5 4) sourceC279) = raw6059 := by
      apply Matrix.ext; unfold tripleCharges sourceA279 sourceB279 sourceC279 difference raw6059; decide +kernel
    rw [ha]
    exact (canonical6059 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA279 + difference 5 0) (sourceB279 + difference 0 5) sourceC279) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2206) := by
    have ha : (tripleCharges (sourceA279 + difference 5 0) (sourceB279 + difference 0 5) sourceC279) = raw6409 := by
      apply Matrix.ext; unfold tripleCharges sourceA279 sourceB279 sourceC279 difference raw6409; decide +kernel
    rw [ha]
    exact (canonical6409 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA279 + difference 5 1) (sourceB279 + difference 1 5) sourceC279) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2673) := by
    have ha : (tripleCharges (sourceA279 + difference 5 1) (sourceB279 + difference 1 5) sourceC279) = raw6410 := by
      apply Matrix.ext; unfold tripleCharges sourceA279 sourceB279 sourceC279 difference raw6410; decide +kernel
    rw [ha]
    exact (canonical6410 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA279 + difference 5 2) (sourceB279 + difference 2 5) sourceC279) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2695) := by
    have ha : (tripleCharges (sourceA279 + difference 5 2) (sourceB279 + difference 2 5) sourceC279) = raw6411 := by
      apply Matrix.ext; unfold tripleCharges sourceA279 sourceB279 sourceC279 difference raw6411; decide +kernel
    rw [ha]
    exact (canonical6411 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA279 + difference 5 3) (sourceB279 + difference 3 5) sourceC279) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2743) := by
    have ha : (tripleCharges (sourceA279 + difference 5 3) (sourceB279 + difference 3 5) sourceC279) = raw6069 := by
      apply Matrix.ext; unfold tripleCharges sourceA279 sourceB279 sourceC279 difference raw6069; decide +kernel
    rw [ha]
    exact (canonical6069 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA279 + difference 5 4) (sourceB279 + difference 4 5) sourceC279) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA279 + difference 5 4) (sourceB279 + difference 4 5) sourceC279) = raw6412 := by
      apply Matrix.ext; unfold tripleCharges sourceA279 sourceB279 sourceC279 difference raw6412; decide +kernel
    rw [ha]
    exact (canonical6412 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA279 sourceB279 sourceC279
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm279, Integer.Sparse.eval]
  linarith only [hs]

def sourceA280 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceB280 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC280 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm280 : Integer.Sparse Master := [(Sum.inr 2496, 1), (Sum.inr 2497, 1), (Sum.inr 2498, 1), (Sum.inr 2516, 1), (Sum.inr 2708, 1), (Sum.inr 2719, 1), (Sum.inr 2722, 1), (Sum.inr 2729, 1), (Sum.inr 2765, 1), (Sum.inr 2777, 1), (Sum.inr 3028, 1), (Sum.inr 3035, 1), (Sum.inr 3038, 1), (Sum.inr 3042, 1), (Sum.inr 3063, 1), (Sum.inr 3064, 1), (Sum.inr 3067, 1), (Sum.inr 3080, 1), (Sum.inr 3086, 2), (Sum.inr 3088, 1), (Sum.inr 3092, 1), (Sum.inr 3098, 1), (Sum.inr 3101, 1), (Sum.inr 3110, 1), (Sum.inr 3121, 1), (Sum.inr 3197, 1), (Sum.inr 3198, 1), (Sum.inr 3211, 1), (Sum.inr 3225, 1)]

theorem sourceEq280 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm280 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA280 + difference 0 1) (sourceB280 + difference 1 0) sourceC280) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2729) := by
    have ha : (tripleCharges (sourceA280 + difference 0 1) (sourceB280 + difference 1 0) sourceC280) = raw6413 := by
      apply Matrix.ext; unfold tripleCharges sourceA280 sourceB280 sourceC280 difference raw6413; decide +kernel
    rw [ha]
    exact (canonical6413 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA280 + difference 0 2) (sourceB280 + difference 2 0) sourceC280) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2708) := by
    have ha : (tripleCharges (sourceA280 + difference 0 2) (sourceB280 + difference 2 0) sourceC280) = raw6414 := by
      apply Matrix.ext; unfold tripleCharges sourceA280 sourceB280 sourceC280 difference raw6414; decide +kernel
    rw [ha]
    exact (canonical6414 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA280 + difference 0 3) (sourceB280 + difference 3 0) sourceC280) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2765) := by
    have ha : (tripleCharges (sourceA280 + difference 0 3) (sourceB280 + difference 3 0) sourceC280) = raw6073 := by
      apply Matrix.ext; unfold tripleCharges sourceA280 sourceB280 sourceC280 difference raw6073; decide +kernel
    rw [ha]
    exact (canonical6073 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA280 + difference 0 4) (sourceB280 + difference 4 0) sourceC280) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA280 + difference 0 4) (sourceB280 + difference 4 0) sourceC280) = raw6415 := by
      apply Matrix.ext; unfold tripleCharges sourceA280 sourceB280 sourceC280 difference raw6415; decide +kernel
    rw [ha]
    exact (canonical6415 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA280 + difference 0 5) (sourceB280 + difference 5 0) sourceC280) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2719) := by
    have ha : (tripleCharges (sourceA280 + difference 0 5) (sourceB280 + difference 5 0) sourceC280) = raw6416 := by
      apply Matrix.ext; unfold tripleCharges sourceA280 sourceB280 sourceC280 difference raw6416; decide +kernel
    rw [ha]
    exact (canonical6416 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA280 + difference 1 0) (sourceB280 + difference 0 1) sourceC280) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3225) := by
    have ha : (tripleCharges (sourceA280 + difference 1 0) (sourceB280 + difference 0 1) sourceC280) = raw6417 := by
      apply Matrix.ext; unfold tripleCharges sourceA280 sourceB280 sourceC280 difference raw6417; decide +kernel
    rw [ha]
    exact (canonical6417 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA280 + difference 1 2) (sourceB280 + difference 2 1) sourceC280) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3086) := by
    have ha : (tripleCharges (sourceA280 + difference 1 2) (sourceB280 + difference 2 1) sourceC280) = raw6418 := by
      apply Matrix.ext; unfold tripleCharges sourceA280 sourceB280 sourceC280 difference raw6418; decide +kernel
    rw [ha]
    exact (canonical6418 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA280 + difference 1 3) (sourceB280 + difference 3 1) sourceC280) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3121) := by
    have ha : (tripleCharges (sourceA280 + difference 1 3) (sourceB280 + difference 3 1) sourceC280) = raw6078 := by
      apply Matrix.ext; unfold tripleCharges sourceA280 sourceB280 sourceC280 difference raw6078; decide +kernel
    rw [ha]
    exact (canonical6078 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA280 + difference 1 4) (sourceB280 + difference 4 1) sourceC280) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3101) := by
    have ha : (tripleCharges (sourceA280 + difference 1 4) (sourceB280 + difference 4 1) sourceC280) = raw6419 := by
      apply Matrix.ext; unfold tripleCharges sourceA280 sourceB280 sourceC280 difference raw6419; decide +kernel
    rw [ha]
    exact (canonical6419 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA280 + difference 1 5) (sourceB280 + difference 5 1) sourceC280) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3098) := by
    have ha : (tripleCharges (sourceA280 + difference 1 5) (sourceB280 + difference 5 1) sourceC280) = raw6420 := by
      apply Matrix.ext; unfold tripleCharges sourceA280 sourceB280 sourceC280 difference raw6420; decide +kernel
    rw [ha]
    exact (canonical6420 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA280 + difference 2 0) (sourceB280 + difference 0 2) sourceC280) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3197) := by
    have ha : (tripleCharges (sourceA280 + difference 2 0) (sourceB280 + difference 0 2) sourceC280) = raw6421 := by
      apply Matrix.ext; unfold tripleCharges sourceA280 sourceB280 sourceC280 difference raw6421; decide +kernel
    rw [ha]
    exact (canonical6421 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA280 + difference 2 1) (sourceB280 + difference 1 2) sourceC280) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3067) := by
    have ha : (tripleCharges (sourceA280 + difference 2 1) (sourceB280 + difference 1 2) sourceC280) = raw6422 := by
      apply Matrix.ext; unfold tripleCharges sourceA280 sourceB280 sourceC280 difference raw6422; decide +kernel
    rw [ha]
    exact (canonical6422 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA280 + difference 2 3) (sourceB280 + difference 3 2) sourceC280) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3086) := by
    have ha : (tripleCharges (sourceA280 + difference 2 3) (sourceB280 + difference 3 2) sourceC280) = raw6083 := by
      apply Matrix.ext; unfold tripleCharges sourceA280 sourceB280 sourceC280 difference raw6083; decide +kernel
    rw [ha]
    exact (canonical6083 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA280 + difference 2 4) (sourceB280 + difference 4 2) sourceC280) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3064) := by
    have ha : (tripleCharges (sourceA280 + difference 2 4) (sourceB280 + difference 4 2) sourceC280) = raw6423 := by
      apply Matrix.ext; unfold tripleCharges sourceA280 sourceB280 sourceC280 difference raw6423; decide +kernel
    rw [ha]
    exact (canonical6423 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA280 + difference 2 5) (sourceB280 + difference 5 2) sourceC280) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3063) := by
    have ha : (tripleCharges (sourceA280 + difference 2 5) (sourceB280 + difference 5 2) sourceC280) = raw6424 := by
      apply Matrix.ext; unfold tripleCharges sourceA280 sourceB280 sourceC280 difference raw6424; decide +kernel
    rw [ha]
    exact (canonical6424 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA280 + difference 3 0) (sourceB280 + difference 0 3) sourceC280) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3198) := by
    have ha : (tripleCharges (sourceA280 + difference 3 0) (sourceB280 + difference 0 3) sourceC280) = raw6425 := by
      apply Matrix.ext; unfold tripleCharges sourceA280 sourceB280 sourceC280 difference raw6425; decide +kernel
    rw [ha]
    exact (canonical6425 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA280 + difference 3 1) (sourceB280 + difference 1 3) sourceC280) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3042) := by
    have ha : (tripleCharges (sourceA280 + difference 3 1) (sourceB280 + difference 1 3) sourceC280) = raw6426 := by
      apply Matrix.ext; unfold tripleCharges sourceA280 sourceB280 sourceC280 difference raw6426; decide +kernel
    rw [ha]
    exact (canonical6426 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA280 + difference 3 2) (sourceB280 + difference 2 3) sourceC280) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3028) := by
    have ha : (tripleCharges (sourceA280 + difference 3 2) (sourceB280 + difference 2 3) sourceC280) = raw6427 := by
      apply Matrix.ext; unfold tripleCharges sourceA280 sourceB280 sourceC280 difference raw6427; decide +kernel
    rw [ha]
    exact (canonical6427 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA280 + difference 3 4) (sourceB280 + difference 4 3) sourceC280) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3038) := by
    have ha : (tripleCharges (sourceA280 + difference 3 4) (sourceB280 + difference 4 3) sourceC280) = raw6428 := by
      apply Matrix.ext; unfold tripleCharges sourceA280 sourceB280 sourceC280 difference raw6428; decide +kernel
    rw [ha]
    exact (canonical6428 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA280 + difference 3 5) (sourceB280 + difference 5 3) sourceC280) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3035) := by
    have ha : (tripleCharges (sourceA280 + difference 3 5) (sourceB280 + difference 5 3) sourceC280) = raw6429 := by
      apply Matrix.ext; unfold tripleCharges sourceA280 sourceB280 sourceC280 difference raw6429; decide +kernel
    rw [ha]
    exact (canonical6429 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA280 + difference 4 0) (sourceB280 + difference 0 4) sourceC280) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2497) := by
    have ha : (tripleCharges (sourceA280 + difference 4 0) (sourceB280 + difference 0 4) sourceC280) = raw6085 := by
      apply Matrix.ext; unfold tripleCharges sourceA280 sourceB280 sourceC280 difference raw6085; decide +kernel
    rw [ha]
    exact (canonical6085 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA280 + difference 4 1) (sourceB280 + difference 1 4) sourceC280) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2498) := by
    have ha : (tripleCharges (sourceA280 + difference 4 1) (sourceB280 + difference 1 4) sourceC280) = raw6086 := by
      apply Matrix.ext; unfold tripleCharges sourceA280 sourceB280 sourceC280 difference raw6086; decide +kernel
    rw [ha]
    exact (canonical6086 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA280 + difference 4 2) (sourceB280 + difference 2 4) sourceC280) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2496) := by
    have ha : (tripleCharges (sourceA280 + difference 4 2) (sourceB280 + difference 2 4) sourceC280) = raw6087 := by
      apply Matrix.ext; unfold tripleCharges sourceA280 sourceB280 sourceC280 difference raw6087; decide +kernel
    rw [ha]
    exact (canonical6087 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA280 + difference 4 3) (sourceB280 + difference 3 4) sourceC280) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2777) := by
    have ha : (tripleCharges (sourceA280 + difference 4 3) (sourceB280 + difference 3 4) sourceC280) = raw6430 := by
      apply Matrix.ext; unfold tripleCharges sourceA280 sourceB280 sourceC280 difference raw6430; decide +kernel
    rw [ha]
    exact (canonical6430 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA280 + difference 4 5) (sourceB280 + difference 5 4) sourceC280) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2516) := by
    have ha : (tripleCharges (sourceA280 + difference 4 5) (sourceB280 + difference 5 4) sourceC280) = raw6089 := by
      apply Matrix.ext; unfold tripleCharges sourceA280 sourceB280 sourceC280 difference raw6089; decide +kernel
    rw [ha]
    exact (canonical6089 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA280 + difference 5 0) (sourceB280 + difference 0 5) sourceC280) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3211) := by
    have ha : (tripleCharges (sourceA280 + difference 5 0) (sourceB280 + difference 0 5) sourceC280) = raw6431 := by
      apply Matrix.ext; unfold tripleCharges sourceA280 sourceB280 sourceC280 difference raw6431; decide +kernel
    rw [ha]
    exact (canonical6431 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA280 + difference 5 1) (sourceB280 + difference 1 5) sourceC280) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3092) := by
    have ha : (tripleCharges (sourceA280 + difference 5 1) (sourceB280 + difference 1 5) sourceC280) = raw6432 := by
      apply Matrix.ext; unfold tripleCharges sourceA280 sourceB280 sourceC280 difference raw6432; decide +kernel
    rw [ha]
    exact (canonical6432 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA280 + difference 5 2) (sourceB280 + difference 2 5) sourceC280) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3080) := by
    have ha : (tripleCharges (sourceA280 + difference 5 2) (sourceB280 + difference 2 5) sourceC280) = raw6433 := by
      apply Matrix.ext; unfold tripleCharges sourceA280 sourceB280 sourceC280 difference raw6433; decide +kernel
    rw [ha]
    exact (canonical6433 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA280 + difference 5 3) (sourceB280 + difference 3 5) sourceC280) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3110) := by
    have ha : (tripleCharges (sourceA280 + difference 5 3) (sourceB280 + difference 3 5) sourceC280) = raw6099 := by
      apply Matrix.ext; unfold tripleCharges sourceA280 sourceB280 sourceC280 difference raw6099; decide +kernel
    rw [ha]
    exact (canonical6099 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA280 + difference 5 4) (sourceB280 + difference 4 5) sourceC280) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3088) := by
    have ha : (tripleCharges (sourceA280 + difference 5 4) (sourceB280 + difference 4 5) sourceC280) = raw6434 := by
      apply Matrix.ext; unfold tripleCharges sourceA280 sourceB280 sourceC280 difference raw6434; decide +kernel
    rw [ha]
    exact (canonical6434 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA280 sourceB280 sourceC280
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm280, Integer.Sparse.eval]
  linarith only [hs]

def sourceA281 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceB281 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC281 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm281 : Integer.Sparse Master := [(Sum.inr 2588, 1), (Sum.inr 3502, 1), (Sum.inr 3506, 1), (Sum.inr 3533, 1), (Sum.inr 3540, 1), (Sum.inr 3582, 1), (Sum.inr 4084, -1)]

theorem sourceEq281 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm281 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA281 + difference 0 0) (sourceB281 + difference 0 0) sourceC281) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3540) := by
    have ha : (tripleCharges (sourceA281 + difference 0 0) (sourceB281 + difference 0 0) sourceC281) = raw6122 := by
      apply Matrix.ext; unfold tripleCharges sourceA281 sourceB281 sourceC281 difference raw6122; decide +kernel
    rw [ha]
    exact (canonical6122 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA281 + difference 0 1) (sourceB281 + difference 1 0) sourceC281) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3506) := by
    have ha : (tripleCharges (sourceA281 + difference 0 1) (sourceB281 + difference 1 0) sourceC281) = raw6435 := by
      apply Matrix.ext; unfold tripleCharges sourceA281 sourceB281 sourceC281 difference raw6435; decide +kernel
    rw [ha]
    exact (canonical6435 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA281 + difference 0 2) (sourceB281 + difference 2 0) sourceC281) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3502) := by
    have ha : (tripleCharges (sourceA281 + difference 0 2) (sourceB281 + difference 2 0) sourceC281) = raw6436 := by
      apply Matrix.ext; unfold tripleCharges sourceA281 sourceB281 sourceC281 difference raw6436; decide +kernel
    rw [ha]
    exact (canonical6436 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA281 + difference 0 3) (sourceB281 + difference 3 0) sourceC281) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3582) := by
    have ha : (tripleCharges (sourceA281 + difference 0 3) (sourceB281 + difference 3 0) sourceC281) = raw6104 := by
      apply Matrix.ext; unfold tripleCharges sourceA281 sourceB281 sourceC281 difference raw6104; decide +kernel
    rw [ha]
    exact (canonical6104 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA281 + difference 0 4) (sourceB281 + difference 4 0) sourceC281) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3533) := by
    have ha : (tripleCharges (sourceA281 + difference 0 4) (sourceB281 + difference 4 0) sourceC281) = raw6437 := by
      apply Matrix.ext; unfold tripleCharges sourceA281 sourceB281 sourceC281 difference raw6437; decide +kernel
    rw [ha]
    exact (canonical6437 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA281 + difference 0 5) (sourceB281 + difference 5 0) sourceC281) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2588) := by
    have ha : (tripleCharges (sourceA281 + difference 0 5) (sourceB281 + difference 5 0) sourceC281) = raw6438 := by
      apply Matrix.ext; unfold tripleCharges sourceA281 sourceB281 sourceC281 difference raw6438; decide +kernel
    rw [ha]
    exact (canonical6438 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA281 + sourceB281) sourceC281) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA281 + sourceB281) sourceC281) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA281 sourceB281 sourceC281 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA281 sourceB281 sourceC281
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm281, Integer.Sparse.eval]
  linarith only [hs]

def sourceA282 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceB282 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC282 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm282 : Integer.Sparse Master := [(Sum.inr 2033, 1), (Sum.inr 2035, 1), (Sum.inr 2039, 1), (Sum.inr 2054, 1), (Sum.inr 2278, 1), (Sum.inr 3540, 1), (Sum.inr 4084, -1)]

theorem sourceEq282 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm282 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA282 + difference 0 0) (sourceB282 + difference 0 0) sourceC282) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3540) := by
    have ha : (tripleCharges (sourceA282 + difference 0 0) (sourceB282 + difference 0 0) sourceC282) = raw6122 := by
      apply Matrix.ext; unfold tripleCharges sourceA282 sourceB282 sourceC282 difference raw6122; decide +kernel
    rw [ha]
    exact (canonical6122 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA282 + difference 1 0) (sourceB282 + difference 0 1) sourceC282) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2278) := by
    have ha : (tripleCharges (sourceA282 + difference 1 0) (sourceB282 + difference 0 1) sourceC282) = raw6439 := by
      apply Matrix.ext; unfold tripleCharges sourceA282 sourceB282 sourceC282 difference raw6439; decide +kernel
    rw [ha]
    exact (canonical6439 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA282 + difference 2 0) (sourceB282 + difference 0 2) sourceC282) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2033) := by
    have ha : (tripleCharges (sourceA282 + difference 2 0) (sourceB282 + difference 0 2) sourceC282) = raw6440 := by
      apply Matrix.ext; unfold tripleCharges sourceA282 sourceB282 sourceC282 difference raw6440; decide +kernel
    rw [ha]
    exact (canonical6440 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA282 + difference 3 0) (sourceB282 + difference 0 3) sourceC282) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2039) := by
    have ha : (tripleCharges (sourceA282 + difference 3 0) (sourceB282 + difference 0 3) sourceC282) = raw6441 := by
      apply Matrix.ext; unfold tripleCharges sourceA282 sourceB282 sourceC282 difference raw6441; decide +kernel
    rw [ha]
    exact (canonical6441 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA282 + difference 4 0) (sourceB282 + difference 0 4) sourceC282) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2035) := by
    have ha : (tripleCharges (sourceA282 + difference 4 0) (sourceB282 + difference 0 4) sourceC282) = raw6442 := by
      apply Matrix.ext; unfold tripleCharges sourceA282 sourceB282 sourceC282 difference raw6442; decide +kernel
    rw [ha]
    exact (canonical6442 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA282 + difference 5 0) (sourceB282 + difference 0 5) sourceC282) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2054) := by
    have ha : (tripleCharges (sourceA282 + difference 5 0) (sourceB282 + difference 0 5) sourceC282) = raw6443 := by
      apply Matrix.ext; unfold tripleCharges sourceA282 sourceB282 sourceC282 difference raw6443; decide +kernel
    rw [ha]
    exact (canonical6443 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA282 + sourceB282) sourceC282) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA282 + sourceB282) sourceC282) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA282 sourceB282 sourceC282 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA282 sourceB282 sourceC282
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm282, Integer.Sparse.eval]
  linarith only [hs]

def sourceA283 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceB283 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC283 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm283 : Integer.Sparse Master := [(Sum.inr 2278, 1), (Sum.inr 2781, 1), (Sum.inr 3540, 2), (Sum.inr 3632, 1), (Sum.inr 3633, 1), (Sum.inr 4084, -1)]

theorem sourceEq283 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm283 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA283 + difference 1 0) (sourceB283 + difference 0 1) sourceC283) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2278) := by
    have ha : (tripleCharges (sourceA283 + difference 1 0) (sourceB283 + difference 0 1) sourceC283) = raw6439 := by
      apply Matrix.ext; unfold tripleCharges sourceA283 sourceB283 sourceC283 difference raw6439; decide +kernel
    rw [ha]
    exact (canonical6439 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA283 + difference 1 1) (sourceB283 + difference 1 1) sourceC283) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3540) := by
    have ha : (tripleCharges (sourceA283 + difference 1 1) (sourceB283 + difference 1 1) sourceC283) = raw6122 := by
      apply Matrix.ext; unfold tripleCharges sourceA283 sourceB283 sourceC283 difference raw6122; decide +kernel
    rw [ha]
    exact (canonical6122 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA283 + difference 1 2) (sourceB283 + difference 2 1) sourceC283) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3540) := by
    have ha : (tripleCharges (sourceA283 + difference 1 2) (sourceB283 + difference 2 1) sourceC283) = raw6444 := by
      apply Matrix.ext; unfold tripleCharges sourceA283 sourceB283 sourceC283 difference raw6444; decide +kernel
    rw [ha]
    exact (canonical6444 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA283 + difference 1 3) (sourceB283 + difference 3 1) sourceC283) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3633) := by
    have ha : (tripleCharges (sourceA283 + difference 1 3) (sourceB283 + difference 3 1) sourceC283) = raw6121 := by
      apply Matrix.ext; unfold tripleCharges sourceA283 sourceB283 sourceC283 difference raw6121; decide +kernel
    rw [ha]
    exact (canonical6121 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA283 + difference 1 4) (sourceB283 + difference 4 1) sourceC283) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3632) := by
    have ha : (tripleCharges (sourceA283 + difference 1 4) (sourceB283 + difference 4 1) sourceC283) = raw6445 := by
      apply Matrix.ext; unfold tripleCharges sourceA283 sourceB283 sourceC283 difference raw6445; decide +kernel
    rw [ha]
    exact (canonical6445 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA283 + difference 1 5) (sourceB283 + difference 5 1) sourceC283) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2781) := by
    have ha : (tripleCharges (sourceA283 + difference 1 5) (sourceB283 + difference 5 1) sourceC283) = raw6446 := by
      apply Matrix.ext; unfold tripleCharges sourceA283 sourceB283 sourceC283 difference raw6446; decide +kernel
    rw [ha]
    exact (canonical6446 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA283 + sourceB283) sourceC283) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA283 + sourceB283) sourceC283) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA283 sourceB283 sourceC283 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA283 sourceB283 sourceC283
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm283, Integer.Sparse.eval]
  linarith only [hs]

def sourceA284 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceB284 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC284 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm284 : Integer.Sparse Master := [(Sum.inr 2978, 1), (Sum.inr 3381, 1), (Sum.inr 3383, 1), (Sum.inr 3392, 1), (Sum.inr 3506, 1), (Sum.inr 3540, 1), (Sum.inr 4084, -1)]

theorem sourceEq284 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm284 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA284 + difference 0 1) (sourceB284 + difference 1 0) sourceC284) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3506) := by
    have ha : (tripleCharges (sourceA284 + difference 0 1) (sourceB284 + difference 1 0) sourceC284) = raw6435 := by
      apply Matrix.ext; unfold tripleCharges sourceA284 sourceB284 sourceC284 difference raw6435; decide +kernel
    rw [ha]
    exact (canonical6435 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA284 + difference 1 1) (sourceB284 + difference 1 1) sourceC284) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3540) := by
    have ha : (tripleCharges (sourceA284 + difference 1 1) (sourceB284 + difference 1 1) sourceC284) = raw6122 := by
      apply Matrix.ext; unfold tripleCharges sourceA284 sourceB284 sourceC284 difference raw6122; decide +kernel
    rw [ha]
    exact (canonical6122 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA284 + difference 2 1) (sourceB284 + difference 1 2) sourceC284) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3381) := by
    have ha : (tripleCharges (sourceA284 + difference 2 1) (sourceB284 + difference 1 2) sourceC284) = raw6447 := by
      apply Matrix.ext; unfold tripleCharges sourceA284 sourceB284 sourceC284 difference raw6447; decide +kernel
    rw [ha]
    exact (canonical6447 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA284 + difference 3 1) (sourceB284 + difference 1 3) sourceC284) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3383) := by
    have ha : (tripleCharges (sourceA284 + difference 3 1) (sourceB284 + difference 1 3) sourceC284) = raw6448 := by
      apply Matrix.ext; unfold tripleCharges sourceA284 sourceB284 sourceC284 difference raw6448; decide +kernel
    rw [ha]
    exact (canonical6448 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA284 + difference 4 1) (sourceB284 + difference 1 4) sourceC284) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2978) := by
    have ha : (tripleCharges (sourceA284 + difference 4 1) (sourceB284 + difference 1 4) sourceC284) = raw6107 := by
      apply Matrix.ext; unfold tripleCharges sourceA284 sourceB284 sourceC284 difference raw6107; decide +kernel
    rw [ha]
    exact (canonical6107 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA284 + difference 5 1) (sourceB284 + difference 1 5) sourceC284) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3392) := by
    have ha : (tripleCharges (sourceA284 + difference 5 1) (sourceB284 + difference 1 5) sourceC284) = raw6449 := by
      apply Matrix.ext; unfold tripleCharges sourceA284 sourceB284 sourceC284 difference raw6449; decide +kernel
    rw [ha]
    exact (canonical6449 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA284 + sourceB284) sourceC284) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA284 + sourceB284) sourceC284) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA284 sourceB284 sourceC284 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA284 sourceB284 sourceC284
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm284, Integer.Sparse.eval]
  linarith only [hs]

def sourceA285 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceB285 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC285 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm285 : Integer.Sparse Master := [(Sum.inr 2033, 1), (Sum.inr 2586, 1), (Sum.inr 3381, 1), (Sum.inr 3539, 1), (Sum.inr 3540, 2), (Sum.inr 4084, -1)]

theorem sourceEq285 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm285 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA285 + difference 2 0) (sourceB285 + difference 0 2) sourceC285) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2033) := by
    have ha : (tripleCharges (sourceA285 + difference 2 0) (sourceB285 + difference 0 2) sourceC285) = raw6440 := by
      apply Matrix.ext; unfold tripleCharges sourceA285 sourceB285 sourceC285 difference raw6440; decide +kernel
    rw [ha]
    exact (canonical6440 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA285 + difference 2 1) (sourceB285 + difference 1 2) sourceC285) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3381) := by
    have ha : (tripleCharges (sourceA285 + difference 2 1) (sourceB285 + difference 1 2) sourceC285) = raw6447 := by
      apply Matrix.ext; unfold tripleCharges sourceA285 sourceB285 sourceC285 difference raw6447; decide +kernel
    rw [ha]
    exact (canonical6447 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA285 + difference 2 2) (sourceB285 + difference 2 2) sourceC285) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3540) := by
    have ha : (tripleCharges (sourceA285 + difference 2 2) (sourceB285 + difference 2 2) sourceC285) = raw6122 := by
      apply Matrix.ext; unfold tripleCharges sourceA285 sourceB285 sourceC285 difference raw6122; decide +kernel
    rw [ha]
    exact (canonical6122 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA285 + difference 2 3) (sourceB285 + difference 3 2) sourceC285) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3540) := by
    have ha : (tripleCharges (sourceA285 + difference 2 3) (sourceB285 + difference 3 2) sourceC285) = raw6112 := by
      apply Matrix.ext; unfold tripleCharges sourceA285 sourceB285 sourceC285 difference raw6112; decide +kernel
    rw [ha]
    exact (canonical6112 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA285 + difference 2 4) (sourceB285 + difference 4 2) sourceC285) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3539) := by
    have ha : (tripleCharges (sourceA285 + difference 2 4) (sourceB285 + difference 4 2) sourceC285) = raw6450 := by
      apply Matrix.ext; unfold tripleCharges sourceA285 sourceB285 sourceC285 difference raw6450; decide +kernel
    rw [ha]
    exact (canonical6450 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA285 + difference 2 5) (sourceB285 + difference 5 2) sourceC285) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2586) := by
    have ha : (tripleCharges (sourceA285 + difference 2 5) (sourceB285 + difference 5 2) sourceC285) = raw6451 := by
      apply Matrix.ext; unfold tripleCharges sourceA285 sourceB285 sourceC285 difference raw6451; decide +kernel
    rw [ha]
    exact (canonical6451 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA285 + sourceB285) sourceC285) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA285 + sourceB285) sourceC285) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA285 sourceB285 sourceC285 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA285 sourceB285 sourceC285
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm285, Integer.Sparse.eval]
  linarith only [hs]

def sourceA286 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceB286 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC286 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm286 : Integer.Sparse Master := [(Sum.inr 2973, 1), (Sum.inr 3490, 1), (Sum.inr 3494, 1), (Sum.inr 3502, 1), (Sum.inr 3540, 2), (Sum.inr 4084, -1)]

theorem sourceEq286 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm286 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA286 + difference 0 2) (sourceB286 + difference 2 0) sourceC286) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3502) := by
    have ha : (tripleCharges (sourceA286 + difference 0 2) (sourceB286 + difference 2 0) sourceC286) = raw6436 := by
      apply Matrix.ext; unfold tripleCharges sourceA286 sourceB286 sourceC286 difference raw6436; decide +kernel
    rw [ha]
    exact (canonical6436 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA286 + difference 1 2) (sourceB286 + difference 2 1) sourceC286) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3540) := by
    have ha : (tripleCharges (sourceA286 + difference 1 2) (sourceB286 + difference 2 1) sourceC286) = raw6444 := by
      apply Matrix.ext; unfold tripleCharges sourceA286 sourceB286 sourceC286 difference raw6444; decide +kernel
    rw [ha]
    exact (canonical6444 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA286 + difference 2 2) (sourceB286 + difference 2 2) sourceC286) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3540) := by
    have ha : (tripleCharges (sourceA286 + difference 2 2) (sourceB286 + difference 2 2) sourceC286) = raw6122 := by
      apply Matrix.ext; unfold tripleCharges sourceA286 sourceB286 sourceC286 difference raw6122; decide +kernel
    rw [ha]
    exact (canonical6122 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA286 + difference 3 2) (sourceB286 + difference 2 3) sourceC286) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3490) := by
    have ha : (tripleCharges (sourceA286 + difference 3 2) (sourceB286 + difference 2 3) sourceC286) = raw6452 := by
      apply Matrix.ext; unfold tripleCharges sourceA286 sourceB286 sourceC286 difference raw6452; decide +kernel
    rw [ha]
    exact (canonical6452 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA286 + difference 4 2) (sourceB286 + difference 2 4) sourceC286) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2973) := by
    have ha : (tripleCharges (sourceA286 + difference 4 2) (sourceB286 + difference 2 4) sourceC286) = raw6115 := by
      apply Matrix.ext; unfold tripleCharges sourceA286 sourceB286 sourceC286 difference raw6115; decide +kernel
    rw [ha]
    exact (canonical6115 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA286 + difference 5 2) (sourceB286 + difference 2 5) sourceC286) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3494) := by
    have ha : (tripleCharges (sourceA286 + difference 5 2) (sourceB286 + difference 2 5) sourceC286) = raw6453 := by
      apply Matrix.ext; unfold tripleCharges sourceA286 sourceB286 sourceC286 difference raw6453; decide +kernel
    rw [ha]
    exact (canonical6453 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA286 + sourceB286) sourceC286) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA286 + sourceB286) sourceC286) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA286 sourceB286 sourceC286 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA286 sourceB286 sourceC286
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm286, Integer.Sparse.eval]
  linarith only [hs]

def sourceA287 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceB287 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC287 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm287 : Integer.Sparse Master := [(Sum.inr 2039, 1), (Sum.inr 2592, 1), (Sum.inr 3383, 1), (Sum.inr 3490, 1), (Sum.inr 3540, 1), (Sum.inr 3541, 1), (Sum.inr 4084, -1)]

theorem sourceEq287 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm287 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA287 + difference 3 0) (sourceB287 + difference 0 3) sourceC287) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2039) := by
    have ha : (tripleCharges (sourceA287 + difference 3 0) (sourceB287 + difference 0 3) sourceC287) = raw6441 := by
      apply Matrix.ext; unfold tripleCharges sourceA287 sourceB287 sourceC287 difference raw6441; decide +kernel
    rw [ha]
    exact (canonical6441 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA287 + difference 3 1) (sourceB287 + difference 1 3) sourceC287) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3383) := by
    have ha : (tripleCharges (sourceA287 + difference 3 1) (sourceB287 + difference 1 3) sourceC287) = raw6448 := by
      apply Matrix.ext; unfold tripleCharges sourceA287 sourceB287 sourceC287 difference raw6448; decide +kernel
    rw [ha]
    exact (canonical6448 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA287 + difference 3 2) (sourceB287 + difference 2 3) sourceC287) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3490) := by
    have ha : (tripleCharges (sourceA287 + difference 3 2) (sourceB287 + difference 2 3) sourceC287) = raw6452 := by
      apply Matrix.ext; unfold tripleCharges sourceA287 sourceB287 sourceC287 difference raw6452; decide +kernel
    rw [ha]
    exact (canonical6452 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA287 + difference 3 3) (sourceB287 + difference 3 3) sourceC287) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3540) := by
    have ha : (tripleCharges (sourceA287 + difference 3 3) (sourceB287 + difference 3 3) sourceC287) = raw6122 := by
      apply Matrix.ext; unfold tripleCharges sourceA287 sourceB287 sourceC287 difference raw6122; decide +kernel
    rw [ha]
    exact (canonical6122 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA287 + difference 3 4) (sourceB287 + difference 4 3) sourceC287) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3541) := by
    have ha : (tripleCharges (sourceA287 + difference 3 4) (sourceB287 + difference 4 3) sourceC287) = raw6454 := by
      apply Matrix.ext; unfold tripleCharges sourceA287 sourceB287 sourceC287 difference raw6454; decide +kernel
    rw [ha]
    exact (canonical6454 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA287 + difference 3 5) (sourceB287 + difference 5 3) sourceC287) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2592) := by
    have ha : (tripleCharges (sourceA287 + difference 3 5) (sourceB287 + difference 5 3) sourceC287) = raw6455 := by
      apply Matrix.ext; unfold tripleCharges sourceA287 sourceB287 sourceC287 difference raw6455; decide +kernel
    rw [ha]
    exact (canonical6455 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA287 + sourceB287) sourceC287) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA287 + sourceB287) sourceC287) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA287 sourceB287 sourceC287 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA287 sourceB287 sourceC287
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm287, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
