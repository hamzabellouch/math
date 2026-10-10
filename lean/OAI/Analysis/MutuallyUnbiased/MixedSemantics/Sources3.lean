import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical35

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA96 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB96 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC96 : Charge := ![2, 1, 0, -1, -1, -1]
def sourceForm96 : Integer.Sparse Master := [(Sum.inr 1206, 1), (Sum.inr 1209, 1), (Sum.inr 1217, 2), (Sum.inr 1249, 1), (Sum.inr 2712, 1), (Sum.inr 4091, -1)]

theorem sourceEq96 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm96 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA96 + difference 0 0) (sourceB96 + difference 0 0) sourceC96) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2712) := by
    have ha : (tripleCharges (sourceA96 + difference 0 0) (sourceB96 + difference 0 0) sourceC96) = raw4200 := by
      apply Matrix.ext; unfold tripleCharges sourceA96 sourceB96 sourceC96 difference raw4200; decide +kernel
    rw [ha]
    exact (canonical4200 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA96 + difference 1 0) (sourceB96 + difference 0 1) sourceC96) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1249) := by
    have ha : (tripleCharges (sourceA96 + difference 1 0) (sourceB96 + difference 0 1) sourceC96) = raw4207 := by
      apply Matrix.ext; unfold tripleCharges sourceA96 sourceB96 sourceC96 difference raw4207; decide +kernel
    rw [ha]
    exact (canonical4207 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA96 + difference 2 0) (sourceB96 + difference 0 2) sourceC96) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1206) := by
    have ha : (tripleCharges (sourceA96 + difference 2 0) (sourceB96 + difference 0 2) sourceC96) = raw4208 := by
      apply Matrix.ext; unfold tripleCharges sourceA96 sourceB96 sourceC96 difference raw4208; decide +kernel
    rw [ha]
    exact (canonical4208 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA96 + difference 3 0) (sourceB96 + difference 0 3) sourceC96) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1217) := by
    have ha : (tripleCharges (sourceA96 + difference 3 0) (sourceB96 + difference 0 3) sourceC96) = raw4209 := by
      apply Matrix.ext; unfold tripleCharges sourceA96 sourceB96 sourceC96 difference raw4209; decide +kernel
    rw [ha]
    exact (canonical4209 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA96 + difference 4 0) (sourceB96 + difference 0 4) sourceC96) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1217) := by
    have ha : (tripleCharges (sourceA96 + difference 4 0) (sourceB96 + difference 0 4) sourceC96) = raw4210 := by
      apply Matrix.ext; unfold tripleCharges sourceA96 sourceB96 sourceC96 difference raw4210; decide +kernel
    rw [ha]
    exact (canonical4210 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA96 + difference 5 0) (sourceB96 + difference 0 5) sourceC96) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1209) := by
    have ha : (tripleCharges (sourceA96 + difference 5 0) (sourceB96 + difference 0 5) sourceC96) = raw4211 := by
      apply Matrix.ext; unfold tripleCharges sourceA96 sourceB96 sourceC96 difference raw4211; decide +kernel
    rw [ha]
    exact (canonical4211 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA96 + sourceB96) sourceC96) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA96 + sourceB96) sourceC96) = raw4206 := by
      apply Matrix.ext; unfold doubleCharges sourceA96 sourceB96 sourceC96 raw4206; decide +kernel
    rw [ha]
    exact (canonical4206 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA96 sourceB96 sourceC96
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm96, Integer.Sparse.eval]
  linarith only [hs]

def sourceA97 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB97 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC97 : Charge := ![2, 1, 0, -1, -1, -1]
def sourceForm97 : Integer.Sparse Master := [(Sum.inr 1249, 1), (Sum.inr 2562, 1), (Sum.inr 2624, 2), (Sum.inr 2712, 1), (Sum.inr 2751, 1), (Sum.inr 4091, -1)]

theorem sourceEq97 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm97 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA97 + difference 1 0) (sourceB97 + difference 0 1) sourceC97) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1249) := by
    have ha : (tripleCharges (sourceA97 + difference 1 0) (sourceB97 + difference 0 1) sourceC97) = raw4207 := by
      apply Matrix.ext; unfold tripleCharges sourceA97 sourceB97 sourceC97 difference raw4207; decide +kernel
    rw [ha]
    exact (canonical4207 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA97 + difference 1 1) (sourceB97 + difference 1 1) sourceC97) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2712) := by
    have ha : (tripleCharges (sourceA97 + difference 1 1) (sourceB97 + difference 1 1) sourceC97) = raw4200 := by
      apply Matrix.ext; unfold tripleCharges sourceA97 sourceB97 sourceC97 difference raw4200; decide +kernel
    rw [ha]
    exact (canonical4200 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA97 + difference 1 2) (sourceB97 + difference 2 1) sourceC97) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2562) := by
    have ha : (tripleCharges (sourceA97 + difference 1 2) (sourceB97 + difference 2 1) sourceC97) = raw4212 := by
      apply Matrix.ext; unfold tripleCharges sourceA97 sourceB97 sourceC97 difference raw4212; decide +kernel
    rw [ha]
    exact (canonical4212 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA97 + difference 1 3) (sourceB97 + difference 3 1) sourceC97) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2624) := by
    have ha : (tripleCharges (sourceA97 + difference 1 3) (sourceB97 + difference 3 1) sourceC97) = raw4213 := by
      apply Matrix.ext; unfold tripleCharges sourceA97 sourceB97 sourceC97 difference raw4213; decide +kernel
    rw [ha]
    exact (canonical4213 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA97 + difference 1 4) (sourceB97 + difference 4 1) sourceC97) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2624) := by
    have ha : (tripleCharges (sourceA97 + difference 1 4) (sourceB97 + difference 4 1) sourceC97) = raw4214 := by
      apply Matrix.ext; unfold tripleCharges sourceA97 sourceB97 sourceC97 difference raw4214; decide +kernel
    rw [ha]
    exact (canonical4214 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA97 + difference 1 5) (sourceB97 + difference 5 1) sourceC97) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2751) := by
    have ha : (tripleCharges (sourceA97 + difference 1 5) (sourceB97 + difference 5 1) sourceC97) = raw4215 := by
      apply Matrix.ext; unfold tripleCharges sourceA97 sourceB97 sourceC97 difference raw4215; decide +kernel
    rw [ha]
    exact (canonical4215 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA97 + sourceB97) sourceC97) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA97 + sourceB97) sourceC97) = raw4206 := by
      apply Matrix.ext; unfold doubleCharges sourceA97 sourceB97 sourceC97 raw4206; decide +kernel
    rw [ha]
    exact (canonical4206 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA97 sourceB97 sourceC97
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm97, Integer.Sparse.eval]
  linarith only [hs]

def sourceA98 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB98 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC98 : Charge := ![2, 1, 0, -1, -1, -1]
def sourceForm98 : Integer.Sparse Master := [(Sum.inr 1388, 1), (Sum.inr 2470, 1), (Sum.inr 2485, 2), (Sum.inr 2712, 1), (Sum.inr 3077, 1), (Sum.inr 4091, -1)]

theorem sourceEq98 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm98 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA98 + difference 0 1) (sourceB98 + difference 1 0) sourceC98) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3077) := by
    have ha : (tripleCharges (sourceA98 + difference 0 1) (sourceB98 + difference 1 0) sourceC98) = raw4201 := by
      apply Matrix.ext; unfold tripleCharges sourceA98 sourceB98 sourceC98 difference raw4201; decide +kernel
    rw [ha]
    exact (canonical4201 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA98 + difference 1 1) (sourceB98 + difference 1 1) sourceC98) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2712) := by
    have ha : (tripleCharges (sourceA98 + difference 1 1) (sourceB98 + difference 1 1) sourceC98) = raw4200 := by
      apply Matrix.ext; unfold tripleCharges sourceA98 sourceB98 sourceC98 difference raw4200; decide +kernel
    rw [ha]
    exact (canonical4200 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA98 + difference 2 1) (sourceB98 + difference 1 2) sourceC98) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2470) := by
    have ha : (tripleCharges (sourceA98 + difference 2 1) (sourceB98 + difference 1 2) sourceC98) = raw4216 := by
      apply Matrix.ext; unfold tripleCharges sourceA98 sourceB98 sourceC98 difference raw4216; decide +kernel
    rw [ha]
    exact (canonical4216 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA98 + difference 3 1) (sourceB98 + difference 1 3) sourceC98) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2485) := by
    have ha : (tripleCharges (sourceA98 + difference 3 1) (sourceB98 + difference 1 3) sourceC98) = raw4217 := by
      apply Matrix.ext; unfold tripleCharges sourceA98 sourceB98 sourceC98 difference raw4217; decide +kernel
    rw [ha]
    exact (canonical4217 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA98 + difference 4 1) (sourceB98 + difference 1 4) sourceC98) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2485) := by
    have ha : (tripleCharges (sourceA98 + difference 4 1) (sourceB98 + difference 1 4) sourceC98) = raw4218 := by
      apply Matrix.ext; unfold tripleCharges sourceA98 sourceB98 sourceC98 difference raw4218; decide +kernel
    rw [ha]
    exact (canonical4218 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA98 + difference 5 1) (sourceB98 + difference 1 5) sourceC98) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1388) := by
    have ha : (tripleCharges (sourceA98 + difference 5 1) (sourceB98 + difference 1 5) sourceC98) = raw4219 := by
      apply Matrix.ext; unfold tripleCharges sourceA98 sourceB98 sourceC98 difference raw4219; decide +kernel
    rw [ha]
    exact (canonical4219 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA98 + sourceB98) sourceC98) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA98 + sourceB98) sourceC98) = raw4206 := by
      apply Matrix.ext; unfold doubleCharges sourceA98 sourceB98 sourceC98 raw4206; decide +kernel
    rw [ha]
    exact (canonical4206 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA98 sourceB98 sourceC98
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm98, Integer.Sparse.eval]
  linarith only [hs]

def sourceA99 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB99 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC99 : Charge := ![2, 1, 0, -1, -1, -1]
def sourceForm99 : Integer.Sparse Master := [(Sum.inr 1206, 1), (Sum.inr 2470, 1), (Sum.inr 2610, 2), (Sum.inr 2709, 1), (Sum.inr 2712, 1), (Sum.inr 4091, -1)]

theorem sourceEq99 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm99 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA99 + difference 2 0) (sourceB99 + difference 0 2) sourceC99) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1206) := by
    have ha : (tripleCharges (sourceA99 + difference 2 0) (sourceB99 + difference 0 2) sourceC99) = raw4208 := by
      apply Matrix.ext; unfold tripleCharges sourceA99 sourceB99 sourceC99 difference raw4208; decide +kernel
    rw [ha]
    exact (canonical4208 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA99 + difference 2 1) (sourceB99 + difference 1 2) sourceC99) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2470) := by
    have ha : (tripleCharges (sourceA99 + difference 2 1) (sourceB99 + difference 1 2) sourceC99) = raw4216 := by
      apply Matrix.ext; unfold tripleCharges sourceA99 sourceB99 sourceC99 difference raw4216; decide +kernel
    rw [ha]
    exact (canonical4216 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA99 + difference 2 2) (sourceB99 + difference 2 2) sourceC99) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2712) := by
    have ha : (tripleCharges (sourceA99 + difference 2 2) (sourceB99 + difference 2 2) sourceC99) = raw4200 := by
      apply Matrix.ext; unfold tripleCharges sourceA99 sourceB99 sourceC99 difference raw4200; decide +kernel
    rw [ha]
    exact (canonical4200 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA99 + difference 2 3) (sourceB99 + difference 3 2) sourceC99) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2610) := by
    have ha : (tripleCharges (sourceA99 + difference 2 3) (sourceB99 + difference 3 2) sourceC99) = raw4220 := by
      apply Matrix.ext; unfold tripleCharges sourceA99 sourceB99 sourceC99 difference raw4220; decide +kernel
    rw [ha]
    exact (canonical4220 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA99 + difference 2 4) (sourceB99 + difference 4 2) sourceC99) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2610) := by
    have ha : (tripleCharges (sourceA99 + difference 2 4) (sourceB99 + difference 4 2) sourceC99) = raw4221 := by
      apply Matrix.ext; unfold tripleCharges sourceA99 sourceB99 sourceC99 difference raw4221; decide +kernel
    rw [ha]
    exact (canonical4221 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA99 + difference 2 5) (sourceB99 + difference 5 2) sourceC99) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2709) := by
    have ha : (tripleCharges (sourceA99 + difference 2 5) (sourceB99 + difference 5 2) sourceC99) = raw4222 := by
      apply Matrix.ext; unfold tripleCharges sourceA99 sourceB99 sourceC99 difference raw4222; decide +kernel
    rw [ha]
    exact (canonical4222 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA99 + sourceB99) sourceC99) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA99 + sourceB99) sourceC99) = raw4206 := by
      apply Matrix.ext; unfold doubleCharges sourceA99 sourceB99 sourceC99 raw4206; decide +kernel
    rw [ha]
    exact (canonical4206 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA99 sourceB99 sourceC99
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm99, Integer.Sparse.eval]
  linarith only [hs]

def sourceA100 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB100 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC100 : Charge := ![2, 1, 0, -1, -1, -1]
def sourceForm100 : Integer.Sparse Master := [(Sum.inr 1378, 1), (Sum.inr 2543, 2), (Sum.inr 2562, 1), (Sum.inr 2712, 1), (Sum.inr 3064, 1), (Sum.inr 4091, -1)]

theorem sourceEq100 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm100 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA100 + difference 0 2) (sourceB100 + difference 2 0) sourceC100) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3064) := by
    have ha : (tripleCharges (sourceA100 + difference 0 2) (sourceB100 + difference 2 0) sourceC100) = raw4202 := by
      apply Matrix.ext; unfold tripleCharges sourceA100 sourceB100 sourceC100 difference raw4202; decide +kernel
    rw [ha]
    exact (canonical4202 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA100 + difference 1 2) (sourceB100 + difference 2 1) sourceC100) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2562) := by
    have ha : (tripleCharges (sourceA100 + difference 1 2) (sourceB100 + difference 2 1) sourceC100) = raw4212 := by
      apply Matrix.ext; unfold tripleCharges sourceA100 sourceB100 sourceC100 difference raw4212; decide +kernel
    rw [ha]
    exact (canonical4212 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA100 + difference 2 2) (sourceB100 + difference 2 2) sourceC100) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2712) := by
    have ha : (tripleCharges (sourceA100 + difference 2 2) (sourceB100 + difference 2 2) sourceC100) = raw4200 := by
      apply Matrix.ext; unfold tripleCharges sourceA100 sourceB100 sourceC100 difference raw4200; decide +kernel
    rw [ha]
    exact (canonical4200 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA100 + difference 3 2) (sourceB100 + difference 2 3) sourceC100) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2543) := by
    have ha : (tripleCharges (sourceA100 + difference 3 2) (sourceB100 + difference 2 3) sourceC100) = raw4223 := by
      apply Matrix.ext; unfold tripleCharges sourceA100 sourceB100 sourceC100 difference raw4223; decide +kernel
    rw [ha]
    exact (canonical4223 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA100 + difference 4 2) (sourceB100 + difference 2 4) sourceC100) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2543) := by
    have ha : (tripleCharges (sourceA100 + difference 4 2) (sourceB100 + difference 2 4) sourceC100) = raw4224 := by
      apply Matrix.ext; unfold tripleCharges sourceA100 sourceB100 sourceC100 difference raw4224; decide +kernel
    rw [ha]
    exact (canonical4224 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA100 + difference 5 2) (sourceB100 + difference 2 5) sourceC100) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1378) := by
    have ha : (tripleCharges (sourceA100 + difference 5 2) (sourceB100 + difference 2 5) sourceC100) = raw4225 := by
      apply Matrix.ext; unfold tripleCharges sourceA100 sourceB100 sourceC100 difference raw4225; decide +kernel
    rw [ha]
    exact (canonical4225 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA100 + sourceB100) sourceC100) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA100 + sourceB100) sourceC100) = raw4206 := by
      apply Matrix.ext; unfold doubleCharges sourceA100 sourceB100 sourceC100 raw4206; decide +kernel
    rw [ha]
    exact (canonical4206 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA100 sourceB100 sourceC100
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm100, Integer.Sparse.eval]
  linarith only [hs]

def sourceA101 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB101 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC101 : Charge := ![2, 1, 0, -1, -1, -1]
def sourceForm101 : Integer.Sparse Master := [(Sum.inr 1217, 1), (Sum.inr 2485, 1), (Sum.inr 2543, 1), (Sum.inr 2618, 1), (Sum.inr 2712, 1), (Sum.inr 2723, 1), (Sum.inr 4091, -1)]

theorem sourceEq101 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm101 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA101 + difference 3 0) (sourceB101 + difference 0 3) sourceC101) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1217) := by
    have ha : (tripleCharges (sourceA101 + difference 3 0) (sourceB101 + difference 0 3) sourceC101) = raw4209 := by
      apply Matrix.ext; unfold tripleCharges sourceA101 sourceB101 sourceC101 difference raw4209; decide +kernel
    rw [ha]
    exact (canonical4209 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA101 + difference 3 1) (sourceB101 + difference 1 3) sourceC101) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2485) := by
    have ha : (tripleCharges (sourceA101 + difference 3 1) (sourceB101 + difference 1 3) sourceC101) = raw4217 := by
      apply Matrix.ext; unfold tripleCharges sourceA101 sourceB101 sourceC101 difference raw4217; decide +kernel
    rw [ha]
    exact (canonical4217 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA101 + difference 3 2) (sourceB101 + difference 2 3) sourceC101) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2543) := by
    have ha : (tripleCharges (sourceA101 + difference 3 2) (sourceB101 + difference 2 3) sourceC101) = raw4223 := by
      apply Matrix.ext; unfold tripleCharges sourceA101 sourceB101 sourceC101 difference raw4223; decide +kernel
    rw [ha]
    exact (canonical4223 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA101 + difference 3 3) (sourceB101 + difference 3 3) sourceC101) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2712) := by
    have ha : (tripleCharges (sourceA101 + difference 3 3) (sourceB101 + difference 3 3) sourceC101) = raw4200 := by
      apply Matrix.ext; unfold tripleCharges sourceA101 sourceB101 sourceC101 difference raw4200; decide +kernel
    rw [ha]
    exact (canonical4200 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA101 + difference 3 4) (sourceB101 + difference 4 3) sourceC101) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2618) := by
    have ha : (tripleCharges (sourceA101 + difference 3 4) (sourceB101 + difference 4 3) sourceC101) = raw4226 := by
      apply Matrix.ext; unfold tripleCharges sourceA101 sourceB101 sourceC101 difference raw4226; decide +kernel
    rw [ha]
    exact (canonical4226 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA101 + difference 3 5) (sourceB101 + difference 5 3) sourceC101) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA101 + difference 3 5) (sourceB101 + difference 5 3) sourceC101) = raw4227 := by
      apply Matrix.ext; unfold tripleCharges sourceA101 sourceB101 sourceC101 difference raw4227; decide +kernel
    rw [ha]
    exact (canonical4227 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA101 + sourceB101) sourceC101) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA101 + sourceB101) sourceC101) = raw4206 := by
      apply Matrix.ext; unfold doubleCharges sourceA101 sourceB101 sourceC101 raw4206; decide +kernel
    rw [ha]
    exact (canonical4206 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA101 sourceB101 sourceC101
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm101, Integer.Sparse.eval]
  linarith only [hs]

def sourceA102 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB102 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC102 : Charge := ![2, 1, 0, -1, -1, -1]
def sourceForm102 : Integer.Sparse Master := [(Sum.inr 1394, 1), (Sum.inr 2610, 1), (Sum.inr 2618, 1), (Sum.inr 2624, 1), (Sum.inr 2712, 1), (Sum.inr 3086, 1), (Sum.inr 4091, -1)]

theorem sourceEq102 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm102 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA102 + difference 0 3) (sourceB102 + difference 3 0) sourceC102) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3086) := by
    have ha : (tripleCharges (sourceA102 + difference 0 3) (sourceB102 + difference 3 0) sourceC102) = raw4203 := by
      apply Matrix.ext; unfold tripleCharges sourceA102 sourceB102 sourceC102 difference raw4203; decide +kernel
    rw [ha]
    exact (canonical4203 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA102 + difference 1 3) (sourceB102 + difference 3 1) sourceC102) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2624) := by
    have ha : (tripleCharges (sourceA102 + difference 1 3) (sourceB102 + difference 3 1) sourceC102) = raw4213 := by
      apply Matrix.ext; unfold tripleCharges sourceA102 sourceB102 sourceC102 difference raw4213; decide +kernel
    rw [ha]
    exact (canonical4213 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA102 + difference 2 3) (sourceB102 + difference 3 2) sourceC102) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2610) := by
    have ha : (tripleCharges (sourceA102 + difference 2 3) (sourceB102 + difference 3 2) sourceC102) = raw4220 := by
      apply Matrix.ext; unfold tripleCharges sourceA102 sourceB102 sourceC102 difference raw4220; decide +kernel
    rw [ha]
    exact (canonical4220 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA102 + difference 3 3) (sourceB102 + difference 3 3) sourceC102) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2712) := by
    have ha : (tripleCharges (sourceA102 + difference 3 3) (sourceB102 + difference 3 3) sourceC102) = raw4200 := by
      apply Matrix.ext; unfold tripleCharges sourceA102 sourceB102 sourceC102 difference raw4200; decide +kernel
    rw [ha]
    exact (canonical4200 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA102 + difference 4 3) (sourceB102 + difference 3 4) sourceC102) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2618) := by
    have ha : (tripleCharges (sourceA102 + difference 4 3) (sourceB102 + difference 3 4) sourceC102) = raw4228 := by
      apply Matrix.ext; unfold tripleCharges sourceA102 sourceB102 sourceC102 difference raw4228; decide +kernel
    rw [ha]
    exact (canonical4228 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA102 + difference 5 3) (sourceB102 + difference 3 5) sourceC102) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1394) := by
    have ha : (tripleCharges (sourceA102 + difference 5 3) (sourceB102 + difference 3 5) sourceC102) = raw4229 := by
      apply Matrix.ext; unfold tripleCharges sourceA102 sourceB102 sourceC102 difference raw4229; decide +kernel
    rw [ha]
    exact (canonical4229 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA102 + sourceB102) sourceC102) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA102 + sourceB102) sourceC102) = raw4206 := by
      apply Matrix.ext; unfold doubleCharges sourceA102 sourceB102 sourceC102 raw4206; decide +kernel
    rw [ha]
    exact (canonical4206 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA102 sourceB102 sourceC102
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm102, Integer.Sparse.eval]
  linarith only [hs]

def sourceA103 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB103 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceC103 : Charge := ![2, 1, 0, -1, -1, -1]
def sourceForm103 : Integer.Sparse Master := [(Sum.inr 1209, 1), (Sum.inr 1378, 1), (Sum.inr 1388, 1), (Sum.inr 1394, 2), (Sum.inr 2712, 1), (Sum.inr 4091, -1)]

theorem sourceEq103 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm103 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA103 + difference 5 0) (sourceB103 + difference 0 5) sourceC103) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1209) := by
    have ha : (tripleCharges (sourceA103 + difference 5 0) (sourceB103 + difference 0 5) sourceC103) = raw4211 := by
      apply Matrix.ext; unfold tripleCharges sourceA103 sourceB103 sourceC103 difference raw4211; decide +kernel
    rw [ha]
    exact (canonical4211 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA103 + difference 5 1) (sourceB103 + difference 1 5) sourceC103) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1388) := by
    have ha : (tripleCharges (sourceA103 + difference 5 1) (sourceB103 + difference 1 5) sourceC103) = raw4219 := by
      apply Matrix.ext; unfold tripleCharges sourceA103 sourceB103 sourceC103 difference raw4219; decide +kernel
    rw [ha]
    exact (canonical4219 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA103 + difference 5 2) (sourceB103 + difference 2 5) sourceC103) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1378) := by
    have ha : (tripleCharges (sourceA103 + difference 5 2) (sourceB103 + difference 2 5) sourceC103) = raw4225 := by
      apply Matrix.ext; unfold tripleCharges sourceA103 sourceB103 sourceC103 difference raw4225; decide +kernel
    rw [ha]
    exact (canonical4225 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA103 + difference 5 3) (sourceB103 + difference 3 5) sourceC103) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1394) := by
    have ha : (tripleCharges (sourceA103 + difference 5 3) (sourceB103 + difference 3 5) sourceC103) = raw4229 := by
      apply Matrix.ext; unfold tripleCharges sourceA103 sourceB103 sourceC103 difference raw4229; decide +kernel
    rw [ha]
    exact (canonical4229 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA103 + difference 5 4) (sourceB103 + difference 4 5) sourceC103) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1394) := by
    have ha : (tripleCharges (sourceA103 + difference 5 4) (sourceB103 + difference 4 5) sourceC103) = raw4230 := by
      apply Matrix.ext; unfold tripleCharges sourceA103 sourceB103 sourceC103 difference raw4230; decide +kernel
    rw [ha]
    exact (canonical4230 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA103 + difference 5 5) (sourceB103 + difference 5 5) sourceC103) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2712) := by
    have ha : (tripleCharges (sourceA103 + difference 5 5) (sourceB103 + difference 5 5) sourceC103) = raw4200 := by
      apply Matrix.ext; unfold tripleCharges sourceA103 sourceB103 sourceC103 difference raw4200; decide +kernel
    rw [ha]
    exact (canonical4200 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA103 + sourceB103) sourceC103) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA103 + sourceB103) sourceC103) = raw4206 := by
      apply Matrix.ext; unfold doubleCharges sourceA103 sourceB103 sourceC103 raw4206; decide +kernel
    rw [ha]
    exact (canonical4206 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA103 sourceB103 sourceC103
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm103, Integer.Sparse.eval]
  linarith only [hs]

def sourceA104 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceB104 : Charge := ![2, 1, 0, -1, -1, -1]
def sourceC104 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceForm104 : Integer.Sparse Master := [(Sum.inr 4830, 2), (Sum.inr 4832, 2), (Sum.inr 4836, 4), (Sum.inr 4890, 2), (Sum.inr 5218, 1), (Sum.inr 5222, 2), (Sum.inr 5225, 2), (Sum.inr 5239, 2), (Sum.inr 5240, 2), (Sum.inr 5252, 3), (Sum.inr 5261, 4), (Sum.inr 5268, 2), (Sum.inr 5296, 2)]

theorem sourceEq104 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm104 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA104 + difference 0 1) (sourceB104 + difference 1 0) sourceC104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5222) := by
    have ha : (tripleCharges (sourceA104 + difference 0 1) (sourceB104 + difference 1 0) sourceC104) = raw4231 := by
      apply Matrix.ext; unfold tripleCharges sourceA104 sourceB104 sourceC104 difference raw4231; decide +kernel
    rw [ha]
    exact (canonical4231 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA104 + difference 0 2) (sourceB104 + difference 2 0) sourceC104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5239) := by
    have ha : (tripleCharges (sourceA104 + difference 0 2) (sourceB104 + difference 2 0) sourceC104) = raw4232 := by
      apply Matrix.ext; unfold tripleCharges sourceA104 sourceB104 sourceC104 difference raw4232; decide +kernel
    rw [ha]
    exact (canonical4232 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA104 + difference 0 3) (sourceB104 + difference 3 0) sourceC104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5261) := by
    have ha : (tripleCharges (sourceA104 + difference 0 3) (sourceB104 + difference 3 0) sourceC104) = raw4036 := by
      apply Matrix.ext; unfold tripleCharges sourceA104 sourceB104 sourceC104 difference raw4036; decide +kernel
    rw [ha]
    exact (canonical4036 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA104 + difference 0 4) (sourceB104 + difference 4 0) sourceC104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5261) := by
    have ha : (tripleCharges (sourceA104 + difference 0 4) (sourceB104 + difference 4 0) sourceC104) = raw4233 := by
      apply Matrix.ext; unfold tripleCharges sourceA104 sourceB104 sourceC104 difference raw4233; decide +kernel
    rw [ha]
    exact (canonical4233 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA104 + difference 0 5) (sourceB104 + difference 5 0) sourceC104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4832) := by
    have ha : (tripleCharges (sourceA104 + difference 0 5) (sourceB104 + difference 5 0) sourceC104) = raw4234 := by
      apply Matrix.ext; unfold tripleCharges sourceA104 sourceB104 sourceC104 difference raw4234; decide +kernel
    rw [ha]
    exact (canonical4234 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA104 + difference 1 0) (sourceB104 + difference 0 1) sourceC104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4890) := by
    have ha : (tripleCharges (sourceA104 + difference 1 0) (sourceB104 + difference 0 1) sourceC104) = raw3684 := by
      apply Matrix.ext; unfold tripleCharges sourceA104 sourceB104 sourceC104 difference raw3684; decide +kernel
    rw [ha]
    exact (canonical3684 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA104 + difference 1 2) (sourceB104 + difference 2 1) sourceC104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5252) := by
    have ha : (tripleCharges (sourceA104 + difference 1 2) (sourceB104 + difference 2 1) sourceC104) = raw4235 := by
      apply Matrix.ext; unfold tripleCharges sourceA104 sourceB104 sourceC104 difference raw4235; decide +kernel
    rw [ha]
    exact (canonical4235 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA104 + difference 1 3) (sourceB104 + difference 3 1) sourceC104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5296) := by
    have ha : (tripleCharges (sourceA104 + difference 1 3) (sourceB104 + difference 3 1) sourceC104) = raw4040 := by
      apply Matrix.ext; unfold tripleCharges sourceA104 sourceB104 sourceC104 difference raw4040; decide +kernel
    rw [ha]
    exact (canonical4040 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA104 + difference 1 4) (sourceB104 + difference 4 1) sourceC104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5296) := by
    have ha : (tripleCharges (sourceA104 + difference 1 4) (sourceB104 + difference 4 1) sourceC104) = raw4236 := by
      apply Matrix.ext; unfold tripleCharges sourceA104 sourceB104 sourceC104 difference raw4236; decide +kernel
    rw [ha]
    exact (canonical4236 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA104 + difference 1 5) (sourceB104 + difference 5 1) sourceC104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4890) := by
    have ha : (tripleCharges (sourceA104 + difference 1 5) (sourceB104 + difference 5 1) sourceC104) = raw3658 := by
      apply Matrix.ext; unfold tripleCharges sourceA104 sourceB104 sourceC104 difference raw3658; decide +kernel
    rw [ha]
    exact (canonical3658 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA104 + difference 2 0) (sourceB104 + difference 0 2) sourceC104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4830) := by
    have ha : (tripleCharges (sourceA104 + difference 2 0) (sourceB104 + difference 0 2) sourceC104) = raw3875 := by
      apply Matrix.ext; unfold tripleCharges sourceA104 sourceB104 sourceC104 difference raw3875; decide +kernel
    rw [ha]
    exact (canonical3875 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA104 + difference 2 1) (sourceB104 + difference 1 2) sourceC104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5218) := by
    have ha : (tripleCharges (sourceA104 + difference 2 1) (sourceB104 + difference 1 2) sourceC104) = raw4237 := by
      apply Matrix.ext; unfold tripleCharges sourceA104 sourceB104 sourceC104 difference raw4237; decide +kernel
    rw [ha]
    exact (canonical4237 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA104 + difference 2 3) (sourceB104 + difference 3 2) sourceC104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5252) := by
    have ha : (tripleCharges (sourceA104 + difference 2 3) (sourceB104 + difference 3 2) sourceC104) = raw4044 := by
      apply Matrix.ext; unfold tripleCharges sourceA104 sourceB104 sourceC104 difference raw4044; decide +kernel
    rw [ha]
    exact (canonical4044 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA104 + difference 2 4) (sourceB104 + difference 4 2) sourceC104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5252) := by
    have ha : (tripleCharges (sourceA104 + difference 2 4) (sourceB104 + difference 4 2) sourceC104) = raw4238 := by
      apply Matrix.ext; unfold tripleCharges sourceA104 sourceB104 sourceC104 difference raw4238; decide +kernel
    rw [ha]
    exact (canonical4238 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA104 + difference 2 5) (sourceB104 + difference 5 2) sourceC104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4830) := by
    have ha : (tripleCharges (sourceA104 + difference 2 5) (sourceB104 + difference 5 2) sourceC104) = raw3856 := by
      apply Matrix.ext; unfold tripleCharges sourceA104 sourceB104 sourceC104 difference raw3856; decide +kernel
    rw [ha]
    exact (canonical3856 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA104 + difference 3 0) (sourceB104 + difference 0 3) sourceC104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4836) := by
    have ha : (tripleCharges (sourceA104 + difference 3 0) (sourceB104 + difference 0 3) sourceC104) = raw4239 := by
      apply Matrix.ext; unfold tripleCharges sourceA104 sourceB104 sourceC104 difference raw4239; decide +kernel
    rw [ha]
    exact (canonical4239 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA104 + difference 3 1) (sourceB104 + difference 1 3) sourceC104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5225) := by
    have ha : (tripleCharges (sourceA104 + difference 3 1) (sourceB104 + difference 1 3) sourceC104) = raw4240 := by
      apply Matrix.ext; unfold tripleCharges sourceA104 sourceB104 sourceC104 difference raw4240; decide +kernel
    rw [ha]
    exact (canonical4240 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA104 + difference 3 2) (sourceB104 + difference 2 3) sourceC104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5240) := by
    have ha : (tripleCharges (sourceA104 + difference 3 2) (sourceB104 + difference 2 3) sourceC104) = raw4241 := by
      apply Matrix.ext; unfold tripleCharges sourceA104 sourceB104 sourceC104 difference raw4241; decide +kernel
    rw [ha]
    exact (canonical4241 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA104 + difference 3 4) (sourceB104 + difference 4 3) sourceC104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5268) := by
    have ha : (tripleCharges (sourceA104 + difference 3 4) (sourceB104 + difference 4 3) sourceC104) = raw4242 := by
      apply Matrix.ext; unfold tripleCharges sourceA104 sourceB104 sourceC104 difference raw4242; decide +kernel
    rw [ha]
    exact (canonical4242 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA104 + difference 3 5) (sourceB104 + difference 5 3) sourceC104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4836) := by
    have ha : (tripleCharges (sourceA104 + difference 3 5) (sourceB104 + difference 5 3) sourceC104) = raw4243 := by
      apply Matrix.ext; unfold tripleCharges sourceA104 sourceB104 sourceC104 difference raw4243; decide +kernel
    rw [ha]
    exact (canonical4243 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA104 + difference 4 0) (sourceB104 + difference 0 4) sourceC104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4836) := by
    have ha : (tripleCharges (sourceA104 + difference 4 0) (sourceB104 + difference 0 4) sourceC104) = raw3681 := by
      apply Matrix.ext; unfold tripleCharges sourceA104 sourceB104 sourceC104 difference raw3681; decide +kernel
    rw [ha]
    exact (canonical3681 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA104 + difference 4 1) (sourceB104 + difference 1 4) sourceC104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5225) := by
    have ha : (tripleCharges (sourceA104 + difference 4 1) (sourceB104 + difference 1 4) sourceC104) = raw4046 := by
      apply Matrix.ext; unfold tripleCharges sourceA104 sourceB104 sourceC104 difference raw4046; decide +kernel
    rw [ha]
    exact (canonical4046 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA104 + difference 4 2) (sourceB104 + difference 2 4) sourceC104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5240) := by
    have ha : (tripleCharges (sourceA104 + difference 4 2) (sourceB104 + difference 2 4) sourceC104) = raw4047 := by
      apply Matrix.ext; unfold tripleCharges sourceA104 sourceB104 sourceC104 difference raw4047; decide +kernel
    rw [ha]
    exact (canonical4047 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA104 + difference 4 3) (sourceB104 + difference 3 4) sourceC104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5268) := by
    have ha : (tripleCharges (sourceA104 + difference 4 3) (sourceB104 + difference 3 4) sourceC104) = raw4244 := by
      apply Matrix.ext; unfold tripleCharges sourceA104 sourceB104 sourceC104 difference raw4244; decide +kernel
    rw [ha]
    exact (canonical4244 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA104 + difference 4 5) (sourceB104 + difference 5 4) sourceC104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4836) := by
    have ha : (tripleCharges (sourceA104 + difference 4 5) (sourceB104 + difference 5 4) sourceC104) = raw3655 := by
      apply Matrix.ext; unfold tripleCharges sourceA104 sourceB104 sourceC104 difference raw3655; decide +kernel
    rw [ha]
    exact (canonical3655 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA104 + difference 5 0) (sourceB104 + difference 0 5) sourceC104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4832) := by
    have ha : (tripleCharges (sourceA104 + difference 5 0) (sourceB104 + difference 0 5) sourceC104) = raw4245 := by
      apply Matrix.ext; unfold tripleCharges sourceA104 sourceB104 sourceC104 difference raw4245; decide +kernel
    rw [ha]
    exact (canonical4245 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA104 + difference 5 1) (sourceB104 + difference 1 5) sourceC104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5222) := by
    have ha : (tripleCharges (sourceA104 + difference 5 1) (sourceB104 + difference 1 5) sourceC104) = raw4246 := by
      apply Matrix.ext; unfold tripleCharges sourceA104 sourceB104 sourceC104 difference raw4246; decide +kernel
    rw [ha]
    exact (canonical4246 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA104 + difference 5 2) (sourceB104 + difference 2 5) sourceC104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5239) := by
    have ha : (tripleCharges (sourceA104 + difference 5 2) (sourceB104 + difference 2 5) sourceC104) = raw4247 := by
      apply Matrix.ext; unfold tripleCharges sourceA104 sourceB104 sourceC104 difference raw4247; decide +kernel
    rw [ha]
    exact (canonical4247 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA104 + difference 5 3) (sourceB104 + difference 3 5) sourceC104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5261) := by
    have ha : (tripleCharges (sourceA104 + difference 5 3) (sourceB104 + difference 3 5) sourceC104) = raw4058 := by
      apply Matrix.ext; unfold tripleCharges sourceA104 sourceB104 sourceC104 difference raw4058; decide +kernel
    rw [ha]
    exact (canonical4058 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA104 + difference 5 4) (sourceB104 + difference 4 5) sourceC104) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5261) := by
    have ha : (tripleCharges (sourceA104 + difference 5 4) (sourceB104 + difference 4 5) sourceC104) = raw4248 := by
      apply Matrix.ext; unfold tripleCharges sourceA104 sourceB104 sourceC104 difference raw4248; decide +kernel
    rw [ha]
    exact (canonical4248 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA104 sourceB104 sourceC104
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm104, Integer.Sparse.eval]
  linarith only [hs]

def sourceA105 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceB105 : Charge := ![2, 1, 0, -1, -1, -1]
def sourceC105 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceForm105 : Integer.Sparse Master := [(Sum.inr 2187, 1), (Sum.inr 2193, 1), (Sum.inr 2197, 2), (Sum.inr 2247, 1), (Sum.inr 2660, 1), (Sum.inr 2664, 1), (Sum.inr 2667, 2), (Sum.inr 2691, 1), (Sum.inr 2692, 2), (Sum.inr 2707, 1), (Sum.inr 2712, 3), (Sum.inr 2716, 2), (Sum.inr 2726, 2), (Sum.inr 2734, 2), (Sum.inr 2755, 1), (Sum.inr 2770, 2), (Sum.inr 3031, 1), (Sum.inr 3061, 1), (Sum.inr 3082, 1), (Sum.inr 3090, 2)]

theorem sourceEq105 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm105 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA105 + difference 0 1) (sourceB105 + difference 1 0) sourceC105) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3031) := by
    have ha : (tripleCharges (sourceA105 + difference 0 1) (sourceB105 + difference 1 0) sourceC105) = raw4249 := by
      apply Matrix.ext; unfold tripleCharges sourceA105 sourceB105 sourceC105 difference raw4249; decide +kernel
    rw [ha]
    exact (canonical4249 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA105 + difference 0 2) (sourceB105 + difference 2 0) sourceC105) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3061) := by
    have ha : (tripleCharges (sourceA105 + difference 0 2) (sourceB105 + difference 2 0) sourceC105) = raw4250 := by
      apply Matrix.ext; unfold tripleCharges sourceA105 sourceB105 sourceC105 difference raw4250; decide +kernel
    rw [ha]
    exact (canonical4250 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA105 + difference 0 3) (sourceB105 + difference 3 0) sourceC105) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3090) := by
    have ha : (tripleCharges (sourceA105 + difference 0 3) (sourceB105 + difference 3 0) sourceC105) = raw4062 := by
      apply Matrix.ext; unfold tripleCharges sourceA105 sourceB105 sourceC105 difference raw4062; decide +kernel
    rw [ha]
    exact (canonical4062 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA105 + difference 0 4) (sourceB105 + difference 4 0) sourceC105) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3090) := by
    have ha : (tripleCharges (sourceA105 + difference 0 4) (sourceB105 + difference 4 0) sourceC105) = raw4251 := by
      apply Matrix.ext; unfold tripleCharges sourceA105 sourceB105 sourceC105 difference raw4251; decide +kernel
    rw [ha]
    exact (canonical4251 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA105 + difference 0 5) (sourceB105 + difference 5 0) sourceC105) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3082) := by
    have ha : (tripleCharges (sourceA105 + difference 0 5) (sourceB105 + difference 5 0) sourceC105) = raw4252 := by
      apply Matrix.ext; unfold tripleCharges sourceA105 sourceB105 sourceC105 difference raw4252; decide +kernel
    rw [ha]
    exact (canonical4252 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA105 + difference 1 0) (sourceB105 + difference 0 1) sourceC105) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2247) := by
    have ha : (tripleCharges (sourceA105 + difference 1 0) (sourceB105 + difference 0 1) sourceC105) = raw3714 := by
      apply Matrix.ext; unfold tripleCharges sourceA105 sourceB105 sourceC105 difference raw3714; decide +kernel
    rw [ha]
    exact (canonical3714 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA105 + difference 1 2) (sourceB105 + difference 2 1) sourceC105) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2712) := by
    have ha : (tripleCharges (sourceA105 + difference 1 2) (sourceB105 + difference 2 1) sourceC105) = raw4253 := by
      apply Matrix.ext; unfold tripleCharges sourceA105 sourceB105 sourceC105 difference raw4253; decide +kernel
    rw [ha]
    exact (canonical4253 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA105 + difference 1 3) (sourceB105 + difference 3 1) sourceC105) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2770) := by
    have ha : (tripleCharges (sourceA105 + difference 1 3) (sourceB105 + difference 3 1) sourceC105) = raw4066 := by
      apply Matrix.ext; unfold tripleCharges sourceA105 sourceB105 sourceC105 difference raw4066; decide +kernel
    rw [ha]
    exact (canonical4066 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA105 + difference 1 4) (sourceB105 + difference 4 1) sourceC105) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2770) := by
    have ha : (tripleCharges (sourceA105 + difference 1 4) (sourceB105 + difference 4 1) sourceC105) = raw4254 := by
      apply Matrix.ext; unfold tripleCharges sourceA105 sourceB105 sourceC105 difference raw4254; decide +kernel
    rw [ha]
    exact (canonical4254 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA105 + difference 1 5) (sourceB105 + difference 5 1) sourceC105) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2755) := by
    have ha : (tripleCharges (sourceA105 + difference 1 5) (sourceB105 + difference 5 1) sourceC105) = raw3688 := by
      apply Matrix.ext; unfold tripleCharges sourceA105 sourceB105 sourceC105 difference raw3688; decide +kernel
    rw [ha]
    exact (canonical3688 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA105 + difference 2 0) (sourceB105 + difference 0 2) sourceC105) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2187) := by
    have ha : (tripleCharges (sourceA105 + difference 2 0) (sourceB105 + difference 0 2) sourceC105) = raw3897 := by
      apply Matrix.ext; unfold tripleCharges sourceA105 sourceB105 sourceC105 difference raw3897; decide +kernel
    rw [ha]
    exact (canonical3897 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA105 + difference 2 1) (sourceB105 + difference 1 2) sourceC105) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2660) := by
    have ha : (tripleCharges (sourceA105 + difference 2 1) (sourceB105 + difference 1 2) sourceC105) = raw4255 := by
      apply Matrix.ext; unfold tripleCharges sourceA105 sourceB105 sourceC105 difference raw4255; decide +kernel
    rw [ha]
    exact (canonical4255 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA105 + difference 2 3) (sourceB105 + difference 3 2) sourceC105) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2712) := by
    have ha : (tripleCharges (sourceA105 + difference 2 3) (sourceB105 + difference 3 2) sourceC105) = raw4070 := by
      apply Matrix.ext; unfold tripleCharges sourceA105 sourceB105 sourceC105 difference raw4070; decide +kernel
    rw [ha]
    exact (canonical4070 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA105 + difference 2 4) (sourceB105 + difference 4 2) sourceC105) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2712) := by
    have ha : (tripleCharges (sourceA105 + difference 2 4) (sourceB105 + difference 4 2) sourceC105) = raw4256 := by
      apply Matrix.ext; unfold tripleCharges sourceA105 sourceB105 sourceC105 difference raw4256; decide +kernel
    rw [ha]
    exact (canonical4256 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA105 + difference 2 5) (sourceB105 + difference 5 2) sourceC105) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2707) := by
    have ha : (tripleCharges (sourceA105 + difference 2 5) (sourceB105 + difference 5 2) sourceC105) = raw3878 := by
      apply Matrix.ext; unfold tripleCharges sourceA105 sourceB105 sourceC105 difference raw3878; decide +kernel
    rw [ha]
    exact (canonical3878 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA105 + difference 3 0) (sourceB105 + difference 0 3) sourceC105) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2197) := by
    have ha : (tripleCharges (sourceA105 + difference 3 0) (sourceB105 + difference 0 3) sourceC105) = raw4257 := by
      apply Matrix.ext; unfold tripleCharges sourceA105 sourceB105 sourceC105 difference raw4257; decide +kernel
    rw [ha]
    exact (canonical4257 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA105 + difference 3 1) (sourceB105 + difference 1 3) sourceC105) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2667) := by
    have ha : (tripleCharges (sourceA105 + difference 3 1) (sourceB105 + difference 1 3) sourceC105) = raw4258 := by
      apply Matrix.ext; unfold tripleCharges sourceA105 sourceB105 sourceC105 difference raw4258; decide +kernel
    rw [ha]
    exact (canonical4258 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA105 + difference 3 2) (sourceB105 + difference 2 3) sourceC105) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2692) := by
    have ha : (tripleCharges (sourceA105 + difference 3 2) (sourceB105 + difference 2 3) sourceC105) = raw4259 := by
      apply Matrix.ext; unfold tripleCharges sourceA105 sourceB105 sourceC105 difference raw4259; decide +kernel
    rw [ha]
    exact (canonical4259 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA105 + difference 3 4) (sourceB105 + difference 4 3) sourceC105) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2734) := by
    have ha : (tripleCharges (sourceA105 + difference 3 4) (sourceB105 + difference 4 3) sourceC105) = raw4260 := by
      apply Matrix.ext; unfold tripleCharges sourceA105 sourceB105 sourceC105 difference raw4260; decide +kernel
    rw [ha]
    exact (canonical4260 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA105 + difference 3 5) (sourceB105 + difference 5 3) sourceC105) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2716) := by
    have ha : (tripleCharges (sourceA105 + difference 3 5) (sourceB105 + difference 5 3) sourceC105) = raw4261 := by
      apply Matrix.ext; unfold tripleCharges sourceA105 sourceB105 sourceC105 difference raw4261; decide +kernel
    rw [ha]
    exact (canonical4261 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA105 + difference 4 0) (sourceB105 + difference 0 4) sourceC105) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2197) := by
    have ha : (tripleCharges (sourceA105 + difference 4 0) (sourceB105 + difference 0 4) sourceC105) = raw3711 := by
      apply Matrix.ext; unfold tripleCharges sourceA105 sourceB105 sourceC105 difference raw3711; decide +kernel
    rw [ha]
    exact (canonical3711 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA105 + difference 4 1) (sourceB105 + difference 1 4) sourceC105) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2667) := by
    have ha : (tripleCharges (sourceA105 + difference 4 1) (sourceB105 + difference 1 4) sourceC105) = raw4072 := by
      apply Matrix.ext; unfold tripleCharges sourceA105 sourceB105 sourceC105 difference raw4072; decide +kernel
    rw [ha]
    exact (canonical4072 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA105 + difference 4 2) (sourceB105 + difference 2 4) sourceC105) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2692) := by
    have ha : (tripleCharges (sourceA105 + difference 4 2) (sourceB105 + difference 2 4) sourceC105) = raw4073 := by
      apply Matrix.ext; unfold tripleCharges sourceA105 sourceB105 sourceC105 difference raw4073; decide +kernel
    rw [ha]
    exact (canonical4073 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA105 + difference 4 3) (sourceB105 + difference 3 4) sourceC105) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2734) := by
    have ha : (tripleCharges (sourceA105 + difference 4 3) (sourceB105 + difference 3 4) sourceC105) = raw4262 := by
      apply Matrix.ext; unfold tripleCharges sourceA105 sourceB105 sourceC105 difference raw4262; decide +kernel
    rw [ha]
    exact (canonical4262 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA105 + difference 4 5) (sourceB105 + difference 5 4) sourceC105) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2716) := by
    have ha : (tripleCharges (sourceA105 + difference 4 5) (sourceB105 + difference 5 4) sourceC105) = raw3685 := by
      apply Matrix.ext; unfold tripleCharges sourceA105 sourceB105 sourceC105 difference raw3685; decide +kernel
    rw [ha]
    exact (canonical3685 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA105 + difference 5 0) (sourceB105 + difference 0 5) sourceC105) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2193) := by
    have ha : (tripleCharges (sourceA105 + difference 5 0) (sourceB105 + difference 0 5) sourceC105) = raw4263 := by
      apply Matrix.ext; unfold tripleCharges sourceA105 sourceB105 sourceC105 difference raw4263; decide +kernel
    rw [ha]
    exact (canonical4263 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA105 + difference 5 1) (sourceB105 + difference 1 5) sourceC105) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2664) := by
    have ha : (tripleCharges (sourceA105 + difference 5 1) (sourceB105 + difference 1 5) sourceC105) = raw4264 := by
      apply Matrix.ext; unfold tripleCharges sourceA105 sourceB105 sourceC105 difference raw4264; decide +kernel
    rw [ha]
    exact (canonical4264 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA105 + difference 5 2) (sourceB105 + difference 2 5) sourceC105) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2691) := by
    have ha : (tripleCharges (sourceA105 + difference 5 2) (sourceB105 + difference 2 5) sourceC105) = raw4265 := by
      apply Matrix.ext; unfold tripleCharges sourceA105 sourceB105 sourceC105 difference raw4265; decide +kernel
    rw [ha]
    exact (canonical4265 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA105 + difference 5 3) (sourceB105 + difference 3 5) sourceC105) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2726) := by
    have ha : (tripleCharges (sourceA105 + difference 5 3) (sourceB105 + difference 3 5) sourceC105) = raw4084 := by
      apply Matrix.ext; unfold tripleCharges sourceA105 sourceB105 sourceC105 difference raw4084; decide +kernel
    rw [ha]
    exact (canonical4084 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA105 + difference 5 4) (sourceB105 + difference 4 5) sourceC105) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2726) := by
    have ha : (tripleCharges (sourceA105 + difference 5 4) (sourceB105 + difference 4 5) sourceC105) = raw4266 := by
      apply Matrix.ext; unfold tripleCharges sourceA105 sourceB105 sourceC105 difference raw4266; decide +kernel
    rw [ha]
    exact (canonical4266 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA105 sourceB105 sourceC105
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm105, Integer.Sparse.eval]
  linarith only [hs]

def sourceA106 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceB106 : Charge := ![2, 1, 0, -1, -1, -1]
def sourceC106 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceForm106 : Integer.Sparse Master := [(Sum.inr 2052, 1), (Sum.inr 3389, 1), (Sum.inr 3492, 1), (Sum.inr 3543, 1), (Sum.inr 3545, 2), (Sum.inr 4085, -1)]

theorem sourceEq106 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm106 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA106 + difference 0 0) (sourceB106 + difference 0 0) sourceC106) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3543) := by
    have ha : (tripleCharges (sourceA106 + difference 0 0) (sourceB106 + difference 0 0) sourceC106) = raw4267 := by
      apply Matrix.ext; unfold tripleCharges sourceA106 sourceB106 sourceC106 difference raw4267; decide +kernel
    rw [ha]
    exact (canonical4267 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA106 + difference 0 1) (sourceB106 + difference 1 0) sourceC106) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3389) := by
    have ha : (tripleCharges (sourceA106 + difference 0 1) (sourceB106 + difference 1 0) sourceC106) = raw4268 := by
      apply Matrix.ext; unfold tripleCharges sourceA106 sourceB106 sourceC106 difference raw4268; decide +kernel
    rw [ha]
    exact (canonical4268 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA106 + difference 0 2) (sourceB106 + difference 2 0) sourceC106) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3492) := by
    have ha : (tripleCharges (sourceA106 + difference 0 2) (sourceB106 + difference 2 0) sourceC106) = raw4269 := by
      apply Matrix.ext; unfold tripleCharges sourceA106 sourceB106 sourceC106 difference raw4269; decide +kernel
    rw [ha]
    exact (canonical4269 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA106 + difference 0 3) (sourceB106 + difference 3 0) sourceC106) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3545) := by
    have ha : (tripleCharges (sourceA106 + difference 0 3) (sourceB106 + difference 3 0) sourceC106) = raw4089 := by
      apply Matrix.ext; unfold tripleCharges sourceA106 sourceB106 sourceC106 difference raw4089; decide +kernel
    rw [ha]
    exact (canonical4089 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA106 + difference 0 4) (sourceB106 + difference 4 0) sourceC106) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3545) := by
    have ha : (tripleCharges (sourceA106 + difference 0 4) (sourceB106 + difference 4 0) sourceC106) = raw4270 := by
      apply Matrix.ext; unfold tripleCharges sourceA106 sourceB106 sourceC106 difference raw4270; decide +kernel
    rw [ha]
    exact (canonical4270 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA106 + difference 0 5) (sourceB106 + difference 5 0) sourceC106) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2052) := by
    have ha : (tripleCharges (sourceA106 + difference 0 5) (sourceB106 + difference 5 0) sourceC106) = raw4271 := by
      apply Matrix.ext; unfold tripleCharges sourceA106 sourceB106 sourceC106 difference raw4271; decide +kernel
    rw [ha]
    exact (canonical4271 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA106 + sourceB106) sourceC106) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA106 + sourceB106) sourceC106) = raw3721 := by
      apply Matrix.ext; unfold doubleCharges sourceA106 sourceB106 sourceC106 raw3721; decide +kernel
    rw [ha]
    exact (canonical3721 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA106 sourceB106 sourceC106
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm106, Integer.Sparse.eval]
  linarith only [hs]

def sourceA107 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceB107 : Charge := ![2, 1, 0, -1, -1, -1]
def sourceC107 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceForm107 : Integer.Sparse Master := [(Sum.inr 2050, 1), (Sum.inr 2052, 1), (Sum.inr 2055, 2), (Sum.inr 2290, 1), (Sum.inr 3543, 1), (Sum.inr 4085, -1)]

theorem sourceEq107 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm107 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA107 + difference 0 0) (sourceB107 + difference 0 0) sourceC107) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3543) := by
    have ha : (tripleCharges (sourceA107 + difference 0 0) (sourceB107 + difference 0 0) sourceC107) = raw4267 := by
      apply Matrix.ext; unfold tripleCharges sourceA107 sourceB107 sourceC107 difference raw4267; decide +kernel
    rw [ha]
    exact (canonical4267 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA107 + difference 1 0) (sourceB107 + difference 0 1) sourceC107) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2290) := by
    have ha : (tripleCharges (sourceA107 + difference 1 0) (sourceB107 + difference 0 1) sourceC107) = raw4272 := by
      apply Matrix.ext; unfold tripleCharges sourceA107 sourceB107 sourceC107 difference raw4272; decide +kernel
    rw [ha]
    exact (canonical4272 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA107 + difference 2 0) (sourceB107 + difference 0 2) sourceC107) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2050) := by
    have ha : (tripleCharges (sourceA107 + difference 2 0) (sourceB107 + difference 0 2) sourceC107) = raw4273 := by
      apply Matrix.ext; unfold tripleCharges sourceA107 sourceB107 sourceC107 difference raw4273; decide +kernel
    rw [ha]
    exact (canonical4273 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA107 + difference 3 0) (sourceB107 + difference 0 3) sourceC107) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2055) := by
    have ha : (tripleCharges (sourceA107 + difference 3 0) (sourceB107 + difference 0 3) sourceC107) = raw4274 := by
      apply Matrix.ext; unfold tripleCharges sourceA107 sourceB107 sourceC107 difference raw4274; decide +kernel
    rw [ha]
    exact (canonical4274 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA107 + difference 4 0) (sourceB107 + difference 0 4) sourceC107) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2055) := by
    have ha : (tripleCharges (sourceA107 + difference 4 0) (sourceB107 + difference 0 4) sourceC107) = raw3734 := by
      apply Matrix.ext; unfold tripleCharges sourceA107 sourceB107 sourceC107 difference raw3734; decide +kernel
    rw [ha]
    exact (canonical3734 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA107 + difference 5 0) (sourceB107 + difference 0 5) sourceC107) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2052) := by
    have ha : (tripleCharges (sourceA107 + difference 5 0) (sourceB107 + difference 0 5) sourceC107) = raw4275 := by
      apply Matrix.ext; unfold tripleCharges sourceA107 sourceB107 sourceC107 difference raw4275; decide +kernel
    rw [ha]
    exact (canonical4275 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA107 + sourceB107) sourceC107) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA107 + sourceB107) sourceC107) = raw3721 := by
      apply Matrix.ext; unfold doubleCharges sourceA107 sourceB107 sourceC107 raw3721; decide +kernel
    rw [ha]
    exact (canonical3721 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA107 sourceB107 sourceC107
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm107, Integer.Sparse.eval]
  linarith only [hs]

def sourceA108 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceB108 : Charge := ![2, 1, 0, -1, -1, -1]
def sourceC108 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceForm108 : Integer.Sparse Master := [(Sum.inr 2290, 2), (Sum.inr 3543, 2), (Sum.inr 3634, 2), (Sum.inr 4085, -1)]

theorem sourceEq108 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm108 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA108 + difference 1 0) (sourceB108 + difference 0 1) sourceC108) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2290) := by
    have ha : (tripleCharges (sourceA108 + difference 1 0) (sourceB108 + difference 0 1) sourceC108) = raw4272 := by
      apply Matrix.ext; unfold tripleCharges sourceA108 sourceB108 sourceC108 difference raw4272; decide +kernel
    rw [ha]
    exact (canonical4272 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA108 + difference 1 1) (sourceB108 + difference 1 1) sourceC108) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3543) := by
    have ha : (tripleCharges (sourceA108 + difference 1 1) (sourceB108 + difference 1 1) sourceC108) = raw4267 := by
      apply Matrix.ext; unfold tripleCharges sourceA108 sourceB108 sourceC108 difference raw4267; decide +kernel
    rw [ha]
    exact (canonical4267 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA108 + difference 1 2) (sourceB108 + difference 2 1) sourceC108) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3543) := by
    have ha : (tripleCharges (sourceA108 + difference 1 2) (sourceB108 + difference 2 1) sourceC108) = raw4276 := by
      apply Matrix.ext; unfold tripleCharges sourceA108 sourceB108 sourceC108 difference raw4276; decide +kernel
    rw [ha]
    exact (canonical4276 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA108 + difference 1 3) (sourceB108 + difference 3 1) sourceC108) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3634) := by
    have ha : (tripleCharges (sourceA108 + difference 1 3) (sourceB108 + difference 3 1) sourceC108) = raw4097 := by
      apply Matrix.ext; unfold tripleCharges sourceA108 sourceB108 sourceC108 difference raw4097; decide +kernel
    rw [ha]
    exact (canonical4097 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA108 + difference 1 4) (sourceB108 + difference 4 1) sourceC108) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3634) := by
    have ha : (tripleCharges (sourceA108 + difference 1 4) (sourceB108 + difference 4 1) sourceC108) = raw4277 := by
      apply Matrix.ext; unfold tripleCharges sourceA108 sourceB108 sourceC108 difference raw4277; decide +kernel
    rw [ha]
    exact (canonical4277 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA108 + difference 1 5) (sourceB108 + difference 5 1) sourceC108) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2290) := by
    have ha : (tripleCharges (sourceA108 + difference 1 5) (sourceB108 + difference 5 1) sourceC108) = raw3719 := by
      apply Matrix.ext; unfold tripleCharges sourceA108 sourceB108 sourceC108 difference raw3719; decide +kernel
    rw [ha]
    exact (canonical3719 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA108 + sourceB108) sourceC108) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA108 + sourceB108) sourceC108) = raw3721 := by
      apply Matrix.ext; unfold doubleCharges sourceA108 sourceB108 sourceC108 raw3721; decide +kernel
    rw [ha]
    exact (canonical3721 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA108 sourceB108 sourceC108
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm108, Integer.Sparse.eval]
  linarith only [hs]

def sourceA109 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceB109 : Charge := ![2, 1, 0, -1, -1, -1]
def sourceC109 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceForm109 : Integer.Sparse Master := [(Sum.inr 3387, 1), (Sum.inr 3389, 2), (Sum.inr 3393, 2), (Sum.inr 3543, 1), (Sum.inr 4085, -1)]

theorem sourceEq109 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm109 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA109 + difference 0 1) (sourceB109 + difference 1 0) sourceC109) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3389) := by
    have ha : (tripleCharges (sourceA109 + difference 0 1) (sourceB109 + difference 1 0) sourceC109) = raw4268 := by
      apply Matrix.ext; unfold tripleCharges sourceA109 sourceB109 sourceC109 difference raw4268; decide +kernel
    rw [ha]
    exact (canonical4268 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA109 + difference 1 1) (sourceB109 + difference 1 1) sourceC109) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3543) := by
    have ha : (tripleCharges (sourceA109 + difference 1 1) (sourceB109 + difference 1 1) sourceC109) = raw4267 := by
      apply Matrix.ext; unfold tripleCharges sourceA109 sourceB109 sourceC109 difference raw4267; decide +kernel
    rw [ha]
    exact (canonical4267 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA109 + difference 2 1) (sourceB109 + difference 1 2) sourceC109) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3387) := by
    have ha : (tripleCharges (sourceA109 + difference 2 1) (sourceB109 + difference 1 2) sourceC109) = raw4278 := by
      apply Matrix.ext; unfold tripleCharges sourceA109 sourceB109 sourceC109 difference raw4278; decide +kernel
    rw [ha]
    exact (canonical4278 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA109 + difference 3 1) (sourceB109 + difference 1 3) sourceC109) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3393) := by
    have ha : (tripleCharges (sourceA109 + difference 3 1) (sourceB109 + difference 1 3) sourceC109) = raw4279 := by
      apply Matrix.ext; unfold tripleCharges sourceA109 sourceB109 sourceC109 difference raw4279; decide +kernel
    rw [ha]
    exact (canonical4279 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA109 + difference 4 1) (sourceB109 + difference 1 4) sourceC109) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3393) := by
    have ha : (tripleCharges (sourceA109 + difference 4 1) (sourceB109 + difference 1 4) sourceC109) = raw4099 := by
      apply Matrix.ext; unfold tripleCharges sourceA109 sourceB109 sourceC109 difference raw4099; decide +kernel
    rw [ha]
    exact (canonical4099 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA109 + difference 5 1) (sourceB109 + difference 1 5) sourceC109) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3389) := by
    have ha : (tripleCharges (sourceA109 + difference 5 1) (sourceB109 + difference 1 5) sourceC109) = raw4280 := by
      apply Matrix.ext; unfold tripleCharges sourceA109 sourceB109 sourceC109 difference raw4280; decide +kernel
    rw [ha]
    exact (canonical4280 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA109 + sourceB109) sourceC109) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA109 + sourceB109) sourceC109) = raw3721 := by
      apply Matrix.ext; unfold doubleCharges sourceA109 sourceB109 sourceC109 raw3721; decide +kernel
    rw [ha]
    exact (canonical3721 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA109 sourceB109 sourceC109
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm109, Integer.Sparse.eval]
  linarith only [hs]

def sourceA110 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceB110 : Charge := ![2, 1, 0, -1, -1, -1]
def sourceC110 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceForm110 : Integer.Sparse Master := [(Sum.inr 2050, 2), (Sum.inr 3387, 1), (Sum.inr 3543, 3), (Sum.inr 4085, -1)]

theorem sourceEq110 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm110 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA110 + difference 2 0) (sourceB110 + difference 0 2) sourceC110) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2050) := by
    have ha : (tripleCharges (sourceA110 + difference 2 0) (sourceB110 + difference 0 2) sourceC110) = raw4273 := by
      apply Matrix.ext; unfold tripleCharges sourceA110 sourceB110 sourceC110 difference raw4273; decide +kernel
    rw [ha]
    exact (canonical4273 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA110 + difference 2 1) (sourceB110 + difference 1 2) sourceC110) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3387) := by
    have ha : (tripleCharges (sourceA110 + difference 2 1) (sourceB110 + difference 1 2) sourceC110) = raw4278 := by
      apply Matrix.ext; unfold tripleCharges sourceA110 sourceB110 sourceC110 difference raw4278; decide +kernel
    rw [ha]
    exact (canonical4278 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA110 + difference 2 2) (sourceB110 + difference 2 2) sourceC110) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3543) := by
    have ha : (tripleCharges (sourceA110 + difference 2 2) (sourceB110 + difference 2 2) sourceC110) = raw4267 := by
      apply Matrix.ext; unfold tripleCharges sourceA110 sourceB110 sourceC110 difference raw4267; decide +kernel
    rw [ha]
    exact (canonical4267 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA110 + difference 2 3) (sourceB110 + difference 3 2) sourceC110) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3543) := by
    have ha : (tripleCharges (sourceA110 + difference 2 3) (sourceB110 + difference 3 2) sourceC110) = raw4103 := by
      apply Matrix.ext; unfold tripleCharges sourceA110 sourceB110 sourceC110 difference raw4103; decide +kernel
    rw [ha]
    exact (canonical4103 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA110 + difference 2 4) (sourceB110 + difference 4 2) sourceC110) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3543) := by
    have ha : (tripleCharges (sourceA110 + difference 2 4) (sourceB110 + difference 4 2) sourceC110) = raw4281 := by
      apply Matrix.ext; unfold tripleCharges sourceA110 sourceB110 sourceC110 difference raw4281; decide +kernel
    rw [ha]
    exact (canonical4281 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA110 + difference 2 5) (sourceB110 + difference 5 2) sourceC110) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2050) := by
    have ha : (tripleCharges (sourceA110 + difference 2 5) (sourceB110 + difference 5 2) sourceC110) = raw3901 := by
      apply Matrix.ext; unfold tripleCharges sourceA110 sourceB110 sourceC110 difference raw3901; decide +kernel
    rw [ha]
    exact (canonical3901 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA110 + sourceB110) sourceC110) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA110 + sourceB110) sourceC110) = raw3721 := by
      apply Matrix.ext; unfold doubleCharges sourceA110 sourceB110 sourceC110 raw3721; decide +kernel
    rw [ha]
    exact (canonical3721 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA110 sourceB110 sourceC110
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm110, Integer.Sparse.eval]
  linarith only [hs]

def sourceA111 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB111 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceC111 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceForm111 : Integer.Sparse Master := [(Sum.inr 4463, 3), (Sum.inr 4468, 1), (Sum.inr 4507, 1), (Sum.inr 4608, 3), (Sum.inr 4625, 1), (Sum.inr 5078, 6), (Sum.inr 5109, 3), (Sum.inr 5174, 3), (Sum.inr 5293, 3), (Sum.inr 5294, 3), (Sum.inr 5309, 1), (Sum.inr 5310, 1), (Sum.inr 5455, 1)]

theorem sourceEq111 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm111 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA111 + difference 0 1) (sourceB111 + difference 1 0) sourceC111) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA111 + difference 0 1) (sourceB111 + difference 1 0) sourceC111) = raw4282 := by
      apply Matrix.ext; unfold tripleCharges sourceA111 sourceB111 sourceC111 difference raw4282; decide +kernel
    rw [ha]
    exact (canonical4282 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA111 + difference 0 2) (sourceB111 + difference 2 0) sourceC111) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA111 + difference 0 2) (sourceB111 + difference 2 0) sourceC111) = raw4283 := by
      apply Matrix.ext; unfold tripleCharges sourceA111 sourceB111 sourceC111 difference raw4283; decide +kernel
    rw [ha]
    exact (canonical4283 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA111 + difference 0 3) (sourceB111 + difference 3 0) sourceC111) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA111 + difference 0 3) (sourceB111 + difference 3 0) sourceC111) = raw4284 := by
      apply Matrix.ext; unfold tripleCharges sourceA111 sourceB111 sourceC111 difference raw4284; decide +kernel
    rw [ha]
    exact (canonical4284 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA111 + difference 0 4) (sourceB111 + difference 4 0) sourceC111) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5310) := by
    have ha : (tripleCharges (sourceA111 + difference 0 4) (sourceB111 + difference 4 0) sourceC111) = raw4285 := by
      apply Matrix.ext; unfold tripleCharges sourceA111 sourceB111 sourceC111 difference raw4285; decide +kernel
    rw [ha]
    exact (canonical4285 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA111 + difference 0 5) (sourceB111 + difference 5 0) sourceC111) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5455) := by
    have ha : (tripleCharges (sourceA111 + difference 0 5) (sourceB111 + difference 5 0) sourceC111) = raw4286 := by
      apply Matrix.ext; unfold tripleCharges sourceA111 sourceB111 sourceC111 difference raw4286; decide +kernel
    rw [ha]
    exact (canonical4286 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA111 + difference 1 0) (sourceB111 + difference 0 1) sourceC111) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4608) := by
    have ha : (tripleCharges (sourceA111 + difference 1 0) (sourceB111 + difference 0 1) sourceC111) = raw4287 := by
      apply Matrix.ext; unfold tripleCharges sourceA111 sourceB111 sourceC111 difference raw4287; decide +kernel
    rw [ha]
    exact (canonical4287 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA111 + difference 1 2) (sourceB111 + difference 2 1) sourceC111) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5078) := by
    have ha : (tripleCharges (sourceA111 + difference 1 2) (sourceB111 + difference 2 1) sourceC111) = raw4288 := by
      apply Matrix.ext; unfold tripleCharges sourceA111 sourceB111 sourceC111 difference raw4288; decide +kernel
    rw [ha]
    exact (canonical4288 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA111 + difference 1 3) (sourceB111 + difference 3 1) sourceC111) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5078) := by
    have ha : (tripleCharges (sourceA111 + difference 1 3) (sourceB111 + difference 3 1) sourceC111) = raw4289 := by
      apply Matrix.ext; unfold tripleCharges sourceA111 sourceB111 sourceC111 difference raw4289; decide +kernel
    rw [ha]
    exact (canonical4289 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA111 + difference 1 4) (sourceB111 + difference 4 1) sourceC111) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5109) := by
    have ha : (tripleCharges (sourceA111 + difference 1 4) (sourceB111 + difference 4 1) sourceC111) = raw4290 := by
      apply Matrix.ext; unfold tripleCharges sourceA111 sourceB111 sourceC111 difference raw4290; decide +kernel
    rw [ha]
    exact (canonical4290 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA111 + difference 1 5) (sourceB111 + difference 5 1) sourceC111) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA111 + difference 1 5) (sourceB111 + difference 5 1) sourceC111) = raw4291 := by
      apply Matrix.ext; unfold tripleCharges sourceA111 sourceB111 sourceC111 difference raw4291; decide +kernel
    rw [ha]
    exact (canonical4291 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA111 + difference 2 0) (sourceB111 + difference 0 2) sourceC111) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4608) := by
    have ha : (tripleCharges (sourceA111 + difference 2 0) (sourceB111 + difference 0 2) sourceC111) = raw4292 := by
      apply Matrix.ext; unfold tripleCharges sourceA111 sourceB111 sourceC111 difference raw4292; decide +kernel
    rw [ha]
    exact (canonical4292 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA111 + difference 2 1) (sourceB111 + difference 1 2) sourceC111) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5078) := by
    have ha : (tripleCharges (sourceA111 + difference 2 1) (sourceB111 + difference 1 2) sourceC111) = raw4293 := by
      apply Matrix.ext; unfold tripleCharges sourceA111 sourceB111 sourceC111 difference raw4293; decide +kernel
    rw [ha]
    exact (canonical4293 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA111 + difference 2 3) (sourceB111 + difference 3 2) sourceC111) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5078) := by
    have ha : (tripleCharges (sourceA111 + difference 2 3) (sourceB111 + difference 3 2) sourceC111) = raw4294 := by
      apply Matrix.ext; unfold tripleCharges sourceA111 sourceB111 sourceC111 difference raw4294; decide +kernel
    rw [ha]
    exact (canonical4294 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA111 + difference 2 4) (sourceB111 + difference 4 2) sourceC111) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5109) := by
    have ha : (tripleCharges (sourceA111 + difference 2 4) (sourceB111 + difference 4 2) sourceC111) = raw4295 := by
      apply Matrix.ext; unfold tripleCharges sourceA111 sourceB111 sourceC111 difference raw4295; decide +kernel
    rw [ha]
    exact (canonical4295 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA111 + difference 2 5) (sourceB111 + difference 5 2) sourceC111) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA111 + difference 2 5) (sourceB111 + difference 5 2) sourceC111) = raw4296 := by
      apply Matrix.ext; unfold tripleCharges sourceA111 sourceB111 sourceC111 difference raw4296; decide +kernel
    rw [ha]
    exact (canonical4296 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA111 + difference 3 0) (sourceB111 + difference 0 3) sourceC111) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4608) := by
    have ha : (tripleCharges (sourceA111 + difference 3 0) (sourceB111 + difference 0 3) sourceC111) = raw4297 := by
      apply Matrix.ext; unfold tripleCharges sourceA111 sourceB111 sourceC111 difference raw4297; decide +kernel
    rw [ha]
    exact (canonical4297 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA111 + difference 3 1) (sourceB111 + difference 1 3) sourceC111) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5078) := by
    have ha : (tripleCharges (sourceA111 + difference 3 1) (sourceB111 + difference 1 3) sourceC111) = raw4298 := by
      apply Matrix.ext; unfold tripleCharges sourceA111 sourceB111 sourceC111 difference raw4298; decide +kernel
    rw [ha]
    exact (canonical4298 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA111 + difference 3 2) (sourceB111 + difference 2 3) sourceC111) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5078) := by
    have ha : (tripleCharges (sourceA111 + difference 3 2) (sourceB111 + difference 2 3) sourceC111) = raw4299 := by
      apply Matrix.ext; unfold tripleCharges sourceA111 sourceB111 sourceC111 difference raw4299; decide +kernel
    rw [ha]
    exact (canonical4299 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA111 + difference 3 4) (sourceB111 + difference 4 3) sourceC111) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5109) := by
    have ha : (tripleCharges (sourceA111 + difference 3 4) (sourceB111 + difference 4 3) sourceC111) = raw4300 := by
      apply Matrix.ext; unfold tripleCharges sourceA111 sourceB111 sourceC111 difference raw4300; decide +kernel
    rw [ha]
    exact (canonical4300 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA111 + difference 3 5) (sourceB111 + difference 5 3) sourceC111) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA111 + difference 3 5) (sourceB111 + difference 5 3) sourceC111) = raw4301 := by
      apply Matrix.ext; unfold tripleCharges sourceA111 sourceB111 sourceC111 difference raw4301; decide +kernel
    rw [ha]
    exact (canonical4301 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA111 + difference 4 0) (sourceB111 + difference 0 4) sourceC111) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4625) := by
    have ha : (tripleCharges (sourceA111 + difference 4 0) (sourceB111 + difference 0 4) sourceC111) = raw4302 := by
      apply Matrix.ext; unfold tripleCharges sourceA111 sourceB111 sourceC111 difference raw4302; decide +kernel
    rw [ha]
    exact (canonical4302 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA111 + difference 4 1) (sourceB111 + difference 1 4) sourceC111) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5174) := by
    have ha : (tripleCharges (sourceA111 + difference 4 1) (sourceB111 + difference 1 4) sourceC111) = raw4303 := by
      apply Matrix.ext; unfold tripleCharges sourceA111 sourceB111 sourceC111 difference raw4303; decide +kernel
    rw [ha]
    exact (canonical4303 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA111 + difference 4 2) (sourceB111 + difference 2 4) sourceC111) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5174) := by
    have ha : (tripleCharges (sourceA111 + difference 4 2) (sourceB111 + difference 2 4) sourceC111) = raw4304 := by
      apply Matrix.ext; unfold tripleCharges sourceA111 sourceB111 sourceC111 difference raw4304; decide +kernel
    rw [ha]
    exact (canonical4304 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA111 + difference 4 3) (sourceB111 + difference 3 4) sourceC111) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5174) := by
    have ha : (tripleCharges (sourceA111 + difference 4 3) (sourceB111 + difference 3 4) sourceC111) = raw4305 := by
      apply Matrix.ext; unfold tripleCharges sourceA111 sourceB111 sourceC111 difference raw4305; decide +kernel
    rw [ha]
    exact (canonical4305 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA111 + difference 4 5) (sourceB111 + difference 5 4) sourceC111) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5309) := by
    have ha : (tripleCharges (sourceA111 + difference 4 5) (sourceB111 + difference 5 4) sourceC111) = raw4306 := by
      apply Matrix.ext; unfold tripleCharges sourceA111 sourceB111 sourceC111 difference raw4306; decide +kernel
    rw [ha]
    exact (canonical4306 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA111 + difference 5 0) (sourceB111 + difference 0 5) sourceC111) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4468) := by
    have ha : (tripleCharges (sourceA111 + difference 5 0) (sourceB111 + difference 0 5) sourceC111) = raw4307 := by
      apply Matrix.ext; unfold tripleCharges sourceA111 sourceB111 sourceC111 difference raw4307; decide +kernel
    rw [ha]
    exact (canonical4307 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA111 + difference 5 1) (sourceB111 + difference 1 5) sourceC111) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4463) := by
    have ha : (tripleCharges (sourceA111 + difference 5 1) (sourceB111 + difference 1 5) sourceC111) = raw4308 := by
      apply Matrix.ext; unfold tripleCharges sourceA111 sourceB111 sourceC111 difference raw4308; decide +kernel
    rw [ha]
    exact (canonical4308 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA111 + difference 5 2) (sourceB111 + difference 2 5) sourceC111) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4463) := by
    have ha : (tripleCharges (sourceA111 + difference 5 2) (sourceB111 + difference 2 5) sourceC111) = raw4309 := by
      apply Matrix.ext; unfold tripleCharges sourceA111 sourceB111 sourceC111 difference raw4309; decide +kernel
    rw [ha]
    exact (canonical4309 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA111 + difference 5 3) (sourceB111 + difference 3 5) sourceC111) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4463) := by
    have ha : (tripleCharges (sourceA111 + difference 5 3) (sourceB111 + difference 3 5) sourceC111) = raw4310 := by
      apply Matrix.ext; unfold tripleCharges sourceA111 sourceB111 sourceC111 difference raw4310; decide +kernel
    rw [ha]
    exact (canonical4310 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA111 + difference 5 4) (sourceB111 + difference 4 5) sourceC111) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4507) := by
    have ha : (tripleCharges (sourceA111 + difference 5 4) (sourceB111 + difference 4 5) sourceC111) = raw4311 := by
      apply Matrix.ext; unfold tripleCharges sourceA111 sourceB111 sourceC111 difference raw4311; decide +kernel
    rw [ha]
    exact (canonical4311 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA111 sourceB111 sourceC111
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm111, Integer.Sparse.eval]
  linarith only [hs]

def sourceA112 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB112 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceC112 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceForm112 : Integer.Sparse Master := [(Sum.inr 1046, 3), (Sum.inr 1051, 1), (Sum.inr 1091, 1), (Sum.inr 1242, 3), (Sum.inr 1304, 1), (Sum.inr 2485, 6), (Sum.inr 2519, 3), (Sum.inr 2601, 3), (Sum.inr 2768, 3), (Sum.inr 2788, 1), (Sum.inr 3102, 3), (Sum.inr 3123, 1), (Sum.inr 4019, 1)]

theorem sourceEq112 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm112 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA112 + difference 0 1) (sourceB112 + difference 1 0) sourceC112) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2768) := by
    have ha : (tripleCharges (sourceA112 + difference 0 1) (sourceB112 + difference 1 0) sourceC112) = raw4312 := by
      apply Matrix.ext; unfold tripleCharges sourceA112 sourceB112 sourceC112 difference raw4312; decide +kernel
    rw [ha]
    exact (canonical4312 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA112 + difference 0 2) (sourceB112 + difference 2 0) sourceC112) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2768) := by
    have ha : (tripleCharges (sourceA112 + difference 0 2) (sourceB112 + difference 2 0) sourceC112) = raw4313 := by
      apply Matrix.ext; unfold tripleCharges sourceA112 sourceB112 sourceC112 difference raw4313; decide +kernel
    rw [ha]
    exact (canonical4313 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA112 + difference 0 3) (sourceB112 + difference 3 0) sourceC112) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2768) := by
    have ha : (tripleCharges (sourceA112 + difference 0 3) (sourceB112 + difference 3 0) sourceC112) = raw4314 := by
      apply Matrix.ext; unfold tripleCharges sourceA112 sourceB112 sourceC112 difference raw4314; decide +kernel
    rw [ha]
    exact (canonical4314 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA112 + difference 0 4) (sourceB112 + difference 4 0) sourceC112) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2788) := by
    have ha : (tripleCharges (sourceA112 + difference 0 4) (sourceB112 + difference 4 0) sourceC112) = raw4315 := by
      apply Matrix.ext; unfold tripleCharges sourceA112 sourceB112 sourceC112 difference raw4315; decide +kernel
    rw [ha]
    exact (canonical4315 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA112 + difference 0 5) (sourceB112 + difference 5 0) sourceC112) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4019) := by
    have ha : (tripleCharges (sourceA112 + difference 0 5) (sourceB112 + difference 5 0) sourceC112) = raw4316 := by
      apply Matrix.ext; unfold tripleCharges sourceA112 sourceB112 sourceC112 difference raw4316; decide +kernel
    rw [ha]
    exact (canonical4316 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA112 + difference 1 0) (sourceB112 + difference 0 1) sourceC112) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1242) := by
    have ha : (tripleCharges (sourceA112 + difference 1 0) (sourceB112 + difference 0 1) sourceC112) = raw4317 := by
      apply Matrix.ext; unfold tripleCharges sourceA112 sourceB112 sourceC112 difference raw4317; decide +kernel
    rw [ha]
    exact (canonical4317 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA112 + difference 1 2) (sourceB112 + difference 2 1) sourceC112) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2485) := by
    have ha : (tripleCharges (sourceA112 + difference 1 2) (sourceB112 + difference 2 1) sourceC112) = raw4318 := by
      apply Matrix.ext; unfold tripleCharges sourceA112 sourceB112 sourceC112 difference raw4318; decide +kernel
    rw [ha]
    exact (canonical4318 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA112 + difference 1 3) (sourceB112 + difference 3 1) sourceC112) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2485) := by
    have ha : (tripleCharges (sourceA112 + difference 1 3) (sourceB112 + difference 3 1) sourceC112) = raw4319 := by
      apply Matrix.ext; unfold tripleCharges sourceA112 sourceB112 sourceC112 difference raw4319; decide +kernel
    rw [ha]
    exact (canonical4319 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA112 + difference 1 4) (sourceB112 + difference 4 1) sourceC112) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2519) := by
    have ha : (tripleCharges (sourceA112 + difference 1 4) (sourceB112 + difference 4 1) sourceC112) = raw4320 := by
      apply Matrix.ext; unfold tripleCharges sourceA112 sourceB112 sourceC112 difference raw4320; decide +kernel
    rw [ha]
    exact (canonical4320 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA112 + difference 1 5) (sourceB112 + difference 5 1) sourceC112) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3102) := by
    have ha : (tripleCharges (sourceA112 + difference 1 5) (sourceB112 + difference 5 1) sourceC112) = raw4321 := by
      apply Matrix.ext; unfold tripleCharges sourceA112 sourceB112 sourceC112 difference raw4321; decide +kernel
    rw [ha]
    exact (canonical4321 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA112 + difference 2 0) (sourceB112 + difference 0 2) sourceC112) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1242) := by
    have ha : (tripleCharges (sourceA112 + difference 2 0) (sourceB112 + difference 0 2) sourceC112) = raw4322 := by
      apply Matrix.ext; unfold tripleCharges sourceA112 sourceB112 sourceC112 difference raw4322; decide +kernel
    rw [ha]
    exact (canonical4322 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA112 + difference 2 1) (sourceB112 + difference 1 2) sourceC112) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2485) := by
    have ha : (tripleCharges (sourceA112 + difference 2 1) (sourceB112 + difference 1 2) sourceC112) = raw4323 := by
      apply Matrix.ext; unfold tripleCharges sourceA112 sourceB112 sourceC112 difference raw4323; decide +kernel
    rw [ha]
    exact (canonical4323 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA112 + difference 2 3) (sourceB112 + difference 3 2) sourceC112) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2485) := by
    have ha : (tripleCharges (sourceA112 + difference 2 3) (sourceB112 + difference 3 2) sourceC112) = raw4324 := by
      apply Matrix.ext; unfold tripleCharges sourceA112 sourceB112 sourceC112 difference raw4324; decide +kernel
    rw [ha]
    exact (canonical4324 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA112 + difference 2 4) (sourceB112 + difference 4 2) sourceC112) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2519) := by
    have ha : (tripleCharges (sourceA112 + difference 2 4) (sourceB112 + difference 4 2) sourceC112) = raw4325 := by
      apply Matrix.ext; unfold tripleCharges sourceA112 sourceB112 sourceC112 difference raw4325; decide +kernel
    rw [ha]
    exact (canonical4325 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA112 + difference 2 5) (sourceB112 + difference 5 2) sourceC112) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3102) := by
    have ha : (tripleCharges (sourceA112 + difference 2 5) (sourceB112 + difference 5 2) sourceC112) = raw4326 := by
      apply Matrix.ext; unfold tripleCharges sourceA112 sourceB112 sourceC112 difference raw4326; decide +kernel
    rw [ha]
    exact (canonical4326 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA112 + difference 3 0) (sourceB112 + difference 0 3) sourceC112) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1242) := by
    have ha : (tripleCharges (sourceA112 + difference 3 0) (sourceB112 + difference 0 3) sourceC112) = raw4327 := by
      apply Matrix.ext; unfold tripleCharges sourceA112 sourceB112 sourceC112 difference raw4327; decide +kernel
    rw [ha]
    exact (canonical4327 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA112 + difference 3 1) (sourceB112 + difference 1 3) sourceC112) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2485) := by
    have ha : (tripleCharges (sourceA112 + difference 3 1) (sourceB112 + difference 1 3) sourceC112) = raw4328 := by
      apply Matrix.ext; unfold tripleCharges sourceA112 sourceB112 sourceC112 difference raw4328; decide +kernel
    rw [ha]
    exact (canonical4328 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA112 + difference 3 2) (sourceB112 + difference 2 3) sourceC112) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2485) := by
    have ha : (tripleCharges (sourceA112 + difference 3 2) (sourceB112 + difference 2 3) sourceC112) = raw4329 := by
      apply Matrix.ext; unfold tripleCharges sourceA112 sourceB112 sourceC112 difference raw4329; decide +kernel
    rw [ha]
    exact (canonical4329 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA112 + difference 3 4) (sourceB112 + difference 4 3) sourceC112) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2519) := by
    have ha : (tripleCharges (sourceA112 + difference 3 4) (sourceB112 + difference 4 3) sourceC112) = raw4330 := by
      apply Matrix.ext; unfold tripleCharges sourceA112 sourceB112 sourceC112 difference raw4330; decide +kernel
    rw [ha]
    exact (canonical4330 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA112 + difference 3 5) (sourceB112 + difference 5 3) sourceC112) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3102) := by
    have ha : (tripleCharges (sourceA112 + difference 3 5) (sourceB112 + difference 5 3) sourceC112) = raw4331 := by
      apply Matrix.ext; unfold tripleCharges sourceA112 sourceB112 sourceC112 difference raw4331; decide +kernel
    rw [ha]
    exact (canonical4331 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA112 + difference 4 0) (sourceB112 + difference 0 4) sourceC112) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1304) := by
    have ha : (tripleCharges (sourceA112 + difference 4 0) (sourceB112 + difference 0 4) sourceC112) = raw4332 := by
      apply Matrix.ext; unfold tripleCharges sourceA112 sourceB112 sourceC112 difference raw4332; decide +kernel
    rw [ha]
    exact (canonical4332 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA112 + difference 4 1) (sourceB112 + difference 1 4) sourceC112) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2601) := by
    have ha : (tripleCharges (sourceA112 + difference 4 1) (sourceB112 + difference 1 4) sourceC112) = raw4333 := by
      apply Matrix.ext; unfold tripleCharges sourceA112 sourceB112 sourceC112 difference raw4333; decide +kernel
    rw [ha]
    exact (canonical4333 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA112 + difference 4 2) (sourceB112 + difference 2 4) sourceC112) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2601) := by
    have ha : (tripleCharges (sourceA112 + difference 4 2) (sourceB112 + difference 2 4) sourceC112) = raw4334 := by
      apply Matrix.ext; unfold tripleCharges sourceA112 sourceB112 sourceC112 difference raw4334; decide +kernel
    rw [ha]
    exact (canonical4334 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA112 + difference 4 3) (sourceB112 + difference 3 4) sourceC112) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2601) := by
    have ha : (tripleCharges (sourceA112 + difference 4 3) (sourceB112 + difference 3 4) sourceC112) = raw4335 := by
      apply Matrix.ext; unfold tripleCharges sourceA112 sourceB112 sourceC112 difference raw4335; decide +kernel
    rw [ha]
    exact (canonical4335 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA112 + difference 4 5) (sourceB112 + difference 5 4) sourceC112) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3123) := by
    have ha : (tripleCharges (sourceA112 + difference 4 5) (sourceB112 + difference 5 4) sourceC112) = raw4336 := by
      apply Matrix.ext; unfold tripleCharges sourceA112 sourceB112 sourceC112 difference raw4336; decide +kernel
    rw [ha]
    exact (canonical4336 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA112 + difference 5 0) (sourceB112 + difference 0 5) sourceC112) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1051) := by
    have ha : (tripleCharges (sourceA112 + difference 5 0) (sourceB112 + difference 0 5) sourceC112) = raw4337 := by
      apply Matrix.ext; unfold tripleCharges sourceA112 sourceB112 sourceC112 difference raw4337; decide +kernel
    rw [ha]
    exact (canonical4337 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA112 + difference 5 1) (sourceB112 + difference 1 5) sourceC112) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1046) := by
    have ha : (tripleCharges (sourceA112 + difference 5 1) (sourceB112 + difference 1 5) sourceC112) = raw4338 := by
      apply Matrix.ext; unfold tripleCharges sourceA112 sourceB112 sourceC112 difference raw4338; decide +kernel
    rw [ha]
    exact (canonical4338 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA112 + difference 5 2) (sourceB112 + difference 2 5) sourceC112) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1046) := by
    have ha : (tripleCharges (sourceA112 + difference 5 2) (sourceB112 + difference 2 5) sourceC112) = raw4339 := by
      apply Matrix.ext; unfold tripleCharges sourceA112 sourceB112 sourceC112 difference raw4339; decide +kernel
    rw [ha]
    exact (canonical4339 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA112 + difference 5 3) (sourceB112 + difference 3 5) sourceC112) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1046) := by
    have ha : (tripleCharges (sourceA112 + difference 5 3) (sourceB112 + difference 3 5) sourceC112) = raw4340 := by
      apply Matrix.ext; unfold tripleCharges sourceA112 sourceB112 sourceC112 difference raw4340; decide +kernel
    rw [ha]
    exact (canonical4340 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA112 + difference 5 4) (sourceB112 + difference 4 5) sourceC112) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1091) := by
    have ha : (tripleCharges (sourceA112 + difference 5 4) (sourceB112 + difference 4 5) sourceC112) = raw4341 := by
      apply Matrix.ext; unfold tripleCharges sourceA112 sourceB112 sourceC112 difference raw4341; decide +kernel
    rw [ha]
    exact (canonical4341 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA112 sourceB112 sourceC112
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm112, Integer.Sparse.eval]
  linarith only [hs]

def sourceA113 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceB113 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC113 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceForm113 : Integer.Sparse Master := [(Sum.inr 4890, 6), (Sum.inr 4897, 2), (Sum.inr 4899, 2), (Sum.inr 5252, 6), (Sum.inr 5261, 6), (Sum.inr 5268, 3), (Sum.inr 5296, 3), (Sum.inr 5312, 2)]

theorem sourceEq113 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm113 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA113 + difference 0 1) (sourceB113 + difference 1 0) sourceC113) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5261) := by
    have ha : (tripleCharges (sourceA113 + difference 0 1) (sourceB113 + difference 1 0) sourceC113) = raw4036 := by
      apply Matrix.ext; unfold tripleCharges sourceA113 sourceB113 sourceC113 difference raw4036; decide +kernel
    rw [ha]
    exact (canonical4036 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA113 + difference 0 2) (sourceB113 + difference 2 0) sourceC113) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5261) := by
    have ha : (tripleCharges (sourceA113 + difference 0 2) (sourceB113 + difference 2 0) sourceC113) = raw4342 := by
      apply Matrix.ext; unfold tripleCharges sourceA113 sourceB113 sourceC113 difference raw4342; decide +kernel
    rw [ha]
    exact (canonical4342 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA113 + difference 0 3) (sourceB113 + difference 3 0) sourceC113) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5261) := by
    have ha : (tripleCharges (sourceA113 + difference 0 3) (sourceB113 + difference 3 0) sourceC113) = raw4343 := by
      apply Matrix.ext; unfold tripleCharges sourceA113 sourceB113 sourceC113 difference raw4343; decide +kernel
    rw [ha]
    exact (canonical4343 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA113 + difference 0 4) (sourceB113 + difference 4 0) sourceC113) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5312) := by
    have ha : (tripleCharges (sourceA113 + difference 0 4) (sourceB113 + difference 4 0) sourceC113) = raw4344 := by
      apply Matrix.ext; unfold tripleCharges sourceA113 sourceB113 sourceC113 difference raw4344; decide +kernel
    rw [ha]
    exact (canonical4344 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA113 + difference 0 5) (sourceB113 + difference 5 0) sourceC113) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4897) := by
    have ha : (tripleCharges (sourceA113 + difference 0 5) (sourceB113 + difference 5 0) sourceC113) = raw4345 := by
      apply Matrix.ext; unfold tripleCharges sourceA113 sourceB113 sourceC113 difference raw4345; decide +kernel
    rw [ha]
    exact (canonical4345 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA113 + difference 1 0) (sourceB113 + difference 0 1) sourceC113) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4890) := by
    have ha : (tripleCharges (sourceA113 + difference 1 0) (sourceB113 + difference 0 1) sourceC113) = raw4346 := by
      apply Matrix.ext; unfold tripleCharges sourceA113 sourceB113 sourceC113 difference raw4346; decide +kernel
    rw [ha]
    exact (canonical4346 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA113 + difference 1 2) (sourceB113 + difference 2 1) sourceC113) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5252) := by
    have ha : (tripleCharges (sourceA113 + difference 1 2) (sourceB113 + difference 2 1) sourceC113) = raw4347 := by
      apply Matrix.ext; unfold tripleCharges sourceA113 sourceB113 sourceC113 difference raw4347; decide +kernel
    rw [ha]
    exact (canonical4347 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA113 + difference 1 3) (sourceB113 + difference 3 1) sourceC113) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5252) := by
    have ha : (tripleCharges (sourceA113 + difference 1 3) (sourceB113 + difference 3 1) sourceC113) = raw4348 := by
      apply Matrix.ext; unfold tripleCharges sourceA113 sourceB113 sourceC113 difference raw4348; decide +kernel
    rw [ha]
    exact (canonical4348 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA113 + difference 1 4) (sourceB113 + difference 4 1) sourceC113) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5296) := by
    have ha : (tripleCharges (sourceA113 + difference 1 4) (sourceB113 + difference 4 1) sourceC113) = raw4349 := by
      apply Matrix.ext; unfold tripleCharges sourceA113 sourceB113 sourceC113 difference raw4349; decide +kernel
    rw [ha]
    exact (canonical4349 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA113 + difference 1 5) (sourceB113 + difference 5 1) sourceC113) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4890) := by
    have ha : (tripleCharges (sourceA113 + difference 1 5) (sourceB113 + difference 5 1) sourceC113) = raw4350 := by
      apply Matrix.ext; unfold tripleCharges sourceA113 sourceB113 sourceC113 difference raw4350; decide +kernel
    rw [ha]
    exact (canonical4350 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA113 + difference 2 0) (sourceB113 + difference 0 2) sourceC113) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4890) := by
    have ha : (tripleCharges (sourceA113 + difference 2 0) (sourceB113 + difference 0 2) sourceC113) = raw3876 := by
      apply Matrix.ext; unfold tripleCharges sourceA113 sourceB113 sourceC113 difference raw3876; decide +kernel
    rw [ha]
    exact (canonical3876 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA113 + difference 2 1) (sourceB113 + difference 1 2) sourceC113) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5252) := by
    have ha : (tripleCharges (sourceA113 + difference 2 1) (sourceB113 + difference 1 2) sourceC113) = raw4044 := by
      apply Matrix.ext; unfold tripleCharges sourceA113 sourceB113 sourceC113 difference raw4044; decide +kernel
    rw [ha]
    exact (canonical4044 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA113 + difference 2 3) (sourceB113 + difference 3 2) sourceC113) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5252) := by
    have ha : (tripleCharges (sourceA113 + difference 2 3) (sourceB113 + difference 3 2) sourceC113) = raw4351 := by
      apply Matrix.ext; unfold tripleCharges sourceA113 sourceB113 sourceC113 difference raw4351; decide +kernel
    rw [ha]
    exact (canonical4351 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA113 + difference 2 4) (sourceB113 + difference 4 2) sourceC113) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5296) := by
    have ha : (tripleCharges (sourceA113 + difference 2 4) (sourceB113 + difference 4 2) sourceC113) = raw4352 := by
      apply Matrix.ext; unfold tripleCharges sourceA113 sourceB113 sourceC113 difference raw4352; decide +kernel
    rw [ha]
    exact (canonical4352 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA113 + difference 2 5) (sourceB113 + difference 5 2) sourceC113) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4890) := by
    have ha : (tripleCharges (sourceA113 + difference 2 5) (sourceB113 + difference 5 2) sourceC113) = raw3857 := by
      apply Matrix.ext; unfold tripleCharges sourceA113 sourceB113 sourceC113 difference raw3857; decide +kernel
    rw [ha]
    exact (canonical3857 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA113 + difference 3 0) (sourceB113 + difference 0 3) sourceC113) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4890) := by
    have ha : (tripleCharges (sourceA113 + difference 3 0) (sourceB113 + difference 0 3) sourceC113) = raw3684 := by
      apply Matrix.ext; unfold tripleCharges sourceA113 sourceB113 sourceC113 difference raw3684; decide +kernel
    rw [ha]
    exact (canonical3684 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA113 + difference 3 1) (sourceB113 + difference 1 3) sourceC113) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5252) := by
    have ha : (tripleCharges (sourceA113 + difference 3 1) (sourceB113 + difference 1 3) sourceC113) = raw4048 := by
      apply Matrix.ext; unfold tripleCharges sourceA113 sourceB113 sourceC113 difference raw4048; decide +kernel
    rw [ha]
    exact (canonical4048 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA113 + difference 3 2) (sourceB113 + difference 2 3) sourceC113) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5252) := by
    have ha : (tripleCharges (sourceA113 + difference 3 2) (sourceB113 + difference 2 3) sourceC113) = raw4235 := by
      apply Matrix.ext; unfold tripleCharges sourceA113 sourceB113 sourceC113 difference raw4235; decide +kernel
    rw [ha]
    exact (canonical4235 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA113 + difference 3 4) (sourceB113 + difference 4 3) sourceC113) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5296) := by
    have ha : (tripleCharges (sourceA113 + difference 3 4) (sourceB113 + difference 4 3) sourceC113) = raw4236 := by
      apply Matrix.ext; unfold tripleCharges sourceA113 sourceB113 sourceC113 difference raw4236; decide +kernel
    rw [ha]
    exact (canonical4236 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA113 + difference 3 5) (sourceB113 + difference 5 3) sourceC113) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4890) := by
    have ha : (tripleCharges (sourceA113 + difference 3 5) (sourceB113 + difference 5 3) sourceC113) = raw3658 := by
      apply Matrix.ext; unfold tripleCharges sourceA113 sourceB113 sourceC113 difference raw3658; decide +kernel
    rw [ha]
    exact (canonical3658 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA113 + difference 4 0) (sourceB113 + difference 0 4) sourceC113) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4899) := by
    have ha : (tripleCharges (sourceA113 + difference 4 0) (sourceB113 + difference 0 4) sourceC113) = raw3683 := by
      apply Matrix.ext; unfold tripleCharges sourceA113 sourceB113 sourceC113 difference raw3683; decide +kernel
    rw [ha]
    exact (canonical3683 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA113 + difference 4 1) (sourceB113 + difference 1 4) sourceC113) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5268) := by
    have ha : (tripleCharges (sourceA113 + difference 4 1) (sourceB113 + difference 1 4) sourceC113) = raw4244 := by
      apply Matrix.ext; unfold tripleCharges sourceA113 sourceB113 sourceC113 difference raw4244; decide +kernel
    rw [ha]
    exact (canonical4244 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA113 + difference 4 2) (sourceB113 + difference 2 4) sourceC113) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5268) := by
    have ha : (tripleCharges (sourceA113 + difference 4 2) (sourceB113 + difference 2 4) sourceC113) = raw4038 := by
      apply Matrix.ext; unfold tripleCharges sourceA113 sourceB113 sourceC113 difference raw4038; decide +kernel
    rw [ha]
    exact (canonical4038 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA113 + difference 4 3) (sourceB113 + difference 3 4) sourceC113) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5268) := by
    have ha : (tripleCharges (sourceA113 + difference 4 3) (sourceB113 + difference 3 4) sourceC113) = raw4039 := by
      apply Matrix.ext; unfold tripleCharges sourceA113 sourceB113 sourceC113 difference raw4039; decide +kernel
    rw [ha]
    exact (canonical4039 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA113 + difference 4 5) (sourceB113 + difference 5 4) sourceC113) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4899) := by
    have ha : (tripleCharges (sourceA113 + difference 4 5) (sourceB113 + difference 5 4) sourceC113) = raw3657 := by
      apply Matrix.ext; unfold tripleCharges sourceA113 sourceB113 sourceC113 difference raw3657; decide +kernel
    rw [ha]
    exact (canonical3657 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA113 + difference 5 0) (sourceB113 + difference 0 5) sourceC113) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4897) := by
    have ha : (tripleCharges (sourceA113 + difference 5 0) (sourceB113 + difference 0 5) sourceC113) = raw4353 := by
      apply Matrix.ext; unfold tripleCharges sourceA113 sourceB113 sourceC113 difference raw4353; decide +kernel
    rw [ha]
    exact (canonical4353 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA113 + difference 5 1) (sourceB113 + difference 1 5) sourceC113) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5261) := by
    have ha : (tripleCharges (sourceA113 + difference 5 1) (sourceB113 + difference 1 5) sourceC113) = raw4058 := by
      apply Matrix.ext; unfold tripleCharges sourceA113 sourceB113 sourceC113 difference raw4058; decide +kernel
    rw [ha]
    exact (canonical4058 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA113 + difference 5 2) (sourceB113 + difference 2 5) sourceC113) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5261) := by
    have ha : (tripleCharges (sourceA113 + difference 5 2) (sourceB113 + difference 2 5) sourceC113) = raw4354 := by
      apply Matrix.ext; unfold tripleCharges sourceA113 sourceB113 sourceC113 difference raw4354; decide +kernel
    rw [ha]
    exact (canonical4354 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA113 + difference 5 3) (sourceB113 + difference 3 5) sourceC113) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5261) := by
    have ha : (tripleCharges (sourceA113 + difference 5 3) (sourceB113 + difference 3 5) sourceC113) = raw4355 := by
      apply Matrix.ext; unfold tripleCharges sourceA113 sourceB113 sourceC113 difference raw4355; decide +kernel
    rw [ha]
    exact (canonical4355 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA113 + difference 5 4) (sourceB113 + difference 4 5) sourceC113) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5312) := by
    have ha : (tripleCharges (sourceA113 + difference 5 4) (sourceB113 + difference 4 5) sourceC113) = raw4356 := by
      apply Matrix.ext; unfold tripleCharges sourceA113 sourceB113 sourceC113 difference raw4356; decide +kernel
    rw [ha]
    exact (canonical4356 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA113 sourceB113 sourceC113
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm113, Integer.Sparse.eval]
  linarith only [hs]

def sourceA114 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceB114 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC114 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceForm114 : Integer.Sparse Master := [(Sum.inr 2247, 3), (Sum.inr 2268, 1), (Sum.inr 2281, 1), (Sum.inr 2712, 6), (Sum.inr 2726, 3), (Sum.inr 2734, 3), (Sum.inr 2755, 3), (Sum.inr 2770, 3), (Sum.inr 2778, 1), (Sum.inr 2790, 1), (Sum.inr 3090, 3), (Sum.inr 3114, 1), (Sum.inr 3126, 1)]

theorem sourceEq114 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm114 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA114 + difference 0 1) (sourceB114 + difference 1 0) sourceC114) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3090) := by
    have ha : (tripleCharges (sourceA114 + difference 0 1) (sourceB114 + difference 1 0) sourceC114) = raw4062 := by
      apply Matrix.ext; unfold tripleCharges sourceA114 sourceB114 sourceC114 difference raw4062; decide +kernel
    rw [ha]
    exact (canonical4062 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA114 + difference 0 2) (sourceB114 + difference 2 0) sourceC114) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3090) := by
    have ha : (tripleCharges (sourceA114 + difference 0 2) (sourceB114 + difference 2 0) sourceC114) = raw4357 := by
      apply Matrix.ext; unfold tripleCharges sourceA114 sourceB114 sourceC114 difference raw4357; decide +kernel
    rw [ha]
    exact (canonical4357 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA114 + difference 0 3) (sourceB114 + difference 3 0) sourceC114) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3090) := by
    have ha : (tripleCharges (sourceA114 + difference 0 3) (sourceB114 + difference 3 0) sourceC114) = raw4358 := by
      apply Matrix.ext; unfold tripleCharges sourceA114 sourceB114 sourceC114 difference raw4358; decide +kernel
    rw [ha]
    exact (canonical4358 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA114 + difference 0 4) (sourceB114 + difference 4 0) sourceC114) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3126) := by
    have ha : (tripleCharges (sourceA114 + difference 0 4) (sourceB114 + difference 4 0) sourceC114) = raw4359 := by
      apply Matrix.ext; unfold tripleCharges sourceA114 sourceB114 sourceC114 difference raw4359; decide +kernel
    rw [ha]
    exact (canonical4359 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA114 + difference 0 5) (sourceB114 + difference 5 0) sourceC114) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3114) := by
    have ha : (tripleCharges (sourceA114 + difference 0 5) (sourceB114 + difference 5 0) sourceC114) = raw4360 := by
      apply Matrix.ext; unfold tripleCharges sourceA114 sourceB114 sourceC114 difference raw4360; decide +kernel
    rw [ha]
    exact (canonical4360 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA114 + difference 1 0) (sourceB114 + difference 0 1) sourceC114) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2247) := by
    have ha : (tripleCharges (sourceA114 + difference 1 0) (sourceB114 + difference 0 1) sourceC114) = raw4361 := by
      apply Matrix.ext; unfold tripleCharges sourceA114 sourceB114 sourceC114 difference raw4361; decide +kernel
    rw [ha]
    exact (canonical4361 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA114 + difference 1 2) (sourceB114 + difference 2 1) sourceC114) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2712) := by
    have ha : (tripleCharges (sourceA114 + difference 1 2) (sourceB114 + difference 2 1) sourceC114) = raw4362 := by
      apply Matrix.ext; unfold tripleCharges sourceA114 sourceB114 sourceC114 difference raw4362; decide +kernel
    rw [ha]
    exact (canonical4362 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA114 + difference 1 3) (sourceB114 + difference 3 1) sourceC114) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2712) := by
    have ha : (tripleCharges (sourceA114 + difference 1 3) (sourceB114 + difference 3 1) sourceC114) = raw4363 := by
      apply Matrix.ext; unfold tripleCharges sourceA114 sourceB114 sourceC114 difference raw4363; decide +kernel
    rw [ha]
    exact (canonical4363 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA114 + difference 1 4) (sourceB114 + difference 4 1) sourceC114) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2770) := by
    have ha : (tripleCharges (sourceA114 + difference 1 4) (sourceB114 + difference 4 1) sourceC114) = raw4364 := by
      apply Matrix.ext; unfold tripleCharges sourceA114 sourceB114 sourceC114 difference raw4364; decide +kernel
    rw [ha]
    exact (canonical4364 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA114 + difference 1 5) (sourceB114 + difference 5 1) sourceC114) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2755) := by
    have ha : (tripleCharges (sourceA114 + difference 1 5) (sourceB114 + difference 5 1) sourceC114) = raw4365 := by
      apply Matrix.ext; unfold tripleCharges sourceA114 sourceB114 sourceC114 difference raw4365; decide +kernel
    rw [ha]
    exact (canonical4365 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA114 + difference 2 0) (sourceB114 + difference 0 2) sourceC114) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2247) := by
    have ha : (tripleCharges (sourceA114 + difference 2 0) (sourceB114 + difference 0 2) sourceC114) = raw3898 := by
      apply Matrix.ext; unfold tripleCharges sourceA114 sourceB114 sourceC114 difference raw3898; decide +kernel
    rw [ha]
    exact (canonical3898 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA114 + difference 2 1) (sourceB114 + difference 1 2) sourceC114) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2712) := by
    have ha : (tripleCharges (sourceA114 + difference 2 1) (sourceB114 + difference 1 2) sourceC114) = raw4070 := by
      apply Matrix.ext; unfold tripleCharges sourceA114 sourceB114 sourceC114 difference raw4070; decide +kernel
    rw [ha]
    exact (canonical4070 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA114 + difference 2 3) (sourceB114 + difference 3 2) sourceC114) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2712) := by
    have ha : (tripleCharges (sourceA114 + difference 2 3) (sourceB114 + difference 3 2) sourceC114) = raw4366 := by
      apply Matrix.ext; unfold tripleCharges sourceA114 sourceB114 sourceC114 difference raw4366; decide +kernel
    rw [ha]
    exact (canonical4366 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA114 + difference 2 4) (sourceB114 + difference 4 2) sourceC114) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2770) := by
    have ha : (tripleCharges (sourceA114 + difference 2 4) (sourceB114 + difference 4 2) sourceC114) = raw4367 := by
      apply Matrix.ext; unfold tripleCharges sourceA114 sourceB114 sourceC114 difference raw4367; decide +kernel
    rw [ha]
    exact (canonical4367 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA114 + difference 2 5) (sourceB114 + difference 5 2) sourceC114) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2755) := by
    have ha : (tripleCharges (sourceA114 + difference 2 5) (sourceB114 + difference 5 2) sourceC114) = raw3879 := by
      apply Matrix.ext; unfold tripleCharges sourceA114 sourceB114 sourceC114 difference raw3879; decide +kernel
    rw [ha]
    exact (canonical3879 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA114 + difference 3 0) (sourceB114 + difference 0 3) sourceC114) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2247) := by
    have ha : (tripleCharges (sourceA114 + difference 3 0) (sourceB114 + difference 0 3) sourceC114) = raw3714 := by
      apply Matrix.ext; unfold tripleCharges sourceA114 sourceB114 sourceC114 difference raw3714; decide +kernel
    rw [ha]
    exact (canonical3714 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA114 + difference 3 1) (sourceB114 + difference 1 3) sourceC114) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2712) := by
    have ha : (tripleCharges (sourceA114 + difference 3 1) (sourceB114 + difference 1 3) sourceC114) = raw4074 := by
      apply Matrix.ext; unfold tripleCharges sourceA114 sourceB114 sourceC114 difference raw4074; decide +kernel
    rw [ha]
    exact (canonical4074 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA114 + difference 3 2) (sourceB114 + difference 2 3) sourceC114) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2712) := by
    have ha : (tripleCharges (sourceA114 + difference 3 2) (sourceB114 + difference 2 3) sourceC114) = raw4253 := by
      apply Matrix.ext; unfold tripleCharges sourceA114 sourceB114 sourceC114 difference raw4253; decide +kernel
    rw [ha]
    exact (canonical4253 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA114 + difference 3 4) (sourceB114 + difference 4 3) sourceC114) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2770) := by
    have ha : (tripleCharges (sourceA114 + difference 3 4) (sourceB114 + difference 4 3) sourceC114) = raw4254 := by
      apply Matrix.ext; unfold tripleCharges sourceA114 sourceB114 sourceC114 difference raw4254; decide +kernel
    rw [ha]
    exact (canonical4254 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA114 + difference 3 5) (sourceB114 + difference 5 3) sourceC114) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2755) := by
    have ha : (tripleCharges (sourceA114 + difference 3 5) (sourceB114 + difference 5 3) sourceC114) = raw3688 := by
      apply Matrix.ext; unfold tripleCharges sourceA114 sourceB114 sourceC114 difference raw3688; decide +kernel
    rw [ha]
    exact (canonical3688 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA114 + difference 4 0) (sourceB114 + difference 0 4) sourceC114) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2281) := by
    have ha : (tripleCharges (sourceA114 + difference 4 0) (sourceB114 + difference 0 4) sourceC114) = raw3713 := by
      apply Matrix.ext; unfold tripleCharges sourceA114 sourceB114 sourceC114 difference raw3713; decide +kernel
    rw [ha]
    exact (canonical3713 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA114 + difference 4 1) (sourceB114 + difference 1 4) sourceC114) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2734) := by
    have ha : (tripleCharges (sourceA114 + difference 4 1) (sourceB114 + difference 1 4) sourceC114) = raw4262 := by
      apply Matrix.ext; unfold tripleCharges sourceA114 sourceB114 sourceC114 difference raw4262; decide +kernel
    rw [ha]
    exact (canonical4262 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA114 + difference 4 2) (sourceB114 + difference 2 4) sourceC114) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2734) := by
    have ha : (tripleCharges (sourceA114 + difference 4 2) (sourceB114 + difference 2 4) sourceC114) = raw4064 := by
      apply Matrix.ext; unfold tripleCharges sourceA114 sourceB114 sourceC114 difference raw4064; decide +kernel
    rw [ha]
    exact (canonical4064 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA114 + difference 4 3) (sourceB114 + difference 3 4) sourceC114) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2734) := by
    have ha : (tripleCharges (sourceA114 + difference 4 3) (sourceB114 + difference 3 4) sourceC114) = raw4065 := by
      apply Matrix.ext; unfold tripleCharges sourceA114 sourceB114 sourceC114 difference raw4065; decide +kernel
    rw [ha]
    exact (canonical4065 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA114 + difference 4 5) (sourceB114 + difference 5 4) sourceC114) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2778) := by
    have ha : (tripleCharges (sourceA114 + difference 4 5) (sourceB114 + difference 5 4) sourceC114) = raw3687 := by
      apply Matrix.ext; unfold tripleCharges sourceA114 sourceB114 sourceC114 difference raw3687; decide +kernel
    rw [ha]
    exact (canonical3687 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA114 + difference 5 0) (sourceB114 + difference 0 5) sourceC114) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2268) := by
    have ha : (tripleCharges (sourceA114 + difference 5 0) (sourceB114 + difference 0 5) sourceC114) = raw4368 := by
      apply Matrix.ext; unfold tripleCharges sourceA114 sourceB114 sourceC114 difference raw4368; decide +kernel
    rw [ha]
    exact (canonical4368 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA114 + difference 5 1) (sourceB114 + difference 1 5) sourceC114) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2726) := by
    have ha : (tripleCharges (sourceA114 + difference 5 1) (sourceB114 + difference 1 5) sourceC114) = raw4084 := by
      apply Matrix.ext; unfold tripleCharges sourceA114 sourceB114 sourceC114 difference raw4084; decide +kernel
    rw [ha]
    exact (canonical4084 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA114 + difference 5 2) (sourceB114 + difference 2 5) sourceC114) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2726) := by
    have ha : (tripleCharges (sourceA114 + difference 5 2) (sourceB114 + difference 2 5) sourceC114) = raw4369 := by
      apply Matrix.ext; unfold tripleCharges sourceA114 sourceB114 sourceC114 difference raw4369; decide +kernel
    rw [ha]
    exact (canonical4369 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA114 + difference 5 3) (sourceB114 + difference 3 5) sourceC114) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2726) := by
    have ha : (tripleCharges (sourceA114 + difference 5 3) (sourceB114 + difference 3 5) sourceC114) = raw4370 := by
      apply Matrix.ext; unfold tripleCharges sourceA114 sourceB114 sourceC114 difference raw4370; decide +kernel
    rw [ha]
    exact (canonical4370 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA114 + difference 5 4) (sourceB114 + difference 4 5) sourceC114) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2790) := by
    have ha : (tripleCharges (sourceA114 + difference 5 4) (sourceB114 + difference 4 5) sourceC114) = raw4371 := by
      apply Matrix.ext; unfold tripleCharges sourceA114 sourceB114 sourceC114 difference raw4371; decide +kernel
    rw [ha]
    exact (canonical4371 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA114 sourceB114 sourceC114
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm114, Integer.Sparse.eval]
  linarith only [hs]

def sourceA115 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceB115 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC115 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceForm115 : Integer.Sparse Master := [(Sum.inr 2292, 1), (Sum.inr 3545, 3), (Sum.inr 3634, 1), (Sum.inr 3636, 1), (Sum.inr 4085, -1)]

theorem sourceEq115 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm115 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA115 + difference 0 0) (sourceB115 + difference 0 0) sourceC115) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3634) := by
    have ha : (tripleCharges (sourceA115 + difference 0 0) (sourceB115 + difference 0 0) sourceC115) = raw4097 := by
      apply Matrix.ext; unfold tripleCharges sourceA115 sourceB115 sourceC115 difference raw4097; decide +kernel
    rw [ha]
    exact (canonical4097 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA115 + difference 0 1) (sourceB115 + difference 1 0) sourceC115) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3545) := by
    have ha : (tripleCharges (sourceA115 + difference 0 1) (sourceB115 + difference 1 0) sourceC115) = raw4089 := by
      apply Matrix.ext; unfold tripleCharges sourceA115 sourceB115 sourceC115 difference raw4089; decide +kernel
    rw [ha]
    exact (canonical4089 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA115 + difference 0 2) (sourceB115 + difference 2 0) sourceC115) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3545) := by
    have ha : (tripleCharges (sourceA115 + difference 0 2) (sourceB115 + difference 2 0) sourceC115) = raw4372 := by
      apply Matrix.ext; unfold tripleCharges sourceA115 sourceB115 sourceC115 difference raw4372; decide +kernel
    rw [ha]
    exact (canonical4372 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA115 + difference 0 3) (sourceB115 + difference 3 0) sourceC115) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3545) := by
    have ha : (tripleCharges (sourceA115 + difference 0 3) (sourceB115 + difference 3 0) sourceC115) = raw4373 := by
      apply Matrix.ext; unfold tripleCharges sourceA115 sourceB115 sourceC115 difference raw4373; decide +kernel
    rw [ha]
    exact (canonical4373 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA115 + difference 0 4) (sourceB115 + difference 4 0) sourceC115) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3636) := by
    have ha : (tripleCharges (sourceA115 + difference 0 4) (sourceB115 + difference 4 0) sourceC115) = raw4374 := by
      apply Matrix.ext; unfold tripleCharges sourceA115 sourceB115 sourceC115 difference raw4374; decide +kernel
    rw [ha]
    exact (canonical4374 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA115 + difference 0 5) (sourceB115 + difference 5 0) sourceC115) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2292) := by
    have ha : (tripleCharges (sourceA115 + difference 0 5) (sourceB115 + difference 5 0) sourceC115) = raw4375 := by
      apply Matrix.ext; unfold tripleCharges sourceA115 sourceB115 sourceC115 difference raw4375; decide +kernel
    rw [ha]
    exact (canonical4375 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA115 + sourceB115) sourceC115) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA115 + sourceB115) sourceC115) = raw3721 := by
      apply Matrix.ext; unfold doubleCharges sourceA115 sourceB115 sourceC115 raw3721; decide +kernel
    rw [ha]
    exact (canonical3721 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA115 sourceB115 sourceC115
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm115, Integer.Sparse.eval]
  linarith only [hs]

def sourceA116 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceB116 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC116 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceForm116 : Integer.Sparse Master := [(Sum.inr 2290, 3), (Sum.inr 2292, 1), (Sum.inr 2294, 1), (Sum.inr 3634, 1), (Sum.inr 4085, -1)]

theorem sourceEq116 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm116 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA116 + difference 0 0) (sourceB116 + difference 0 0) sourceC116) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3634) := by
    have ha : (tripleCharges (sourceA116 + difference 0 0) (sourceB116 + difference 0 0) sourceC116) = raw4097 := by
      apply Matrix.ext; unfold tripleCharges sourceA116 sourceB116 sourceC116 difference raw4097; decide +kernel
    rw [ha]
    exact (canonical4097 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA116 + difference 1 0) (sourceB116 + difference 0 1) sourceC116) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2290) := by
    have ha : (tripleCharges (sourceA116 + difference 1 0) (sourceB116 + difference 0 1) sourceC116) = raw4376 := by
      apply Matrix.ext; unfold tripleCharges sourceA116 sourceB116 sourceC116 difference raw4376; decide +kernel
    rw [ha]
    exact (canonical4376 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA116 + difference 2 0) (sourceB116 + difference 0 2) sourceC116) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2290) := by
    have ha : (tripleCharges (sourceA116 + difference 2 0) (sourceB116 + difference 0 2) sourceC116) = raw4377 := by
      apply Matrix.ext; unfold tripleCharges sourceA116 sourceB116 sourceC116 difference raw4377; decide +kernel
    rw [ha]
    exact (canonical4377 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA116 + difference 3 0) (sourceB116 + difference 0 3) sourceC116) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2290) := by
    have ha : (tripleCharges (sourceA116 + difference 3 0) (sourceB116 + difference 0 3) sourceC116) = raw4272 := by
      apply Matrix.ext; unfold tripleCharges sourceA116 sourceB116 sourceC116 difference raw4272; decide +kernel
    rw [ha]
    exact (canonical4272 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA116 + difference 4 0) (sourceB116 + difference 0 4) sourceC116) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2294) := by
    have ha : (tripleCharges (sourceA116 + difference 4 0) (sourceB116 + difference 0 4) sourceC116) = raw4091 := by
      apply Matrix.ext; unfold tripleCharges sourceA116 sourceB116 sourceC116 difference raw4091; decide +kernel
    rw [ha]
    exact (canonical4091 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA116 + difference 5 0) (sourceB116 + difference 0 5) sourceC116) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2292) := by
    have ha : (tripleCharges (sourceA116 + difference 5 0) (sourceB116 + difference 0 5) sourceC116) = raw4378 := by
      apply Matrix.ext; unfold tripleCharges sourceA116 sourceB116 sourceC116 difference raw4378; decide +kernel
    rw [ha]
    exact (canonical4378 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA116 + sourceB116) sourceC116) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA116 + sourceB116) sourceC116) = raw3721 := by
      apply Matrix.ext; unfold doubleCharges sourceA116 sourceB116 sourceC116 raw3721; decide +kernel
    rw [ha]
    exact (canonical3721 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA116 sourceB116 sourceC116
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm116, Integer.Sparse.eval]
  linarith only [hs]

def sourceA117 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB117 : Charge := ![1, 0, 0, 0, 2, -3]
def sourceC117 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceForm117 : Integer.Sparse Master := [(Sum.inr 4276, 3), (Sum.inr 4280, 1), (Sum.inr 4285, 1), (Sum.inr 4572, 3), (Sum.inr 4621, 1), (Sum.inr 4747, 6), (Sum.inr 4754, 3), (Sum.inr 4871, 3), (Sum.inr 4898, 3), (Sum.inr 4899, 1), (Sum.inr 5302, 3), (Sum.inr 5310, 1), (Sum.inr 5456, 1)]

theorem sourceEq117 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm117 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA117 + difference 0 1) (sourceB117 + difference 1 0) sourceC117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4898) := by
    have ha : (tripleCharges (sourceA117 + difference 0 1) (sourceB117 + difference 1 0) sourceC117) = raw2657 := by
      apply Matrix.ext; unfold tripleCharges sourceA117 sourceB117 sourceC117 difference raw2657; decide +kernel
    rw [ha]
    exact (canonical2657 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA117 + difference 0 2) (sourceB117 + difference 2 0) sourceC117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4898) := by
    have ha : (tripleCharges (sourceA117 + difference 0 2) (sourceB117 + difference 2 0) sourceC117) = raw2658 := by
      apply Matrix.ext; unfold tripleCharges sourceA117 sourceB117 sourceC117 difference raw2658; decide +kernel
    rw [ha]
    exact (canonical2658 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA117 + difference 0 3) (sourceB117 + difference 3 0) sourceC117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4898) := by
    have ha : (tripleCharges (sourceA117 + difference 0 3) (sourceB117 + difference 3 0) sourceC117) = raw2659 := by
      apply Matrix.ext; unfold tripleCharges sourceA117 sourceB117 sourceC117 difference raw2659; decide +kernel
    rw [ha]
    exact (canonical2659 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA117 + difference 0 4) (sourceB117 + difference 4 0) sourceC117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4899) := by
    have ha : (tripleCharges (sourceA117 + difference 0 4) (sourceB117 + difference 4 0) sourceC117) = raw2660 := by
      apply Matrix.ext; unfold tripleCharges sourceA117 sourceB117 sourceC117 difference raw2660; decide +kernel
    rw [ha]
    exact (canonical2660 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA117 + difference 0 5) (sourceB117 + difference 5 0) sourceC117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5456) := by
    have ha : (tripleCharges (sourceA117 + difference 0 5) (sourceB117 + difference 5 0) sourceC117) = raw4379 := by
      apply Matrix.ext; unfold tripleCharges sourceA117 sourceB117 sourceC117 difference raw4379; decide +kernel
    rw [ha]
    exact (canonical4379 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA117 + difference 1 0) (sourceB117 + difference 0 1) sourceC117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4572) := by
    have ha : (tripleCharges (sourceA117 + difference 1 0) (sourceB117 + difference 0 1) sourceC117) = raw4380 := by
      apply Matrix.ext; unfold tripleCharges sourceA117 sourceB117 sourceC117 difference raw4380; decide +kernel
    rw [ha]
    exact (canonical4380 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA117 + difference 1 2) (sourceB117 + difference 2 1) sourceC117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4747) := by
    have ha : (tripleCharges (sourceA117 + difference 1 2) (sourceB117 + difference 2 1) sourceC117) = raw4381 := by
      apply Matrix.ext; unfold tripleCharges sourceA117 sourceB117 sourceC117 difference raw4381; decide +kernel
    rw [ha]
    exact (canonical4381 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA117 + difference 1 3) (sourceB117 + difference 3 1) sourceC117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4747) := by
    have ha : (tripleCharges (sourceA117 + difference 1 3) (sourceB117 + difference 3 1) sourceC117) = raw4382 := by
      apply Matrix.ext; unfold tripleCharges sourceA117 sourceB117 sourceC117 difference raw4382; decide +kernel
    rw [ha]
    exact (canonical4382 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA117 + difference 1 4) (sourceB117 + difference 4 1) sourceC117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4754) := by
    have ha : (tripleCharges (sourceA117 + difference 1 4) (sourceB117 + difference 4 1) sourceC117) = raw4383 := by
      apply Matrix.ext; unfold tripleCharges sourceA117 sourceB117 sourceC117 difference raw4383; decide +kernel
    rw [ha]
    exact (canonical4383 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA117 + difference 1 5) (sourceB117 + difference 5 1) sourceC117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA117 + difference 1 5) (sourceB117 + difference 5 1) sourceC117) = raw2636 := by
      apply Matrix.ext; unfold tripleCharges sourceA117 sourceB117 sourceC117 difference raw2636; decide +kernel
    rw [ha]
    exact (canonical2636 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA117 + difference 2 0) (sourceB117 + difference 0 2) sourceC117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4572) := by
    have ha : (tripleCharges (sourceA117 + difference 2 0) (sourceB117 + difference 0 2) sourceC117) = raw4384 := by
      apply Matrix.ext; unfold tripleCharges sourceA117 sourceB117 sourceC117 difference raw4384; decide +kernel
    rw [ha]
    exact (canonical4384 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA117 + difference 2 1) (sourceB117 + difference 1 2) sourceC117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4747) := by
    have ha : (tripleCharges (sourceA117 + difference 2 1) (sourceB117 + difference 1 2) sourceC117) = raw4385 := by
      apply Matrix.ext; unfold tripleCharges sourceA117 sourceB117 sourceC117 difference raw4385; decide +kernel
    rw [ha]
    exact (canonical4385 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA117 + difference 2 3) (sourceB117 + difference 3 2) sourceC117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4747) := by
    have ha : (tripleCharges (sourceA117 + difference 2 3) (sourceB117 + difference 3 2) sourceC117) = raw4386 := by
      apply Matrix.ext; unfold tripleCharges sourceA117 sourceB117 sourceC117 difference raw4386; decide +kernel
    rw [ha]
    exact (canonical4386 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA117 + difference 2 4) (sourceB117 + difference 4 2) sourceC117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4754) := by
    have ha : (tripleCharges (sourceA117 + difference 2 4) (sourceB117 + difference 4 2) sourceC117) = raw4387 := by
      apply Matrix.ext; unfold tripleCharges sourceA117 sourceB117 sourceC117 difference raw4387; decide +kernel
    rw [ha]
    exact (canonical4387 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA117 + difference 2 5) (sourceB117 + difference 5 2) sourceC117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA117 + difference 2 5) (sourceB117 + difference 5 2) sourceC117) = raw2641 := by
      apply Matrix.ext; unfold tripleCharges sourceA117 sourceB117 sourceC117 difference raw2641; decide +kernel
    rw [ha]
    exact (canonical2641 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA117 + difference 3 0) (sourceB117 + difference 0 3) sourceC117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4572) := by
    have ha : (tripleCharges (sourceA117 + difference 3 0) (sourceB117 + difference 0 3) sourceC117) = raw4388 := by
      apply Matrix.ext; unfold tripleCharges sourceA117 sourceB117 sourceC117 difference raw4388; decide +kernel
    rw [ha]
    exact (canonical4388 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA117 + difference 3 1) (sourceB117 + difference 1 3) sourceC117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4747) := by
    have ha : (tripleCharges (sourceA117 + difference 3 1) (sourceB117 + difference 1 3) sourceC117) = raw4389 := by
      apply Matrix.ext; unfold tripleCharges sourceA117 sourceB117 sourceC117 difference raw4389; decide +kernel
    rw [ha]
    exact (canonical4389 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA117 + difference 3 2) (sourceB117 + difference 2 3) sourceC117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4747) := by
    have ha : (tripleCharges (sourceA117 + difference 3 2) (sourceB117 + difference 2 3) sourceC117) = raw4390 := by
      apply Matrix.ext; unfold tripleCharges sourceA117 sourceB117 sourceC117 difference raw4390; decide +kernel
    rw [ha]
    exact (canonical4390 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA117 + difference 3 4) (sourceB117 + difference 4 3) sourceC117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4754) := by
    have ha : (tripleCharges (sourceA117 + difference 3 4) (sourceB117 + difference 4 3) sourceC117) = raw4391 := by
      apply Matrix.ext; unfold tripleCharges sourceA117 sourceB117 sourceC117 difference raw4391; decide +kernel
    rw [ha]
    exact (canonical4391 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA117 + difference 3 5) (sourceB117 + difference 5 3) sourceC117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA117 + difference 3 5) (sourceB117 + difference 5 3) sourceC117) = raw2646 := by
      apply Matrix.ext; unfold tripleCharges sourceA117 sourceB117 sourceC117 difference raw2646; decide +kernel
    rw [ha]
    exact (canonical2646 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA117 + difference 4 0) (sourceB117 + difference 0 4) sourceC117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4621) := by
    have ha : (tripleCharges (sourceA117 + difference 4 0) (sourceB117 + difference 0 4) sourceC117) = raw4392 := by
      apply Matrix.ext; unfold tripleCharges sourceA117 sourceB117 sourceC117 difference raw4392; decide +kernel
    rw [ha]
    exact (canonical4392 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA117 + difference 4 1) (sourceB117 + difference 1 4) sourceC117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4871) := by
    have ha : (tripleCharges (sourceA117 + difference 4 1) (sourceB117 + difference 1 4) sourceC117) = raw4393 := by
      apply Matrix.ext; unfold tripleCharges sourceA117 sourceB117 sourceC117 difference raw4393; decide +kernel
    rw [ha]
    exact (canonical4393 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA117 + difference 4 2) (sourceB117 + difference 2 4) sourceC117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4871) := by
    have ha : (tripleCharges (sourceA117 + difference 4 2) (sourceB117 + difference 2 4) sourceC117) = raw4394 := by
      apply Matrix.ext; unfold tripleCharges sourceA117 sourceB117 sourceC117 difference raw4394; decide +kernel
    rw [ha]
    exact (canonical4394 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA117 + difference 4 3) (sourceB117 + difference 3 4) sourceC117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4871) := by
    have ha : (tripleCharges (sourceA117 + difference 4 3) (sourceB117 + difference 3 4) sourceC117) = raw4395 := by
      apply Matrix.ext; unfold tripleCharges sourceA117 sourceB117 sourceC117 difference raw4395; decide +kernel
    rw [ha]
    exact (canonical4395 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA117 + difference 4 5) (sourceB117 + difference 5 4) sourceC117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5310) := by
    have ha : (tripleCharges (sourceA117 + difference 4 5) (sourceB117 + difference 5 4) sourceC117) = raw2651 := by
      apply Matrix.ext; unfold tripleCharges sourceA117 sourceB117 sourceC117 difference raw2651; decide +kernel
    rw [ha]
    exact (canonical2651 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA117 + difference 5 0) (sourceB117 + difference 0 5) sourceC117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4280) := by
    have ha : (tripleCharges (sourceA117 + difference 5 0) (sourceB117 + difference 0 5) sourceC117) = raw4396 := by
      apply Matrix.ext; unfold tripleCharges sourceA117 sourceB117 sourceC117 difference raw4396; decide +kernel
    rw [ha]
    exact (canonical4396 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA117 + difference 5 1) (sourceB117 + difference 1 5) sourceC117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4276) := by
    have ha : (tripleCharges (sourceA117 + difference 5 1) (sourceB117 + difference 1 5) sourceC117) = raw4397 := by
      apply Matrix.ext; unfold tripleCharges sourceA117 sourceB117 sourceC117 difference raw4397; decide +kernel
    rw [ha]
    exact (canonical4397 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA117 + difference 5 2) (sourceB117 + difference 2 5) sourceC117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4276) := by
    have ha : (tripleCharges (sourceA117 + difference 5 2) (sourceB117 + difference 2 5) sourceC117) = raw4398 := by
      apply Matrix.ext; unfold tripleCharges sourceA117 sourceB117 sourceC117 difference raw4398; decide +kernel
    rw [ha]
    exact (canonical4398 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA117 + difference 5 3) (sourceB117 + difference 3 5) sourceC117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4276) := by
    have ha : (tripleCharges (sourceA117 + difference 5 3) (sourceB117 + difference 3 5) sourceC117) = raw4399 := by
      apply Matrix.ext; unfold tripleCharges sourceA117 sourceB117 sourceC117 difference raw4399; decide +kernel
    rw [ha]
    exact (canonical4399 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA117 + difference 5 4) (sourceB117 + difference 4 5) sourceC117) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4285) := by
    have ha : (tripleCharges (sourceA117 + difference 5 4) (sourceB117 + difference 4 5) sourceC117) = raw4400 := by
      apply Matrix.ext; unfold tripleCharges sourceA117 sourceB117 sourceC117 difference raw4400; decide +kernel
    rw [ha]
    exact (canonical4400 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA117 sourceB117 sourceC117
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm117, Integer.Sparse.eval]
  linarith only [hs]

def sourceA118 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB118 : Charge := ![1, 0, 0, 0, 2, -3]
def sourceC118 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceForm118 : Integer.Sparse Master := [(Sum.inr 828, 3), (Sum.inr 832, 1), (Sum.inr 860, 1), (Sum.inr 1190, 3), (Sum.inr 1297, 1), (Sum.inr 1926, 6), (Sum.inr 1951, 3), (Sum.inr 2112, 3), (Sum.inr 2279, 3), (Sum.inr 2294, 1), (Sum.inr 3054, 3), (Sum.inr 3121, 1), (Sum.inr 3916, 1)]

theorem sourceEq118 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm118 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA118 + difference 0 1) (sourceB118 + difference 1 0) sourceC118) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2279) := by
    have ha : (tripleCharges (sourceA118 + difference 0 1) (sourceB118 + difference 1 0) sourceC118) = raw4401 := by
      apply Matrix.ext; unfold tripleCharges sourceA118 sourceB118 sourceC118 difference raw4401; decide +kernel
    rw [ha]
    exact (canonical4401 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA118 + difference 0 2) (sourceB118 + difference 2 0) sourceC118) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2279) := by
    have ha : (tripleCharges (sourceA118 + difference 0 2) (sourceB118 + difference 2 0) sourceC118) = raw4402 := by
      apply Matrix.ext; unfold tripleCharges sourceA118 sourceB118 sourceC118 difference raw4402; decide +kernel
    rw [ha]
    exact (canonical4402 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA118 + difference 0 3) (sourceB118 + difference 3 0) sourceC118) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2279) := by
    have ha : (tripleCharges (sourceA118 + difference 0 3) (sourceB118 + difference 3 0) sourceC118) = raw4403 := by
      apply Matrix.ext; unfold tripleCharges sourceA118 sourceB118 sourceC118 difference raw4403; decide +kernel
    rw [ha]
    exact (canonical4403 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA118 + difference 0 4) (sourceB118 + difference 4 0) sourceC118) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2294) := by
    have ha : (tripleCharges (sourceA118 + difference 0 4) (sourceB118 + difference 4 0) sourceC118) = raw4404 := by
      apply Matrix.ext; unfold tripleCharges sourceA118 sourceB118 sourceC118 difference raw4404; decide +kernel
    rw [ha]
    exact (canonical4404 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA118 + difference 0 5) (sourceB118 + difference 5 0) sourceC118) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3916) := by
    have ha : (tripleCharges (sourceA118 + difference 0 5) (sourceB118 + difference 5 0) sourceC118) = raw4405 := by
      apply Matrix.ext; unfold tripleCharges sourceA118 sourceB118 sourceC118 difference raw4405; decide +kernel
    rw [ha]
    exact (canonical4405 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA118 + difference 1 0) (sourceB118 + difference 0 1) sourceC118) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1190) := by
    have ha : (tripleCharges (sourceA118 + difference 1 0) (sourceB118 + difference 0 1) sourceC118) = raw4406 := by
      apply Matrix.ext; unfold tripleCharges sourceA118 sourceB118 sourceC118 difference raw4406; decide +kernel
    rw [ha]
    exact (canonical4406 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA118 + difference 1 2) (sourceB118 + difference 2 1) sourceC118) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1926) := by
    have ha : (tripleCharges (sourceA118 + difference 1 2) (sourceB118 + difference 2 1) sourceC118) = raw4407 := by
      apply Matrix.ext; unfold tripleCharges sourceA118 sourceB118 sourceC118 difference raw4407; decide +kernel
    rw [ha]
    exact (canonical4407 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA118 + difference 1 3) (sourceB118 + difference 3 1) sourceC118) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1926) := by
    have ha : (tripleCharges (sourceA118 + difference 1 3) (sourceB118 + difference 3 1) sourceC118) = raw4408 := by
      apply Matrix.ext; unfold tripleCharges sourceA118 sourceB118 sourceC118 difference raw4408; decide +kernel
    rw [ha]
    exact (canonical4408 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA118 + difference 1 4) (sourceB118 + difference 4 1) sourceC118) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1951) := by
    have ha : (tripleCharges (sourceA118 + difference 1 4) (sourceB118 + difference 4 1) sourceC118) = raw4409 := by
      apply Matrix.ext; unfold tripleCharges sourceA118 sourceB118 sourceC118 difference raw4409; decide +kernel
    rw [ha]
    exact (canonical4409 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA118 + difference 1 5) (sourceB118 + difference 5 1) sourceC118) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3054) := by
    have ha : (tripleCharges (sourceA118 + difference 1 5) (sourceB118 + difference 5 1) sourceC118) = raw4410 := by
      apply Matrix.ext; unfold tripleCharges sourceA118 sourceB118 sourceC118 difference raw4410; decide +kernel
    rw [ha]
    exact (canonical4410 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA118 + difference 2 0) (sourceB118 + difference 0 2) sourceC118) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1190) := by
    have ha : (tripleCharges (sourceA118 + difference 2 0) (sourceB118 + difference 0 2) sourceC118) = raw4411 := by
      apply Matrix.ext; unfold tripleCharges sourceA118 sourceB118 sourceC118 difference raw4411; decide +kernel
    rw [ha]
    exact (canonical4411 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA118 + difference 2 1) (sourceB118 + difference 1 2) sourceC118) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1926) := by
    have ha : (tripleCharges (sourceA118 + difference 2 1) (sourceB118 + difference 1 2) sourceC118) = raw4412 := by
      apply Matrix.ext; unfold tripleCharges sourceA118 sourceB118 sourceC118 difference raw4412; decide +kernel
    rw [ha]
    exact (canonical4412 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA118 + difference 2 3) (sourceB118 + difference 3 2) sourceC118) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1926) := by
    have ha : (tripleCharges (sourceA118 + difference 2 3) (sourceB118 + difference 3 2) sourceC118) = raw4413 := by
      apply Matrix.ext; unfold tripleCharges sourceA118 sourceB118 sourceC118 difference raw4413; decide +kernel
    rw [ha]
    exact (canonical4413 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA118 + difference 2 4) (sourceB118 + difference 4 2) sourceC118) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1951) := by
    have ha : (tripleCharges (sourceA118 + difference 2 4) (sourceB118 + difference 4 2) sourceC118) = raw4414 := by
      apply Matrix.ext; unfold tripleCharges sourceA118 sourceB118 sourceC118 difference raw4414; decide +kernel
    rw [ha]
    exact (canonical4414 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA118 + difference 2 5) (sourceB118 + difference 5 2) sourceC118) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3054) := by
    have ha : (tripleCharges (sourceA118 + difference 2 5) (sourceB118 + difference 5 2) sourceC118) = raw4415 := by
      apply Matrix.ext; unfold tripleCharges sourceA118 sourceB118 sourceC118 difference raw4415; decide +kernel
    rw [ha]
    exact (canonical4415 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA118 + difference 3 0) (sourceB118 + difference 0 3) sourceC118) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1190) := by
    have ha : (tripleCharges (sourceA118 + difference 3 0) (sourceB118 + difference 0 3) sourceC118) = raw4416 := by
      apply Matrix.ext; unfold tripleCharges sourceA118 sourceB118 sourceC118 difference raw4416; decide +kernel
    rw [ha]
    exact (canonical4416 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA118 + difference 3 1) (sourceB118 + difference 1 3) sourceC118) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1926) := by
    have ha : (tripleCharges (sourceA118 + difference 3 1) (sourceB118 + difference 1 3) sourceC118) = raw4417 := by
      apply Matrix.ext; unfold tripleCharges sourceA118 sourceB118 sourceC118 difference raw4417; decide +kernel
    rw [ha]
    exact (canonical4417 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA118 + difference 3 2) (sourceB118 + difference 2 3) sourceC118) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1926) := by
    have ha : (tripleCharges (sourceA118 + difference 3 2) (sourceB118 + difference 2 3) sourceC118) = raw4418 := by
      apply Matrix.ext; unfold tripleCharges sourceA118 sourceB118 sourceC118 difference raw4418; decide +kernel
    rw [ha]
    exact (canonical4418 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA118 + difference 3 4) (sourceB118 + difference 4 3) sourceC118) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1951) := by
    have ha : (tripleCharges (sourceA118 + difference 3 4) (sourceB118 + difference 4 3) sourceC118) = raw4419 := by
      apply Matrix.ext; unfold tripleCharges sourceA118 sourceB118 sourceC118 difference raw4419; decide +kernel
    rw [ha]
    exact (canonical4419 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA118 + difference 3 5) (sourceB118 + difference 5 3) sourceC118) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3054) := by
    have ha : (tripleCharges (sourceA118 + difference 3 5) (sourceB118 + difference 5 3) sourceC118) = raw4420 := by
      apply Matrix.ext; unfold tripleCharges sourceA118 sourceB118 sourceC118 difference raw4420; decide +kernel
    rw [ha]
    exact (canonical4420 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA118 + difference 4 0) (sourceB118 + difference 0 4) sourceC118) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1297) := by
    have ha : (tripleCharges (sourceA118 + difference 4 0) (sourceB118 + difference 0 4) sourceC118) = raw4421 := by
      apply Matrix.ext; unfold tripleCharges sourceA118 sourceB118 sourceC118 difference raw4421; decide +kernel
    rw [ha]
    exact (canonical4421 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA118 + difference 4 1) (sourceB118 + difference 1 4) sourceC118) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2112) := by
    have ha : (tripleCharges (sourceA118 + difference 4 1) (sourceB118 + difference 1 4) sourceC118) = raw4422 := by
      apply Matrix.ext; unfold tripleCharges sourceA118 sourceB118 sourceC118 difference raw4422; decide +kernel
    rw [ha]
    exact (canonical4422 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA118 + difference 4 2) (sourceB118 + difference 2 4) sourceC118) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2112) := by
    have ha : (tripleCharges (sourceA118 + difference 4 2) (sourceB118 + difference 2 4) sourceC118) = raw4423 := by
      apply Matrix.ext; unfold tripleCharges sourceA118 sourceB118 sourceC118 difference raw4423; decide +kernel
    rw [ha]
    exact (canonical4423 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA118 + difference 4 3) (sourceB118 + difference 3 4) sourceC118) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2112) := by
    have ha : (tripleCharges (sourceA118 + difference 4 3) (sourceB118 + difference 3 4) sourceC118) = raw4424 := by
      apply Matrix.ext; unfold tripleCharges sourceA118 sourceB118 sourceC118 difference raw4424; decide +kernel
    rw [ha]
    exact (canonical4424 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA118 + difference 4 5) (sourceB118 + difference 5 4) sourceC118) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3121) := by
    have ha : (tripleCharges (sourceA118 + difference 4 5) (sourceB118 + difference 5 4) sourceC118) = raw4425 := by
      apply Matrix.ext; unfold tripleCharges sourceA118 sourceB118 sourceC118 difference raw4425; decide +kernel
    rw [ha]
    exact (canonical4425 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA118 + difference 5 0) (sourceB118 + difference 0 5) sourceC118) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 832) := by
    have ha : (tripleCharges (sourceA118 + difference 5 0) (sourceB118 + difference 0 5) sourceC118) = raw4426 := by
      apply Matrix.ext; unfold tripleCharges sourceA118 sourceB118 sourceC118 difference raw4426; decide +kernel
    rw [ha]
    exact (canonical4426 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA118 + difference 5 1) (sourceB118 + difference 1 5) sourceC118) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 828) := by
    have ha : (tripleCharges (sourceA118 + difference 5 1) (sourceB118 + difference 1 5) sourceC118) = raw4427 := by
      apply Matrix.ext; unfold tripleCharges sourceA118 sourceB118 sourceC118 difference raw4427; decide +kernel
    rw [ha]
    exact (canonical4427 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA118 + difference 5 2) (sourceB118 + difference 2 5) sourceC118) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 828) := by
    have ha : (tripleCharges (sourceA118 + difference 5 2) (sourceB118 + difference 2 5) sourceC118) = raw4428 := by
      apply Matrix.ext; unfold tripleCharges sourceA118 sourceB118 sourceC118 difference raw4428; decide +kernel
    rw [ha]
    exact (canonical4428 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA118 + difference 5 3) (sourceB118 + difference 3 5) sourceC118) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 828) := by
    have ha : (tripleCharges (sourceA118 + difference 5 3) (sourceB118 + difference 3 5) sourceC118) = raw4429 := by
      apply Matrix.ext; unfold tripleCharges sourceA118 sourceB118 sourceC118 difference raw4429; decide +kernel
    rw [ha]
    exact (canonical4429 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA118 + difference 5 4) (sourceB118 + difference 4 5) sourceC118) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 860) := by
    have ha : (tripleCharges (sourceA118 + difference 5 4) (sourceB118 + difference 4 5) sourceC118) = raw4430 := by
      apply Matrix.ext; unfold tripleCharges sourceA118 sourceB118 sourceC118 difference raw4430; decide +kernel
    rw [ha]
    exact (canonical4430 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA118 sourceB118 sourceC118
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm118, Integer.Sparse.eval]
  linarith only [hs]

def sourceA119 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB119 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC119 : Charge := ![1, 0, 0, 0, 2, -3]
def sourceForm119 : Integer.Sparse Master := [(Sum.inr 4476, 3), (Sum.inr 4478, 3), (Sum.inr 4481, 1), (Sum.inr 4507, 1), (Sum.inr 4508, 1), (Sum.inr 4817, 6), (Sum.inr 4843, 3), (Sum.inr 4881, 3), (Sum.inr 4896, 3), (Sum.inr 4901, 1), (Sum.inr 5276, 3), (Sum.inr 5310, 1), (Sum.inr 5311, 1)]

theorem sourceEq119 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm119 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA119 + difference 0 1) (sourceB119 + difference 1 0) sourceC119) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4896) := by
    have ha : (tripleCharges (sourceA119 + difference 0 1) (sourceB119 + difference 1 0) sourceC119) = raw4431 := by
      apply Matrix.ext; unfold tripleCharges sourceA119 sourceB119 sourceC119 difference raw4431; decide +kernel
    rw [ha]
    exact (canonical4431 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA119 + difference 0 2) (sourceB119 + difference 2 0) sourceC119) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4896) := by
    have ha : (tripleCharges (sourceA119 + difference 0 2) (sourceB119 + difference 2 0) sourceC119) = raw4432 := by
      apply Matrix.ext; unfold tripleCharges sourceA119 sourceB119 sourceC119 difference raw4432; decide +kernel
    rw [ha]
    exact (canonical4432 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA119 + difference 0 3) (sourceB119 + difference 3 0) sourceC119) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4896) := by
    have ha : (tripleCharges (sourceA119 + difference 0 3) (sourceB119 + difference 3 0) sourceC119) = raw4433 := by
      apply Matrix.ext; unfold tripleCharges sourceA119 sourceB119 sourceC119 difference raw4433; decide +kernel
    rw [ha]
    exact (canonical4433 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA119 + difference 0 4) (sourceB119 + difference 4 0) sourceC119) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4901) := by
    have ha : (tripleCharges (sourceA119 + difference 0 4) (sourceB119 + difference 4 0) sourceC119) = raw4434 := by
      apply Matrix.ext; unfold tripleCharges sourceA119 sourceB119 sourceC119 difference raw4434; decide +kernel
    rw [ha]
    exact (canonical4434 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA119 + difference 0 5) (sourceB119 + difference 5 0) sourceC119) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5310) := by
    have ha : (tripleCharges (sourceA119 + difference 0 5) (sourceB119 + difference 5 0) sourceC119) = raw4435 := by
      apply Matrix.ext; unfold tripleCharges sourceA119 sourceB119 sourceC119 difference raw4435; decide +kernel
    rw [ha]
    exact (canonical4435 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA119 + difference 1 0) (sourceB119 + difference 0 1) sourceC119) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4478) := by
    have ha : (tripleCharges (sourceA119 + difference 1 0) (sourceB119 + difference 0 1) sourceC119) = raw4436 := by
      apply Matrix.ext; unfold tripleCharges sourceA119 sourceB119 sourceC119 difference raw4436; decide +kernel
    rw [ha]
    exact (canonical4436 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA119 + difference 1 2) (sourceB119 + difference 2 1) sourceC119) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4817) := by
    have ha : (tripleCharges (sourceA119 + difference 1 2) (sourceB119 + difference 2 1) sourceC119) = raw4437 := by
      apply Matrix.ext; unfold tripleCharges sourceA119 sourceB119 sourceC119 difference raw4437; decide +kernel
    rw [ha]
    exact (canonical4437 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA119 + difference 1 3) (sourceB119 + difference 3 1) sourceC119) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4817) := by
    have ha : (tripleCharges (sourceA119 + difference 1 3) (sourceB119 + difference 3 1) sourceC119) = raw4438 := by
      apply Matrix.ext; unfold tripleCharges sourceA119 sourceB119 sourceC119 difference raw4438; decide +kernel
    rw [ha]
    exact (canonical4438 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA119 + difference 1 4) (sourceB119 + difference 4 1) sourceC119) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4843) := by
    have ha : (tripleCharges (sourceA119 + difference 1 4) (sourceB119 + difference 4 1) sourceC119) = raw4439 := by
      apply Matrix.ext; unfold tripleCharges sourceA119 sourceB119 sourceC119 difference raw4439; decide +kernel
    rw [ha]
    exact (canonical4439 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA119 + difference 1 5) (sourceB119 + difference 5 1) sourceC119) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5276) := by
    have ha : (tripleCharges (sourceA119 + difference 1 5) (sourceB119 + difference 5 1) sourceC119) = raw4440 := by
      apply Matrix.ext; unfold tripleCharges sourceA119 sourceB119 sourceC119 difference raw4440; decide +kernel
    rw [ha]
    exact (canonical4440 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA119 + difference 2 0) (sourceB119 + difference 0 2) sourceC119) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4478) := by
    have ha : (tripleCharges (sourceA119 + difference 2 0) (sourceB119 + difference 0 2) sourceC119) = raw4441 := by
      apply Matrix.ext; unfold tripleCharges sourceA119 sourceB119 sourceC119 difference raw4441; decide +kernel
    rw [ha]
    exact (canonical4441 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA119 + difference 2 1) (sourceB119 + difference 1 2) sourceC119) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4817) := by
    have ha : (tripleCharges (sourceA119 + difference 2 1) (sourceB119 + difference 1 2) sourceC119) = raw4442 := by
      apply Matrix.ext; unfold tripleCharges sourceA119 sourceB119 sourceC119 difference raw4442; decide +kernel
    rw [ha]
    exact (canonical4442 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA119 + difference 2 3) (sourceB119 + difference 3 2) sourceC119) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4817) := by
    have ha : (tripleCharges (sourceA119 + difference 2 3) (sourceB119 + difference 3 2) sourceC119) = raw4443 := by
      apply Matrix.ext; unfold tripleCharges sourceA119 sourceB119 sourceC119 difference raw4443; decide +kernel
    rw [ha]
    exact (canonical4443 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA119 + difference 2 4) (sourceB119 + difference 4 2) sourceC119) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4843) := by
    have ha : (tripleCharges (sourceA119 + difference 2 4) (sourceB119 + difference 4 2) sourceC119) = raw4444 := by
      apply Matrix.ext; unfold tripleCharges sourceA119 sourceB119 sourceC119 difference raw4444; decide +kernel
    rw [ha]
    exact (canonical4444 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA119 + difference 2 5) (sourceB119 + difference 5 2) sourceC119) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5276) := by
    have ha : (tripleCharges (sourceA119 + difference 2 5) (sourceB119 + difference 5 2) sourceC119) = raw4445 := by
      apply Matrix.ext; unfold tripleCharges sourceA119 sourceB119 sourceC119 difference raw4445; decide +kernel
    rw [ha]
    exact (canonical4445 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA119 + difference 3 0) (sourceB119 + difference 0 3) sourceC119) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4478) := by
    have ha : (tripleCharges (sourceA119 + difference 3 0) (sourceB119 + difference 0 3) sourceC119) = raw4446 := by
      apply Matrix.ext; unfold tripleCharges sourceA119 sourceB119 sourceC119 difference raw4446; decide +kernel
    rw [ha]
    exact (canonical4446 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA119 + difference 3 1) (sourceB119 + difference 1 3) sourceC119) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4817) := by
    have ha : (tripleCharges (sourceA119 + difference 3 1) (sourceB119 + difference 1 3) sourceC119) = raw4447 := by
      apply Matrix.ext; unfold tripleCharges sourceA119 sourceB119 sourceC119 difference raw4447; decide +kernel
    rw [ha]
    exact (canonical4447 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA119 + difference 3 2) (sourceB119 + difference 2 3) sourceC119) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4817) := by
    have ha : (tripleCharges (sourceA119 + difference 3 2) (sourceB119 + difference 2 3) sourceC119) = raw4448 := by
      apply Matrix.ext; unfold tripleCharges sourceA119 sourceB119 sourceC119 difference raw4448; decide +kernel
    rw [ha]
    exact (canonical4448 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA119 + difference 3 4) (sourceB119 + difference 4 3) sourceC119) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4843) := by
    have ha : (tripleCharges (sourceA119 + difference 3 4) (sourceB119 + difference 4 3) sourceC119) = raw4449 := by
      apply Matrix.ext; unfold tripleCharges sourceA119 sourceB119 sourceC119 difference raw4449; decide +kernel
    rw [ha]
    exact (canonical4449 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA119 + difference 3 5) (sourceB119 + difference 5 3) sourceC119) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5276) := by
    have ha : (tripleCharges (sourceA119 + difference 3 5) (sourceB119 + difference 5 3) sourceC119) = raw4450 := by
      apply Matrix.ext; unfold tripleCharges sourceA119 sourceB119 sourceC119 difference raw4450; decide +kernel
    rw [ha]
    exact (canonical4450 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA119 + difference 4 0) (sourceB119 + difference 0 4) sourceC119) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4508) := by
    have ha : (tripleCharges (sourceA119 + difference 4 0) (sourceB119 + difference 0 4) sourceC119) = raw4451 := by
      apply Matrix.ext; unfold tripleCharges sourceA119 sourceB119 sourceC119 difference raw4451; decide +kernel
    rw [ha]
    exact (canonical4451 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA119 + difference 4 1) (sourceB119 + difference 1 4) sourceC119) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4881) := by
    have ha : (tripleCharges (sourceA119 + difference 4 1) (sourceB119 + difference 1 4) sourceC119) = raw4452 := by
      apply Matrix.ext; unfold tripleCharges sourceA119 sourceB119 sourceC119 difference raw4452; decide +kernel
    rw [ha]
    exact (canonical4452 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA119 + difference 4 2) (sourceB119 + difference 2 4) sourceC119) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4881) := by
    have ha : (tripleCharges (sourceA119 + difference 4 2) (sourceB119 + difference 2 4) sourceC119) = raw4453 := by
      apply Matrix.ext; unfold tripleCharges sourceA119 sourceB119 sourceC119 difference raw4453; decide +kernel
    rw [ha]
    exact (canonical4453 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA119 + difference 4 3) (sourceB119 + difference 3 4) sourceC119) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4881) := by
    have ha : (tripleCharges (sourceA119 + difference 4 3) (sourceB119 + difference 3 4) sourceC119) = raw4454 := by
      apply Matrix.ext; unfold tripleCharges sourceA119 sourceB119 sourceC119 difference raw4454; decide +kernel
    rw [ha]
    exact (canonical4454 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA119 + difference 4 5) (sourceB119 + difference 5 4) sourceC119) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5311) := by
    have ha : (tripleCharges (sourceA119 + difference 4 5) (sourceB119 + difference 5 4) sourceC119) = raw4455 := by
      apply Matrix.ext; unfold tripleCharges sourceA119 sourceB119 sourceC119 difference raw4455; decide +kernel
    rw [ha]
    exact (canonical4455 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA119 + difference 5 0) (sourceB119 + difference 0 5) sourceC119) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4481) := by
    have ha : (tripleCharges (sourceA119 + difference 5 0) (sourceB119 + difference 0 5) sourceC119) = raw4456 := by
      apply Matrix.ext; unfold tripleCharges sourceA119 sourceB119 sourceC119 difference raw4456; decide +kernel
    rw [ha]
    exact (canonical4456 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA119 + difference 5 1) (sourceB119 + difference 1 5) sourceC119) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4476) := by
    have ha : (tripleCharges (sourceA119 + difference 5 1) (sourceB119 + difference 1 5) sourceC119) = raw4457 := by
      apply Matrix.ext; unfold tripleCharges sourceA119 sourceB119 sourceC119 difference raw4457; decide +kernel
    rw [ha]
    exact (canonical4457 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA119 + difference 5 2) (sourceB119 + difference 2 5) sourceC119) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4476) := by
    have ha : (tripleCharges (sourceA119 + difference 5 2) (sourceB119 + difference 2 5) sourceC119) = raw4458 := by
      apply Matrix.ext; unfold tripleCharges sourceA119 sourceB119 sourceC119 difference raw4458; decide +kernel
    rw [ha]
    exact (canonical4458 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA119 + difference 5 3) (sourceB119 + difference 3 5) sourceC119) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4476) := by
    have ha : (tripleCharges (sourceA119 + difference 5 3) (sourceB119 + difference 3 5) sourceC119) = raw4459 := by
      apply Matrix.ext; unfold tripleCharges sourceA119 sourceB119 sourceC119 difference raw4459; decide +kernel
    rw [ha]
    exact (canonical4459 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA119 + difference 5 4) (sourceB119 + difference 4 5) sourceC119) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4507) := by
    have ha : (tripleCharges (sourceA119 + difference 5 4) (sourceB119 + difference 4 5) sourceC119) = raw4460 := by
      apply Matrix.ext; unfold tripleCharges sourceA119 sourceB119 sourceC119 difference raw4460; decide +kernel
    rw [ha]
    exact (canonical4460 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA119 sourceB119 sourceC119
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm119, Integer.Sparse.eval]
  linarith only [hs]

def sourceA120 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB120 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC120 : Charge := ![1, 0, 0, 0, 2, -3]
def sourceForm120 : Integer.Sparse Master := [(Sum.inr 1061, 3), (Sum.inr 1064, 1), (Sum.inr 1092, 1), (Sum.inr 1372, 3), (Sum.inr 1445, 1), (Sum.inr 2497, 6), (Sum.inr 2520, 3), (Sum.inr 2642, 3), (Sum.inr 2777, 3), (Sum.inr 2789, 1), (Sum.inr 3121, 1), (Sum.inr 3225, 3), (Sum.inr 3231, 1)]

theorem sourceEq120 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm120 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA120 + difference 0 1) (sourceB120 + difference 1 0) sourceC120) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3225) := by
    have ha : (tripleCharges (sourceA120 + difference 0 1) (sourceB120 + difference 1 0) sourceC120) = raw4461 := by
      apply Matrix.ext; unfold tripleCharges sourceA120 sourceB120 sourceC120 difference raw4461; decide +kernel
    rw [ha]
    exact (canonical4461 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA120 + difference 0 2) (sourceB120 + difference 2 0) sourceC120) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3225) := by
    have ha : (tripleCharges (sourceA120 + difference 0 2) (sourceB120 + difference 2 0) sourceC120) = raw4462 := by
      apply Matrix.ext; unfold tripleCharges sourceA120 sourceB120 sourceC120 difference raw4462; decide +kernel
    rw [ha]
    exact (canonical4462 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA120 + difference 0 3) (sourceB120 + difference 3 0) sourceC120) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3225) := by
    have ha : (tripleCharges (sourceA120 + difference 0 3) (sourceB120 + difference 3 0) sourceC120) = raw4463 := by
      apply Matrix.ext; unfold tripleCharges sourceA120 sourceB120 sourceC120 difference raw4463; decide +kernel
    rw [ha]
    exact (canonical4463 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA120 + difference 0 4) (sourceB120 + difference 4 0) sourceC120) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3231) := by
    have ha : (tripleCharges (sourceA120 + difference 0 4) (sourceB120 + difference 4 0) sourceC120) = raw4464 := by
      apply Matrix.ext; unfold tripleCharges sourceA120 sourceB120 sourceC120 difference raw4464; decide +kernel
    rw [ha]
    exact (canonical4464 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA120 + difference 0 5) (sourceB120 + difference 5 0) sourceC120) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3121) := by
    have ha : (tripleCharges (sourceA120 + difference 0 5) (sourceB120 + difference 5 0) sourceC120) = raw4465 := by
      apply Matrix.ext; unfold tripleCharges sourceA120 sourceB120 sourceC120 difference raw4465; decide +kernel
    rw [ha]
    exact (canonical4465 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA120 + difference 1 0) (sourceB120 + difference 0 1) sourceC120) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1061) := by
    have ha : (tripleCharges (sourceA120 + difference 1 0) (sourceB120 + difference 0 1) sourceC120) = raw4466 := by
      apply Matrix.ext; unfold tripleCharges sourceA120 sourceB120 sourceC120 difference raw4466; decide +kernel
    rw [ha]
    exact (canonical4466 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA120 + difference 1 2) (sourceB120 + difference 2 1) sourceC120) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2497) := by
    have ha : (tripleCharges (sourceA120 + difference 1 2) (sourceB120 + difference 2 1) sourceC120) = raw4467 := by
      apply Matrix.ext; unfold tripleCharges sourceA120 sourceB120 sourceC120 difference raw4467; decide +kernel
    rw [ha]
    exact (canonical4467 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA120 + difference 1 3) (sourceB120 + difference 3 1) sourceC120) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2497) := by
    have ha : (tripleCharges (sourceA120 + difference 1 3) (sourceB120 + difference 3 1) sourceC120) = raw4468 := by
      apply Matrix.ext; unfold tripleCharges sourceA120 sourceB120 sourceC120 difference raw4468; decide +kernel
    rw [ha]
    exact (canonical4468 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA120 + difference 1 4) (sourceB120 + difference 4 1) sourceC120) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2642) := by
    have ha : (tripleCharges (sourceA120 + difference 1 4) (sourceB120 + difference 4 1) sourceC120) = raw4469 := by
      apply Matrix.ext; unfold tripleCharges sourceA120 sourceB120 sourceC120 difference raw4469; decide +kernel
    rw [ha]
    exact (canonical4469 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA120 + difference 1 5) (sourceB120 + difference 5 1) sourceC120) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2777) := by
    have ha : (tripleCharges (sourceA120 + difference 1 5) (sourceB120 + difference 5 1) sourceC120) = raw4470 := by
      apply Matrix.ext; unfold tripleCharges sourceA120 sourceB120 sourceC120 difference raw4470; decide +kernel
    rw [ha]
    exact (canonical4470 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA120 + difference 2 0) (sourceB120 + difference 0 2) sourceC120) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1061) := by
    have ha : (tripleCharges (sourceA120 + difference 2 0) (sourceB120 + difference 0 2) sourceC120) = raw4471 := by
      apply Matrix.ext; unfold tripleCharges sourceA120 sourceB120 sourceC120 difference raw4471; decide +kernel
    rw [ha]
    exact (canonical4471 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA120 + difference 2 1) (sourceB120 + difference 1 2) sourceC120) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2497) := by
    have ha : (tripleCharges (sourceA120 + difference 2 1) (sourceB120 + difference 1 2) sourceC120) = raw4472 := by
      apply Matrix.ext; unfold tripleCharges sourceA120 sourceB120 sourceC120 difference raw4472; decide +kernel
    rw [ha]
    exact (canonical4472 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA120 + difference 2 3) (sourceB120 + difference 3 2) sourceC120) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2497) := by
    have ha : (tripleCharges (sourceA120 + difference 2 3) (sourceB120 + difference 3 2) sourceC120) = raw4473 := by
      apply Matrix.ext; unfold tripleCharges sourceA120 sourceB120 sourceC120 difference raw4473; decide +kernel
    rw [ha]
    exact (canonical4473 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA120 + difference 2 4) (sourceB120 + difference 4 2) sourceC120) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2642) := by
    have ha : (tripleCharges (sourceA120 + difference 2 4) (sourceB120 + difference 4 2) sourceC120) = raw4474 := by
      apply Matrix.ext; unfold tripleCharges sourceA120 sourceB120 sourceC120 difference raw4474; decide +kernel
    rw [ha]
    exact (canonical4474 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA120 + difference 2 5) (sourceB120 + difference 5 2) sourceC120) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2777) := by
    have ha : (tripleCharges (sourceA120 + difference 2 5) (sourceB120 + difference 5 2) sourceC120) = raw4475 := by
      apply Matrix.ext; unfold tripleCharges sourceA120 sourceB120 sourceC120 difference raw4475; decide +kernel
    rw [ha]
    exact (canonical4475 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA120 + difference 3 0) (sourceB120 + difference 0 3) sourceC120) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1061) := by
    have ha : (tripleCharges (sourceA120 + difference 3 0) (sourceB120 + difference 0 3) sourceC120) = raw4476 := by
      apply Matrix.ext; unfold tripleCharges sourceA120 sourceB120 sourceC120 difference raw4476; decide +kernel
    rw [ha]
    exact (canonical4476 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA120 + difference 3 1) (sourceB120 + difference 1 3) sourceC120) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2497) := by
    have ha : (tripleCharges (sourceA120 + difference 3 1) (sourceB120 + difference 1 3) sourceC120) = raw4477 := by
      apply Matrix.ext; unfold tripleCharges sourceA120 sourceB120 sourceC120 difference raw4477; decide +kernel
    rw [ha]
    exact (canonical4477 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA120 + difference 3 2) (sourceB120 + difference 2 3) sourceC120) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2497) := by
    have ha : (tripleCharges (sourceA120 + difference 3 2) (sourceB120 + difference 2 3) sourceC120) = raw4478 := by
      apply Matrix.ext; unfold tripleCharges sourceA120 sourceB120 sourceC120 difference raw4478; decide +kernel
    rw [ha]
    exact (canonical4478 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA120 + difference 3 4) (sourceB120 + difference 4 3) sourceC120) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2642) := by
    have ha : (tripleCharges (sourceA120 + difference 3 4) (sourceB120 + difference 4 3) sourceC120) = raw4479 := by
      apply Matrix.ext; unfold tripleCharges sourceA120 sourceB120 sourceC120 difference raw4479; decide +kernel
    rw [ha]
    exact (canonical4479 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA120 + difference 3 5) (sourceB120 + difference 5 3) sourceC120) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2777) := by
    have ha : (tripleCharges (sourceA120 + difference 3 5) (sourceB120 + difference 5 3) sourceC120) = raw4480 := by
      apply Matrix.ext; unfold tripleCharges sourceA120 sourceB120 sourceC120 difference raw4480; decide +kernel
    rw [ha]
    exact (canonical4480 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA120 + difference 4 0) (sourceB120 + difference 0 4) sourceC120) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1092) := by
    have ha : (tripleCharges (sourceA120 + difference 4 0) (sourceB120 + difference 0 4) sourceC120) = raw4481 := by
      apply Matrix.ext; unfold tripleCharges sourceA120 sourceB120 sourceC120 difference raw4481; decide +kernel
    rw [ha]
    exact (canonical4481 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA120 + difference 4 1) (sourceB120 + difference 1 4) sourceC120) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2520) := by
    have ha : (tripleCharges (sourceA120 + difference 4 1) (sourceB120 + difference 1 4) sourceC120) = raw4482 := by
      apply Matrix.ext; unfold tripleCharges sourceA120 sourceB120 sourceC120 difference raw4482; decide +kernel
    rw [ha]
    exact (canonical4482 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA120 + difference 4 2) (sourceB120 + difference 2 4) sourceC120) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2520) := by
    have ha : (tripleCharges (sourceA120 + difference 4 2) (sourceB120 + difference 2 4) sourceC120) = raw4483 := by
      apply Matrix.ext; unfold tripleCharges sourceA120 sourceB120 sourceC120 difference raw4483; decide +kernel
    rw [ha]
    exact (canonical4483 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA120 + difference 4 3) (sourceB120 + difference 3 4) sourceC120) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2520) := by
    have ha : (tripleCharges (sourceA120 + difference 4 3) (sourceB120 + difference 3 4) sourceC120) = raw4484 := by
      apply Matrix.ext; unfold tripleCharges sourceA120 sourceB120 sourceC120 difference raw4484; decide +kernel
    rw [ha]
    exact (canonical4484 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA120 + difference 4 5) (sourceB120 + difference 5 4) sourceC120) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2789) := by
    have ha : (tripleCharges (sourceA120 + difference 4 5) (sourceB120 + difference 5 4) sourceC120) = raw4485 := by
      apply Matrix.ext; unfold tripleCharges sourceA120 sourceB120 sourceC120 difference raw4485; decide +kernel
    rw [ha]
    exact (canonical4485 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA120 + difference 5 0) (sourceB120 + difference 0 5) sourceC120) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1064) := by
    have ha : (tripleCharges (sourceA120 + difference 5 0) (sourceB120 + difference 0 5) sourceC120) = raw4486 := by
      apply Matrix.ext; unfold tripleCharges sourceA120 sourceB120 sourceC120 difference raw4486; decide +kernel
    rw [ha]
    exact (canonical4486 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA120 + difference 5 1) (sourceB120 + difference 1 5) sourceC120) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1372) := by
    have ha : (tripleCharges (sourceA120 + difference 5 1) (sourceB120 + difference 1 5) sourceC120) = raw4487 := by
      apply Matrix.ext; unfold tripleCharges sourceA120 sourceB120 sourceC120 difference raw4487; decide +kernel
    rw [ha]
    exact (canonical4487 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA120 + difference 5 2) (sourceB120 + difference 2 5) sourceC120) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1372) := by
    have ha : (tripleCharges (sourceA120 + difference 5 2) (sourceB120 + difference 2 5) sourceC120) = raw4488 := by
      apply Matrix.ext; unfold tripleCharges sourceA120 sourceB120 sourceC120 difference raw4488; decide +kernel
    rw [ha]
    exact (canonical4488 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA120 + difference 5 3) (sourceB120 + difference 3 5) sourceC120) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1372) := by
    have ha : (tripleCharges (sourceA120 + difference 5 3) (sourceB120 + difference 3 5) sourceC120) = raw4489 := by
      apply Matrix.ext; unfold tripleCharges sourceA120 sourceB120 sourceC120 difference raw4489; decide +kernel
    rw [ha]
    exact (canonical4489 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA120 + difference 5 4) (sourceB120 + difference 4 5) sourceC120) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1445) := by
    have ha : (tripleCharges (sourceA120 + difference 5 4) (sourceB120 + difference 4 5) sourceC120) = raw4490 := by
      apply Matrix.ext; unfold tripleCharges sourceA120 sourceB120 sourceC120 difference raw4490; decide +kernel
    rw [ha]
    exact (canonical4490 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA120 sourceB120 sourceC120
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm120, Integer.Sparse.eval]
  linarith only [hs]

def sourceA121 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB121 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC121 : Charge := ![1, 0, 0, 0, 2, -3]
def sourceForm121 : Integer.Sparse Master := [(Sum.inr 1729, 3), (Sum.inr 1746, 3), (Sum.inr 1747, 1), (Sum.inr 1756, 1), (Sum.inr 1757, 1), (Sum.inr 2207, 6), (Sum.inr 2230, 3), (Sum.inr 2266, 3), (Sum.inr 2267, 3), (Sum.inr 2293, 1), (Sum.inr 2744, 3), (Sum.inr 2788, 1), (Sum.inr 2789, 1)]

theorem sourceEq121 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm121 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA121 + difference 0 1) (sourceB121 + difference 1 0) sourceC121) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2266) := by
    have ha : (tripleCharges (sourceA121 + difference 0 1) (sourceB121 + difference 1 0) sourceC121) = raw4491 := by
      apply Matrix.ext; unfold tripleCharges sourceA121 sourceB121 sourceC121 difference raw4491; decide +kernel
    rw [ha]
    exact (canonical4491 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA121 + difference 0 2) (sourceB121 + difference 2 0) sourceC121) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2266) := by
    have ha : (tripleCharges (sourceA121 + difference 0 2) (sourceB121 + difference 2 0) sourceC121) = raw4492 := by
      apply Matrix.ext; unfold tripleCharges sourceA121 sourceB121 sourceC121 difference raw4492; decide +kernel
    rw [ha]
    exact (canonical4492 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA121 + difference 0 3) (sourceB121 + difference 3 0) sourceC121) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2266) := by
    have ha : (tripleCharges (sourceA121 + difference 0 3) (sourceB121 + difference 3 0) sourceC121) = raw4493 := by
      apply Matrix.ext; unfold tripleCharges sourceA121 sourceB121 sourceC121 difference raw4493; decide +kernel
    rw [ha]
    exact (canonical4493 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA121 + difference 0 4) (sourceB121 + difference 4 0) sourceC121) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2293) := by
    have ha : (tripleCharges (sourceA121 + difference 0 4) (sourceB121 + difference 4 0) sourceC121) = raw4494 := by
      apply Matrix.ext; unfold tripleCharges sourceA121 sourceB121 sourceC121 difference raw4494; decide +kernel
    rw [ha]
    exact (canonical4494 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA121 + difference 0 5) (sourceB121 + difference 5 0) sourceC121) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2788) := by
    have ha : (tripleCharges (sourceA121 + difference 0 5) (sourceB121 + difference 5 0) sourceC121) = raw4495 := by
      apply Matrix.ext; unfold tripleCharges sourceA121 sourceB121 sourceC121 difference raw4495; decide +kernel
    rw [ha]
    exact (canonical4495 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA121 + difference 1 0) (sourceB121 + difference 0 1) sourceC121) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1746) := by
    have ha : (tripleCharges (sourceA121 + difference 1 0) (sourceB121 + difference 0 1) sourceC121) = raw4496 := by
      apply Matrix.ext; unfold tripleCharges sourceA121 sourceB121 sourceC121 difference raw4496; decide +kernel
    rw [ha]
    exact (canonical4496 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA121 + difference 1 2) (sourceB121 + difference 2 1) sourceC121) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2207) := by
    have ha : (tripleCharges (sourceA121 + difference 1 2) (sourceB121 + difference 2 1) sourceC121) = raw4497 := by
      apply Matrix.ext; unfold tripleCharges sourceA121 sourceB121 sourceC121 difference raw4497; decide +kernel
    rw [ha]
    exact (canonical4497 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA121 + difference 1 3) (sourceB121 + difference 3 1) sourceC121) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2207) := by
    have ha : (tripleCharges (sourceA121 + difference 1 3) (sourceB121 + difference 3 1) sourceC121) = raw4498 := by
      apply Matrix.ext; unfold tripleCharges sourceA121 sourceB121 sourceC121 difference raw4498; decide +kernel
    rw [ha]
    exact (canonical4498 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA121 + difference 1 4) (sourceB121 + difference 4 1) sourceC121) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2230) := by
    have ha : (tripleCharges (sourceA121 + difference 1 4) (sourceB121 + difference 4 1) sourceC121) = raw4499 := by
      apply Matrix.ext; unfold tripleCharges sourceA121 sourceB121 sourceC121 difference raw4499; decide +kernel
    rw [ha]
    exact (canonical4499 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA121 + difference 1 5) (sourceB121 + difference 5 1) sourceC121) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2744) := by
    have ha : (tripleCharges (sourceA121 + difference 1 5) (sourceB121 + difference 5 1) sourceC121) = raw4500 := by
      apply Matrix.ext; unfold tripleCharges sourceA121 sourceB121 sourceC121 difference raw4500; decide +kernel
    rw [ha]
    exact (canonical4500 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA121 + difference 2 0) (sourceB121 + difference 0 2) sourceC121) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1746) := by
    have ha : (tripleCharges (sourceA121 + difference 2 0) (sourceB121 + difference 0 2) sourceC121) = raw4501 := by
      apply Matrix.ext; unfold tripleCharges sourceA121 sourceB121 sourceC121 difference raw4501; decide +kernel
    rw [ha]
    exact (canonical4501 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA121 + difference 2 1) (sourceB121 + difference 1 2) sourceC121) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2207) := by
    have ha : (tripleCharges (sourceA121 + difference 2 1) (sourceB121 + difference 1 2) sourceC121) = raw4502 := by
      apply Matrix.ext; unfold tripleCharges sourceA121 sourceB121 sourceC121 difference raw4502; decide +kernel
    rw [ha]
    exact (canonical4502 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA121 + difference 2 3) (sourceB121 + difference 3 2) sourceC121) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2207) := by
    have ha : (tripleCharges (sourceA121 + difference 2 3) (sourceB121 + difference 3 2) sourceC121) = raw4503 := by
      apply Matrix.ext; unfold tripleCharges sourceA121 sourceB121 sourceC121 difference raw4503; decide +kernel
    rw [ha]
    exact (canonical4503 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA121 + difference 2 4) (sourceB121 + difference 4 2) sourceC121) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2230) := by
    have ha : (tripleCharges (sourceA121 + difference 2 4) (sourceB121 + difference 4 2) sourceC121) = raw4504 := by
      apply Matrix.ext; unfold tripleCharges sourceA121 sourceB121 sourceC121 difference raw4504; decide +kernel
    rw [ha]
    exact (canonical4504 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA121 + difference 2 5) (sourceB121 + difference 5 2) sourceC121) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2744) := by
    have ha : (tripleCharges (sourceA121 + difference 2 5) (sourceB121 + difference 5 2) sourceC121) = raw4505 := by
      apply Matrix.ext; unfold tripleCharges sourceA121 sourceB121 sourceC121 difference raw4505; decide +kernel
    rw [ha]
    exact (canonical4505 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA121 + difference 3 0) (sourceB121 + difference 0 3) sourceC121) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1746) := by
    have ha : (tripleCharges (sourceA121 + difference 3 0) (sourceB121 + difference 0 3) sourceC121) = raw4506 := by
      apply Matrix.ext; unfold tripleCharges sourceA121 sourceB121 sourceC121 difference raw4506; decide +kernel
    rw [ha]
    exact (canonical4506 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA121 + difference 3 1) (sourceB121 + difference 1 3) sourceC121) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2207) := by
    have ha : (tripleCharges (sourceA121 + difference 3 1) (sourceB121 + difference 1 3) sourceC121) = raw4507 := by
      apply Matrix.ext; unfold tripleCharges sourceA121 sourceB121 sourceC121 difference raw4507; decide +kernel
    rw [ha]
    exact (canonical4507 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA121 + difference 3 2) (sourceB121 + difference 2 3) sourceC121) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2207) := by
    have ha : (tripleCharges (sourceA121 + difference 3 2) (sourceB121 + difference 2 3) sourceC121) = raw4508 := by
      apply Matrix.ext; unfold tripleCharges sourceA121 sourceB121 sourceC121 difference raw4508; decide +kernel
    rw [ha]
    exact (canonical4508 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA121 + difference 3 4) (sourceB121 + difference 4 3) sourceC121) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2230) := by
    have ha : (tripleCharges (sourceA121 + difference 3 4) (sourceB121 + difference 4 3) sourceC121) = raw4509 := by
      apply Matrix.ext; unfold tripleCharges sourceA121 sourceB121 sourceC121 difference raw4509; decide +kernel
    rw [ha]
    exact (canonical4509 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA121 + difference 3 5) (sourceB121 + difference 5 3) sourceC121) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2744) := by
    have ha : (tripleCharges (sourceA121 + difference 3 5) (sourceB121 + difference 5 3) sourceC121) = raw4510 := by
      apply Matrix.ext; unfold tripleCharges sourceA121 sourceB121 sourceC121 difference raw4510; decide +kernel
    rw [ha]
    exact (canonical4510 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA121 + difference 4 0) (sourceB121 + difference 0 4) sourceC121) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1747) := by
    have ha : (tripleCharges (sourceA121 + difference 4 0) (sourceB121 + difference 0 4) sourceC121) = raw4511 := by
      apply Matrix.ext; unfold tripleCharges sourceA121 sourceB121 sourceC121 difference raw4511; decide +kernel
    rw [ha]
    exact (canonical4511 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA121 + difference 4 1) (sourceB121 + difference 1 4) sourceC121) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2267) := by
    have ha : (tripleCharges (sourceA121 + difference 4 1) (sourceB121 + difference 1 4) sourceC121) = raw4512 := by
      apply Matrix.ext; unfold tripleCharges sourceA121 sourceB121 sourceC121 difference raw4512; decide +kernel
    rw [ha]
    exact (canonical4512 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA121 + difference 4 2) (sourceB121 + difference 2 4) sourceC121) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2267) := by
    have ha : (tripleCharges (sourceA121 + difference 4 2) (sourceB121 + difference 2 4) sourceC121) = raw4513 := by
      apply Matrix.ext; unfold tripleCharges sourceA121 sourceB121 sourceC121 difference raw4513; decide +kernel
    rw [ha]
    exact (canonical4513 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA121 + difference 4 3) (sourceB121 + difference 3 4) sourceC121) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2267) := by
    have ha : (tripleCharges (sourceA121 + difference 4 3) (sourceB121 + difference 3 4) sourceC121) = raw4514 := by
      apply Matrix.ext; unfold tripleCharges sourceA121 sourceB121 sourceC121 difference raw4514; decide +kernel
    rw [ha]
    exact (canonical4514 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA121 + difference 4 5) (sourceB121 + difference 5 4) sourceC121) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2789) := by
    have ha : (tripleCharges (sourceA121 + difference 4 5) (sourceB121 + difference 5 4) sourceC121) = raw4515 := by
      apply Matrix.ext; unfold tripleCharges sourceA121 sourceB121 sourceC121 difference raw4515; decide +kernel
    rw [ha]
    exact (canonical4515 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA121 + difference 5 0) (sourceB121 + difference 0 5) sourceC121) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1757) := by
    have ha : (tripleCharges (sourceA121 + difference 5 0) (sourceB121 + difference 0 5) sourceC121) = raw4516 := by
      apply Matrix.ext; unfold tripleCharges sourceA121 sourceB121 sourceC121 difference raw4516; decide +kernel
    rw [ha]
    exact (canonical4516 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA121 + difference 5 1) (sourceB121 + difference 1 5) sourceC121) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1729) := by
    have ha : (tripleCharges (sourceA121 + difference 5 1) (sourceB121 + difference 1 5) sourceC121) = raw4517 := by
      apply Matrix.ext; unfold tripleCharges sourceA121 sourceB121 sourceC121 difference raw4517; decide +kernel
    rw [ha]
    exact (canonical4517 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA121 + difference 5 2) (sourceB121 + difference 2 5) sourceC121) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1729) := by
    have ha : (tripleCharges (sourceA121 + difference 5 2) (sourceB121 + difference 2 5) sourceC121) = raw4518 := by
      apply Matrix.ext; unfold tripleCharges sourceA121 sourceB121 sourceC121 difference raw4518; decide +kernel
    rw [ha]
    exact (canonical4518 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA121 + difference 5 3) (sourceB121 + difference 3 5) sourceC121) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1729) := by
    have ha : (tripleCharges (sourceA121 + difference 5 3) (sourceB121 + difference 3 5) sourceC121) = raw4519 := by
      apply Matrix.ext; unfold tripleCharges sourceA121 sourceB121 sourceC121 difference raw4519; decide +kernel
    rw [ha]
    exact (canonical4519 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA121 + difference 5 4) (sourceB121 + difference 4 5) sourceC121) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1756) := by
    have ha : (tripleCharges (sourceA121 + difference 5 4) (sourceB121 + difference 4 5) sourceC121) = raw4520 := by
      apply Matrix.ext; unfold tripleCharges sourceA121 sourceB121 sourceC121 difference raw4520; decide +kernel
    rw [ha]
    exact (canonical4520 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA121 sourceB121 sourceC121
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm121, Integer.Sparse.eval]
  linarith only [hs]

def sourceA122 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB122 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC122 : Charge := ![1, 0, 0, 0, 2, -3]
def sourceForm122 : Integer.Sparse Master := [(Sum.inr 2278, 3), (Sum.inr 2281, 1), (Sum.inr 2293, 1), (Sum.inr 3633, 1), (Sum.inr 4084, -1)]

theorem sourceEq122 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm122 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA122 + difference 0 0) (sourceB122 + difference 0 0) sourceC122) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2281) := by
    have ha : (tripleCharges (sourceA122 + difference 0 0) (sourceB122 + difference 0 0) sourceC122) = raw4521 := by
      apply Matrix.ext; unfold tripleCharges sourceA122 sourceB122 sourceC122 difference raw4521; decide +kernel
    rw [ha]
    exact (canonical4521 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA122 + difference 0 1) (sourceB122 + difference 1 0) sourceC122) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2278) := by
    have ha : (tripleCharges (sourceA122 + difference 0 1) (sourceB122 + difference 1 0) sourceC122) = raw4522 := by
      apply Matrix.ext; unfold tripleCharges sourceA122 sourceB122 sourceC122 difference raw4522; decide +kernel
    rw [ha]
    exact (canonical4522 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA122 + difference 0 2) (sourceB122 + difference 2 0) sourceC122) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2278) := by
    have ha : (tripleCharges (sourceA122 + difference 0 2) (sourceB122 + difference 2 0) sourceC122) = raw4523 := by
      apply Matrix.ext; unfold tripleCharges sourceA122 sourceB122 sourceC122 difference raw4523; decide +kernel
    rw [ha]
    exact (canonical4523 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA122 + difference 0 3) (sourceB122 + difference 3 0) sourceC122) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2278) := by
    have ha : (tripleCharges (sourceA122 + difference 0 3) (sourceB122 + difference 3 0) sourceC122) = raw4524 := by
      apply Matrix.ext; unfold tripleCharges sourceA122 sourceB122 sourceC122 difference raw4524; decide +kernel
    rw [ha]
    exact (canonical4524 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA122 + difference 0 4) (sourceB122 + difference 4 0) sourceC122) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2293) := by
    have ha : (tripleCharges (sourceA122 + difference 0 4) (sourceB122 + difference 4 0) sourceC122) = raw4525 := by
      apply Matrix.ext; unfold tripleCharges sourceA122 sourceB122 sourceC122 difference raw4525; decide +kernel
    rw [ha]
    exact (canonical4525 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA122 + difference 0 5) (sourceB122 + difference 5 0) sourceC122) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3633) := by
    have ha : (tripleCharges (sourceA122 + difference 0 5) (sourceB122 + difference 5 0) sourceC122) = raw4526 := by
      apply Matrix.ext; unfold tripleCharges sourceA122 sourceB122 sourceC122 difference raw4526; decide +kernel
    rw [ha]
    exact (canonical4526 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA122 + sourceB122) sourceC122) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA122 + sourceB122) sourceC122) = raw4527 := by
      apply Matrix.ext; unfold doubleCharges sourceA122 sourceB122 sourceC122 raw4527; decide +kernel
    rw [ha]
    exact (canonical4527 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA122 sourceB122 sourceC122
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm122, Integer.Sparse.eval]
  linarith only [hs]

def sourceA123 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB123 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC123 : Charge := ![1, 0, 0, 0, 2, -3]
def sourceForm123 : Integer.Sparse Master := [(Sum.inr 1064, 1), (Sum.inr 1369, 3), (Sum.inr 1438, 1), (Sum.inr 2281, 1), (Sum.inr 4084, -1)]

theorem sourceEq123 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm123 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA123 + difference 0 0) (sourceB123 + difference 0 0) sourceC123) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2281) := by
    have ha : (tripleCharges (sourceA123 + difference 0 0) (sourceB123 + difference 0 0) sourceC123) = raw4521 := by
      apply Matrix.ext; unfold tripleCharges sourceA123 sourceB123 sourceC123 difference raw4521; decide +kernel
    rw [ha]
    exact (canonical4521 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA123 + difference 1 0) (sourceB123 + difference 0 1) sourceC123) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1369) := by
    have ha : (tripleCharges (sourceA123 + difference 1 0) (sourceB123 + difference 0 1) sourceC123) = raw4528 := by
      apply Matrix.ext; unfold tripleCharges sourceA123 sourceB123 sourceC123 difference raw4528; decide +kernel
    rw [ha]
    exact (canonical4528 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA123 + difference 2 0) (sourceB123 + difference 0 2) sourceC123) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1369) := by
    have ha : (tripleCharges (sourceA123 + difference 2 0) (sourceB123 + difference 0 2) sourceC123) = raw4529 := by
      apply Matrix.ext; unfold tripleCharges sourceA123 sourceB123 sourceC123 difference raw4529; decide +kernel
    rw [ha]
    exact (canonical4529 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA123 + difference 3 0) (sourceB123 + difference 0 3) sourceC123) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1369) := by
    have ha : (tripleCharges (sourceA123 + difference 3 0) (sourceB123 + difference 0 3) sourceC123) = raw4530 := by
      apply Matrix.ext; unfold tripleCharges sourceA123 sourceB123 sourceC123 difference raw4530; decide +kernel
    rw [ha]
    exact (canonical4530 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA123 + difference 4 0) (sourceB123 + difference 0 4) sourceC123) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1438) := by
    have ha : (tripleCharges (sourceA123 + difference 4 0) (sourceB123 + difference 0 4) sourceC123) = raw4531 := by
      apply Matrix.ext; unfold tripleCharges sourceA123 sourceB123 sourceC123 difference raw4531; decide +kernel
    rw [ha]
    exact (canonical4531 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA123 + difference 5 0) (sourceB123 + difference 0 5) sourceC123) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1064) := by
    have ha : (tripleCharges (sourceA123 + difference 5 0) (sourceB123 + difference 0 5) sourceC123) = raw4532 := by
      apply Matrix.ext; unfold tripleCharges sourceA123 sourceB123 sourceC123 difference raw4532; decide +kernel
    rw [ha]
    exact (canonical4532 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA123 + sourceB123) sourceC123) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA123 + sourceB123) sourceC123) = raw4527 := by
      apply Matrix.ext; unfold doubleCharges sourceA123 sourceB123 sourceC123 raw4527; decide +kernel
    rw [ha]
    exact (canonical4527 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA123 sourceB123 sourceC123
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm123, Integer.Sparse.eval]
  linarith only [hs]

def sourceA124 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB124 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC124 : Charge := ![1, 0, 0, 0, 2, -3]
def sourceForm124 : Integer.Sparse Master := [(Sum.inr 1369, 1), (Sum.inr 2035, 2), (Sum.inr 2062, 1), (Sum.inr 2281, 1), (Sum.inr 3052, 1), (Sum.inr 4084, -1)]

theorem sourceEq124 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm124 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA124 + difference 1 0) (sourceB124 + difference 0 1) sourceC124) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1369) := by
    have ha : (tripleCharges (sourceA124 + difference 1 0) (sourceB124 + difference 0 1) sourceC124) = raw4528 := by
      apply Matrix.ext; unfold tripleCharges sourceA124 sourceB124 sourceC124 difference raw4528; decide +kernel
    rw [ha]
    exact (canonical4528 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA124 + difference 1 1) (sourceB124 + difference 1 1) sourceC124) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2281) := by
    have ha : (tripleCharges (sourceA124 + difference 1 1) (sourceB124 + difference 1 1) sourceC124) = raw4521 := by
      apply Matrix.ext; unfold tripleCharges sourceA124 sourceB124 sourceC124 difference raw4521; decide +kernel
    rw [ha]
    exact (canonical4521 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA124 + difference 1 2) (sourceB124 + difference 2 1) sourceC124) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2035) := by
    have ha : (tripleCharges (sourceA124 + difference 1 2) (sourceB124 + difference 2 1) sourceC124) = raw4533 := by
      apply Matrix.ext; unfold tripleCharges sourceA124 sourceB124 sourceC124 difference raw4533; decide +kernel
    rw [ha]
    exact (canonical4533 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA124 + difference 1 3) (sourceB124 + difference 3 1) sourceC124) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2035) := by
    have ha : (tripleCharges (sourceA124 + difference 1 3) (sourceB124 + difference 3 1) sourceC124) = raw4534 := by
      apply Matrix.ext; unfold tripleCharges sourceA124 sourceB124 sourceC124 difference raw4534; decide +kernel
    rw [ha]
    exact (canonical4534 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA124 + difference 1 4) (sourceB124 + difference 4 1) sourceC124) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2062) := by
    have ha : (tripleCharges (sourceA124 + difference 1 4) (sourceB124 + difference 4 1) sourceC124) = raw4535 := by
      apply Matrix.ext; unfold tripleCharges sourceA124 sourceB124 sourceC124 difference raw4535; decide +kernel
    rw [ha]
    exact (canonical4535 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA124 + difference 1 5) (sourceB124 + difference 5 1) sourceC124) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3052) := by
    have ha : (tripleCharges (sourceA124 + difference 1 5) (sourceB124 + difference 5 1) sourceC124) = raw4536 := by
      apply Matrix.ext; unfold tripleCharges sourceA124 sourceB124 sourceC124 difference raw4536; decide +kernel
    rw [ha]
    exact (canonical4536 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA124 + sourceB124) sourceC124) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA124 + sourceB124) sourceC124) = raw4527 := by
      apply Matrix.ext; unfold doubleCharges sourceA124 sourceB124 sourceC124 raw4527; decide +kernel
    rw [ha]
    exact (canonical4527 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA124 sourceB124 sourceC124
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm124, Integer.Sparse.eval]
  linarith only [hs]

def sourceA125 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB125 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC125 : Charge := ![1, 0, 0, 0, 2, -3]
def sourceForm125 : Integer.Sparse Master := [(Sum.inr 1059, 1), (Sum.inr 2035, 2), (Sum.inr 2134, 1), (Sum.inr 2278, 1), (Sum.inr 2281, 1), (Sum.inr 4084, -1)]

theorem sourceEq125 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm125 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA125 + difference 0 1) (sourceB125 + difference 1 0) sourceC125) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2278) := by
    have ha : (tripleCharges (sourceA125 + difference 0 1) (sourceB125 + difference 1 0) sourceC125) = raw4522 := by
      apply Matrix.ext; unfold tripleCharges sourceA125 sourceB125 sourceC125 difference raw4522; decide +kernel
    rw [ha]
    exact (canonical4522 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA125 + difference 1 1) (sourceB125 + difference 1 1) sourceC125) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2281) := by
    have ha : (tripleCharges (sourceA125 + difference 1 1) (sourceB125 + difference 1 1) sourceC125) = raw4521 := by
      apply Matrix.ext; unfold tripleCharges sourceA125 sourceB125 sourceC125 difference raw4521; decide +kernel
    rw [ha]
    exact (canonical4521 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA125 + difference 2 1) (sourceB125 + difference 1 2) sourceC125) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2035) := by
    have ha : (tripleCharges (sourceA125 + difference 2 1) (sourceB125 + difference 1 2) sourceC125) = raw4537 := by
      apply Matrix.ext; unfold tripleCharges sourceA125 sourceB125 sourceC125 difference raw4537; decide +kernel
    rw [ha]
    exact (canonical4537 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA125 + difference 3 1) (sourceB125 + difference 1 3) sourceC125) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2035) := by
    have ha : (tripleCharges (sourceA125 + difference 3 1) (sourceB125 + difference 1 3) sourceC125) = raw4538 := by
      apply Matrix.ext; unfold tripleCharges sourceA125 sourceB125 sourceC125 difference raw4538; decide +kernel
    rw [ha]
    exact (canonical4538 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA125 + difference 4 1) (sourceB125 + difference 1 4) sourceC125) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2134) := by
    have ha : (tripleCharges (sourceA125 + difference 4 1) (sourceB125 + difference 1 4) sourceC125) = raw4539 := by
      apply Matrix.ext; unfold tripleCharges sourceA125 sourceB125 sourceC125 difference raw4539; decide +kernel
    rw [ha]
    exact (canonical4539 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA125 + difference 5 1) (sourceB125 + difference 1 5) sourceC125) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1059) := by
    have ha : (tripleCharges (sourceA125 + difference 5 1) (sourceB125 + difference 1 5) sourceC125) = raw4540 := by
      apply Matrix.ext; unfold tripleCharges sourceA125 sourceB125 sourceC125 difference raw4540; decide +kernel
    rw [ha]
    exact (canonical4540 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA125 + sourceB125) sourceC125) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA125 + sourceB125) sourceC125) = raw4527 := by
      apply Matrix.ext; unfold doubleCharges sourceA125 sourceB125 sourceC125 raw4527; decide +kernel
    rw [ha]
    exact (canonical4527 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA125 sourceB125 sourceC125
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm125, Integer.Sparse.eval]
  linarith only [hs]

def sourceA126 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB126 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC126 : Charge := ![1, 0, 0, 0, 2, -3]
def sourceForm126 : Integer.Sparse Master := [(Sum.inr 1438, 1), (Sum.inr 2134, 3), (Sum.inr 2281, 1), (Sum.inr 2789, 1), (Sum.inr 4084, -1)]

theorem sourceEq126 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm126 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA126 + difference 4 0) (sourceB126 + difference 0 4) sourceC126) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1438) := by
    have ha : (tripleCharges (sourceA126 + difference 4 0) (sourceB126 + difference 0 4) sourceC126) = raw4531 := by
      apply Matrix.ext; unfold tripleCharges sourceA126 sourceB126 sourceC126 difference raw4531; decide +kernel
    rw [ha]
    exact (canonical4531 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA126 + difference 4 1) (sourceB126 + difference 1 4) sourceC126) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2134) := by
    have ha : (tripleCharges (sourceA126 + difference 4 1) (sourceB126 + difference 1 4) sourceC126) = raw4539 := by
      apply Matrix.ext; unfold tripleCharges sourceA126 sourceB126 sourceC126 difference raw4539; decide +kernel
    rw [ha]
    exact (canonical4539 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA126 + difference 4 2) (sourceB126 + difference 2 4) sourceC126) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2134) := by
    have ha : (tripleCharges (sourceA126 + difference 4 2) (sourceB126 + difference 2 4) sourceC126) = raw4541 := by
      apply Matrix.ext; unfold tripleCharges sourceA126 sourceB126 sourceC126 difference raw4541; decide +kernel
    rw [ha]
    exact (canonical4541 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA126 + difference 4 3) (sourceB126 + difference 3 4) sourceC126) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2134) := by
    have ha : (tripleCharges (sourceA126 + difference 4 3) (sourceB126 + difference 3 4) sourceC126) = raw4542 := by
      apply Matrix.ext; unfold tripleCharges sourceA126 sourceB126 sourceC126 difference raw4542; decide +kernel
    rw [ha]
    exact (canonical4542 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA126 + difference 4 4) (sourceB126 + difference 4 4) sourceC126) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2281) := by
    have ha : (tripleCharges (sourceA126 + difference 4 4) (sourceB126 + difference 4 4) sourceC126) = raw4521 := by
      apply Matrix.ext; unfold tripleCharges sourceA126 sourceB126 sourceC126 difference raw4521; decide +kernel
    rw [ha]
    exact (canonical4521 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA126 + difference 4 5) (sourceB126 + difference 5 4) sourceC126) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2789) := by
    have ha : (tripleCharges (sourceA126 + difference 4 5) (sourceB126 + difference 5 4) sourceC126) = raw4543 := by
      apply Matrix.ext; unfold tripleCharges sourceA126 sourceB126 sourceC126 difference raw4543; decide +kernel
    rw [ha]
    exact (canonical4543 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA126 + sourceB126) sourceC126) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA126 + sourceB126) sourceC126) = raw4527 := by
      apply Matrix.ext; unfold doubleCharges sourceA126 sourceB126 sourceC126 raw4527; decide +kernel
    rw [ha]
    exact (canonical4527 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA126 sourceB126 sourceC126
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm126, Integer.Sparse.eval]
  linarith only [hs]

def sourceA127 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB127 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC127 : Charge := ![1, 0, 0, 0, 2, -3]
def sourceForm127 : Integer.Sparse Master := [(Sum.inr 1091, 1), (Sum.inr 2062, 3), (Sum.inr 2281, 1), (Sum.inr 2293, 1), (Sum.inr 4084, -1)]

theorem sourceEq127 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm127 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA127 + difference 0 4) (sourceB127 + difference 4 0) sourceC127) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2293) := by
    have ha : (tripleCharges (sourceA127 + difference 0 4) (sourceB127 + difference 4 0) sourceC127) = raw4525 := by
      apply Matrix.ext; unfold tripleCharges sourceA127 sourceB127 sourceC127 difference raw4525; decide +kernel
    rw [ha]
    exact (canonical4525 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA127 + difference 1 4) (sourceB127 + difference 4 1) sourceC127) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2062) := by
    have ha : (tripleCharges (sourceA127 + difference 1 4) (sourceB127 + difference 4 1) sourceC127) = raw4535 := by
      apply Matrix.ext; unfold tripleCharges sourceA127 sourceB127 sourceC127 difference raw4535; decide +kernel
    rw [ha]
    exact (canonical4535 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA127 + difference 2 4) (sourceB127 + difference 4 2) sourceC127) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2062) := by
    have ha : (tripleCharges (sourceA127 + difference 2 4) (sourceB127 + difference 4 2) sourceC127) = raw4544 := by
      apply Matrix.ext; unfold tripleCharges sourceA127 sourceB127 sourceC127 difference raw4544; decide +kernel
    rw [ha]
    exact (canonical4544 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA127 + difference 3 4) (sourceB127 + difference 4 3) sourceC127) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2062) := by
    have ha : (tripleCharges (sourceA127 + difference 3 4) (sourceB127 + difference 4 3) sourceC127) = raw4545 := by
      apply Matrix.ext; unfold tripleCharges sourceA127 sourceB127 sourceC127 difference raw4545; decide +kernel
    rw [ha]
    exact (canonical4545 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA127 + difference 4 4) (sourceB127 + difference 4 4) sourceC127) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2281) := by
    have ha : (tripleCharges (sourceA127 + difference 4 4) (sourceB127 + difference 4 4) sourceC127) = raw4521 := by
      apply Matrix.ext; unfold tripleCharges sourceA127 sourceB127 sourceC127 difference raw4521; decide +kernel
    rw [ha]
    exact (canonical4521 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA127 + difference 5 4) (sourceB127 + difference 4 5) sourceC127) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1091) := by
    have ha : (tripleCharges (sourceA127 + difference 5 4) (sourceB127 + difference 4 5) sourceC127) = raw4546 := by
      apply Matrix.ext; unfold tripleCharges sourceA127 sourceB127 sourceC127 difference raw4546; decide +kernel
    rw [ha]
    exact (canonical4546 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA127 + sourceB127) sourceC127) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA127 + sourceB127) sourceC127) = raw4527 := by
      apply Matrix.ext; unfold doubleCharges sourceA127 sourceB127 sourceC127 raw4527; decide +kernel
    rw [ha]
    exact (canonical4527 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA127 sourceB127 sourceC127
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm127, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
